// ==UserScript==
// @name         Network Debugger
// @name:zh-CN   网络请求拦截与调试面板
// @namespace    http://tampermonkey.net/
// @version      1.0.0
// @description  Intercept XMLHttpRequest & fetch on any page, inspect requests/responses/headers in a floating dark-theme panel with search, export, and per-field detail views.
// @description:zh-CN  拦截任意网页中的 XMLHttpRequest 与 fetch 请求，在深色悬浮面板中实时查看请求方法、状态码、URL、Query 参数、Body、请求/响应头与响应内容，支持搜索过滤、单字段弹窗、JSON 自动格式化、一键复制与导出。
// @author       -
// @match        *://*/*
// @run-at       document-start
// @grant        none
// @noframes
// @license      MIT
// @homepageURL  https://github.com/xbeeant/tampermonkey-scripts
// @supportURL   https://github.com/xbeeant/tampermonkey-scripts/issues
// @compatible   chrome
// @compatible   firefox
// @compatible   edge
// @compatible   safari
// @downloadURL https://update.greasyfork.org/scripts/601227/Network%20Debugger.user.js
// @updateURL https://update.greasyfork.org/scripts/601227/Network%20Debugger.meta.js


// ==/UserScript==


(function () {
  'use strict';

  /* ============================== 配置 ============================== */
  const MAX_RECORDS = 1000;
  const MAX_RESOURCE_RECORDS = 2000;
  const PANEL_Z = 2147483600;
  const OVERLAY_Z = 2147483640;
  const RENDER_DELAY = 50;
  const SSE_RENDER_DELAY = 250;
  const LARGE_RESP_THRESHOLD = 10240;
  const MAX_BINARY_PREVIEW = 2 * 1024 * 1024;
  const SSE_MAX_BUFFER = 512 * 1024;
  const HIGHLIGHT_MAX_BYTES = 200 * 1024;

  const DEFAULT_SLOW_THRESHOLD = 1000;
  const DEFAULT_LARGE_RES_THRESHOLD = 10240;
  const DEFAULT_RES_SLOW_THRESHOLD = 1000;
  const LS_KEY_SLOW = '__nrp_slow_threshold__';
  const LS_KEY_LARGE_RES = '__nrp_large_res_threshold__';
  const LS_KEY_RES_SLOW = '__nrp_res_slow_threshold__';
  const LS_KEY_GROUP = '__nrp_group_by__';

  const TAB_NETWORK = 'network';
  const TAB_RESOURCE = 'resource';
  const TAB_STORAGE = 'storage';
  const TAB_WS = 'websocket';

  /* 资源类型归一化与中文标签 */
  function normalizeResType(t) {
    const s = String(t || '').toLowerCase();
    if (s === 'navigation') return 'doc';
    if (s === 'script') return 'script';
    if (s === 'link' || s === 'css') return 'css';
    if (s === 'img' || s === 'image') return 'img';
    if (s === 'font') return 'font';
    if (s === 'video') return 'video';
    if (s === 'audio') return 'audio';
    if (s === 'iframe') return 'iframe';
    if (s === 'beacon') return 'beacon';
    if (!s || s === 'other') return 'other';
    return s;
  }

  const RES_TYPE_LABELS = {
    doc: 'Document', script: 'JS', css: 'CSS', img: 'Image', font: 'Font',
    video: 'Video', audio: 'Audio', iframe: 'iframe', beacon: 'Beacon', other: 'Other'
  };

  function resTypeLabel(t) {
    return RES_TYPE_LABELS[t] || t || 'Other';
  }

  const IS_TOP = (function () {
    try { return window.top === window.self; }
    catch (e) { return false; }
  })();

  /* ============================== 状态 ============================== */
  let records = [];
  let seq = 0;
  let renderTimer = null;
  let currentCopyText = '';

  let slowThreshold = (function () {
    try {
      const v = parseInt(localStorage.getItem(LS_KEY_SLOW), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_SLOW_THRESHOLD;
  })();

  let largeResThreshold = (function () {
    try {
      const v = parseInt(localStorage.getItem(LS_KEY_LARGE_RES), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_LARGE_RES_THRESHOLD;
  })();

  let resSlowThreshold = (function () {
    try {
      const v = parseInt(localStorage.getItem(LS_KEY_RES_SLOW), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_RES_SLOW_THRESHOLD;
  })();

  const VALID_GROUP_MODES = ['url', 'domain', 'status', 'method', 'kind', 'respType'];

  let groupBy = (function () {
    try {
      const v = localStorage.getItem(LS_KEY_GROUP) || '';
      if (VALID_GROUP_MODES.indexOf(v) !== -1) return v;
    } catch (e) { /* ignore */ }
    return '';
  })();

  let collapsedGroups = {};
  let isFullscreen = false;

  let currentTab = TAB_NETWORK;
  const tabState = {
    network: { search: '', groupBy: groupBy, collapsed: {} },
    resource: { search: '', groupBy: '', collapsed: {} },
    storage: { search: '' },
    websocket: { search: '' }
  };
  const resFilterState = {
    type: new Set(),
    cache: new Set(),
    quick: new Set()
  };

  let streamSeq = 0;
  const streamMap = {};
  let currentModalRecord = null;
  let currentModalExtra = null;
  let responseViewMode = 'raw'; // raw | tree
  let responseSearchTerm = '';

  /* WebSocket 支持 */
  let wsRecords = [];
  let wsSeq = 0;
  const wsMap = {};
  let wsTableWrapEl = null;

  let filterState = {
    kind: new Set(),
    method: new Set(),
    status: new Set(),
    source: new Set(),
    flags: new Set()
  };

  let rootEl = null;
  let panelEl = null;
  let tbodyEl = null;
  let netTableWrapEl = null;
  let resTableWrapEl = null;
  let netTbodyEl = null;
  let resTbodyEl = null;
  let statsEl = null;
  let searchEl = null;
  let chipsEl = null;
  let chipsResEl = null;
  let groupSelectEl = null;
  let netTabBtnEl = null;
  let resTabBtnEl = null;
  let slowInputEl = null;
  let fsBtn = null;
  let copyBtn = null;

  /* 统一模态框句柄（替代原 overlayEl / modalEl） */
  let netModal = null;
  let storeAddModal = null;
  let storeViewModal = null;

  /* 以下变量指向模态框内部节点，保持原渲染函数兼容 */
  let overlayEl = null;       /* = netModal.overlay（兼容别名） */
  let modalContentEl = null;  /* = netModal.body（兼容别名） */
  let modalHeadlineEl = null; /* = netModal.titleEl（兼容别名） */
  let modalParamsEl = null;
  let modalHeadersEl = null;
  let modalResponseEl = null;
  let modalPreviewEl = null;
  let modalBodyEl = null;

  /* ---------------- Tab：存储 ---------------- */
  let storeTabBtnEl = null;
  let storeWrapEl = null;
  let storeTabsEl = null;
  let storeToolsEl = null;
  let storeTableWrapEl = null;
  let groupWrapEl = null;
  let clearBtnEl = null;
  let exportBtnEl = null;
  let storeSubTab = 'local';
  const STORE_SUB_LABELS = { cookie: 'Cookies', local: 'LocalStorage', session: 'SessionStorage' };

  /* Storage 新增条目模态框内部节点 */
  let storeAddOverlayEl = null; /* = storeAddModal.overlay */
  let storeAddTitleEl = null;
  let storeAddKeyEl = null;
  let storeAddValueEl = null;
  let storeAddSaveEl = null;

  /* Storage 查看模态框内部节点 */
  let storeViewOverlayEl = null; /* = storeViewModal.overlay */
  let storeViewTitleEl = null;
  let storeViewKeyEl = null;
  let storeViewValueEl = null;
  let storeViewSaveEl = null;
  let storeViewHlEl = null;
  let storeViewPreColEl = null;
  let storeViewTabsEl = null;
  let storeViewTab = 'edit';
  let storeViewEntry = null;
  let wsTabBtnEl = null;

  /* ============================ 通用小工具 ============================ */

  function clearEl(el) {
    if (!el) return;
    while (el.firstChild) el.removeChild(el.firstChild);
  }

  function showEl(el) {
    if (el) el.style.display = '';
  }

  function hideEl(el) {
    if (el) el.style.display = 'none';
  }

  function clearAndHide(el) {
    if (!el) return;
    clearEl(el);
    el.style.display = 'none';
  }

  function clearAndShow(el) {
    if (!el) return;
    clearEl(el);
    el.style.display = '';
  }

  function addClass(el, cls) {
    if (el && cls) el.classList.add(cls);
  }

  function removeClass(el, cls) {
    if (el && cls) el.classList.remove(cls);
  }

  function openNetworkModal() {
    if (copyBtn) copyBtn.textContent = 'Copy';
    if (netModal) netModal.open();
  }

  function openNetworkModalWithCopy(text) {
    if (copyBtn) copyBtn.textContent = 'Copy';
    currentCopyText = text != null ? text : currentCopyText;
    if (netModal) netModal.open();
  }

  function prettyJSONText(v) {
    try { return JSON.stringify(JSON.parse(v), null, 2); } catch (e) { return v; }
  }

  function makeTabButton(label, countId, title, active) {
    return h('button', {
      class: 'nrp-tab' + (active ? ' nrp-tab-active' : ''),
      type: 'button',
      title: title
    }, [label, h('span', { class: 'nrp-tab-count', id: countId }, '0')]);
  }

  function absUrl(u) {
    try { return new URL(String(u), location.href).href; }
    catch (e) { return String(u); }
  }

  function bodyToString(b) {
    if (b == null) return '';
    try {
      if (typeof b === 'string') return b;
      if (typeof URLSearchParams !== 'undefined' && b instanceof URLSearchParams) return b.toString();
      if (typeof FormData !== 'undefined' && b instanceof FormData) {
        const out = [];
        b.forEach(function (v, k) {
          if (typeof v === 'string') out.push(k + '=' + v);
          else if (v && typeof v === 'object' && 'name' in v && 'size' in v) out.push(k + '=[File ' + v.name + ', ' + v.size + ' bytes]');
          else out.push(k + '=' + String(v));
        });
        return out.join('&');
      }
      if (typeof Blob !== 'undefined' && b instanceof Blob) {
        return '[Blob ' + b.size + ' bytes, type=' + (b.type || 'unknown') + ']';
      }
      if (typeof ArrayBuffer !== 'undefined' &&
          (b instanceof ArrayBuffer || ArrayBuffer.isView(b))) {
        return '[binary ' + (b.byteLength != null ? b.byteLength : b.length) + ' bytes]';
      }
      if (typeof b === 'object') {
        try { return JSON.stringify(b); } catch (e) { return String(b); }
      }
      return String(b);
    } catch (e) {
      return String(b);
    }
  }

  function extractQuery(url) {
    try {
      const u = new URL(String(url), location.href);
      if (u.search && u.search.length > 1) {
        const arr = [];
        u.searchParams.forEach(function (v, k) { arr.push(k + '=' + v); });
        return arr.join('&');
      }
    } catch (e) { /* ignore */ }
    return '';
  }

  function headersToString(h) {
    if (!h) return '';
    try {
      const lines = [];

      if (Array.isArray(h)) {
        h.forEach(function (pair) {
          if (Array.isArray(pair) && pair.length >= 2) {
            lines.push(String(pair[0]) + ': ' + String(pair[1]));
          }
        });
        return lines.join('\n');
      }

      if (typeof h.entries === 'function') {
        try {
          const it = h.entries();
          let step = it.next();
          while (!step.done) {
            const pair = step.value;
            if (Array.isArray(pair) && pair.length >= 2) {
              lines.push(String(pair[0]) + ': ' + String(pair[1]));
            }
            step = it.next();
          }
        } catch (e) { /* ignore */ }
      } else if (typeof h.forEach === 'function' && typeof h.get === 'function') {
        try {
          h.forEach(function (v, k) { lines.push(String(k) + ': ' + String(v)); });
        } catch (e) { /* ignore */ }
      }

      if (lines.length) return lines.join('\n');

      if (typeof Headers !== 'undefined' && h instanceof Headers) {
        h.forEach(function (v, k) { lines.push(k + ': ' + v); });
      } else if (typeof h === 'object') {
        Object.keys(h).forEach(function (k) { lines.push(k + ': ' + String(h[k])); });
      } else {
        lines.push(String(h));
      }
      return lines.join('\n');
    } catch (e) {
      return '';
    }
  }

  function isJSONString(s) {
    if (!s) return false;
    try { JSON.parse(s); return true; } catch (e) { return false; }
  }

  function escapeHTML(s) {
    return String(s).replace(/[&<>]/g, function (c) {
      return c === '&' ? '&amp;' : c === '<' ? '&lt;' : '&gt;';
    });
  }

  function highlightJSON(json) {
    const esc = escapeHTML(json);
    return esc.replace(
        /("(?:\\.|[^"\\])*")(\s*:)?|\b(true|false|null)\b|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/g,
        function (match, str, colon, lit) {
          if (str != null) {
            if (colon) return '<span class="nrp-hl-key">' + str + '</span>' + colon;
            return '<span class="nrp-hl-str">' + str + '</span>';
          }
          if (lit != null) {
            const cls = lit === 'null' ? 'nrp-hl-null' : 'nrp-hl-bool';
            return '<span class="' + cls + '">' + lit + '</span>';
          }
          return '<span class="nrp-hl-num">' + match + '</span>';
        }
    );
  }

  function rawHeadersToLines(raw) {
    if (!raw) return '';
    const out = [];
    raw.split(/\r?\n/).forEach(function (line) {
      const s = line.trim();
      if (!s) return;
      const idx = s.indexOf(':');
      if (idx === -1) out.push(s);
      else out.push(s.slice(0, idx).trim() + ': ' + s.slice(idx + 1).trim());
    });
    return out.join('\n');
  }

  function statusBucket(status) {
    if (status >= 200 && status < 300) return '2xx';
    if (status >= 300 && status < 400) return '3xx';
    if (status >= 400 && status < 500) return '4xx';
    if (status >= 500 && status < 600) return '5xx';
    return 'err';
  }

  function statusInfo(r) {
    const s = r.status;
    if (s >= 200 && s < 300) return { text: String(s), cls: 'nrp-st-ok' };
    if (s) return { text: String(s), cls: s >= 400 ? 'nrp-st-err' : 'nrp-st-other' };
    if (r.responseKind === 'sse') return { text: 'SSE', cls: 'nrp-st-other' };
    return { text: 'ERR', cls: 'nrp-st-err' };
  }

  function isErrorRec(r) {
    return r.status === 0 || r.status >= 400;
  }

  function respSize(r) {
    if (!r.response) return 0;
    return r.response.length;
  }

  function matchRecord(r, terms) {
    if (filterState.kind.size) {
      const kindOk = filterState.kind.has(r.kind) ||
          (filterState.kind.has('sse') && r.responseKind === 'sse');
      if (!kindOk) return false;
    }
    if (filterState.method.size && !filterState.method.has(r.method)) return false;
    if (filterState.status.size) {
      const b = statusBucket(r.status);
      if (!filterState.status.has(b)) return false;
    }
    if (filterState.source.size) {
      const src = r.frameUrl ? 'iframe' : 'top';
      if (!filterState.source.has(src)) return false;
    }
    if (filterState.flags.size) {
      for (const flag of filterState.flags) {
        if (flag === 'slow' && !(r.duration != null && r.duration >= slowThreshold)) return false;
        if (flag === 'hasBody' && !r.body) return false;
        if (flag === 'hasParams' && !r.params) return false;
        if (flag === 'largeResp' && !(respSize(r) >= LARGE_RESP_THRESHOLD)) return false;
        if (flag === 'error' && !isErrorRec(r)) return false;
      }
    }

    if (!terms.length) return true;

    const hay = (
        r.method + ' ' + r.url + ' ' + (r.params || '') + ' ' + (r.body || '') + ' ' +
        (r.reqHeaders || '') + ' ' + (r.respHeaders || '') + ' ' +
        (r.status == null ? '' : r.status) + ' ' +
        (r.response || '').slice(0, 5000) + ' ' +
        (r.frameUrl || '') + ' ' + (r.mimeType || '')
    ).toLowerCase();
    for (let i = 0; i < terms.length; i++) {
      if (hay.indexOf(terms[i]) === -1) return false;
    }
    return true;
  }

  function pad(n, len) {
    let s = String(n);
    while (s.length < len) s = '0' + s;
    return s;
  }

  function formatTime(ts) {
    const d = new Date(ts);
    return pad(d.getHours(), 2) + ':' + pad(d.getMinutes(), 2) + ':' +
        pad(d.getSeconds(), 2) + '.' + pad(d.getMilliseconds(), 3);
  }

  function formatFullTime(ts) {
    const d = new Date(ts);
    return d.getFullYear() + '-' + pad(d.getMonth() + 1, 2) + '-' + pad(d.getDate(), 2) + ' ' +
        pad(d.getHours(), 2) + ':' + pad(d.getMinutes(), 2) + ':' + pad(d.getSeconds(), 2) + '.' +
        pad(d.getMilliseconds(), 3);
  }

  function formatDuration(ms) {
    if (ms == null) return '';
    if (ms < 1000) return ms + 'ms';
    return (ms / 1000).toFixed(2) + 's';
  }

  function formatSize(bytes) {
    if (bytes == null) return '';
    if (bytes < 1024) return bytes + ' B';
    if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
    return (bytes / (1024 * 1024)).toFixed(2) + ' MB';
  }

  function extractContentType(respHeaders) {
    if (!respHeaders) return '';
    const lines = respHeaders.split('\n');
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const idx = line.indexOf(':');
      if (idx === -1) continue;
      if (line.slice(0, idx).trim().toLowerCase() === 'content-type') {
        return line.slice(idx + 1).trim();
      }
    }
    return '';
  }

  function isImageMime(mime) {
    return /^image\//i.test(mime || '');
  }

  function isSseMime(mime) {
    return /^text\/event-stream/i.test((mime || '').split(';')[0].trim());
  }

  function countSseEvents(text) {
    if (!text) return 0;
    let n = 0;
    text.split('\n').forEach(function (line) {
      if (/^data:/i.test(line.trim())) n++;
    });
    return n;
  }

  function isTextMime(mime) {
    if (!mime) return true;
    const m = mime.toLowerCase();
    if (m.indexOf('image/') === 0) return false;
    if (m.indexOf('audio/') === 0 || m.indexOf('video/') === 0) return false;
    if (m.indexOf('application/octet-stream') === 0) return false;
    if (m.indexOf('application/pdf') === 0) return false;
    if (m.indexOf('application/zip') === 0) return false;
    if (m.indexOf('font/') === 0) return false;
    if (m.indexOf('application/wasm') === 0) return false;
    return true;
  }

  function arrayBufferToBase64(buf) {
    let binary = '';
    const bytes = new Uint8Array(buf);
    const chunk = 0x8000;
    for (let i = 0; i < bytes.length; i += chunk) {
      binary += String.fromCharCode.apply(null, bytes.subarray(i, i + chunk));
    }
    return btoa(binary);
  }

  /* ============================ 分组键提取 ============================ */

  function getGroupKey(r, mode) {
    if (mode === 'url') {
      try {
        const u = new URL(r.url);
        return (u.origin || '') + (u.pathname || '/');
      } catch (e) { return r.url || '(unknown)'; }
    }
    if (mode === 'domain') {
      try { return new URL(r.url).host || '(unknown)'; }
      catch (e) { return '(unknown)'; }
    }
    if (mode === 'status') {
      const b = statusBucket(r.status);
      if (r.status) return r.status + ' ' + b;
      return 'ERR';
    }
    if (mode === 'method') return r.method || '(unknown)';
    if (mode === 'kind') {
      if (r.kind === 'sse') return 'SSE';
      return r.kind === 'fetch' ? 'fetch' : 'XHR';
    }
    if (mode === 'respType') {
      if (r.responseKind === 'sse') return 'SSE';
      if (r.responseKind === 'image') return '图片';
      if (r.responseKind === 'binary') return '二进制';
      const mime = (r.mimeType || '').toLowerCase();
      if (mime.indexOf('json') !== -1) return 'JSON';
      if (mime.indexOf('xml') !== -1) return 'XML';
      if (mime.indexOf('html') !== -1) return 'HTML';
      if (mime.indexOf('css') !== -1) return 'CSS';
      if (mime.indexOf('javascript') !== -1 || mime.indexOf('ecmascript') !== -1) return 'JS';
      return '文本';
    }
    if (mode === 'resType') return resTypeLabel(r.resType);
    if (mode === 'resSize') {
      const s = r.size || 0;
      if (s <= 0) return '缓存/未知';
      if (s < 1024) return '< 1 KB';
      if (s < 10 * 1024) return '1 – 10 KB';
      if (s < 100 * 1024) return '10 – 100 KB';
      if (s < 1024 * 1024) return '100 KB – 1 MB';
      return '≥ 1 MB';
    }
    if (mode === 'resCache') {
      return r.cache === 'cache' ? '缓存' : (r.cache === 'network' ? '网络' : '未知');
    }
    return '';
  }

  /* ========================== 记录入列 ========================== */

  const MSG_TAG = '__NRP_RECORD__';
  const MSG_TAG_UPDATE = '__NRP_UPDATE__';

  function nextStreamId() {
    return 's' + (++streamSeq) + '-' + Date.now().toString(36) + '-' +
        Math.random().toString(36).slice(2, 8);
  }

  function pushRecord(rec) {
    rec.id = ++seq;
    if (!rec.time) rec.time = Date.now();
    if (!rec.frameUrl && !IS_TOP) {
      try { rec.frameUrl = location.href; } catch (e) { rec.frameUrl = ''; }
    }
    if (rec.streamId) streamMap[rec.streamId] = rec;
    records.push(rec);

    const cap = rec.kind === 'resource' ? MAX_RESOURCE_RECORDS : MAX_RECORDS;
    const wantRes = rec.kind === 'resource';
    let count = 0;
    for (let i = records.length - 1; i >= 0; i--) {
      if ((records[i].kind === 'resource') !== wantRes) continue;
      count++;
      if (count > cap) {
        const removed = records.splice(i, 1)[0];
        if (removed && removed.streamId) delete streamMap[removed.streamId];
        break;
      }
    }
    scheduleRender();
  }

  function updateRecord(streamId, patch) {
    if (!streamId || !patch) return;
    if (IS_TOP) {
      const rec = streamMap[streamId];
      if (!rec) return;
      for (const k in patch) {
        if (Object.prototype.hasOwnProperty.call(patch, k)) rec[k] = patch[k];
      }
      refreshStreamModal(rec);
      scheduleRender(SSE_RENDER_DELAY);
      return;
    }
    try {
      window.top.postMessage({ tag: MSG_TAG_UPDATE, streamId: streamId, patch: patch }, '*');
    } catch (e) { /* ignore */ }
  }

  function addRecord(rec) {
    if (IS_TOP) {
      pushRecord(rec);
    } else {
      try {
        rec.frameUrl = location.href;
        window.top.postMessage({ tag: MSG_TAG, record: rec }, '*');
      } catch (e) {
        pushRecord(rec);
      }
    }
  }

  function installMessageListener() {
    if (!IS_TOP) return;
    window.addEventListener('message', function (ev) {
      try {
        const data = ev.data;
        if (!data) return;
        if (data.tag === MSG_TAG && data.record) {
          pushRecord(data.record);
        } else if (data.tag === MSG_TAG_UPDATE && data.streamId) {
          updateRecord(data.streamId, data.patch);
        }
      } catch (e) { /* ignore */ }
    }, false);
  }

  /* ========================== SSE 流式读取 ========================== */

  function readSseStream(res, base, bodyPromise) {
    const streamId = nextStreamId();

    const rec = {
      kind: base.kind || 'fetch',
      method: base.method,
      url: base.url,
      params: base.params,
      body: '',
      reqHeaders: base.reqHeaders,
      respHeaders: base.respHeaders,
      status: base.status,
      response: '',
      responseKind: 'sse',
      mimeType: base.mimeType,
      binarySize: 0,
      previewUrl: '',
      duration: base.duration,
      time: base.time,
      streamId: streamId,
      sseEvents: 0,
      sseDone: false,
      sseTruncated: false
    };
    addRecord(rec);

    if (bodyPromise && typeof bodyPromise.then === 'function') {
      bodyPromise.then(function (b) { updateRecord(streamId, { body: b }); }, function () {});
    }

    function tailNote() {
      return truncated ? '\n\n…[buffer 超限，仅保留最后 ' + formatSize(SSE_MAX_BUFFER) + ']' : '';
    }

    let reader;
    try {
      reader = res.clone().body.getReader();
    } catch (e) {
      updateRecord(streamId, { response: '[unable to read SSE stream]', sseDone: true });
      return;
    }

    const decoder = new TextDecoder('utf-8');
    let acc = '';
    let truncated = false;
    let finished = false;

    function push() {
      updateRecord(streamId, {
        response: acc + tailNote(),
        sseEvents: countSseEvents(acc),
        sseTruncated: truncated
      });
    }

    function finish(note) {
      if (finished) return;
      finished = true;
      updateRecord(streamId, {
        response: acc + tailNote() + (note ? '\n\n' + note : ''),
        sseEvents: countSseEvents(acc),
        sseTruncated: truncated,
        sseDone: true
      });
    }

    function pump() {
      reader.read().then(function (result) {
        if (result.done) { finish('[stream closed]'); return; }
        const chunk = result.value;
        if (chunk) {
          try { acc += decoder.decode(chunk, { stream: true }); }
          catch (e) { acc += String(chunk); }
          if (acc.length > SSE_MAX_BUFFER) {
            acc = acc.slice(acc.length - SSE_MAX_BUFFER);
            truncated = true;
          }
        }
        push();
        pump();
      }, function (err) {
        finish('[stream error] ' + (err && err.message ? err.message : ''));
      });
    }

    pump();
  }

  /* ---------------- EventSource 拦截 ---------------- */

  function instrumentEventSource(es, url) {
    const streamId = nextStreamId();
    const startTime = Date.now();
    const finalUrl = absUrl(String(url));

    let acc = '';
    let done = false;
    let truncated = false;

    function tailNote() {
      return truncated ? '\n\n…[buffer 超限，仅保留最后 ' + formatSize(SSE_MAX_BUFFER) + ']' : '';
    }

    function push(extra) {
      updateRecord(streamId, {
        response: acc + tailNote() + (extra ? '\n\n' + extra : ''),
        sseEvents: countSseEvents(acc),
        sseTruncated: truncated,
        sseDone: done
      });
    }

    function append(text) {
      acc += text;
      if (acc.length > SSE_MAX_BUFFER) {
        acc = acc.slice(acc.length - SSE_MAX_BUFFER);
        truncated = true;
      }
    }

    addRecord({
      kind: 'sse', method: 'GET', url: finalUrl,
      params: extractQuery(finalUrl), body: '',
      reqHeaders: 'Accept: text/event-stream', respHeaders: '',
      status: 0, response: '', responseKind: 'sse',
      mimeType: 'text/event-stream', binarySize: 0,
      duration: null, time: startTime,
      streamId: streamId, sseEvents: 0, sseDone: false, sseTruncated: false
    });

    es.addEventListener('open', function () {
      updateRecord(streamId, { status: 200, duration: Date.now() - startTime });
    });

    es.addEventListener('message', function (ev) {
      const lines = [];
      if (ev.lastEventId) lines.push('id: ' + ev.lastEventId);
      if (ev.type && ev.type !== 'message') lines.push('event: ' + ev.type);
      String(ev.data == null ? '' : ev.data).split('\n').forEach(function (l) {
        lines.push('data: ' + l);
      });
      append(lines.join('\n') + '\n\n');
      push();
    });

    es.addEventListener('error', function () {
      if (es.readyState === 2) { done = true; push('[connection closed]'); }
      else push('[error, readyState=' + es.readyState + ']');
    });

    try {
      const origClose = es.close;
      es.close = function () {
        done = true;
        push('[closed by page]');
        return origClose.apply(this, arguments);
      };
    } catch (e) { /* ignore */ }
  }

  /* ========================== 静态资源采集 ========================== */

  const seenResourceKeys = new Set();

  function navStartTime() {
    if (performance && performance.timeOrigin != null) return performance.timeOrigin;
    if (performance && performance.timing && performance.timing.navigationStart) {
      return performance.timing.navigationStart;
    }
    return Date.now();
  }

  function resourceTimingBreakdown(e) {
    function seg(a, b) {
      const v = e[b] - e[a];
      return isFinite(v) && v > 0 ? v : 0;
    }
    return {
      blocked: seg('startTime', 'requestStart'),
      dns: seg('domainLookupStart', 'domainLookupEnd'),
      tcp: seg('connectStart', 'connectEnd'),
      ttfb: seg('requestStart', 'responseStart'),
      download: seg('responseStart', 'responseEnd'),
      total: e.duration || 0
    };
  }

  function resourceCacheState(e) {
    const transfer = e.transferSize || 0;
    const encoded = e.encodedBodySize || 0;
    if (transfer > 0) return 'network';
    if (encoded > 0) return 'cache';
    return 'unknown';
  }

  function addResourceRecord(e) {
    const type = normalizeResType(e.initiatorType);
    if (type === 'fetch' || type === 'xhr') return;

    const key = e.name + '|' + e.startTime;
    if (seenResourceKeys.has(key)) return;
    seenResourceKeys.add(key);

    addRecord({
      kind: 'resource', method: 'GET', url: e.name,
      params: '', body: '', reqHeaders: '', respHeaders: '',
      status: 0, response: '', responseKind: 'resource',
      mimeType: '', initiatorType: e.initiatorType || '',
      resType: type, size: e.transferSize || 0,
      encodedSize: e.encodedBodySize || 0,
      decodedSize: e.decodedBodySize || 0,
      cache: resourceCacheState(e),
      protocol: e.nextHopProtocol || '',
      duration: e.duration || 0,
      timing: resourceTimingBreakdown(e),
      time: navStartTime() + (e.startTime || 0)
    });
  }

  function installResourceObserver() {
    if (typeof PerformanceObserver !== 'function' || !performance) return;
    try {
      const obs = new PerformanceObserver(function (list) {
        const entries = list.getEntries();
        for (let i = 0; i < entries.length; i++) {
          try { addResourceRecord(entries[i]); } catch (e) { /* ignore */ }
        }
      });
      obs.observe({ type: 'resource', buffered: true });
    } catch (e) { /* ignore */ }
  }


  /* ========================== WebSocket 拦截 ========================== */

  function addWsRecord(rec) {
    rec.id = 'ws' + (++wsSeq);
    if (!rec.time) rec.time = Date.now();
    if (!rec.frameUrl && !IS_TOP) {
      try { rec.frameUrl = location.href; } catch (e) { rec.frameUrl = ''; }
    }
    wsRecords.push(rec);
    if (wsRecords.length > 1000) wsRecords.splice(0, wsRecords.length - 1000);
    scheduleRender();
  }

  function updateWsRecord(wsId, patch) {
    const rec = wsMap[wsId];
    if (!rec) return;
    for (const k in patch) {
      if (Object.prototype.hasOwnProperty.call(patch, k)) rec[k] = patch[k];
    }
    scheduleRender();
  }

  function installWebSocketInterceptor() {
    if (typeof WebSocket === 'undefined') return;
    if (WebSocket.__nrpWsPatched) return;
    const OrigWS = WebSocket;
    function PatchedWS(url, protocols) {
      const ws = protocols !== undefined ? new OrigWS(url, protocols) : new OrigWS(url);
      const wsId = 'ws' + (++wsSeq) + '-' + Date.now().toString(36);
      const start = Date.now();
      const finalUrl = absUrl(url);
      const rec = {
        id: wsId,
        kind: 'ws',
        url: finalUrl,
        time: start,
        state: 'connecting',
        messages: []
      };
      wsMap[wsId] = rec;
      addWsRecord(rec);

      try {
        ws.addEventListener('open', function () {
          updateWsRecord(wsId, { state: 'open', openTime: Date.now() - start });
        });
      } catch (e) {}
      try {
        ws.addEventListener('close', function (ev) {
          updateWsRecord(wsId, { state: 'closed', closeTime: Date.now() - start, closeCode: ev.code, closeReason: ev.reason });
        });
      } catch (e) {}
      try {
        ws.addEventListener('error', function () {
          updateWsRecord(wsId, { state: 'error' });
        });
      } catch (e) {}
      try {
        ws.addEventListener('message', function (ev) {
          let data = ev.data;
          if (data instanceof Blob) {
            data = '[Blob ' + data.size + ' bytes]';
          } else if (data instanceof ArrayBuffer) {
            data = '[ArrayBuffer ' + data.byteLength + ' bytes]';
          } else {
            data = String(data);
          }
          const rec = wsMap[wsId];
          if (rec) {
            if (!rec.messages) rec.messages = [];
            rec.messages.push({ dir: 'in', data: data, time: Date.now() });
            if (rec.messages.length > 500) rec.messages.splice(0, rec.messages.length - 500);
            updateWsRecord(wsId, { messages: rec.messages });
          }
        });
      } catch (e) {}

      const origSend = ws.send;
      try {
        ws.send = function (data) {
          try {
            let out = data;
            if (out instanceof Blob) out = '[Blob ' + out.size + ' bytes]';
            else if (out instanceof ArrayBuffer) out = '[ArrayBuffer ' + out.byteLength + ' bytes]';
            else out = String(out);
            const rec = wsMap[wsId];
            if (rec) {
              if (!rec.messages) rec.messages = [];
              rec.messages.push({ dir: 'out', data: out, time: Date.now() });
              if (rec.messages.length > 500) rec.messages.splice(0, rec.messages.length - 500);
              updateWsRecord(wsId, { messages: rec.messages });
            }
          } catch (e) {}
          return origSend.apply(this, arguments);
        };
      } catch (e) {}

      return ws;
    }
    PatchedWS.prototype = OrigWS.prototype;
    PatchedWS.CONNECTING = OrigWS.CONNECTING;
    PatchedWS.OPEN = OrigWS.OPEN;
    PatchedWS.CLOSING = OrigWS.CLOSING;
    PatchedWS.CLOSED = OrigWS.CLOSED;
    PatchedWS.__nrpWsPatched = true;
    try { window.WebSocket = PatchedWS; } catch (e) {}
  }

  /* ========================== 请求拦截 ========================== */

  function installInterceptors() {
    /* ---------------- XMLHttpRequest ---------------- */
    const XHRProto = window.XMLHttpRequest && window.XMLHttpRequest.prototype;
    if (XHRProto && !XHRProto.__nrpPatched) {
      XHRProto.__nrpPatched = true;

      const origOpen = XHRProto.open;
      const origSend = XHRProto.send;
      const origSetHeader = XHRProto.setRequestHeader;

      XHRProto.open = function (method, url) {
        try {
          this.__nrpMeta = {
            method: String(method || 'GET').toUpperCase(),
            url: String(url == null ? '' : url),
            bodyStr: '', reqHeaders: [], startTime: 0
          };
        } catch (e) { /* ignore */ }
        return origOpen.apply(this, arguments);
      };

      if (typeof origSetHeader === 'function') {
        XHRProto.setRequestHeader = function (name, value) {
          try {
            if (this.__nrpMeta && this.__nrpMeta.reqHeaders) {
              this.__nrpMeta.reqHeaders.push([String(name), String(value)]);
            }
          } catch (e) { /* ignore */ }
          return origSetHeader.apply(this, arguments);
        };
      }

      XHRProto.send = function (body) {
        const xhr = this;
        const meta = xhr.__nrpMeta || { method: 'GET', url: '', bodyStr: '', reqHeaders: [], startTime: 0 };

        try { meta.bodyStr = bodyToString(body); }
        catch (e) { meta.bodyStr = '[unreadable body]'; }

        meta.startTime = Date.now();

        try {
          xhr.addEventListener('readystatechange', function () {
            try {
              if (xhr.readyState < 2) return;
              const sseHeaders = rawHeadersToLines(xhr.getAllResponseHeaders());
              const sseMime = extractContentType(sseHeaders);
              if (!isSseMime(sseMime)) return;

              if (!meta.streamId) meta.streamId = nextStreamId();

              let txt = '';
              try { txt = xhr.responseText || ''; } catch (e) { txt = ''; }

              if (!meta.sseRecorded) {
                meta.sseRecorded = true;
                addRecord({
                  kind: 'xhr', method: meta.method, url: absUrl(meta.url),
                  params: extractQuery(meta.url), body: meta.bodyStr,
                  reqHeaders: headersToString(meta.reqHeaders),
                  respHeaders: sseHeaders, status: xhr.status,
                  response: txt, responseKind: 'sse',
                  mimeType: sseMime, binarySize: 0,
                  duration: null, time: meta.startTime || Date.now(),
                  streamId: meta.streamId, sseDone: false,
                  sseEvents: countSseEvents(txt)
                });
              } else {
                updateRecord(meta.streamId, {
                  response: txt, respHeaders: sseHeaders,
                  sseEvents: countSseEvents(txt), status: xhr.status || 0
                });
              }
            } catch (e) { /* ignore */ }
          });
        } catch (e) { /* ignore */ }

        try {
          xhr.addEventListener('loadend', function () {
            const endTime = Date.now();
            const duration = meta.startTime ? (endTime - meta.startTime) : null;

            const rt = xhr.responseType || '';
            let respHeaders = '';
            try { respHeaders = rawHeadersToLines(xhr.getAllResponseHeaders()); } catch (e) {}

            const mime = extractContentType(respHeaders);

            let text = '';
            let responseKind = 'text';
            let binarySize = 0;

            try {
              if (rt === '' || rt === 'text') {
                text = xhr.responseText || '';
              } else if (rt === 'json') {
                text = xhr.response == null ? '' : JSON.stringify(xhr.response);
              } else if (rt === 'document') {
                text = xhr.responseXML ? new XMLSerializer().serializeToString(xhr.responseXML) : '';
              } else if (rt === 'blob') {
                const blob = xhr.response;
                if (blob) {
                  binarySize = blob.size;
                  responseKind = isImageMime(blob.type || mime) ? 'image' : 'binary';
                  text = '[Blob ' + formatSize(blob.size) + ', type=' + (blob.type || mime || 'unknown') + ']';
                }
              } else if (rt === 'arraybuffer') {
                const buf = xhr.response;
                if (buf) {
                  binarySize = buf.byteLength;
                  responseKind = isImageMime(mime) ? 'image' : 'binary';
                  if (isTextMime(mime) && buf.byteLength <= MAX_BINARY_PREVIEW) {
                    try {
                      text = new TextDecoder('utf-8').decode(buf);
                      responseKind = 'text';
                    } catch (e) {
                      text = '[ArrayBuffer ' + formatSize(buf.byteLength) + ', type=' + (mime || 'unknown') + ']';
                    }
                  } else {
                    text = '[ArrayBuffer ' + formatSize(buf.byteLength) + ', type=' + (mime || 'unknown') + ']';
                  }
                }
              } else {
                text = '[binary response: ' + rt + ']';
                responseKind = 'binary';
              }
            } catch (e) {
              text = '[unreadable response]';
            }

            if (meta.sseRecorded) {
              let sseText = '';
              try { sseText = xhr.responseText || ''; } catch (e) {}
              updateRecord(meta.streamId, {
                status: xhr.status, response: sseText, respHeaders: respHeaders,
                sseEvents: countSseEvents(sseText), sseDone: true, duration: duration
              });
              return;
            }

            addRecord({
              kind: 'xhr', method: meta.method, url: absUrl(meta.url),
              params: extractQuery(meta.url), body: meta.bodyStr,
              reqHeaders: headersToString(meta.reqHeaders),
              respHeaders: respHeaders, status: xhr.status,
              response: text, responseKind: responseKind,
              mimeType: mime, binarySize: binarySize,
              duration: duration, time: meta.startTime || Date.now()
            });
          }, { once: true });
        } catch (e) { /* ignore */ }

        return origSend.apply(this, arguments);
      };
    }

    /* ---------------- fetch ---------------- */
    const nativeFetch = window.fetch;
    if (typeof nativeFetch === 'function' && !nativeFetch.__nrpPatched) {
      const patched = function (input, init) {
        let method = 'GET';
        let url = '';
        let bodyPromise = Promise.resolve('');
        let reqHeadersStr = '';

        try {
          const isRequest = typeof Request !== 'undefined' && input instanceof Request;

          if (typeof input === 'string') url = input;
          else if (input && typeof input === 'object' && input.url) url = String(input.url);
          else url = String(input);

          if (init && init.method) method = String(init.method);
          else if (input && typeof input === 'object' && input.method) method = String(input.method);

          if (init && init.headers != null) {
            reqHeadersStr = headersToString(init.headers);
          } else if (isRequest && input.headers) {
            try { reqHeadersStr = headersToString(input.headers); } catch (e) {}
          }

          if (init && init.body != null) {
            bodyPromise = Promise.resolve(bodyToString(init.body));
          } else if (isRequest && input.body != null) {
            try {
              if (typeof input.clone === 'function' && !input.bodyUsed) {
                const cloned = input.clone();
                bodyPromise = cloned.text().then(function (t) { return t; }, function () { return '[unreadable body]'; });
              } else if (typeof input.text === 'function') {
                bodyPromise = input.text().then(function (t) { return t; }, function () { return '[unreadable body]'; });
              } else {
                bodyPromise = Promise.resolve('[stream body]');
              }
            } catch (e) { bodyPromise = Promise.resolve('[unreadable body]'); }
          } else if (!isRequest && input && typeof input === 'object' && input.body != null) {
            try { bodyPromise = Promise.resolve(bodyToString(input.body)); }
            catch (e) { bodyPromise = Promise.resolve('[unreadable body]'); }
          }
        } catch (e) {
          bodyPromise = Promise.resolve('[unreadable body]');
        }

        const finalUrl = absUrl(url);
        const upperMethod = String(method).toUpperCase();
        const reqTime = Date.now();
        const queryStr = extractQuery(url);

        const promise = nativeFetch.apply(this, arguments);

        return promise.then(function (res) {
          const endTime = Date.now();
          const duration = endTime - reqTime;

          let respHeadersStr = '';
          try { respHeadersStr = headersToString(res.headers); } catch (e) {}

          const mime = (res.headers && res.headers.get) ? (res.headers.get('content-type') || '') : extractContentType(respHeadersStr);

          if (isSseMime(mime) && res.body && typeof res.body.getReader === 'function') {
            readSseStream(res, {
              kind: 'fetch', method: upperMethod, url: finalUrl, params: queryStr,
              reqHeaders: reqHeadersStr, respHeaders: respHeadersStr,
              status: res.status, mimeType: mime, duration: duration, time: reqTime
            }, bodyPromise);
            return res;
          }

          const isImg = isImageMime(mime);
          const isText = isTextMime(mime);

          function finalize(responseText, responseKind, binarySize, previewUrl) {
            bodyPromise.then(function (bodyStr) {
              addRecord({
                kind: 'fetch', method: upperMethod, url: finalUrl, params: queryStr,
                body: bodyStr, reqHeaders: reqHeadersStr, respHeaders: respHeadersStr,
                status: res.status, response: responseText, responseKind: responseKind,
                mimeType: mime, binarySize: binarySize, previewUrl: previewUrl || '',
                duration: duration, time: reqTime
              });
            }).catch(function () {
              addRecord({
                kind: 'fetch', method: upperMethod, url: finalUrl, params: queryStr,
                body: '', reqHeaders: reqHeadersStr, respHeaders: respHeadersStr,
                status: res.status, response: responseText, responseKind: responseKind,
                mimeType: mime, binarySize: binarySize, previewUrl: previewUrl || '',
                duration: duration, time: reqTime
              });
            });
          }

          try {
            if (isImg) {
              const clone = res.clone();
              clone.arrayBuffer().then(function (buf) {
                let previewUrl = '';
                let text = '[Image ' + formatSize(buf.byteLength) + ', type=' + (mime || 'unknown') + ']';
                if (buf.byteLength <= MAX_BINARY_PREVIEW) {
                  try {
                    const b64 = arrayBufferToBase64(buf);
                    const type = (mime || 'image/png').split(';')[0].trim();
                    previewUrl = 'data:' + type + ';base64,' + b64;
                  } catch (e) {}
                }
                finalize(text, 'image', buf.byteLength, previewUrl);
              }, function () { finalize('[unreadable image]', 'binary', 0, ''); });
            } else if (!isText) {
              const clone = res.clone();
              clone.arrayBuffer().then(function (buf) {
                const text = '[' + (mime || 'binary') + ' ' + formatSize(buf.byteLength) + ']';
                finalize(text, 'binary', buf.byteLength, '');
              }, function () { finalize('[unreadable binary]', 'binary', 0, ''); });
            } else {
              const clone = res.clone();
              clone.text().then(function (text) { finalize(text, 'text', 0, ''); },
                  function () { finalize('[unreadable response]', 'text', 0, ''); });
            }
          } catch (e) {
            finalize('[unreadable response]', 'text', 0, '');
          }

          return res;
        }, function (err) {
          const endTime = Date.now();
          const duration = endTime - reqTime;
          bodyPromise.then(function (bodyStr) {
            addRecord({
              kind: 'fetch', method: upperMethod, url: finalUrl, params: queryStr,
              body: bodyStr, reqHeaders: reqHeadersStr, respHeaders: '',
              status: 0, response: '[network error] ' + (err && err.message ? err.message : ''),
              responseKind: 'text', mimeType: '', binarySize: 0,
              duration: duration, time: reqTime
            });
          }).catch(function () {
            addRecord({
              kind: 'fetch', method: upperMethod, url: finalUrl, params: queryStr,
              body: '', reqHeaders: reqHeadersStr, respHeaders: '',
              status: 0, response: '[network error] ' + (err && err.message ? err.message : ''),
              responseKind: 'text', mimeType: '', binarySize: 0,
              duration: duration, time: reqTime
            });
          });
          throw err;
        });
      };

      patched.__nrpPatched = true;
      window.fetch = patched;
    }

    /* ---------------- EventSource ---------------- */
    const OrigES = window.EventSource;
    if (typeof OrigES === 'function' && !OrigES.__nrpPatched) {
      const PatchedES = function (url, config) {
        const es = new OrigES(url, config);
        try { instrumentEventSource(es, url); } catch (e) {}
        return es;
      };
      PatchedES.prototype = OrigES.prototype;
      PatchedES.CONNECTING = OrigES.CONNECTING != null ? OrigES.CONNECTING : 0;
      PatchedES.OPEN = OrigES.OPEN != null ? OrigES.OPEN : 1;
      PatchedES.CLOSED = OrigES.CLOSED != null ? OrigES.CLOSED : 2;
      PatchedES.__nrpPatched = true;
      try { window.EventSource = PatchedES; } catch (e) {}
    }
  }

  /* ============================ h() 工具 ============================ */

  function h(tag, attrs, children) {
    const node = document.createElement(tag);
    if (attrs) {
      for (const k in attrs) {
        if (!Object.prototype.hasOwnProperty.call(attrs, k)) continue;
        const v = attrs[k];
        if (v == null) continue;
        if (k === 'class') node.className = v;
        else if (k === 'text') node.textContent = v;
        else if (k === 'style') node.style.cssText = v;
        else node.setAttribute(k, v);
      }
    }
    if (children) {
      (Array.isArray(children) ? children : [children]).forEach(function (c) {
        if (c == null) return;
        node.appendChild(typeof c === 'string' ? document.createTextNode(c) : c);
      });
    }
    return node;
  }


  /* ============================ 可复用模态框工厂 ============================ */

  /* 打开的模态框栈：Esc 仅关闭最上层 */
  const openModals = [];

  /**
   * 创建可复用模态框
   * @param {Object} opts
   * @param {string}   [opts.modalClass]           附加到 .nrp-modal
   * @param {string}   [opts.overlayClass]         附加到 .nrp-overlay
   * @param {string}   [opts.headClass]            附加到 .nrp-modal-head
   * @param {string}   [opts.titleClass]           附加到 .nrp-modal-title
   * @param {string}   [opts.toolsClass]           附加到 .nrp-modal-tools
   * @param {string}   [opts.bodyClass]            附加到 .nrp-modal-content
   * @param {string}   [opts.footerClass]          附加到 .nrp-modal-footer
   * @param {Node|string|Array} [opts.title]       标题内容
   * @param {Node|Array}        [opts.tools]       头部右侧按钮（关闭按钮自动追加在末尾）
   * @param {Node|Array}        [opts.body]        主体内容
   * @param {Node|Array}        [opts.footer]      页脚内容（存在时才显示页脚）
   * @param {boolean}  [opts.showClose=true]       是否自动追加 × 关闭按钮
   * @param {boolean}  [opts.closeOnBackdrop=true] 点击遮罩是否关闭
   * @param {Function} [opts.onOpen]               打开回调
   * @param {Function} [opts.onClose]              关闭回调
   */
  function createModal(opts) {
    opts = opts || {};

    const overlay = h('div', {
      class: 'nrp-overlay' + (opts.overlayClass ? ' ' + opts.overlayClass : '')
    });
    const modal = h('div', {
      class: 'nrp-modal' + (opts.modalClass ? ' ' + opts.modalClass : '')
    });
    const head = h('div', {
      class: 'nrp-modal-head' + (opts.headClass ? ' ' + opts.headClass : '')
    });
    const titleEl = h('div', {
      class: 'nrp-modal-title' + (opts.titleClass ? ' ' + opts.titleClass : '')
    });
    const toolsEl = h('div', {
      class: 'nrp-modal-tools' + (opts.toolsClass ? ' ' + opts.toolsClass : '')
    });
    const bodyEl = h('div', {
      class: 'nrp-modal-content' + (opts.bodyClass ? ' ' + opts.bodyClass : '')
    });
    const footerEl = h('div', {
      class: 'nrp-modal-footer' + (opts.footerClass ? ' ' + opts.footerClass : '')
    });

    head.appendChild(titleEl);
    head.appendChild(toolsEl);
    modal.appendChild(head);
    modal.appendChild(bodyEl);
    modal.appendChild(footerEl);
    overlay.appendChild(modal);

    function applyContent(slot, content) {
      clearEl(slot);
      if (content == null) return;
      const list = Array.isArray(content) ? content : [content];
      for (let i = 0; i < list.length; i++) {
        const item = list[i];
        if (item == null) continue;
        slot.appendChild(item instanceof Node ? item : document.createTextNode(String(item)));
      }
    }

    const closeBtn = h('button', {
      class: 'nrp-btn', type: 'button', title: 'Close'
    }, '×');

    const handle = {
      overlay: overlay,
      modal: modal,
      head: head,
      titleEl: titleEl,
      toolsEl: toolsEl,
      body: bodyEl,
      footer: footerEl,
      isOpen: false,

      setTitle: function (t) { applyContent(titleEl, t); },
      setTools: function (t) {
        clearEl(toolsEl);
        applyContent(toolsEl, t);
        if (opts.showClose !== false) toolsEl.appendChild(closeBtn);
      },
      setBody: function (b) { applyContent(bodyEl, b); },
      setFooter: function (f) {
        applyContent(footerEl, f);
        footerEl.style.display = footerEl.childNodes.length ? '' : 'none';
      },
      open: function () {
        if (!handle.isOpen) {
          handle.isOpen = true;
          openModals.push(handle);
        }
        overlay.classList.add('nrp-open');
        if (typeof opts.onOpen === 'function') {
          try { opts.onOpen(); } catch (e) { /* ignore */ }
        }
      },
      close: function () {
        if (!handle.isOpen) return;
        handle.isOpen = false;
        overlay.classList.remove('nrp-open');
        const idx = openModals.indexOf(handle);
        if (idx >= 0) openModals.splice(idx, 1);
        if (typeof opts.onClose === 'function') {
          try { opts.onClose(); } catch (e) { /* ignore */ }
        }
      }
    };

    closeBtn.addEventListener('click', function () { handle.close(); });

    if (opts.closeOnBackdrop !== false) {
      overlay.addEventListener('click', function (e) {
        if (e.target === overlay) handle.close();
      });
    }

    if (opts.title != null) handle.setTitle(opts.title);
    handle.setTools(opts.tools || []);
    if (opts.body != null) handle.setBody(opts.body);
    if (opts.footer != null) handle.setFooter(opts.footer);
    else footerEl.style.display = 'none';

    return handle;
  }

  /* ============================ CSS ============================ */

  const CSS = `
#nrp-root {
  position: fixed;
  right: 16px;
  bottom: 16px;
  z-index: ${PANEL_Z};
  font-family: ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, "Liberation Mono", monospace;
  font-size: 12px;
  line-height: 1.45;
  color: #c9d1d9;
  text-align: left;
  pointer-events: none;
  -webkit-font-smoothing: antialiased;
}
#nrp-root *,
#nrp-root *::before,
#nrp-root *::after { box-sizing: border-box; }

#nrp-root .nrp-panel {
  pointer-events: auto;
  width: 1180px;
  max-width: calc(100vw - 32px);
  background: #0d1117;
  border: 1px solid #30363d;
  border-radius: 8px;
  box-shadow: 0 10px 40px rgba(0,0,0,.65);
  display: flex;
  flex-direction: column;
  overflow: hidden;
  transition: width .15s ease, max-width .15s ease, height .15s ease, max-height .15s ease, border-radius .15s ease;
}

#nrp-root .nrp-panel.nrp-fullscreen {
  position: fixed; inset: 0;
  width: 100vw; max-width: 100vw;
  height: 100vh; max-height: 100vh;
  border-radius: 0; box-shadow: none;
  border-left: none; border-right: none; border-top: none; border-bottom: none;
}
#nrp-root .nrp-panel.nrp-fullscreen .nrp-body { height: auto; max-height: none; flex: 1 1 auto; }

#nrp-root .nrp-header {
  display: flex; align-items: center; justify-content: space-between;
  gap: 8px; padding: 6px 8px 6px 10px;
  background: #161b22; border-bottom: 1px solid #30363d;
}
#nrp-root .nrp-title {
  display: flex; align-items: center; gap: 6px;
  font-weight: 700; font-size: 12px; color: #e6edf3;
  letter-spacing: .2px; white-space: nowrap;
}
#nrp-root .nrp-dot {
  width: 8px; height: 8px; border-radius: 50%;
  background: #3fb950; box-shadow: 0 0 8px rgba(63,185,80,.9);
}
#nrp-root .nrp-actions { display: flex; gap: 4px; }

#nrp-root .nrp-tabs {
  display: flex; align-items: center; gap: 2px;
  flex-shrink: 0; margin-left: 8px;
}
#nrp-root .nrp-tab,
#nrp-root .nrp-store-tab,
#nrp-root .nrp-store-view-tab {
  appearance: none; -webkit-appearance: none;
  display: inline-flex; align-items: center;
  border: 1px solid #30363d; background: transparent; color: #8b949e;
  font-family: inherit; font-size: 11px; font-weight: 600; line-height: 1.2;
  border-radius: 6px; cursor: pointer;
  white-space: nowrap;
  transition: background .12s, color .12s, border-color .12s;
}
#nrp-root .nrp-tab { gap: 5px; padding: 3px 9px; }
#nrp-root .nrp-store-tab { padding: 3px 9px; }
#nrp-root .nrp-store-view-tab { gap: 5px; padding: 4px 10px; }
#nrp-root .nrp-tab:hover,
#nrp-root .nrp-store-tab:hover,
#nrp-root .nrp-store-view-tab:hover { background: #21262d; color: #c9d1d9; border-color: #484f58; }
#nrp-root .nrp-tab-active,
#nrp-root .nrp-store-tab-active,
#nrp-root .nrp-store-view-tab.nrp-store-view-tab-active {
  background: rgba(56,139,253,.16); color: #79c0ff;
  border-color: rgba(56,139,253,.55);
}
#nrp-root .nrp-tab-count {
  display: inline-block; min-width: 16px; padding: 0 4px;
  border-radius: 8px; background: #21262d; color: #8b949e;
  font-size: 10px; font-weight: 700; text-align: center;
}
#nrp-root .nrp-tab-active .nrp-tab-count { background: rgba(56,139,253,.25); color: #79c0ff; }

#nrp-root .nrp-store {
  display: flex; flex-direction: column;
  flex: 1 1 auto; min-height: 0; overflow: hidden;
}
#nrp-root .nrp-store-tabs {
  display: flex; align-items: center; gap: 4px;
  padding: 6px 8px; border-bottom: 1px solid #21262d;
  flex-shrink: 0; background: #0d1117;
}
#nrp-root .nrp-store-tools {
  display: flex; align-items: center; gap: 6px;
  padding: 6px 8px; border-bottom: 1px solid #21262d;
  flex-shrink: 0; background: #161b22;
}
#nrp-root .nrp-btn-sm { padding: 2px 8px; font-size: 11px; }
#nrp-root .nrp-store-table-wrap { flex: 1 1 auto; overflow: auto; }
#nrp-root .nrp-store-table { width: 100%; border-collapse: collapse; table-layout: fixed; }
#nrp-root .nrp-store-th {
  text-align: left; padding: 6px 10px; font-size: 11px; font-weight: 700;
  color: #8b949e; background: #161b22; border-bottom: 1px solid #30363d;
  position: sticky; top: 0; z-index: 1;
}
#nrp-root .nrp-store-actions { text-align: right; }
#nrp-root .nrp-store-td {
  padding: 5px 10px; border-bottom: 1px solid #21262d;
  font-size: 12px; vertical-align: top;
}
#nrp-root .nrp-store-row:hover .nrp-store-td { background: #161b22; }
#nrp-root .nrp-store-name {
  color: #79c0ff; word-break: break-all; font-weight: 600;
}
#nrp-root .nrp-store-value { padding: 0 10px; vertical-align: middle; min-width: 0; }
#nrp-root .nrp-store-value-text {
  display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical;
  overflow: hidden; word-break: break-all; cursor: pointer;
  color: #e6edf3; line-height: 1.45;
}
#nrp-root .nrp-store-value-text:hover { color: #79c0ff; }
#nrp-root .nrp-store-actions { text-align: right; white-space: nowrap; }
#nrp-root .nrp-store-input {
  width: 100%; box-sizing: border-box;
  background: #010409; border: 1px solid #1f6feb; color: #e6edf3;
  border-radius: 4px; padding: 3px 6px;
  font-family: inherit; font-size: 12px; outline: none;
}
#nrp-root .nrp-store-empty { color: #8b949e; text-align: center; padding: 18px 10px; }

#nrp-root .nrp-cell-restype { font-weight: 600; }
#nrp-root .nrp-restype-doc    { color: #e6edf3; }
#nrp-root .nrp-restype-script { color: #d29922; }
#nrp-root .nrp-restype-css    { color: #79c0ff; }
#nrp-root .nrp-restype-img    { color: #56d364; }
#nrp-root .nrp-restype-font   { color: #d2a8ff; }
#nrp-root .nrp-restype-iframe { color: #f0883e; }
#nrp-root .nrp-restype-video,
#nrp-root .nrp-restype-audio  { color: #f85149; }
#nrp-root .nrp-restype-beacon { color: #a5d6ff; }
#nrp-root .nrp-restype-other  { color: #8b949e; }
#nrp-root .nrp-cell-size { color: #c9d1d9; text-align: right; }
#nrp-root .nrp-cell-cache { font-weight: 600; }
#nrp-root .nrp-cache-network { color: #8b949e; }
#nrp-root .nrp-cache-cache   { color: #3fb950; }
#nrp-root .nrp-cache-unknown { color: #6e7681; font-style: italic; }
#nrp-root .nrp-chip-resType.nrp-chip-active {
  background: rgba(210,168,255,.2); color: #d2a8ff; border-color: rgba(210,168,255,.6);
}

#nrp-root .nrp-btn {
  appearance: none; -webkit-appearance: none;
  border: 1px solid #30363d; background: #21262d; color: #c9d1d9;
  font-family: inherit; font-size: 11px; line-height: 1.2;
  padding: 3px 8px; border-radius: 5px; cursor: pointer;
  white-space: nowrap;
  transition: background .12s, color .12s, border-color .12s;
}
#nrp-root .nrp-btn:hover { background: #30363d; color: #fff; border-color: #484f58; }
#nrp-root .nrp-btn:active { transform: translateY(1px); }
#nrp-root .nrp-btn.nrp-btn-active {
  background: rgba(56,139,253,.2); color: #79c0ff;
  border-color: rgba(56,139,253,.6);
}
#nrp-root .nrp-btn-primary { background: #238636; border-color: #2ea043; color: #fff; }
#nrp-root .nrp-btn-primary:hover { background: #2ea043; }
#nrp-root .nrp-btn-danger { background: #da3633; border-color: #f85149; color: #fff; }
#nrp-root .nrp-btn-danger:hover { background: #f85149; }

#nrp-root .nrp-body {
  display: flex; flex-direction: column;
  height: 480px; max-height: 70vh;
}
#nrp-root .nrp-panel.nrp-collapsed .nrp-body { display: none; }

#nrp-root .nrp-toolbar {
  display: flex; align-items: center; gap: 8px;
  padding: 6px 8px; border-bottom: 1px solid #21262d;
  background: #0d1117; flex-shrink: 0;
}
#nrp-root .nrp-search,
#nrp-root .nrp-store-add-input {
  background: #010409; border: 1px solid #30363d; color: #e6edf3;
  border-radius: 5px; font-family: inherit; font-size: 12px; outline: none;
}
#nrp-root .nrp-search { flex: 1 1 auto; min-width: 0; padding: 4px 8px; }
#nrp-root .nrp-store-add-input { padding: 6px 8px; width: 100%; }
#nrp-root .nrp-search:focus,
#nrp-root .nrp-store-add-input:focus,
#nrp-root .nrp-slow-input:focus,
#nrp-root .nrp-group-select:focus {
  border-color: #1f6feb; box-shadow: 0 0 0 2px rgba(31,111,235,.25);
}
#nrp-root .nrp-search::placeholder { color: #6e7681; }
#nrp-root .nrp-stats { color: #8b949e; font-size: 11px; white-space: nowrap; }

#nrp-root .nrp-group-wrap {
  display: flex; align-items: center; gap: 4px; white-space: nowrap;
}
#nrp-root .nrp-group-label {
  color: #6e7681; font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: .5px;
}
#nrp-root .nrp-group-select {
  appearance: none; -webkit-appearance: none;
  background: #010409; border: 1px solid #30363d; color: #e6edf3;
  border-radius: 5px; padding: 3px 22px 3px 8px;
  font-family: inherit; font-size: 11px; outline: none; cursor: pointer;
  background-image:
    linear-gradient(45deg, transparent 50%, #8b949e 50%),
    linear-gradient(135deg, #8b949e 50%, transparent 50%);
  background-position:
    calc(100% - 12px) calc(50% - 2px),
    calc(100% - 8px) calc(50% - 2px);
  background-size: 4px 4px, 4px 4px;
  background-repeat: no-repeat;
}

#nrp-root .nrp-chips {
  display: flex; flex-wrap: wrap; align-items: center;
  gap: 6px 10px; padding: 6px 8px;
  border-bottom: 1px solid #21262d; background: #0d1117;
  flex-shrink: 0;
  max-height: 120px; overflow-y: auto;
}
#nrp-root .nrp-chips-row {
  display: flex; align-items: center; flex-wrap: wrap; gap: 4px;
}
#nrp-root .nrp-chips-label {
  color: #6e7681; font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: .5px;
  margin-right: 2px; min-width: 52px;
}
#nrp-root .nrp-chip {
  appearance: none; -webkit-appearance: none;
  border: 1px solid #30363d; background: #161b22; color: #8b949e;
  font-family: inherit; font-size: 11px; line-height: 1.2;
  padding: 2px 8px; border-radius: 10px; cursor: pointer;
  white-space: nowrap;
  transition: background .12s, color .12s, border-color .12s;
}
#nrp-root .nrp-chip:hover { background: #21262d; color: #c9d1d9; border-color: #484f58; }
#nrp-root .nrp-chip.nrp-chip-active {
  background: rgba(56,139,253,.2); color: #79c0ff;
  border-color: rgba(56,139,253,.6);
}
#nrp-root .nrp-chip-kind.nrp-chip-active {
  background: rgba(121,192,255,.2); color: #79c0ff; border-color: rgba(121,192,255,.6);
}
#nrp-root .nrp-chip-method.nrp-chip-active {
  background: rgba(56,139,253,.2); color: #79c0ff; border-color: rgba(56,139,253,.6);
}
#nrp-root .nrp-chip-st2xx.nrp-chip-active {
  background: rgba(63,185,80,.2); color: #3fb950; border-color: rgba(63,185,80,.6);
}
#nrp-root .nrp-chip-st3xx.nrp-chip-active {
  background: rgba(210,153,34,.2); color: #d29922; border-color: rgba(210,153,34,.6);
}
#nrp-root .nrp-chip-st4xx.nrp-chip-active,
#nrp-root .nrp-chip-st5xx.nrp-chip-active,
#nrp-root .nrp-chip-sterr.nrp-chip-active,
#nrp-root .nrp-chip-error.nrp-chip-active {
  background: rgba(248,81,73,.2); color: #f85149; border-color: rgba(248,81,73,.6);
}
#nrp-root .nrp-chip-flag.nrp-chip-active {
  background: rgba(210,168,255,.2); color: #d2a8ff; border-color: rgba(210,168,255,.6);
}
#nrp-root .nrp-chips-reset {
  margin-left: auto; color: #6e7681; font-size: 11px;
  background: transparent; border: 1px solid transparent;
  padding: 2px 6px; border-radius: 5px; cursor: pointer;
  white-space: nowrap;
}
#nrp-root .nrp-chips-reset:hover { color: #c9d1d9; border-color: #30363d; }

#nrp-root .nrp-slow-threshold {
  display: inline-flex; align-items: center; gap: 3px; margin-left: 2px;
}
#nrp-root .nrp-slow-threshold-label {
  color: #6e7681; font-size: 10px; font-weight: 700; letter-spacing: .3px;
}
#nrp-root .nrp-slow-input {
  width: 58px;
  background: #010409; border: 1px solid #30363d; color: #e6edf3;
  border-radius: 5px; padding: 2px 6px;
  font-family: inherit; font-size: 11px; outline: none;
  text-align: right;
}
#nrp-root .nrp-slow-unit { color: #8b949e; font-size: 10px; }

#nrp-root .nrp-table-wrap { flex: 1 1 auto; overflow: auto; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar,
#nrp-root .nrp-store-table-wrap::-webkit-scrollbar { width: 10px; height: 10px; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-track,
#nrp-root .nrp-store-table-wrap::-webkit-scrollbar-track { background: #0d1117; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-thumb,
#nrp-root .nrp-store-table-wrap::-webkit-scrollbar-thumb { background: #30363d; border-radius: 5px; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-thumb:hover,
#nrp-root .nrp-store-table-wrap::-webkit-scrollbar-thumb:hover { background: #484f58; }

#nrp-root table { width: 100%; border-collapse: collapse; table-layout: fixed; }
#nrp-root th {
  position: sticky; top: 0; z-index: 1;
  background: #161b22; color: #8b949e;
  font-size: 11px; font-weight: 700; text-align: left;
  padding: 5px 8px; border-bottom: 1px solid #30363d;
  white-space: nowrap;
}
#nrp-root td {
  padding: 4px 8px; border-bottom: 1px solid #1b222b;
  overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
  vertical-align: middle;
}
#nrp-root tbody tr { cursor: pointer; }
#nrp-root tbody tr.nrp-data-row:nth-child(even) { background: #10161d; }
#nrp-root tbody tr.nrp-data-row:hover { background: #1c2733; }

#nrp-root .nrp-cell-method { color: #79c0ff; font-weight: 600; }
#nrp-root .nrp-cell-time { color: #8b949e; }
#nrp-root .nrp-dim { color: #8b949e; }
#nrp-root .nrp-cell-query { color: #d29922; }
#nrp-root .nrp-cell-body { color: #a5d6ff; }
#nrp-root .nrp-cell-headers { color: #d2a8ff; }
#nrp-root .nrp-cell-image { color: #56d364; font-style: italic; }
#nrp-root .nrp-cell-sse { color: #d2a8ff; font-weight: 600; }
#nrp-root .nrp-st-ok { color: #3fb950; font-weight: 700; }
#nrp-root .nrp-st-err { color: #f85149; font-weight: 700; }
#nrp-root .nrp-st-other { color: #c9d1d9; font-weight: 700; }

#nrp-root .nrp-cell-clickable {
  cursor: pointer;
  text-decoration: underline;
  text-decoration-style: dotted;
  text-underline-offset: 3px;
}
#nrp-root .nrp-cell-clickable:hover { color: #e6edf3; }

#nrp-root .nrp-group-row { cursor: pointer; background: #161b22 !important; }
#nrp-root .nrp-group-row:hover { background: #1c2733 !important; }
#nrp-root td.nrp-group-cell {
  padding: 5px 8px;
  color: #e6edf3; font-weight: 700; font-size: 11px;
  border-top: 1px solid #30363d;
  border-bottom: 1px solid #30363d;
}
#nrp-root .nrp-group-caret {
  display: inline-block; width: 12px; text-align: center;
  color: #8b949e; transition: transform .12s;
}
#nrp-root tr.nrp-group-row.nrp-group-collapsed .nrp-group-caret { transform: rotate(-90deg); }
#nrp-root .nrp-group-key { color: #79c0ff; margin-left: 4px; }
#nrp-root .nrp-group-count {
  color: #8b949e; font-weight: 400; margin-left: 8px; font-size: 10px;
}
#nrp-root .nrp-group-badge {
  display: inline-block; margin-left: 6px;
  padding: 0 6px; border-radius: 8px;
  background: #21262d; color: #8b949e;
  font-size: 10px; font-weight: 400;
}

#nrp-root .nrp-empty-row { cursor: default; background: transparent !important; }
#nrp-root td.nrp-empty {
  text-align: center; color: #6e7681;
  padding: 28px 8px; font-style: italic;
}

#nrp-root .nrp-fab {
  display: none; pointer-events: auto;
  position: absolute; right: 0; bottom: 0;
  width: 46px; height: 46px; border-radius: 50%;
  border: 1px solid #30363d; background: #161b22; color: #3fb950;
  font-family: inherit; font-size: 11px; font-weight: 700;
  cursor: pointer; align-items: center; justify-content: center;
  box-shadow: 0 6px 20px rgba(0,0,0,.6);
}
#nrp-root .nrp-fab:hover { background: #21262d; color: #56d364; }

/* ============ 通用模态框：可复用 head / body / footer ============ */
#nrp-root .nrp-overlay {
  display: none;
  position: fixed; inset: 0;
  z-index: ${OVERLAY_Z};
  background: rgba(1,4,9,.72);
  align-items: center; justify-content: center;
  padding: 24px;
  pointer-events: auto;
}
#nrp-root .nrp-overlay.nrp-open { display: flex; }

#nrp-root .nrp-modal {
  width: 920px; max-width: 92vw;
  max-height: 82vh;
  background: #0d1117;
  border: 1px solid #30363d;
  border-radius: 8px;
  box-shadow: 0 20px 60px rgba(0,0,0,.7);
  display: flex; flex-direction: column;
  overflow: hidden;
}
#nrp-root .nrp-modal-head {
  display: flex; align-items: flex-start; justify-content: space-between;
  gap: 10px; padding: 10px 12px;
  background: #161b22; border-bottom: 1px solid #30363d;
  flex-shrink: 0;
}
#nrp-root .nrp-modal-title {
  display: flex; align-items: center; gap: 8px;
  flex-wrap: wrap; min-width: 0; flex: 1 1 auto;
}
#nrp-root .nrp-modal-tools { display: flex; gap: 6px; flex-shrink: 0; }
#nrp-root .nrp-modal-content {
  flex: 1 1 auto;
  overflow-y: auto;
  display: flex;
  flex-direction: column;
  min-height: 0;
}
#nrp-root .nrp-modal-footer {
  display: flex; justify-content: flex-end; gap: 8px;
  padding: 10px 12px;
  border-top: 1px solid #21262d; background: #0d1117;
  flex-shrink: 0;
}
#nrp-root .nrp-modal-footer:empty { display: none; }

/* 头部徽章 */
#nrp-root .nrp-headline {
  display: flex; align-items: center; gap: 8px;
  flex-wrap: wrap; min-width: 0; flex: 1 1 auto;
}
#nrp-root .nrp-badge {
  display: inline-block; padding: 2px 7px; border-radius: 5px;
  font-size: 11px; font-weight: 700; white-space: nowrap;
  border: 1px solid transparent;
}
#nrp-root .nrp-badge-method { background: rgba(56,139,253,.15); color: #79c0ff; border-color: rgba(56,139,253,.4); }
#nrp-root .nrp-badge-ok     { background: rgba(63,185,80,.15);  color: #3fb950; border-color: rgba(63,185,80,.4); }
#nrp-root .nrp-badge-err    { background: rgba(248,81,73,.15);  color: #f85149; border-color: rgba(248,81,73,.4); }
#nrp-root .nrp-badge-other  { background: rgba(110,118,129,.15);color: #c9d1d9; border-color: rgba(110,118,129,.4); }
#nrp-root .nrp-badge-time   { background: rgba(210,153,34,.15); color: #d29922; border-color: rgba(210,153,34,.4); }
#nrp-root .nrp-badge-frame  { background: rgba(210,168,255,.15);color: #d2a8ff; border-color: rgba(210,168,255,.4); }
#nrp-root .nrp-badge-dur    { background: rgba(121,192,255,.15);color: #79c0ff; border-color: rgba(121,192,255,.4); }
#nrp-root .nrp-badge-mime   { background: rgba(86,211,100,.15); color: #56d364; border-color: rgba(86,211,100,.4); }
#nrp-root .nrp-badge-sse    { background: rgba(210,168,255,.15);color: #d2a8ff; border-color: rgba(210,168,255,.4); }
#nrp-root .nrp-badge-live   {
  background: rgba(63,185,80,.15); color: #3fb950; border-color: rgba(63,185,80,.4);
  animation: nrp-live-pulse 1.4s ease-in-out infinite;
}
@keyframes nrp-live-pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: .45; }
}

#nrp-root .nrp-modal-url {
  color: #c9d1d9; font-size: 12px; line-height: 1.5;
  word-break: break-all; min-width: 0;
}

/* 响应/头部等 <pre> 内容：强制自动换行 */
#nrp-root .nrp-modal-body {
  margin: 0; padding: 0; max-width: 100%;
  white-space: pre-wrap;
  word-break: break-all;
  overflow-wrap: anywhere;
}

/* JSON 语法高亮配色 */
#nrp-root .nrp-hl-key  { color: #79c0ff; }
#nrp-root .nrp-hl-str  { color: #a5d6ff; }
#nrp-root .nrp-hl-num  { color: #d29922; }
#nrp-root .nrp-hl-bool { color: #ff7b72; }
#nrp-root .nrp-hl-null { color: #ff7b72; }

/* Params / Body 容器 */
#nrp-root .nrp-modal-params {
  background: #0d1117;
  flex-shrink: 0;
}

/* 通用可折叠区块 */
#nrp-root .nrp-section {
  border-bottom: 1px solid #21262d;
  background: #0d1117;
  flex-shrink: 0;
}
#nrp-root .nrp-section-title {
  display: flex; align-items: center; gap: 6px;
  padding: 6px 12px; cursor: pointer;
  color: #8b949e; font-size: 11px; font-weight: 700;
  user-select: none;
  background: #0d1117;
  position: sticky; top: 0; z-index: 1;
}
#nrp-root .nrp-section-title:hover { color: #c9d1d9; }
#nrp-root .nrp-section-title .nrp-caret {
  display: inline-block; width: 10px; text-align: center;
  transition: transform .12s;
}
#nrp-root .nrp-section-title.nrp-collapsed .nrp-caret { transform: rotate(-90deg); }
#nrp-root .nrp-section-content {
  padding: 0 12px 8px 12px;
  font-size: 12px; color: #a5d6ff;
  white-space: pre-wrap; word-break: break-all;
}
#nrp-root .nrp-section-title.nrp-collapsed + .nrp-section-content { display: none; }

#nrp-root .nrp-section-params .nrp-section-content {
  color: #d29922;
  background: #010409;
  padding: 8px 12px;
  white-space: pre-wrap;
  word-break: break-all;
}
#nrp-root .nrp-section-body .nrp-section-content {
  color: #a5d6ff;
  background: #010409;
  padding: 8px 12px;
  white-space: pre-wrap;
  word-break: break-all;
}
#nrp-root .nrp-section-response .nrp-section-content {
  color: #c9d1d9;
  background: #010409;
  padding: 10px 12px;
  white-space: pre-wrap;
  word-break: break-word;
  font-size: 12px;
  line-height: 1.6;
}

/* 图片预览 */
#nrp-root .nrp-image-wrap {
  padding: 12px;
  background: #010409;
  display: flex; flex-direction: column; align-items: center;
  gap: 10px;
}
#nrp-root .nrp-image-info {
  color: #8b949e; font-size: 11px; text-align: center;
}
#nrp-root .nrp-image-preview {
  max-width: 100%; max-height: 400px;
  border: 1px solid #30363d; border-radius: 6px;
  background:
    linear-gradient(45deg, #1a1f27 25%, transparent 25%),
    linear-gradient(-45deg, #1a1f27 25%, transparent 25%),
    linear-gradient(45deg, transparent 75%, #1a1f27 75%),
    linear-gradient(-45deg, transparent 75%, #1a1f27 75%);
  background-size: 16px 16px;
  background-position: 0 0, 0 8px, 8px -8px, -8px 0;
  image-rendering: auto;
}
#nrp-root .nrp-image-fallback {
  color: #f85149; font-size: 12px;
  padding: 8px 12px; border: 1px solid rgba(248,81,73,.4);
  border-radius: 6px; background: rgba(248,81,73,.1);
}

/* 二进制文件信息 */
#nrp-root .nrp-binary-wrap {
  padding: 16px;
  background: #010409;
  display: flex; flex-direction: column; align-items: flex-start;
  gap: 10px;
}
#nrp-root .nrp-binary-icon { font-size: 28px; line-height: 1; color: #79c0ff; }
#nrp-root .nrp-binary-title { color: #e6edf3; font-size: 13px; font-weight: 700; }
#nrp-root .nrp-binary-meta {
  color: #8b949e; font-size: 12px;
  white-space: pre-wrap; word-break: break-all;
}

/* ============ Storage 新增条目模态框（基于 .nrp-modal） ============ */
#nrp-root .nrp-modal.nrp-store-add-modal {
  width: 420px; max-width: calc(100vw - 48px);
}
#nrp-root .nrp-store-add-modal .nrp-modal-content {
  padding: 10px 14px 12px;
  display: flex; flex-direction: column; gap: 6px;
}
#nrp-root .nrp-store-add-modal .nrp-modal-head { padding: 10px 14px; }
#nrp-root .nrp-store-add-modal .nrp-modal-footer { padding: 10px 14px 12px; }
#nrp-root .nrp-store-add-title {
  font-size: 13px; font-weight: 700; color: #e6edf3;
}
#nrp-root .nrp-store-add-label {
  font-size: 11px; color: #8b949e; margin-top: 4px;
}
#nrp-root .nrp-store-add-textarea {
  resize: vertical; min-height: 72px; line-height: 1.5;
  white-space: pre-wrap; word-break: break-all;
}

/* ============ Storage 查看模态框（覆盖尺寸，其余继承 .nrp-modal） ============ */
#nrp-root .nrp-modal.nrp-store-view-modal {
  width: 920px; max-width: calc(100vw - 24px);
  height: min(calc(100vh - 24px), 760px);
  max-height: calc(100vh - 24px);
}
#nrp-root .nrp-store-view-overlay { padding: 12px; }
#nrp-root .nrp-store-view-body {
  flex: 1 1 auto; min-height: 0;
  overflow-y: auto;
  display: flex; flex-direction: column; gap: 6px;
  padding: 12px 16px;
}
#nrp-root .nrp-store-view-split {
  display: flex; gap: 12px; align-items: stretch;
  flex: 1 1 auto; min-height: 0;
  margin-top: 6px;
}
#nrp-root .nrp-store-view-col {
  flex: 1 1 0; min-width: 0; min-height: 0;
  display: flex; flex-direction: column;
}
#nrp-root .nrp-store-view-col .nrp-store-add-label { margin-top: 0; }
#nrp-root .nrp-store-view-textarea { flex: 1 1 auto; min-height: 0; height: auto; resize: none; }
#nrp-root .nrp-store-view-tabs { display: none; }
#nrp-root .nrp-store-view-hl {
  background: #010409; border: 1px solid #30363d; border-radius: 5px;
  padding: 8px 10px; overflow: auto; margin: 0;
  flex: 1 1 auto; min-height: 0;
}

/* ============ 移动端适配（<=768px） ============ */
@media (max-width: 768px) {
  #nrp-root { right: 0; }
  #nrp-root .nrp-panel {
    right: 0;
    width: 100vw;
    max-width: 100vw;
    border-radius: 0;
    border-left: none;
    border-right: none;
  }
  #nrp-root .nrp-body { height: auto; max-height: 82vh; }
  #nrp-root .nrp-header { flex-wrap: wrap; gap: 4px 6px; padding: 6px; }
  #nrp-root .nrp-title { flex: 1 1 auto; min-width: 0; }
  #nrp-root .nrp-actions { flex-wrap: wrap; justify-content: flex-end; gap: 4px; }
  #nrp-root .nrp-tabs {
    order: 10; flex-basis: 100%; width: 100%; margin-left: 0;
    overflow-x: auto; -webkit-overflow-scrolling: touch;
  }
  #nrp-root .nrp-toolbar { flex-wrap: wrap; gap: 6px; }
  #nrp-root .nrp-search { flex: 1 1 100%; }
  #nrp-root .nrp-group-wrap { flex: 1 1 auto; }
  #nrp-root .nrp-table-wrap,
  #nrp-root .nrp-store-table-wrap {
    -webkit-overflow-scrolling: touch;
    overscroll-behavior-x: contain;
  }
  #nrp-root .nrp-table-wrap table { width: 880px; max-width: none; }
  #nrp-root .nrp-store-table { width: 640px; max-width: none; }
  #nrp-root .nrp-btn,
  #nrp-root .nrp-tab,
  #nrp-root .nrp-store-tab,
  #nrp-root .nrp-chip { padding-top: 5px; padding-bottom: 5px; }
  #nrp-root td, #nrp-root th { padding: 6px 8px; }
  #nrp-root .nrp-store-view-tabs { display: flex; gap: 4px; margin-bottom: 4px; }
  #nrp-root .nrp-store-view-split { flex-direction: column; }
  #nrp-root .nrp-store-view-textarea { min-height: 160px; }
  #nrp-root .nrp-store-view-hl {
    height: auto;
    flex: 0 0 auto;
    min-height: 40vh;
    max-height: calc(100vh - 220px);
    overflow-y: auto;
  }
}
`;


  /* ---------- 快捷过滤 chips 构建 ---------- */

  const CHIP_GROUPS = [
    {
      label: 'Type', key: 'kind',
      items: [
        { value: 'xhr', label: 'XHR' },
        { value: 'fetch', label: 'fetch' },
        { value: 'sse', label: 'SSE' }
      ],
      cls: 'kind'
    },
    {
      label: 'Method', key: 'method',
      items: [
        { value: 'GET', label: 'GET' },
        { value: 'POST', label: 'POST' },
        { value: 'PUT', label: 'PUT' },
        { value: 'DELETE', label: 'DELETE' },
        { value: 'PATCH', label: 'PATCH' },
        { value: 'HEAD', label: 'HEAD' },
        { value: 'OPTIONS', label: 'OPTIONS' }
      ],
      cls: 'method'
    },
    {
      label: 'Status', key: 'status',
      items: [
        { value: '2xx', label: '2xx', cls: 'st2xx' },
        { value: '3xx', label: '3xx', cls: 'st3xx' },
        { value: '4xx', label: '4xx', cls: 'st4xx' },
        { value: '5xx', label: '5xx', cls: 'st5xx' },
        { value: 'err', label: 'ERR', cls: 'sterr' }
      ],
      cls: ''
    },
    {
      label: 'Source', key: 'source',
      items: [
        { value: 'top', label: '主页面' },
        { value: 'iframe', label: 'iframe' }
      ],
      cls: 'flag'
    },
    {
      label: 'Flags', key: 'flags',
      items: [
        { value: 'error', label: '错误', cls: 'error' },
        { value: 'slow', label: '慢请求', cls: 'flag' },
        { value: 'hasBody', label: '有 Body', cls: 'flag' },
        { value: 'hasParams', label: '有 Params', cls: 'flag' },
        { value: 'largeResp', label: '大响应', cls: 'flag' }
      ],
      cls: ''
    }
  ];

  const RES_CHIP_GROUPS = [
    {
      label: 'Type', key: 'type',
      items: [
        { value: 'script', label: 'JS', cls: 'resType' },
        { value: 'css', label: 'CSS', cls: 'resType' },
        { value: 'img', label: 'Image', cls: 'resType' },
        { value: 'font', label: 'Font', cls: 'resType' },
        { value: 'doc', label: 'Doc', cls: 'resType' },
        { value: 'iframe', label: 'iframe', cls: 'resType' },
        { value: 'video', label: 'Video', cls: 'resType' },
        { value: 'audio', label: 'Audio', cls: 'resType' },
        { value: 'beacon', label: 'Beacon', cls: 'resType' },
        { value: 'other', label: 'Other', cls: 'resType' }
      ],
      cls: ''
    },
    {
      label: 'Source', key: 'cache',
      items: [
        { value: 'network', label: '网络', cls: 'st2xx' },
        { value: 'cache', label: '缓存', cls: 'flag' },
        { value: 'unknown', label: '未知', cls: '' }
      ],
      cls: ''
    },
    {
      label: 'Quick', key: 'quick',
      items: [
        { value: 'slow', label: '慢请求', cls: 'flag' },
        { value: 'large', label: '资源过大', cls: 'flag' }
      ],
      cls: ''
    }
  ];

  function buildSlowThresholdControl() {
    const wrap = h('div', { class: 'nrp-slow-threshold', title: '慢请求阈值（毫秒）' });
    wrap.appendChild(h('span', { class: 'nrp-slow-threshold-label' }, '≥'));
    slowInputEl = h('input', {
      class: 'nrp-slow-input', type: 'number', min: '0', step: '100',
      value: String(slowThreshold)
    });
    wrap.appendChild(slowInputEl);
    wrap.appendChild(h('span', { class: 'nrp-slow-unit' }, 'ms'));

    slowInputEl.addEventListener('input', function () {
      const v = parseInt(slowInputEl.value, 10);
      if (isNaN(v) || v < 0) return;
      slowThreshold = v;
      try { localStorage.setItem(LS_KEY_SLOW, String(v)); } catch (e) {}
      scheduleRender();
    });
    slowInputEl.addEventListener('blur', function () {
      const v = parseInt(slowInputEl.value, 10);
      if (isNaN(v) || v < 0) slowInputEl.value = String(slowThreshold);
      else { slowThreshold = v; slowInputEl.value = String(v); }
    });
    return wrap;
  }

  function buildLargeResThresholdControl() {
    const wrap = h('div', { class: 'nrp-slow-threshold', title: '资源大小阈值（KB）' });
    wrap.appendChild(h('span', { class: 'nrp-slow-threshold-label' }, '≥'));
    const input = h('input', {
      class: 'nrp-slow-input', type: 'number', min: '0', step: '10',
      value: String(Math.round(largeResThreshold / 1024))
    });
    wrap.appendChild(input);
    wrap.appendChild(h('span', { class: 'nrp-slow-unit' }, 'KB'));

    function commit() {
      const v = parseFloat(input.value);
      if (isNaN(v) || v < 0) return;
      largeResThreshold = Math.round(v * 1024);
      try { localStorage.setItem(LS_KEY_LARGE_RES, String(largeResThreshold)); } catch (e) {}
      scheduleRender();
    }
    input.addEventListener('input', commit);
    input.addEventListener('blur', function () {
      const v = parseFloat(input.value);
      if (isNaN(v) || v < 0) input.value = String(Math.round(largeResThreshold / 1024));
      else { largeResThreshold = Math.round(v * 1024); input.value = String(Math.round(largeResThreshold / 1024)); }
    });
    return wrap;
  }

  function buildResSlowThresholdControl() {
    const wrap = h('div', { class: 'nrp-slow-threshold', title: '资源慢请求阈值（毫秒）' });
    wrap.appendChild(h('span', { class: 'nrp-slow-threshold-label' }, '≥'));
    const input = h('input', {
      class: 'nrp-slow-input', type: 'number', min: '0', step: '100',
      value: String(resSlowThreshold)
    });
    wrap.appendChild(input);
    wrap.appendChild(h('span', { class: 'nrp-slow-unit' }, 'ms'));

    input.addEventListener('input', function () {
      const v = parseInt(input.value, 10);
      if (isNaN(v) || v < 0) return;
      resSlowThreshold = v;
      try { localStorage.setItem(LS_KEY_RES_SLOW, String(v)); } catch (e) {}
      scheduleRender();
    });
    input.addEventListener('blur', function () {
      const v = parseInt(input.value, 10);
      if (isNaN(v) || v < 0) input.value = String(resSlowThreshold);
      else { resSlowThreshold = v; input.value = String(v); }
    });
    return wrap;
  }

  function getInlineChipControl(gkey, ivalue) {
    if (gkey === 'flags' && ivalue === 'slow') return buildSlowThresholdControl();
    if (gkey === 'quick' && ivalue === 'slow') return buildResSlowThresholdControl();
    if (gkey === 'quick' && ivalue === 'large') return buildLargeResThresholdControl();
    return null;
  }

  function buildChipsFrom(groups, store, resetTitle) {
    const container = h('div', { class: 'nrp-chips' });

    groups.forEach(function (group) {
      const row = h('div', { class: 'nrp-chips-row' });
      row.appendChild(h('span', { class: 'nrp-chips-label' }, group.label));

      group.items.forEach(function (item) {
        const active = store[group.key].has(item.value);
        const cls = 'nrp-chip' +
            (group.cls ? ' nrp-chip-' + group.cls : '') +
            (item.cls ? ' nrp-chip-' + item.cls : '') +
            (active ? ' nrp-chip-active' : '');
        const btn = h('button', {
          class: cls, type: 'button',
          'data-group': group.key, 'data-value': item.value
        }, item.label);

        btn.addEventListener('click', function () {
          const s = store[group.key];
          if (s.has(item.value)) { s.delete(item.value); btn.classList.remove('nrp-chip-active'); }
          else { s.add(item.value); btn.classList.add('nrp-chip-active'); }
          scheduleRender();
        });

        row.appendChild(btn);

        const inlineCtl = getInlineChipControl(group.key, item.value);
        if (inlineCtl) row.appendChild(inlineCtl);
      });

      container.appendChild(row);
    });

    const resetBtn = h('button', {
      class: 'nrp-chips-reset', type: 'button', title: resetTitle
    }, 'Reset');
    resetBtn.addEventListener('click', function () {
      Object.keys(store).forEach(function (k) { store[k].clear(); });
      container.querySelectorAll('.nrp-chip-active').forEach(function (el) {
        el.classList.remove('nrp-chip-active');
      });
      scheduleRender();
    });
    container.appendChild(resetBtn);

    return container;
  }

  function buildChips() {
    return buildChipsFrom(CHIP_GROUPS, filterState, '清除所有快捷过滤');
  }

  const GROUP_OPTIONS = {
    network: [
      { v: '', t: 'None' },
      { v: 'url', t: 'URL' },
      { v: 'domain', t: 'Domain' },
      { v: 'status', t: 'Status' },
      { v: 'method', t: 'Method' },
      { v: 'kind', t: 'API (XHR/fetch)' },
      { v: 'respType', t: 'Resp Type' }
    ],
    resource: [
      { v: '', t: 'None' },
      { v: 'url', t: 'URL' },
      { v: 'domain', t: 'Domain' },
      { v: 'resType', t: 'Resource Type' },
      { v: 'resSize', t: 'Size Bucket' },
      { v: 'resCache', t: 'Source (cache/network)' }
    ]
  };

  function fillGroupOptions() {
    if (!groupSelectEl) return;
    const options = GROUP_OPTIONS[currentTab] || GROUP_OPTIONS.network;
    clearEl(groupSelectEl);
    options.forEach(function (opt) {
      const o = document.createElement('option');
      o.value = opt.v;
      o.textContent = opt.t;
      if (opt.v === groupBy) o.selected = true;
      groupSelectEl.appendChild(o);
    });
  }

  function buildGroupSelector() {
    const wrap = h('div', { class: 'nrp-group-wrap', title: '按维度分组展示' });
    wrap.appendChild(h('span', { class: 'nrp-group-label' }, 'Group'));
    groupSelectEl = h('select', { class: 'nrp-group-select' });
    fillGroupOptions();

    groupSelectEl.addEventListener('change', function () {
      groupBy = groupSelectEl.value || '';
      if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
      const st = tabState[currentTab];
      st.groupBy = groupBy;
      if (currentTab === TAB_NETWORK) {
        try { localStorage.setItem(LS_KEY_GROUP, groupBy); } catch (e) {}
      }
      collapsedGroups = {};
      st.collapsed = collapsedGroups;
      scheduleRender();
    });

    wrap.appendChild(groupSelectEl);
    return wrap;
  }

  function countNetworkRecords() {
    let n = 0;
    for (let i = 0; i < records.length; i++) {
      if (records[i].kind !== 'resource') n++;
    }
    return n;
  }

  function updateTabButtons() {
    if (netTabBtnEl) {
      netTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_NETWORK);
      const c = netTabBtnEl.querySelector('.nrp-tab-count');
      if (c) c.textContent = String(countNetworkRecords());
    }
    if (resTabBtnEl) {
      resTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_RESOURCE);
      const c = resTabBtnEl.querySelector('.nrp-tab-count');
      if (c) c.textContent = String(countByKind('resource'));
    }
    if (typeof wsTabBtnEl !== 'undefined' && wsTabBtnEl) {
      wsTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_WS);
      const c2 = wsTabBtnEl.querySelector('.nrp-tab-count');
      if (c2) c2.textContent = String(wsRecords.length);
    }
    if (storeTabBtnEl) {
      storeTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_STORAGE);
      const c = storeTabBtnEl.querySelector('.nrp-tab-count');
      if (c) c.textContent = String(countStorageEntries());
    }
  }

  function switchTab(tab) {
    if (tab === currentTab) return;
    if (tab !== TAB_NETWORK && tab !== TAB_RESOURCE && tab !== TAB_STORAGE && tab !== TAB_WS) return;

    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    const st = tabState[currentTab];
    st.search = searchEl ? searchEl.value : '';
    if (currentTab !== TAB_STORAGE && currentTab !== TAB_WS) {
      st.groupBy = groupBy;
      st.collapsed = collapsedGroups;
    }

    currentTab = tab;
    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    const next = tabState[currentTab];
    if (tab !== TAB_STORAGE && tab !== TAB_WS) {
      groupBy = next.groupBy || '';
      collapsedGroups = next.collapsed || {};
    }

    if (searchEl) {
      searchEl.value = next.search || '';
      searchEl.placeholder = tab === TAB_RESOURCE
          ? 'Search url / type / source (cache/network) / protocol …'
          : (tab === TAB_STORAGE
              ? 'Search name / value …'
              : 'Search url / method / params / body / headers / status / response / mime …');
    }
    fillGroupOptions();

    if (groupWrapEl) groupWrapEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (netTableWrapEl) netTableWrapEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (resTableWrapEl) resTableWrapEl.style.display = tab === TAB_RESOURCE ? '' : 'none';
    if (typeof wsTableWrapEl !== 'undefined' && wsTableWrapEl) wsTableWrapEl.style.display = tab === TAB_WS ? '' : 'none';
    if (storeWrapEl) storeWrapEl.style.display = tab === TAB_STORAGE ? '' : 'none';
    if (chipsEl) chipsEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (chipsResEl) chipsResEl.style.display = tab === TAB_RESOURCE ? '' : 'none';
    if (clearBtnEl) clearBtnEl.style.display = (tab === TAB_STORAGE || tab === TAB_WS) ? 'none' : '';
    if (exportBtnEl) exportBtnEl.style.display = (tab === TAB_STORAGE || tab === TAB_WS) ? 'none' : '';
    if (typeof harBtnEl !== 'undefined' && harBtnEl) harBtnEl.style.display = (tab === TAB_STORAGE || tab === TAB_WS) ? 'none' : '';
    if (tab === TAB_RESOURCE) tbodyEl = resTbodyEl;
    else if (tab === TAB_NETWORK) tbodyEl = netTbodyEl;
    else tbodyEl = null;

    updateTabButtons();
    render();
  }

  function toggleFullscreen() {
    isFullscreen = !isFullscreen;
    if (isFullscreen) {
      panelEl.classList.add('nrp-fullscreen');
      if (fsBtn) { fsBtn.textContent = '⤡'; fsBtn.title = 'Restore'; fsBtn.classList.add('nrp-btn-active'); }
      if (panelEl.classList.contains('nrp-collapsed')) {
        panelEl.classList.remove('nrp-collapsed');
        const collapseBtn = panelEl.querySelector('[data-nrp-collapse]');
        if (collapseBtn) { collapseBtn.textContent = '—'; collapseBtn.title = 'Minimize'; }
      }
    } else {
      panelEl.classList.remove('nrp-fullscreen');
      if (fsBtn) { fsBtn.textContent = '⤢'; fsBtn.title = 'Fullscreen'; fsBtn.classList.remove('nrp-btn-active'); }
    }
    scheduleRender();
  }


  /* ============================ UI 构建 ============================ */

  function buildUI() {
    if (rootEl) return;

    const styleEl = document.createElement('style');
    styleEl.id = 'nrp-style';
    styleEl.textContent = CSS;
    (document.head || document.documentElement).appendChild(styleEl);

    const collapseBtn = h('button', {
      class: 'nrp-btn', type: 'button', title: 'Minimize / Maximize', 'data-nrp-collapse': '1'
    }, '—');
    clearBtnEl = h('button', { class: 'nrp-btn', type: 'button', title: 'Clear records of the current tab' }, 'Clear');
    exportBtnEl = h('button', { class: 'nrp-btn', type: 'button', title: 'Export filtered records of the current tab as JSON' }, 'Export');
    const harBtnEl = h('button', { class: 'nrp-btn', type: 'button', title: 'Export filtered network records as HAR' }, 'HAR');
    fsBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Fullscreen' }, '⤢');
    const hideBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Hide panel' }, '×');

    searchEl = h('input', {
      class: 'nrp-search', type: 'text',
      placeholder: 'Search url / method / params / body / headers / status / response / mime …',
      spellcheck: 'false'
    });
    searchEl.value = tabState.network.search || '';
    statsEl = h('span', { class: 'nrp-stats' }, '0 / 0');
    groupSelectEl = null;
    groupWrapEl = buildGroupSelector();

    chipsEl = buildChips();
    chipsResEl = buildChipsFrom(RES_CHIP_GROUPS, resFilterState, '清除资源过滤');
    chipsResEl.style.display = 'none';

    netTbodyEl = h('tbody');
    const netTable = h('table', null, [
      h('colgroup', null, [
        h('col', { style: 'width:8%' }), h('col', { style: 'width:5%' }),
        h('col', { style: 'width:5%' }), h('col', { style: 'width:14%' }),
        h('col', { style: 'width:12%' }), h('col', { style: 'width:10%' }),
        h('col', { style: 'width:12%' }), h('col', { style: 'width:12%' }),
        h('col', { style: 'width:17%' }), h('col', { style: 'width:5%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', null, 'Time'), h('th', null, 'Method'), h('th', null, 'Status'),
        h('th', null, 'URL'), h('th', null, 'Request Header'), h('th', null, 'Request Params'),
        h('th', null, 'Request Body'), h('th', null, 'Response Header'),
        h('th', null, 'Response Body'), h('th', null, 'Time(ms)')
      ])),
      netTbodyEl
    ]);

    resTbodyEl = h('tbody');
    const resTable = h('table', null, [
      h('colgroup', null, [
        h('col', { style: 'width:11%' }), h('col', { style: 'width:8%' }),
        h('col', { style: 'width:41%' }), h('col', { style: 'width:10%' }),
        h('col', { style: 'width:10%' }), h('col', { style: 'width:20%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', null, 'Time'), h('th', null, 'Type'), h('th', null, 'URL'),
        h('th', null, 'Size'), h('th', null, 'Timing'), h('th', null, 'Source')
      ])),
      resTbodyEl
    ]);

    netTableWrapEl = h('div', { class: 'nrp-table-wrap' }, netTable);
    resTableWrapEl = h('div', { class: 'nrp-table-wrap' }, resTable);
    resTableWrapEl.style.display = 'none';

    const wsTbodyEl = h('tbody');
    const wsTable = h('table', null, [
      h('colgroup', null, [
        h('col', { style: 'width:10%' }), h('col', { style: 'width:8%' }),
        h('col', { style: 'width:50%' }), h('col', { style: 'width:12%' }),
        h('col', { style: 'width:20%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', null, 'Time'), h('th', null, 'State'), h('th', null, 'URL'),
        h('th', null, 'Messages'), h('th', null, 'Info')
      ])),
      wsTbodyEl
    ]);
    wsTableWrapEl = h('div', { class: 'nrp-table-wrap' }, wsTable);
    wsTableWrapEl.style.display = 'none';

    tbodyEl = netTbodyEl;

    /* ---------------- Storage 子页 ---------------- */
    storeTabsEl = h('div', { class: 'nrp-store-tabs' }, [
      h('button', { class: 'nrp-store-tab', type: 'button', 'data-store': 'cookie' }, 'Cookies'),
      h('button', { class: 'nrp-store-tab', type: 'button', 'data-store': 'local' }, 'LocalStorage'),
      h('button', { class: 'nrp-store-tab', type: 'button', 'data-store': 'session' }, 'SessionStorage')
    ]);
    storeToolsEl = h('div', { class: 'nrp-store-tools' }, [
      h('button', { class: 'nrp-btn nrp-btn-sm', type: 'button', title: '新增条目' }, '+ Add'),
      h('button', { class: 'nrp-btn nrp-btn-sm', type: 'button', title: '刷新列表' }, 'Refresh')
    ]);
    storeTableWrapEl = h('div', { class: 'nrp-store-table-wrap' });
    storeWrapEl = h('div', { class: 'nrp-store' }, [storeTabsEl, storeToolsEl, storeTableWrapEl]);
    storeWrapEl.style.display = 'none';
    updateStoreSubTabButtons();

    netTabBtnEl = makeTabButton('Network', 'nrp-tab-count-network', '接口请求（XHR / fetch / SSE）', true);
    resTabBtnEl = makeTabButton('Resources', 'nrp-tab-count-resource', '静态资源', false);
    wsTabBtnEl = makeTabButton('WS', 'nrp-tab-count-ws', 'WebSocket 连接与消息', false);
    storeTabBtnEl = makeTabButton('Storage', 'nrp-tab-count-storage', '查看 / 编辑 Cookies、LocalStorage、SessionStorage', false);

    const header = h('div', { class: 'nrp-header' }, [
      h('div', { class: 'nrp-title' }, [h('span', { class: 'nrp-dot' }), 'Network Debugger']),
      h('div', { class: 'nrp-tabs' }, [netTabBtnEl, resTabBtnEl, wsTabBtnEl, storeTabBtnEl]),
      h('div', { class: 'nrp-actions' }, [collapseBtn, clearBtnEl, exportBtnEl, harBtnEl, fsBtn, hideBtn])
    ]);

    const body = h('div', { class: 'nrp-body' }, [
      h('div', { class: 'nrp-toolbar' }, [searchEl, groupWrapEl, statsEl]),
      chipsEl, chipsResEl, netTableWrapEl, resTableWrapEl, wsTableWrapEl, storeWrapEl
    ]);

    panelEl = h('div', { class: 'nrp-panel' }, [header, body]);

    const fab = h('button', { class: 'nrp-fab', type: 'button', title: 'Show Network Debugger' }, 'NET');

    /* ---------- Network 详情模态框（统一工厂创建） ---------- */
    copyBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Copy' }, 'Copy');
    const curlBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Copy as cURL' }, 'cURL');
    const replayBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Replay request' }, 'Replay');
    modalParamsEl = h('div', { class: 'nrp-modal-params' });
    modalHeadersEl = h('div', { class: 'nrp-headers' });
    modalResponseEl = h('div', { class: 'nrp-section nrp-section-response' });

    netModal = createModal({
      titleClass: 'nrp-headline',
      tools: [curlBtn, replayBtn, copyBtn],
      body: [modalParamsEl, modalHeadersEl, modalResponseEl]
    });

    /* 兼容别名：原渲染函数中的引用直接指向工厂内部节点 */
    overlayEl = netModal.overlay;
    modalHeadlineEl = netModal.titleEl;
    modalContentEl = netModal.body;

    /* ---------- Storage 新增条目模态框 ---------- */
    storeAddTitleEl = h('span', null, '新增条目');
    storeAddKeyEl = h('input', {
      class: 'nrp-store-add-input', type: 'text',
      placeholder: 'Key（键名）', spellcheck: 'false'
    });
    storeAddValueEl = h('textarea', {
      class: 'nrp-store-add-input nrp-store-add-textarea',
      placeholder: 'Value（值）', spellcheck: 'false', rows: '4'
    });
    storeAddSaveEl = h('button', { class: 'nrp-btn nrp-btn-primary', type: 'button' }, 'Save');
    const storeAddCancelEl = h('button', { class: 'nrp-btn', type: 'button' }, 'Cancel');

    storeAddModal = createModal({
      overlayClass: 'nrp-store-add-overlay',
      modalClass: 'nrp-store-add-modal',
      titleClass: 'nrp-store-add-title',
      title: storeAddTitleEl,
      body: [
        h('label', { class: 'nrp-store-add-label' }, 'Key'),
        storeAddKeyEl,
        h('label', { class: 'nrp-store-add-label' }, 'Value'),
        storeAddValueEl
      ],
      footer: [storeAddSaveEl, storeAddCancelEl]
    });
    storeAddOverlayEl = storeAddModal.overlay;

    /* ---------- Storage 查看/编辑模态框 ---------- */
    storeViewTitleEl = h('span', null, '查看 / 编辑条目');
    storeViewKeyEl = h('input', {
      class: 'nrp-store-add-input', type: 'text',
      placeholder: 'Key（键名）', spellcheck: 'false'
    });
    storeViewValueEl = h('textarea', {
      class: 'nrp-store-add-input nrp-store-add-textarea nrp-store-view-textarea',
      placeholder: 'Value（值）', spellcheck: 'false', rows: '10'
    });
    storeViewSaveEl = h('button', { class: 'nrp-btn nrp-btn-primary', type: 'button' }, 'Save');
    const storeViewDeleteEl = h('button', {
      class: 'nrp-btn nrp-btn-danger', type: 'button', title: '删除该条目'
    }, 'Delete');
    const storeViewCloseEl = h('button', { class: 'nrp-btn', type: 'button' }, 'Close');

    storeViewHlEl = h('pre', { class: 'nrp-modal-body nrp-store-view-hl' }, '');
    storeViewHlEl.style.display = 'none';
    storeViewPreColEl = h('div', { class: 'nrp-store-view-col' }, [
      h('label', { class: 'nrp-store-add-label' }, 'JSON 预览（只读）'),
      storeViewHlEl
    ]);
    storeViewPreColEl.style.display = 'none';

    storeViewTabsEl = h('div', { class: 'nrp-store-view-tabs' }, [
      h('button', { class: 'nrp-store-view-tab nrp-store-view-tab-active', type: 'button', 'data-svtab': 'edit' }, '编辑 Value'),
      h('button', { class: 'nrp-store-view-tab', type: 'button', 'data-svtab': 'preview' }, 'JSON 预览')
    ]);

    const storeViewSplitEl = h('div', { class: 'nrp-store-view-split' }, [
      h('div', { class: 'nrp-store-view-col' }, [
        h('label', { class: 'nrp-store-add-label' }, 'Value'),
        storeViewValueEl
      ]),
      storeViewPreColEl
    ]);

    storeViewModal = createModal({
      overlayClass: 'nrp-store-add-overlay nrp-store-view-overlay',
      modalClass: 'nrp-store-view-modal',
      bodyClass: 'nrp-store-view-body',
      titleClass: 'nrp-store-add-title',
      title: storeViewTitleEl,
      body: [
        h('label', { class: 'nrp-store-add-label' }, 'Key'),
        storeViewKeyEl,
        storeViewTabsEl,
        storeViewSplitEl
      ],
      footer: [storeViewDeleteEl, storeViewCloseEl, storeViewSaveEl],
      showClose: false
    });
    storeViewOverlayEl = storeViewModal.overlay;

    rootEl = h('div', { id: 'nrp-root' }, [
      panelEl, fab,
      netModal.overlay,
      storeAddModal.overlay,
      storeViewModal.overlay
    ]);
    (document.documentElement || document.body).appendChild(rootEl);

    panelEl.style.display = 'none';
    fab.style.display = 'flex';

    collapseBtn.addEventListener('click', function () {
      const collapsed = panelEl.classList.toggle('nrp-collapsed');
      collapseBtn.textContent = collapsed ? '□' : '—';
      collapseBtn.title = collapsed ? 'Maximize' : 'Minimize';
    });

    netTabBtnEl.addEventListener('click', function () { switchTab(TAB_NETWORK); });
    resTabBtnEl.addEventListener('click', function () { switchTab(TAB_RESOURCE); });
    if (typeof wsTabBtnEl !== 'undefined' && wsTabBtnEl) wsTabBtnEl.addEventListener('click', function () { switchTab(TAB_WS); });
    storeTabBtnEl.addEventListener('click', function () { switchTab(TAB_STORAGE); });

    Array.prototype.forEach.call(storeTabsEl.children, function (btn) {
      btn.addEventListener('click', function () {
        storeSubTab = btn.getAttribute('data-store') || 'local';
        updateStoreSubTabButtons();
        if (currentTab === TAB_STORAGE) renderStorage();
      });
    });
    storeToolsEl.children[0].addEventListener('click', addStorageEntry);
    storeToolsEl.children[1].addEventListener('click', function () {
      if (currentTab === TAB_STORAGE) renderStorage();
    });

    /* Storage 新增条目事件 */
    storeAddSaveEl.addEventListener('click', saveAddStorageModal);
    storeAddCancelEl.addEventListener('click', closeAddStorageModal);
    storeAddKeyEl.addEventListener('keydown', function (e) {
      if (e.key === 'Enter') { e.preventDefault(); storeAddValueEl.focus(); }
      else if (e.key === 'Escape') { e.preventDefault(); closeAddStorageModal(); }
    });
    storeAddValueEl.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); saveAddStorageModal(); }
      else if (e.key === 'Escape') { e.preventDefault(); closeAddStorageModal(); }
    });

    /* Storage 查看/编辑事件 */
    storeViewSaveEl.addEventListener('click', saveViewStorageModal);
    storeViewDeleteEl.addEventListener('click', deleteFromViewModal);
    storeViewCloseEl.addEventListener('click', closeViewStorageModal);
    storeViewValueEl.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); saveViewStorageModal(); }
      else if (e.key === 'Escape') { e.preventDefault(); closeViewStorageModal(); }
    });
    storeViewValueEl.addEventListener('input', updateStoreViewHighlight);
    Array.prototype.forEach.call(storeViewTabsEl.children, function (btn) {
      btn.addEventListener('click', function () {
        setStoreViewTab(btn.getAttribute('data-svtab') === 'preview' ? 'preview' : 'edit');
      });
    });
    window.addEventListener('resize', function () { applyStoreViewTab(); });

    clearBtnEl.addEventListener('click', function () {
      const wantRes = currentTab === TAB_RESOURCE;
      const kept = [];
      for (let i = 0; i < records.length; i++) {
        const r = records[i];
        if ((r.kind === 'resource') === wantRes) {
          if (r.streamId) delete streamMap[r.streamId];
          continue;
        }
        kept.push(r);
      }
      records = kept;
      collapsedGroups = {};
      if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
      if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
      tabState[currentTab].collapsed = collapsedGroups;
      render();
    });

    exportBtnEl.addEventListener('click', exportJSON);
    if (typeof harBtnEl !== 'undefined' && harBtnEl) harBtnEl.addEventListener('click', exportHAR);
    fsBtn.addEventListener('click', toggleFullscreen);

    hideBtn.addEventListener('click', function () {
      panelEl.style.display = 'none';
      fab.style.display = 'flex';
    });
    fab.addEventListener('click', function () {
      panelEl.style.display = '';
      fab.style.display = 'none';
    });

    searchEl.addEventListener('input', scheduleRender);

    copyBtn.addEventListener('click', function () {
      copyText(currentCopyText).then(function () {
        copyBtn.textContent = 'Copied!';
        setTimeout(function () { copyBtn.textContent = 'Copy'; }, 1500);
      }, function () {
        copyBtn.textContent = 'Failed';
        setTimeout(function () { copyBtn.textContent = 'Copy'; }, 1500);
      });
    });

    /* cURL / Replay 按钮 */
    const curlBtnEl = netModal.toolsEl.querySelectorAll('.nrp-btn')[0];
    const replayBtnEl = netModal.toolsEl.querySelectorAll('.nrp-btn')[1];
    if (curlBtnEl) {
      curlBtnEl.addEventListener('click', function () {
        const r = currentModalRecord;
        if (!r) { curlBtnEl.textContent = 'N/A'; setTimeout(function(){curlBtnEl.textContent='cURL';},1000); return; }
        const c = buildCurlCommand(r);
        copyText(c).then(function () {
          curlBtnEl.textContent = 'Copied!';
          setTimeout(function () { curlBtnEl.textContent = 'cURL'; }, 1500);
        }, function () {
          curlBtnEl.textContent = 'Failed';
          setTimeout(function () { curlBtnEl.textContent = 'cURL'; }, 1500);
        });
      });
    }
    if (replayBtnEl) {
      replayBtnEl.addEventListener('click', function () {
        const r = currentModalRecord;
        if (!r) { replayBtnEl.textContent = 'N/A'; setTimeout(function(){replayBtnEl.textContent='Replay';},1000); return; }
        replayRequest(r);
      });
    }

    render();
  }

  /* ============================ 渲染逻辑 ============================ */

  function scheduleRender(delay) {
    if (renderTimer) return;
    renderTimer = setTimeout(function () {
      renderTimer = null;
      render();
    }, delay == null ? RENDER_DELAY : delay);
  }

  function matchResourceRecord(r, terms) {
    if (resFilterState.type.size && !resFilterState.type.has(r.resType)) return false;
    if (resFilterState.cache.size && !resFilterState.cache.has(r.cache)) return false;
    if (resFilterState.quick.size) {
      for (const flag of resFilterState.quick) {
        if (flag === 'slow' && !(r.duration != null && r.duration >= resSlowThreshold)) return false;
        if (flag === 'large' && !(r.size != null && r.size >= largeResThreshold)) return false;
      }
    }

    if (!terms.length) return true;

    const hay = (
        r.url + ' ' + (r.resType || '') + ' ' + resTypeLabel(r.resType) + ' ' +
        (r.initiatorType || '') + ' ' + (r.cache || '') + ' ' + (r.protocol || '') + ' ' +
        (r.duration == null ? '' : r.duration) + ' ' + (r.size || 0) + ' ' + (r.frameUrl || '')
    ).toLowerCase();
    for (let i = 0; i < terms.length; i++) {
      if (hay.indexOf(terms[i]) === -1) return false;
    }
    return true;
  }

  function getFiltered() {
    const raw = searchEl && searchEl.value ? searchEl.value : '';
    const q = raw.trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];
    const isRes = currentTab === TAB_RESOURCE;
    const out = [];
    for (let i = 0; i < records.length; i++) {
      const r = records[i];
      if (isRes ? r.kind !== 'resource' : r.kind === 'resource') continue;
      if (isRes ? matchResourceRecord(r, terms) : matchRecord(r, terms)) out.push(r);
    }
    return out;
  }

  function countByKind(kind) {
    let n = 0;
    for (let i = 0; i < records.length; i++) {
      if (records[i].kind === kind) n++;
    }
    return n;
  }

  function cell(text, cls, title) {
    const td = document.createElement('td');
    td.textContent = text;
    if (cls) td.className = cls;
    if (title) td.title = title;
    return td;
  }

  function buildRow(r) {
    const tr = document.createElement('tr');
    tr.className = 'nrp-data-row';

    tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
    tr.appendChild(cell(r.method, 'nrp-cell-method', r.method));

    const st = statusInfo(r);
    tr.appendChild(cell(st.text, st.cls, 'Status: ' + st.text));

    const urlTd = cell(r.url, 'nrp-cell-clickable', r.url);
    urlTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'url');
    });
    tr.appendChild(urlTd);

    const reqHeaderPreview = r.reqHeaders ? r.reqHeaders.split('\n').filter(Boolean).slice(0, 2).join('; ') : '';
    const reqHeaderTd = cell(reqHeaderPreview, 'nrp-cell-clickable nrp-cell-headers', r.reqHeaders || '(no request headers)');
    reqHeaderTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'req-headers');
    });
    tr.appendChild(reqHeaderTd);

    const params = r.params || '';
    const paramsTd = cell(params, 'nrp-cell-clickable nrp-cell-query', params);
    paramsTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'params');
    });
    tr.appendChild(paramsTd);

    const bodyStr = r.body || '';
    const bodyTd = cell(bodyStr, 'nrp-cell-clickable nrp-cell-body', bodyStr);
    bodyTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'body');
    });
    tr.appendChild(bodyTd);

    const respHeaderPreview = r.respHeaders ? r.respHeaders.split('\n').filter(Boolean).slice(0, 2).join('; ') : '';
    const respHeaderTd = cell(respHeaderPreview, 'nrp-cell-clickable nrp-cell-headers', r.respHeaders || '(no response headers)');
    respHeaderTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'resp-headers');
    });
    tr.appendChild(respHeaderTd);

    let preview;
    let previewCls = 'nrp-dim';
    if (r.responseKind === 'sse') {
      preview = '[SSE] ' + (r.sseEvents || 0) + ' events' +
          (r.sseDone ? '' : ' · streaming…') +
          (r.response ? ' · ' + formatSize(r.response.length) : '');
      previewCls = 'nrp-cell-sse';
    } else if (r.responseKind === 'image') {
      preview = '[Image] ' + (r.mimeType || '') + ' ' + (r.binarySize ? formatSize(r.binarySize) : '');
    } else if (r.responseKind === 'binary') {
      preview = '[Binary] ' + (r.mimeType || '') + ' ' + (r.binarySize ? formatSize(r.binarySize) : '');
    } else {
      preview = (r.response || '').replace(/\s+/g, ' ').slice(0, 400);
    }
    const respTd = cell(preview, 'nrp-cell-clickable ' + previewCls, preview.slice(0, 2000));
    respTd.addEventListener('click', function (e) {
      e.stopPropagation(); openFieldModal(r, 'response');
    });
    tr.appendChild(respTd);

    const durText = r.duration != null ? formatDuration(r.duration) : '';
    const durCls = 'nrp-dim' + (r.duration != null && r.duration >= slowThreshold ? ' nrp-st-err' : '');
    tr.appendChild(cell(durText, durCls, durText));

    tr.addEventListener('click', function () { openModal(r); });
    return tr;
  }

  function fmtMs(v) {
    return (Math.round((v || 0) * 100) / 100) + 'ms';
  }

  function timingSummary(t) {
    if (!t) return '';
    return 'blocked: ' + fmtMs(t.blocked) + '\n' +
        'dns: ' + fmtMs(t.dns) + '\n' +
        'tcp: ' + fmtMs(t.tcp) + '\n' +
        'ttfb: ' + fmtMs(t.ttfb) + '\n' +
        'download: ' + fmtMs(t.download) + '\n' +
        'total: ' + fmtMs(t.total);
  }

  function buildResourceRow(r) {
    const tr = document.createElement('tr');
    tr.className = 'nrp-data-row';

    tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));

    const typeText = resTypeLabel(r.resType);
    tr.appendChild(cell(
        typeText,
        'nrp-cell-restype nrp-restype-' + (r.resType || 'other'),
        (r.initiatorType || r.resType || '') + (r.protocol ? ' · ' + r.protocol : '')
    ));

    const urlTd = cell(r.url, 'nrp-cell-clickable', r.url);
    urlTd.addEventListener('click', function (e) {
      e.stopPropagation(); openResourceModal(r);
    });
    tr.appendChild(urlTd);

    const sizeText = r.size > 0 ? formatSize(r.size) : '—';
    const sizeTitle = 'transfer: ' + formatSize(r.size) + '\ndecoded: ' + formatSize(r.decodedSize) +
        '\nencoded: ' + formatSize(r.encodedSize) +
        '\n（≥ ' + formatSize(largeResThreshold) + ' 标红）';
    tr.appendChild(cell(
        sizeText,
        'nrp-cell-size' + (r.size >= largeResThreshold ? ' nrp-st-err' : ''),
        sizeTitle
    ));

    const dur = r.duration || 0;
    tr.appendChild(cell(dur > 0 ? formatDuration(dur) : '—',
        'nrp-dim' + (dur >= resSlowThreshold ? ' nrp-st-err' : ''),
        timingSummary(r.timing)));

    const srcText = r.cache === 'cache' ? 'cache' : (r.cache === 'network' ? 'network' : 'unknown');
    tr.appendChild(cell(srcText, 'nrp-cell-cache nrp-cache-' + r.cache, 'Source: ' + srcText));

    tr.addEventListener('click', function () { openResourceModal(r); });
    return tr;
  }

  function buildResourceHeadline(r) {
    clearEl(modalHeadlineEl);
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-sse' }, resTypeLabel(r.resType)));
    modalHeadlineEl.appendChild(h('span', {
      class: 'nrp-badge nrp-badge-mime', title: 'transfer size'
    }, r.size > 0 ? formatSize(r.size) : 'unknown size'));

    const cacheCls = r.cache === 'cache' ? 'nrp-badge-ok'
        : (r.cache === 'network' ? 'nrp-badge-time' : 'nrp-badge-other');
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge ' + cacheCls, title: 'Source' },
        r.cache === 'cache' ? 'cache' : (r.cache === 'network' ? 'network' : 'unknown')));

    if (r.protocol) {
      modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-frame', title: 'Protocol' }, r.protocol));
    }
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-dur', title: 'Duration' }, fmtMs(r.duration)));
    modalHeadlineEl.appendChild(
        h('span', { class: 'nrp-badge nrp-badge-time', title: formatFullTime(r.time) }, formatTime(r.time))
    );

    if (r.frameUrl) {
      let frameShort = r.frameUrl;
      try {
        const u = new URL(r.frameUrl);
        frameShort = u.host || u.href;
      } catch (e) { /* ignore */ }
      modalHeadlineEl.appendChild(
          h('span', { class: 'nrp-badge nrp-badge-frame', title: 'Frame: ' + r.frameUrl }, 'frame: ' + frameShort)
      );
    }

    modalHeadlineEl.appendChild(h('span', { class: 'nrp-modal-url', title: r.url }, r.url));
  }

  function buildResourceImagePreview(r) {
    const wrap = h('div', { class: 'nrp-image-wrap' });
    const info = (r.mimeType || 'img') + (r.size > 0 ? ' · ' + formatSize(r.size) : '');
    wrap.appendChild(h('div', { class: 'nrp-image-info' }, info));
    const img = h('img', {
      class: 'nrp-image-preview', src: r.url, alt: r.url,
      loading: 'lazy', referrerpolicy: 'no-referrer'
    });
    img.addEventListener('click', function () {
      try { window.open(r.url, '_blank'); } catch (e) {}
    });
    img.addEventListener('error', function () {
      const fb = h('div', { class: 'nrp-image-fallback' },
          '图片加载失败：可能被防盗链/跨域策略阻止，或地址已失效');
      wrap.appendChild(fb);
      img.remove();
    });
    wrap.appendChild(img);
    return wrap;
  }

  function openResourceModal(r) {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    currentModalRecord = null;
    currentModalExtra = null;

    buildResourceHeadline(r);

    clearEl(modalParamsEl);
    modalParamsEl.style.display = '';
    [
      ['Type', resTypeLabel(r.resType) + (r.initiatorType ? ' (initiator: ' + r.initiatorType + ')' : '')],
      ['Size', 'transfer ' + formatSize(r.size) + ' · decoded ' + formatSize(r.decodedSize) +
      ' · encoded ' + formatSize(r.encodedSize)],
      ['Source', r.cache === 'cache' ? 'cache'
          : (r.cache === 'network' ? 'network' : 'unknown（跨域资源默认不返回 transferSize=0）')],
      ['Protocol', r.protocol || 'unknown']
    ].forEach(function (pair) {
      const sec = makeSection(pair[0], pair[1], 'nrp-section-params');
      if (sec) modalParamsEl.appendChild(sec);
    });

    clearEl(modalHeadersEl);
    modalHeadersEl.style.display = '';
    const t = r.timing || {};
    const timingText = [
      'blocked  ' + fmtMs(t.blocked), 'dns      ' + fmtMs(t.dns),
      'tcp      ' + fmtMs(t.tcp), 'ttfb     ' + fmtMs(t.ttfb),
      'download ' + fmtMs(t.download), 'total    ' + fmtMs(t.total)
    ].join('\n');
    const tsec = makeSection('Timing', timingText, 'nrp-section-body');
    if (tsec) modalHeadersEl.appendChild(tsec);

    clearEl(modalResponseEl);
    modalResponseEl.style.display = '';
    const usec = makeSection('URL', r.url, 'nrp-section-params');
    if (usec) modalResponseEl.appendChild(usec);

    if (r.resType === 'img') {
      const psec = makeSection('Image Preview', buildResourceImagePreview(r), 'nrp-section-response');
      if (psec) modalResponseEl.appendChild(psec);
    }

    currentCopyText = r.url;
    openNetworkModal();
  }

  function buildGroupHeaderRow(key, count, colSpan) {
    const tr = document.createElement('tr');
    const collapsed = !!collapsedGroups[key];
    tr.className = 'nrp-group-row' + (collapsed ? ' nrp-group-collapsed' : '');

    const td = document.createElement('td');
    td.className = 'nrp-group-cell';
    td.colSpan = colSpan || 10;

    td.appendChild(h('span', { class: 'nrp-group-caret' }, '▾'));
    td.appendChild(h('span', { class: 'nrp-group-key' }, key || '(unknown)'));
    td.appendChild(h('span', { class: 'nrp-group-count' }, '— ' + count + ' request' + (count === 1 ? '' : 's')));

    tr.appendChild(td);

    tr.addEventListener('click', function () {
      collapsedGroups[key] = !collapsedGroups[key];
      render();
    });

    return tr;
  }

  function renderGrouped(filtered) {
    const groups = {};
    const order = [];
    filtered.forEach(function (r) {
      const key = getGroupKey(r, groupBy);
      if (!groups[key]) {
        groups[key] = [];
        order.push(key);
      }
      groups[key].push(r);
    });

    order.sort(function (a, b) { return groups[b].length - groups[a].length; });

    const frag = document.createDocumentFragment();
    const colSpan = currentTab === TAB_RESOURCE ? 6 : 10;

    order.forEach(function (key) {
      frag.appendChild(buildGroupHeaderRow(key, groups[key].length, colSpan));
      if (collapsedGroups[key]) return;
      const items = groups[key].slice().sort(function (a, b) { return a.time - b.time; });
      items.forEach(function (r) { frag.appendChild(buildRowFor(r)); });
    });

    return frag;
  }

  function renderFlat(filtered) {
    const frag = document.createDocumentFragment();
    for (let i = filtered.length - 1; i >= 0; i--) {
      frag.appendChild(buildRowFor(filtered[i]));
    }
    return frag;
  }

  function buildRowFor(r) {
    return currentTab === TAB_RESOURCE ? buildResourceRow(r) : buildRow(r);
  }

  function render() {
    if (currentTab === TAB_STORAGE) { renderStorage(); return; }
    if (currentTab === TAB_WS) { renderWS(); updateTabButtons(); return; }
    if (!tbodyEl) return;

    const isRes = currentTab === TAB_RESOURCE;
    const filtered = getFiltered();
    const total = isRes ? countByKind('resource') : countNetworkRecords();

    updateTabButtons();
    if (statsEl) statsEl.textContent = filtered.length + ' / ' + total;

    let frag;
    if (groupBy && filtered.length) frag = renderGrouped(filtered);
    else frag = renderFlat(filtered);

    if (!filtered.length) {
      const tr = document.createElement('tr');
      tr.className = 'nrp-empty-row';
      const td = document.createElement('td');
      td.className = 'nrp-empty';
      td.colSpan = isRes ? 6 : 10;
      td.textContent = total
          ? 'No records match the current filter.'
          : (isRes ? 'Waiting for static resources…' : 'Waiting for network requests…');
      tr.appendChild(td);
      frag.appendChild(tr);
    }

    clearEl(tbodyEl);
    tbodyEl.appendChild(frag);
  }


  /* ============================ Storage Tab ============================ */

  function updateStoreSubTabButtons() {
    if (!storeTabsEl) return;
    Array.prototype.forEach.call(storeTabsEl.children, function (btn) {
      const active = (btn.getAttribute('data-store') || '') === storeSubTab;
      btn.classList.toggle('nrp-store-tab-active', active);
    });
  }

  function getStorageEntries() {
    try {
      if (storeSubTab === 'cookie') {
        const out = [];
        const src = document.cookie || '';
        const pairs = src.split(';');
        for (let i = 0; i < pairs.length; i++) {
          const pair = pairs[i];
          if (!pair) continue;
          const idx = pair.indexOf('=');
          const name = (idx < 0 ? pair : pair.slice(0, idx)).trim();
          const value = idx < 0 ? '' : pair.slice(idx + 1).trim();
          if (name) out.push({ name: name, value: value });
        }
        return out;
      }
      const store = storeSubTab === 'local' ? localStorage : sessionStorage;
      const out = [];
      for (let i = 0; i < store.length; i++) {
        const k = store.key(i);
        out.push({ name: k, value: store.getItem(k) });
      }
      return out;
    } catch (e) {
      return [];
    }
  }

  function countStorageEntries() {
    try { return getStorageEntries().length; } catch (e) { return 0; }
  }

  function setStorageEntry(name, value) {
    try {
      if (storeSubTab === 'cookie') {
        document.cookie = name + '=' + encodeURIComponent(value) + '; path=/';
      } else {
        const store = storeSubTab === 'local' ? localStorage : sessionStorage;
        store.setItem(name, value);
      }
    } catch (e) { /* ignore */ }
  }

  function deleteStorageEntry(name) {
    try {
      if (storeSubTab === 'cookie') {
        document.cookie = name + '=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/';
      } else {
        const store = storeSubTab === 'local' ? localStorage : sessionStorage;
        store.removeItem(name);
      }
    } catch (e) { /* ignore */ }
  }

  function openAddStorageModal() {
    if (!storeAddModal) return;
    storeAddModal.setTitle('新增到 ' + STORE_SUB_LABELS[storeSubTab]);
    storeAddKeyEl.value = '';
    storeAddValueEl.value = '';
    storeAddModal.open();
    storeAddKeyEl.focus();
  }

  function closeAddStorageModal() {
    if (storeAddModal) storeAddModal.close();
  }

  function saveAddStorageModal() {
    const n = (storeAddKeyEl.value || '').trim();
    if (!n) { storeAddKeyEl.focus(); return; }
    setStorageEntry(n, storeAddValueEl.value || '');
    closeAddStorageModal();
    renderStorage();
  }

  function addStorageEntry() {
    openAddStorageModal();
  }

  function updateStoreViewHighlight() {
    if (!storeViewHlEl) return;
    const v = storeViewValueEl.value || '';
    if (isJSONString(v) && v.length <= HIGHLIGHT_MAX_BYTES) {
      storeViewHlEl.innerHTML = highlightJSON(prettyJSONText(v));
      storeViewHlEl.style.display = '';
      if (storeViewPreColEl) storeViewPreColEl.style.display = '';
    } else {
      storeViewHlEl.style.display = 'none';
      if (storeViewPreColEl) storeViewPreColEl.style.display = 'none';
    }
    applyStoreViewTab();
  }

  function isMobileView() {
    try { return window.matchMedia('(max-width: 768px)').matches; }
    catch (e) { return false; }
  }

  function setStoreViewTabButtons() {
    if (!storeViewTabsEl) return;
    const btns = storeViewTabsEl.children;
    for (let i = 0; i < btns.length; i++) {
      btns[i].classList.toggle('nrp-store-view-tab-active', btns[i].getAttribute('data-svtab') === storeViewTab);
    }
  }

  function applyStoreViewTab() {
    if (!storeViewValueEl || !storeViewPreColEl) return;
    const mobile = isMobileView();
    const valueCol = storeViewValueEl.parentNode;
    const previewOk = !!(storeViewHlEl && storeViewHlEl.style.display !== 'none');
    if (!mobile) {
      if (valueCol) valueCol.style.display = '';
      return;
    }
    if (storeViewTab === 'preview' && !previewOk) {
      storeViewTab = 'edit';
      setStoreViewTabButtons();
    }
    const showPreview = storeViewTab === 'preview' && previewOk;
    if (valueCol) valueCol.style.display = showPreview ? 'none' : '';
    storeViewPreColEl.style.display = showPreview ? '' : 'none';
  }

  function setStoreViewTab(tab) {
    storeViewTab = tab;
    setStoreViewTabButtons();
    applyStoreViewTab();
  }

  function openViewStorageModal(entry) {
    if (!storeViewModal) return;
    storeViewEntry = entry;
    storeViewTab = 'edit';
    setStoreViewTabButtons();
    storeViewModal.setTitle('查看 / 编辑 · ' + STORE_SUB_LABELS[storeSubTab]);
    storeViewKeyEl.value = entry.name;
    storeViewValueEl.value = entry.value;
    updateStoreViewHighlight();
    storeViewModal.open();
    storeViewValueEl.focus();
  }

  function closeViewStorageModal() {
    if (storeViewModal) storeViewModal.close();
  }

  function saveViewStorageModal() {
    if (!storeViewEntry) return;
    const n = (storeViewKeyEl.value || '').trim();
    if (!n) { storeViewKeyEl.focus(); return; }
    if (n !== storeViewEntry.name) deleteStorageEntry(storeViewEntry.name);
    setStorageEntry(n, storeViewValueEl.value || '');
    closeViewStorageModal();
    renderStorage();
  }

  function deleteFromViewModal() {
    if (!storeViewEntry) return;
    deleteStorageEntry(storeViewEntry.name);
    closeViewStorageModal();
    renderStorage();
  }

  function buildStorageRow(entry) {
    const tr = document.createElement('tr');
    tr.className = 'nrp-store-row';

    const tdName = document.createElement('td');
    tdName.className = 'nrp-store-td nrp-store-name';
    tdName.textContent = entry.name;
    tdName.title = entry.name;
    tr.appendChild(tdName);

    const tdVal = document.createElement('td');
    tdVal.className = 'nrp-store-td nrp-store-value';
    const valText = document.createElement('div');
    valText.className = 'nrp-store-value-text';
    valText.textContent = entry.value;
    valText.title = '点击查看 / 编辑完整内容';
    valText.addEventListener('click', function () { openViewStorageModal(entry); });
    tdVal.appendChild(valText);
    tr.appendChild(tdVal);

    const tdAct = document.createElement('td');
    tdAct.className = 'nrp-store-td nrp-store-actions';
    const delBtn = h('button', { class: 'nrp-btn nrp-btn-sm', type: 'button', title: '删除该条目' }, 'Delete');
    delBtn.addEventListener('click', function () {
      deleteStorageEntry(entry.name);
      renderStorage();
    });
    tdAct.appendChild(delBtn);
    tr.appendChild(tdAct);

    return tr;
  }

  function renderStorage() {
    if (!storeTableWrapEl) return;

    const q = (searchEl && searchEl.value ? searchEl.value : '').trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];

    let entries;
    try { entries = getStorageEntries(); } catch (e) { entries = []; }

    const filtered = entries.filter(function (e) {
      if (!terms.length) return true;
      const hay = (e.name + ' ' + e.value).toLowerCase();
      for (let i = 0; i < terms.length; i++) {
        if (hay.indexOf(terms[i]) === -1) return false;
      }
      return true;
    });

    if (statsEl) statsEl.textContent = filtered.length + ' / ' + entries.length;
    updateTabButtons();

    const table = h('table', { class: 'nrp-store-table' }, [
      h('colgroup', null, [
        h('col', { style: 'width:30%' }),
        h('col', { style: 'width:55%' }),
        h('col', { style: 'width:15%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', { class: 'nrp-store-th' }, 'Name'),
        h('th', { class: 'nrp-store-th' }, 'Value'),
        h('th', { class: 'nrp-store-th nrp-store-actions' }, 'Actions')
      ]))
    ]);
    const tbody = h('tbody');

    if (!filtered.length) {
      const tr = document.createElement('tr');
      tr.className = 'nrp-store-empty-row';
      const td = document.createElement('td');
      td.className = 'nrp-store-empty';
      td.colSpan = 3;
      td.textContent = entries.length
          ? '没有匹配当前搜索的条目。'
          : ('当前 ' + STORE_SUB_LABELS[storeSubTab] + ' 为空。');
      tr.appendChild(td);
      tbody.appendChild(tr);
    } else {
      filtered.forEach(function (e) { tbody.appendChild(buildStorageRow(e)); });
    }

    table.appendChild(tbody);

    clearEl(storeTableWrapEl);
    storeTableWrapEl.appendChild(table);
  }


  function renderWS() {
    if (!wsTableWrapEl) return;
    const q = (searchEl && searchEl.value ? searchEl.value : '').trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];
    let list = wsRecords.slice();
    if (terms.length) {
      list = list.filter(function (r) {
        const hay = (r.url + ' ' + (r.state || '')).toLowerCase();
        for (let i = 0; i < terms.length; i++) {
          if (hay.indexOf(terms[i]) === -1) return false;
        }
        return true;
      });
    }
    if (statsEl) statsEl.textContent = list.length + ' / ' + wsRecords.length;
    const tbody = wsTableWrapEl.querySelector('tbody');
    if (!tbody) return;
    clearEl(tbody);
    if (!list.length) {
      const tr = document.createElement('tr');
      tr.className = 'nrp-empty-row';
      const td = document.createElement('td');
      td.className = 'nrp-empty';
      td.colSpan = 5;
      td.textContent = wsRecords.length ? 'No WebSocket connections match the filter.' : 'Waiting for WebSocket connections...';
      tr.appendChild(td);
      tbody.appendChild(tr);
      return;
    }
    for (let i = list.length - 1; i >= 0; i--) {
      const r = list[i];
      const tr = document.createElement('tr');
      tr.className = 'nrp-data-row';
      tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
      tr.appendChild(cell(r.state || '', 'nrp-cell-method'));
      const urlTd = cell(r.url, 'nrp-cell-clickable');
      urlTd.addEventListener('click', function () { openWSModal(r); });
      tr.appendChild(urlTd);
      tr.appendChild(cell(String((r.messages && r.messages.length) || 0), 'nrp-cell-method'));
      const info = r.state === 'closed' ? ('closed' + (r.closeCode != null ? ' ' + r.closeCode : '')) : (r.state || '');
      tr.appendChild(cell(info, 'nrp-dim'));
      tr.addEventListener('click', function () { openWSModal(r); });
      tbody.appendChild(tr);
    }
  }

  function openWSModal(r) {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    currentModalRecord = null;
    currentModalExtra = null;
    clearEl(modalHeadlineEl);
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-other' }, 'WebSocket'));
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-mime' }, r.state || ''));
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-modal-url', title: r.url }, r.url));
    clearEl(modalParamsEl);
    modalParamsEl.style.display = 'none';
    clearEl(modalHeadersEl);
    modalHeadersEl.style.display = '';
    const info = [
      'State: ' + (r.state || ''),
      'Messages: ' + ((r.messages && r.messages.length) || 0),
      r.openTime != null ? ('Open after: ' + r.openTime + 'ms') : '',
      r.closeCode != null ? ('Close code: ' + r.closeCode) : '',
      r.closeReason ? ('Close reason: ' + r.closeReason) : ''
    ].filter(Boolean).join('\n');
    const sec = makeSection('Connection Info', info);
    if (sec) modalHeadersEl.appendChild(sec);
    clearEl(modalResponseEl);
    modalResponseEl.style.display = '';
    let msgText = '';
    if (r.messages && r.messages.length) {
      for (let i = 0; i < r.messages.length; i++) {
        const m = r.messages[i];
        const d = new Date(m.time);
        const ts = pad(d.getHours(),2)+':'+pad(d.getMinutes(),2)+':'+pad(d.getSeconds(),2)+'.'+pad(d.getMilliseconds(),3);
        msgText += '[' + ts + '] ' + (m.dir === 'out' ? '→ SEND' : '← RECV') + '\n' + m.data + '\n\n';
      }
    } else {
      msgText = '(no messages)';
    }
    currentCopyText = msgText;
    const msec = makeSection('Messages (' + ((r.messages && r.messages.length) || 0) + ')', msgText, 'nrp-section-response');
    if (msec) modalResponseEl.appendChild(msec);
    copyBtn.textContent = 'Copy';
    if (netModal) netModal.open();
  }


  /* ============================ 弹窗逻辑 ============================ */

  function addBadge(cls, text, title) {
    return h('span', { class: 'nrp-badge ' + cls, title: title || undefined }, text);
  }

  function frameBadgeText(url) {
    if (!url) return '';
    try {
      const u = new URL(url);
      return u.host || u.href;
    } catch (e) {
      return url;
    }
  }

  function buildHeadline(r, extraLabel) {
    clearEl(modalHeadlineEl);
    modalHeadlineEl.appendChild(addBadge('nrp-badge-method', r.method));

    const isSse = r.kind === 'sse';
    modalHeadlineEl.appendChild(addBadge(
        isSse ? 'nrp-badge-sse' : 'nrp-badge-other',
        isSse ? 'SSE' : (r.kind === 'fetch' ? 'fetch' : 'XHR'),
        'Request type'
    ));

    const st = statusInfo(r);
    const stCls = st.cls === 'nrp-st-ok' ? 'nrp-badge-ok'
        : (st.cls === 'nrp-st-err' ? 'nrp-badge-err' : 'nrp-badge-other');
    modalHeadlineEl.appendChild(addBadge(stCls, st.text, 'Status: ' + st.text));

    if (r.responseKind === 'sse' && !r.sseDone) {
      modalHeadlineEl.appendChild(addBadge('nrp-badge-live', '● LIVE', '流尚未结束'));
    }

    modalHeadlineEl.appendChild(addBadge('nrp-badge-time', formatTime(r.time), formatFullTime(r.time)));

    if (r.duration != null) {
      modalHeadlineEl.appendChild(addBadge('nrp-badge-dur', formatDuration(r.duration), 'Duration'));
    }

    if (r.mimeType) {
      modalHeadlineEl.appendChild(addBadge('nrp-badge-mime', r.mimeType.split(';')[0].trim(), 'MIME: ' + r.mimeType));
    }

    if (r.frameUrl) {
      modalHeadlineEl.appendChild(addBadge('nrp-badge-frame', 'frame: ' + frameBadgeText(r.frameUrl), 'Frame: ' + r.frameUrl));
    }

    if (extraLabel) {
      modalHeadlineEl.appendChild(addBadge('nrp-badge-other', extraLabel));
    }

    modalHeadlineEl.appendChild(h('span', { class: 'nrp-modal-url', title: r.url }, r.url));
  }

  function countParams(s) {
    if (!s) return 0;
    return s.split('&').filter(Boolean).length;
  }

  function fillParamsBlock(r, onlyField) {
    clearEl(modalParamsEl);

    const hasQuery = !!r.params;
    const hasBody = !!r.body;

    if (!onlyField && !hasQuery && !hasBody) {
      modalParamsEl.style.display = 'none';
      return;
    }
    if (onlyField && onlyField !== 'params' && onlyField !== 'body') {
      modalParamsEl.style.display = 'none';
      return;
    }

    modalParamsEl.style.display = '';

    if (!onlyField || onlyField === 'params') {
      const sec = makeSection(
          'Params (' + countParams(r.params) + ')',
          hasQuery ? r.params : '(no params)',
          'nrp-section-params'
      );
      if (sec) modalParamsEl.appendChild(sec);
    }

    if (!onlyField || onlyField === 'body') {
      const title = 'Body' + (hasBody ? ' (' + formatSize(r.body.length) + ')' : ' (0)');
      const sec = makeSection(title, hasBody ? r.body : '(no body)', 'nrp-section-body');
      if (sec) modalParamsEl.appendChild(sec);
    }
  }

  function makeSection(title, content, extraClass) {
    if (content == null && !extraClass) return null;

    const titleEl = h('div', { class: 'nrp-section-title' }, [
      h('span', { class: 'nrp-caret' }, '▾'),
      title
    ]);
    const contentEl = h('div', { class: 'nrp-section-content' });

    if (content instanceof Node) {
      contentEl.appendChild(content);
    } else if (content != null) {
      contentEl.textContent = String(content);
    }

    titleEl.addEventListener('click', function () {
      titleEl.classList.toggle('nrp-collapsed');
    });

    return h('div', { class: 'nrp-section' + (extraClass ? ' ' + extraClass : '') }, [
      titleEl, contentEl
    ]);
  }

  function fillHeadersBlockFor(r, mode) {
    clearEl(modalHeadersEl);
    const parts = [];
    if (mode !== 'resp') {
      parts.push(makeSection(
          'Request Headers (' + (r.reqHeaders ? r.reqHeaders.split('\n').filter(Boolean).length : 0) + ')',
          r.reqHeaders || '(no request headers)'
      ));
    }
    if (mode !== 'req') {
      parts.push(makeSection(
          'Response Headers (' + (r.respHeaders ? r.respHeaders.split('\n').filter(Boolean).length : 0) + ')',
          r.respHeaders || '(no response headers)'
      ));
    }
    parts.forEach(function (sec) { if (sec) modalHeadersEl.appendChild(sec); });
    modalHeadersEl.style.display = '';
  }

  function fillHeadersBlock(r) { fillHeadersBlockFor(r, 'both'); }
  function fillReqHeadersBlock(r) { fillHeadersBlockFor(r, 'req'); }
  function fillRespHeadersBlock(r) { fillHeadersBlockFor(r, 'resp'); }


  function tryParseJSON(s) {
    try {
      const t = String(s || '').trim();
      if (!t) return null;
      if ((t[0] === '{' && t[t.length-1] === '}') || (t[0] === '[' && t[t.length-1] === ']')) {
        return JSON.parse(t);
      }
      return null;
    } catch (e) { return null; }
  }

  function buildJSONTree(obj, search) {
    const container = document.createElement('div');
    container.className = 'nrp-json-tree';
    function renderNode(val, key, depth) {
      const wrap = document.createElement('div');
      wrap.className = 'nrp-json-node';
      wrap.style.paddingLeft = (depth * 12) + 'px';
      if (val === null) {
        wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '<span class="nrp-hl-null">null</span>';
        return wrap;
      }
      if (typeof val === 'boolean') {
        wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '<span class="nrp-hl-bool">' + val + '</span>';
        return wrap;
      }
      if (typeof val === 'number') {
        wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '<span class="nrp-hl-num">' + val + '</span>';
        return wrap;
      }
      if (typeof val === 'string') {
        let s2 = val;
        if (search && s2.toLowerCase().indexOf(search.toLowerCase()) !== -1) {
          s2 = escapeHTML(s2).replace(new RegExp(escapeHTML(search).replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'ig'), function(m){ return '<mark>' + m + '</mark>'; });
          wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '<span class="nrp-hl-str">"' + s2 + '"</span>';
        } else {
          wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '<span class="nrp-hl-str">"' + escapeHTML(s2) + '"</span>';
        }
        return wrap;
      }
      if (Array.isArray(val)) {
        const details = document.createElement('details');
        details.open = depth < 2;
        const summary = document.createElement('summary');
        summary.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '[Array(' + val.length + ')]';
        details.appendChild(summary);
        for (let i = 0; i < val.length; i++) {
          details.appendChild(renderNode(val[i], i, depth + 1));
        }
        wrap.appendChild(details);
        return wrap;
      }
      if (typeof val === 'object') {
        const keys = Object.keys(val);
        const details = document.createElement('details');
        details.open = depth < 2;
        const summary = document.createElement('summary');
        summary.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '{Object(' + keys.length + ')}';
        details.appendChild(summary);
        for (let i = 0; i < keys.length; i++) {
          details.appendChild(renderNode(val[keys[i]], keys[i], depth + 1));
        }
        wrap.appendChild(details);
        return wrap;
      }
      wrap.textContent = String(val);
      return wrap;
    }
    container.appendChild(renderNode(obj, null, 0));
    return container;
  }


  function buildResponseContent(r) {
    if (r.responseKind === 'image' && r.previewUrl) {
      const wrap = h('div', { class: 'nrp-image-wrap' });
      wrap.appendChild(h('div', { class: 'nrp-image-info' },
          (r.mimeType || 'image') + (r.binarySize ? ' · ' + formatSize(r.binarySize) : '')
      ));
      const img = h('img', {
        class: 'nrp-image-preview', src: r.previewUrl, alt: 'response image'
      });
      img.addEventListener('error', function () {
        const fb = h('div', { class: 'nrp-image-fallback' }, '图片无法显示（可能已损坏或被跨域策略阻止）');
        wrap.appendChild(fb);
        img.remove();
      });
      wrap.appendChild(img);
      currentCopyText = r.previewUrl;
      return wrap;
    }

    if (r.responseKind === 'image' && !r.previewUrl) {
      const wrap = h('div', { class: 'nrp-binary-wrap' });
      wrap.appendChild(h('div', { class: 'nrp-binary-icon' }, '🖼'));
      wrap.appendChild(h('div', { class: 'nrp-binary-title' }, 'Image Response'));
      wrap.appendChild(h('div', { class: 'nrp-binary-meta' },
          'MIME: ' + (r.mimeType || 'unknown') + '\n' +
          'Size: ' + (r.binarySize ? formatSize(r.binarySize) : 'unknown') + '\n' +
          '预览不可用（超过 ' + formatSize(MAX_BINARY_PREVIEW) + ' 或读取失败）'
      ));
      currentCopyText = r.response || '';
      return wrap;
    }

    if (r.responseKind === 'binary') {
      const wrap = h('div', { class: 'nrp-binary-wrap' });
      wrap.appendChild(h('div', { class: 'nrp-binary-icon' }, '📦'));
      wrap.appendChild(h('div', { class: 'nrp-binary-title' }, 'Binary Response'));
      wrap.appendChild(h('div', { class: 'nrp-binary-meta' },
          'MIME: ' + (r.mimeType || 'unknown') + '\n' +
          'Size: ' + (r.binarySize ? formatSize(r.binarySize) : 'unknown') + '\n' +
          '二进制内容无法以文本形式展示'
      ));
      currentCopyText = r.response || '';
      return wrap;
    }

    const raw = r.response == null ? '' : String(r.response);
    const trimmed = raw.trim();

    let formatted, isJson = false;
    if (!trimmed) {
      formatted = r.responseKind === 'sse' ? '(waiting for events…)' : '(empty response)';
    } else if (r.responseKind === 'sse') {
      formatted = raw;
    } else {
      formatted = raw;
      try { formatted = prettyJSONText(trimmed); isJson = true; } catch (e) {}
    }

    currentCopyText = formatted;
    const container = document.createElement('div');
    container.className = 'nrp-response-container';

    const modeWrap = document.createElement('div');
    modeWrap.className = 'nrp-response-mode';
    const rawBtn = document.createElement('button');
    rawBtn.className = 'nrp-btn nrp-btn-sm' + (responseViewMode !== 'tree' ? ' nrp-btn-active' : '');
    rawBtn.textContent = 'Raw';
    const treeBtn = document.createElement('button');
    treeBtn.className = 'nrp-btn nrp-btn-sm' + (responseViewMode === 'tree' ? ' nrp-btn-active' : '');
    treeBtn.textContent = 'Tree';
    modeWrap.appendChild(rawBtn);
    modeWrap.appendChild(treeBtn);
    container.appendChild(modeWrap);

    const bodyWrap = document.createElement('div');
    bodyWrap.className = 'nrp-response-body-wrap';

    function renderBody() {
      clearEl(bodyWrap);
      if (responseViewMode === 'tree' && isJson && r.responseKind !== 'sse') {
        try {
          const parsed = tryParseJSON(formatted) || tryParseJSON(trimmed);
          if (parsed != null) {
            const tree = buildJSONTree(parsed, '');
            bodyWrap.appendChild(tree);
            return;
          }
        } catch (e) {}
      }
      const pre = document.createElement('pre');
      pre.className = 'nrp-modal-body';
      const liveSse = r.responseKind === 'sse' && !r.sseDone;
      if (isJson && !liveSse && responseViewMode !== 'tree' && formatted.length <= HIGHLIGHT_MAX_BYTES) {
        pre.innerHTML = highlightJSON(formatted);
      } else {
        pre.textContent = formatted;
      }
      bodyWrap.appendChild(pre);
    }

    rawBtn.addEventListener('click', function () {
      responseViewMode = 'raw';
      rawBtn.classList.add('nrp-btn-active');
      treeBtn.classList.remove('nrp-btn-active');
      renderBody();
    });
    treeBtn.addEventListener('click', function () {
      responseViewMode = 'tree';
      treeBtn.classList.add('nrp-btn-active');
      rawBtn.classList.remove('nrp-btn-active');
      renderBody();
    });

    container.appendChild(bodyWrap);
    renderBody();
    return container;
  }

  function responseSectionTitle(r) {
    if (r.responseKind === 'sse') {
      return 'Response · SSE · ' + (r.sseEvents || 0) + ' events' + (r.sseDone ? '' : ' · live');
    }
    if (r.responseKind === 'image') return 'Response · Image';
    if (r.responseKind === 'binary') return 'Response · Binary';
    return 'Response';
  }

  function refreshStreamModal(rec) {
    if (!currentModalRecord || currentModalRecord !== rec) return;
    if (!netModal || !netModal.isOpen) return;

    buildHeadline(rec, currentModalExtra);

    if (currentModalExtra === 'resp-headers') {
      const oldTitle = modalHeadersEl.querySelector('.nrp-section-title');
      const collapsed = oldTitle ? oldTitle.classList.contains('nrp-collapsed') : false;
      currentCopyText = rec.respHeaders || '';
      fillRespHeadersBlock(rec);
      if (collapsed) {
        const newTitle = modalHeadersEl.querySelector('.nrp-section-title');
        if (newTitle) newTitle.classList.add('nrp-collapsed');
      }
      return;
    }

    if (currentModalExtra === 'req-headers') {
      const oldTitle = modalHeadersEl.querySelector('.nrp-section-title');
      const collapsed = oldTitle ? oldTitle.classList.contains('nrp-collapsed') : false;
      currentCopyText = rec.reqHeaders || '';
      fillReqHeadersBlock(rec);
      if (collapsed) {
        const newTitle = modalHeadersEl.querySelector('.nrp-section-title');
        if (newTitle) newTitle.classList.add('nrp-collapsed');
      }
      return;
    }

    if (currentModalExtra === 'headers') {
      fillHeadersBlock(rec);
      return;
    }

    const oldTitle = modalResponseEl.querySelector('.nrp-section-title');
    const collapsed = oldTitle ? oldTitle.classList.contains('nrp-collapsed') : false;
    fillResponseBlock(rec);
    if (collapsed) {
      const newTitle = modalResponseEl.querySelector('.nrp-section-title');
      if (newTitle) newTitle.classList.add('nrp-collapsed');
    }
  }

  function fillResponseBlock(r) {
    clearEl(modalResponseEl);

    const content = buildResponseContent(r);
    const sec = makeSection(responseSectionTitle(r), content, 'nrp-section-response');
    if (sec) {
      modalResponseEl.appendChild(sec);
      modalResponseEl.style.display = '';
    } else {
      modalResponseEl.style.display = 'none';
    }
  }

  function prepModalForDetail() {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    clearAndHide(modalParamsEl);
    clearAndHide(modalHeadersEl);
    clearAndHide(modalResponseEl);
  }

  function openModal(r) {
    prepModalForDetail();

    currentModalRecord = r;
    currentModalExtra = null;

    buildHeadline(r, null);
    showEl(modalParamsEl);
    showEl(modalHeadersEl);
    showEl(modalResponseEl);
    fillParamsBlock(r);
    fillHeadersBlock(r);
    fillResponseBlock(r);

    openNetworkModal();
  }

  function openFieldModal(r, field) {
    prepModalForDetail();

    if (field === 'response') {
      currentModalRecord = r;
      currentModalExtra = 'Response';
      buildHeadline(r, 'Response');
      showEl(modalResponseEl);
      fillResponseBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'req-headers') {
      currentModalRecord = r;
      currentModalExtra = 'Request Headers';
      buildHeadline(r, 'Request Headers');
      currentCopyText = r.reqHeaders || '';
      showEl(modalHeadersEl);
      fillReqHeadersBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'resp-headers') {
      currentModalRecord = r;
      currentModalExtra = 'Response Headers';
      buildHeadline(r, 'Response Headers');
      currentCopyText = r.respHeaders || '';
      showEl(modalHeadersEl);
      fillRespHeadersBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'headers') {
      currentModalRecord = r;
      currentModalExtra = 'Headers';
      buildHeadline(r, 'Headers');

      const parts = [];
      if (r.reqHeaders) parts.push('Request Headers:\n' + r.reqHeaders);
      if (r.respHeaders) parts.push('Response Headers:\n' + r.respHeaders);
      const content = parts.length ? parts.join('\n\n') : '(no headers)';
      currentCopyText = content;
      const sec = makeSection('Headers', content);
      if (sec) { clearEl(modalHeadersEl); modalHeadersEl.appendChild(sec); }
      showEl(modalHeadersEl);

      showEl(modalResponseEl);
      fillResponseBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'params' || field === 'body') {
      currentModalRecord = r;
      currentModalExtra = field === 'params' ? 'Params' : 'Body';
      currentCopyText = (field === 'params' ? r.params : r.body) || '';
      buildHeadline(r, field === 'params' ? 'Params' : 'Body');
      showEl(modalParamsEl);
      fillParamsBlock(r, field);
      openNetworkModal();
      return;
    }

    currentModalRecord = r;
    currentModalExtra = 'URL';
    const contentText = r.url || '(empty url)';
    currentCopyText = contentText;

    buildHeadline(r, 'URL');

    const sec = makeSection('URL', contentText);
    if (sec) { clearEl(modalResponseEl); modalResponseEl.appendChild(sec); }
    showEl(modalResponseEl);

    openNetworkModal();
  }

  /* ============================ 复制 / 导出 ============================ */



  function replayRequest(r) {
    try {
      if (!r) return;
      const method = r.method || 'GET';
      const url = r.url || '';
      if (!url) return;
      const headers = {};
      if (r.reqHeaders) {
        const lines = r.reqHeaders.split(/\r?\n/);
        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          if (!line.trim()) continue;
          const idx = line.indexOf(':');
          if (idx === -1) continue;
          const k = line.slice(0, idx).trim();
          const v = line.slice(idx + 1).trim();
          if (!k) continue;
          if (k.toLowerCase() === 'host') continue;
          if (k.toLowerCase() === 'content-length') continue;
          headers[k] = v;
        }
      }
      const opts = { method: method, headers: headers };
      const body = r.body || '';
      if (body && method !== 'GET' && method !== 'HEAD') {
        opts.body = body;
      }
      fetch(url, opts).then(function (res) {
        try {
          if (window.nrpLog) window.nrpLog('Replayed', method, url, '->', res.status);
        } catch (e) {}
        alert('Replay: ' + method + ' ' + url + '\nStatus: ' + res.status);
      }).catch(function (e) {
        alert('Replay failed: ' + (e && e.message ? e.message : e));
      });
    } catch (e) {
      alert('Replay failed');
    }
  }

  function buildCurlCommand(r) {
    try {
      const url = r.url || '';
      if (!url) return '';
      let cmd = "curl -X " + (r.method || "GET") + " '" + url.replace(/'/g, "'\''") + "'";
      const reqHeaders = r.reqHeaders || '';
      if (reqHeaders) {
        const lines = reqHeaders.split(/\r?\n/);
        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          if (!line.trim()) continue;
          const idx = line.indexOf(':');
          if (idx === -1) continue;
          const k = line.slice(0, idx).trim();
          const v = line.slice(idx + 1).trim();
          if (!k) continue;
          if (k.toLowerCase() === 'content-length') continue;
          if (k.toLowerCase() === 'host') continue;
          cmd += " -H '" + (k + ": " + v).replace(/'/g, "'\''") + "'";
        }
      }
      const body = r.body || '';
      if (body && (r.method === 'POST' || r.method === 'PUT' || r.method === 'PATCH' || r.method === 'DELETE')) {
        cmd += " --data-raw '" + body.replace(/'/g, "'\''") + "'";
      }
      if (r.method === 'GET' && body) {
        cmd += " --data-raw '" + body.replace(/'/g, "'\''") + "'";
      }
      return cmd;
    } catch (e) {
      return '';
    }
  }

  function copyText(text) {
    return new Promise(function (resolve, reject) {
      function fallback() {
        try {
          const ta = document.createElement('textarea');
          ta.value = text;
          ta.setAttribute('readonly', '');
          ta.style.cssText = 'position:fixed;top:0;left:0;width:1px;height:1px;padding:0;border:0;opacity:0;';
          (document.body || document.documentElement).appendChild(ta);
          ta.select();
          ta.setSelectionRange(0, ta.value.length);
          const ok = document.execCommand('copy');
          ta.remove();
          ok ? resolve() : reject(new Error('copy failed'));
        } catch (e) {
          reject(e);
        }
      }

      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(resolve, fallback);
      } else {
        fallback();
      }
    });
  }


  function exportHAR() {
    const isRes = currentTab === TAB_RESOURCE;
    if (isRes) {
      // HAR is primarily for network; still export what we have
    }
    const entries = getFiltered().filter(function (r) { return r.kind !== 'resource'; }).map(function (r) {
      const reqHeaders = [];
      if (r.reqHeaders) {
        r.reqHeaders.split(/\r?\n/).forEach(function (line) {
          if (!line.trim()) return;
          const idx = line.indexOf(':');
          if (idx === -1) return;
          reqHeaders.push({ name: line.slice(0, idx).trim(), value: line.slice(idx + 1).trim() });
        });
      }
      const respHeaders = [];
      if (r.respHeaders) {
        r.respHeaders.split(/\r?\n/).forEach(function (line) {
          if (!line.trim()) return;
          const idx = line.indexOf(':');
          if (idx === -1) return;
          respHeaders.push({ name: line.slice(0, idx).trim(), value: line.slice(idx + 1).trim() });
        });
      }
      let cookies = [];
      let postData = undefined;
      if (r.body && (r.method === 'POST' || r.method === 'PUT' || r.method === 'PATCH')) {
        postData = { mimeType: (r.mimeType || 'text/plain'), text: r.body };
      }
      const started = r.time || Date.now();
      const timings = { blocked: -1, dns: -1, connect: -1, send: 0, wait: r.duration != null ? r.duration : -1, receive: 0, ssl: -1 };
      return {
        startedDateTime: new Date(started).toISOString(),
        time: r.duration != null ? r.duration : 0,
        request: {
          method: r.method || 'GET',
          url: r.url || '',
          httpVersion: 'HTTP/1.1',
          cookies: cookies,
          headers: reqHeaders,
          queryString: [],
          postData: postData,
          headersSize: -1,
          bodySize: r.body ? r.body.length : -1
        },
        response: {
          status: r.status || 0,
          statusText: statusInfo(r).text || '',
          httpVersion: 'HTTP/1.1',
          cookies: [],
          headers: respHeaders,
          content: {
            size: r.response ? r.response.length : 0,
            mimeType: r.mimeType || 'text/plain',
            text: r.response || ''
          },
          redirectURL: '',
          headersSize: -1,
          bodySize: r.response ? r.response.length : -1
        },
        cache: {},
        timings: timings
      };
    });
    const har = {
      log: {
        version: '1.2',
        creator: { name: 'Network Debugger', version: '1.0.0' },
        pages: [],
        entries: entries
      }
    };
    const json = JSON.stringify(har, null, 2);
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'network-' + new Date().toISOString().replace(/[:.]/g, '-') + '.har';
    a.style.display = 'none';
    (document.body || document.documentElement).appendChild(a);
    a.click();
    setTimeout(function () { a.remove(); URL.revokeObjectURL(url); }, 0);
  }

  function exportJSON() {
    const isRes = currentTab === TAB_RESOURCE;

    const data = getFiltered().map(function (r) {
      if (r.kind === 'resource') {
        return {
          id: r.id, type: 'resource', resType: r.resType,
          initiatorType: r.initiatorType, url: r.url,
          transferSize: r.size, encodedBodySize: r.encodedSize,
          decodedBodySize: r.decodedSize, cache: r.cache,
          protocol: r.protocol || '', duration: r.duration,
          timing: r.timing, frameUrl: r.frameUrl || '',
          time: formatFullTime(r.time)
        };
      }
      return {
        id: r.id, type: r.kind, method: r.method, url: r.url,
        params: r.params, body: r.body, reqHeaders: r.reqHeaders,
        respHeaders: r.respHeaders, status: r.status,
        responseKind: r.responseKind || 'text',
        sseEvents: r.sseEvents || 0, sseDone: !!r.sseDone,
        mimeType: r.mimeType || '', binarySize: r.binarySize || 0,
        response: r.response, duration: r.duration,
        frameUrl: r.frameUrl || '', time: formatFullTime(r.time)
      };
    });

    const json = JSON.stringify(data, null, 2);
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);

    const a = document.createElement('a');
    a.href = url;
    a.download = (isRes ? 'resources-' : 'network-requests-') +
        new Date().toISOString().replace(/[:.]/g, '-') + '.json';
    a.style.display = 'none';

    (document.body || document.documentElement).appendChild(a);
    a.click();

    setTimeout(function () {
      a.remove();
      URL.revokeObjectURL(url);
    }, 0);
  }

  /* ============================== 启动 ============================== */

  installInterceptors();
  installMessageListener();
  installResourceObserver();
  try { installWebSocketInterceptor(); } catch (e) {}

  /* 全局 Esc：先关最上层模态框，无模态框时退出全屏 */
  document.addEventListener('keydown', function (e) {
    if (e.key !== 'Escape') return;
    for (let i = openModals.length - 1; i >= 0; i--) {
      if (openModals[i].isOpen) { openModals[i].close(); return; }
    }
    if (isFullscreen) toggleFullscreen();
  });

  function bootstrap() {
    if (!IS_TOP) return;
    if (!document.documentElement) {
      setTimeout(bootstrap, 10);
      return;
    }
    buildUI();
  }

  bootstrap();
})();

