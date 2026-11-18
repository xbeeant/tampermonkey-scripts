// ==UserScript==
// @name         Network Debugger
// @namespace    http://tampermonkey.net/
// @version      1.2.2
// @description  Intercept XMLHttpRequest & fetch on any page, inspect requests/responses/headers in a draggable dark-theme panel with waterfall timing, resizable columns, search, grouping, JSON tree, HAR/JSON export, and a centralized settings panel.
// @description:zh-CN  拦截任意网页中的 XMLHttpRequest 与 fetch 请求，在可拖拽的深色悬浮面板中实时查看请求方法、状态码、URL、Query 参数、Body、请求/响应头与响应内容；支持请求耗时瀑布图、列宽拖拽、搜索过滤与分组、JSON Tree、cURL 复制、HAR/JSON 导出脱敏、导入会话及集中设置面板。
// @author       -
// @match        *://*/*
// @run-at       document-start
// @grant        GM_cookie
// @grant        unsafeWindow
// @license      MIT
// @homepageURL  https://github.com/xbeeant/tampermonkey-scripts
// @supportURL   https://github.com/xbeeant/tampermonkey-scripts/issues
// @downloadURL https://update.greasyfork.org/scripts/601227/Network%20Debugger.user.js
// @updateURL https://update.greasyfork.org/scripts/601227/Network%20Debugger.meta.js


// ==/UserScript==


(function () {
  'use strict';

  /* 有 @grant 时运行在隔离世界：window 是沙箱对象，页面 API 必须走 unsafeWindow */
  const win = (typeof unsafeWindow !== 'undefined' && unsafeWindow) ? unsafeWindow : window;

  /* ============================== 配置 ============================== */
  const DEFAULT_MAX_RECORDS = 1000;
  const DEFAULT_MAX_RESOURCE_RECORDS = 2000;
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
  const LS_KEY_FAB_POS = '__nrp_fab_pos__';
  const LS_KEY_PAUSED = '__nrp_paused__';
  const LS_KEY_MASK_EXPORT = '__nrp_mask_export__';
  const LS_KEY_COL_WIDTHS = '__nrp_col_widths__';
  const LS_KEY_DENSE = '__nrp_dense__';
  const LS_KEY_MAX_RECORDS = '__nrp_max_records__';
  const LS_KEY_MAX_RES_RECORDS = '__nrp_max_res_records__';
  const LS_KEY_WF_SCALE = '__nrp_wf_scale__';
  const FAB_DRAG_THRESHOLD = 4;
  const FAB_SIZE = 46;
  const FAB_EDGE = 6;
  const MIN_COL_WIDTH = 44;          // 列宽拖拽下限（px）
  const WF_BAR_MIN_PCT = 0.5;        // 瀑布图最短条占比，保证 0ms 请求可见

  const SCRIPT_VERSION = '1.3.0';
  const MAX_TEXT_RESPONSE = 512 * 1024;      // 单条文本响应最多保留的字符数
  const MAX_IMAGE_PREVIEW = 256 * 1024;      // 图片预览阈值（超过则只记元信息）
  const MAX_BINARY_READ = 2 * 1024 * 1024;   // 二进制响应最多读取的字节数
  const MAX_WS_RECORDS = 1000;
  const MAX_TREE_NODES = 2000;               // JSON Tree 最大节点数
  const MAX_SEEN_RESOURCE_KEYS = 10000;
  const MASK_PLACEHOLDER = '[masked]';

  const TAB_NETWORK = 'network';
  const TAB_RESOURCE = 'resource';
  const TAB_STORAGE = 'storage';
  const TAB_WS = 'websocket';
  const TAB_WATERFALL = 'waterfall';
  const TAB_CONSOLE = 'console';

  const MAX_CONSOLE_RECORDS = 2000;
  const MAX_CONSOLE_TEXT = 20000;
  const MAX_CONSOLE_ARG_TEXT = 4000;
  const MAX_CONSOLE_DEPTH = 4;
  const MAX_CONSOLE_KEYS = 50;

  const CONSOLE_LEVEL_GROUPS = [
    { label: 'Level', key: 'level', items: [
      { value: 'log',   label: 'log',   cls: 'clevel-log' },
      { value: 'info',  label: 'info',  cls: 'clevel-info' },
      { value: 'warn',  label: 'warn',  cls: 'clevel-warn' },
      { value: 'error', label: 'error', cls: 'clevel-error' },
      { value: 'debug', label: 'debug', cls: 'clevel-debug' },
      { value: 'other', label: '其他',  cls: 'clevel-other' }
    ], cls: '' }
  ];

  /* 表格列宽默认值（百分比），与 buildUI 中 colgroup 保持一致 */
  const COL_WIDTH_KEYS = ['network', 'resource', 'websocket'];
  const COL_DEFAULTS = {
    network: [8, 5, 5, 14, 12, 10, 12, 12, 17, 5],
    resource: [11, 8, 41, 10, 10, 20],
    websocket: [10, 8, 50, 12, 20]
  };
  /* 瀑布图时间窗：0 = 自适应全部请求 */
  const WF_SCALE_OPTIONS = [
    { value: 0, label: 'Fit all' },
    { value: 200, label: '200 ms' },
    { value: 500, label: '500 ms' },
    { value: 1000, label: '1 s' },
    { value: 2000, label: '2 s' },
    { value: 5000, label: '5 s' },
    { value: 10000, label: '10 s' }
  ];

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
    try { return win.top === win.self; }
    catch (e) { return false; }
  })();

  /* ============================== 状态 ============================== */
  let records = [];
  let seq = 0;
  let renderTimer = null;
  let currentCopyText = '';

  let slowThreshold = (function () {
    try {
      const v = parseInt(win.localStorage.getItem(LS_KEY_SLOW), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_SLOW_THRESHOLD;
  })();

  let largeResThreshold = (function () {
    try {
      const v = parseInt(win.localStorage.getItem(LS_KEY_LARGE_RES), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_LARGE_RES_THRESHOLD;
  })();

  let resSlowThreshold = (function () {
    try {
      const v = parseInt(win.localStorage.getItem(LS_KEY_RES_SLOW), 10);
      if (!isNaN(v) && v >= 0) return v;
    } catch (e) { /* ignore */ }
    return DEFAULT_RES_SLOW_THRESHOLD;
  })();

  const VALID_GROUP_MODES = ['url', 'domain', 'status', 'method', 'kind', 'respType'];

  let groupBy = (function () {
    try {
      const v = win.localStorage.getItem(LS_KEY_GROUP) || '';
      if (VALID_GROUP_MODES.indexOf(v) !== -1) return v;
    } catch (e) { /* ignore */ }
    return '';
  })();

  let collapsedGroups = Object.create(null);
  let isFullscreen = false;

  /* 悬浮图标位置：null 表示使用默认右下角；拖拽后为 { left, top } 并持久化 */
  let fabPos = (function () {
    try {
      const raw = win.localStorage.getItem(LS_KEY_FAB_POS);
      if (!raw) return null;
      const p = JSON.parse(raw);
      if (p && typeof p.left === 'number' && typeof p.top === 'number' &&
          isFinite(p.left) && isFinite(p.top) && p.left >= 0 && p.top >= 0) {
        return { left: p.left, top: p.top };
      }
    } catch (e) { /* ignore */ }
    return null;
  })();

  function readBoolSetting(key, fallback) {
    try {
      const v = win.localStorage.getItem(key);
      if (v === '1') return true;
      if (v === '0') return false;
    } catch (e) { /* ignore */ }
    return fallback;
  }

  function readIntSetting(key, fallback, min, max) {
    try {
      const v = parseInt(win.localStorage.getItem(key), 10);
      if (!isNaN(v) && v >= min && v <= max) return v;
    } catch (e) { /* ignore */ }
    return fallback;
  }

  function writeSetting(key, value) {
    try { win.localStorage.setItem(key, String(value)); } catch (e) { /* ignore */ }
  }

  /* 暂停记录 / 导出脱敏 / 紧凑行高：设置写入页面 origin 的 localStorage */
  let capturePaused = readBoolSetting(LS_KEY_PAUSED, false);
  let maskOnExport = readBoolSetting(LS_KEY_MASK_EXPORT, true);
  let denseRows = readBoolSetting(LS_KEY_DENSE, false);
  let maxRecords = readIntSetting(LS_KEY_MAX_RECORDS, DEFAULT_MAX_RECORDS, 50, 10000);
  let maxResourceRecords = readIntSetting(LS_KEY_MAX_RES_RECORDS, DEFAULT_MAX_RESOURCE_RECORDS, 50, 20000);
  let wfScaleMs = readIntSetting(LS_KEY_WF_SCALE, 0, 0, 60000);
  if (!WF_SCALE_OPTIONS.some(function (o) { return o.value === wfScaleMs; })) wfScaleMs = 0;

  let currentTab = TAB_NETWORK;
  const tabState = {
    network: { search: '', groupBy: groupBy, collapsed: Object.create(null) },
    resource: { search: '', groupBy: '', collapsed: Object.create(null) },
    storage: { search: '' },
    websocket: { search: '' },
    waterfall: { search: '' },
    console: { search: '' }
  };
  const consoleFilter = { level: new Set() };
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

  /* Console 支持 */
  let consoleRecords = [];
  let consoleSeq = 0;
  let consoleTableWrapEl = null;
  let consoleToolsWrapEl = null;
  let consoleChipsWrapEl = null;
  let consoleTabBtnEl = null;
  let consoleAutoScrollEl = null;
  let consoleAutoScroll = true;
  let consoleCapturing = false; /* 防止序列化时递归触发 console */

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
  let harBtnEl = null;
  let pauseBtnEl = null;
  let importBtnEl = null;
  let importFileEl = null;
  let maskBtnEl = null;
  let needsRender = false;
  let storeSubTab = 'local';
  const STORE_SUB_LABELS = { cookie: 'Cookies', local: 'LocalStorage', session: 'SessionStorage' };

  /* 响应头 Set-Cookie 还原快照：页面 JS 读不到 HttpOnly Cookie，只能从拦截到的响应头还原 */
  const MAX_SET_COOKIE_ENTRIES = 300;
  const setCookieStore = Object.create(null);

  /* GM_cookie 快照（唯一能读到 HttpOnly 的入口），异步拉取后触发 Storage 重绘 */
  const GM_COOKIE_TTL = 1500;
  let gmCookies = null;
  let gmCookiesAt = 0;
  let gmCookiesBusy = false;

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
  let storeViewDeleteBtnEl = null;
  let storeViewHlEl = null;
  let storeViewPreColEl = null;
  let storeViewTabsEl = null;
  let storeViewTab = 'edit';
  let storeViewEntry = null;
  let wsTabBtnEl = null;
  let wfTabBtnEl = null;
  let largeResInputEl = null;
  let resSlowInputEl = null;

  /* ---------------- 视图：请求耗时瀑布图 ---------------- */
  let waterfallWrapEl = null;
  let wfAxisRowEl = null;
  let wfAxisEl = null;
  let wfRowsEl = null;
  let wfSummaryEl = null;
  let wfScaleSelectEl = null;
  let wfSortSelectEl = null;
  let wfRowMap = Object.create(null);
  let wfSortMode = 'start';

  /* ---------------- 表格列宽拖拽 ---------------- */
  let columnWidths = loadColumnWidths();
  const colTableRefs = Object.create(null);

  /* ---------------- 集中设置面板 ---------------- */
  let settingsBtnEl = null;
  let settingsModal = null;
  let settingsBodyEl = null;
  let settingsStatusEl = null;
  let fabEl = null;
  const settingsCtl = Object.create(null);

  /* ============================ 通用小工具 ============================ */

  function clearEl(el) {
    if (!el) return;
    while (el.firstChild) el.removeChild(el.firstChild);
  }

  function openNetworkModal() {
    if (copyBtn) copyBtn.textContent = 'Copy';
    if (netModal) netModal.open();
  }

  function formatJSONOrNull(v) {
    try { return JSON.stringify(JSON.parse(v), null, 2); } catch (e) { return null; }
  }

  function prettyJSONText(v) {
    return formatJSONOrNull(v) || v;
  }

  function truncateText(s, limit) {
    if (typeof s !== 'string') return s;
    const max = limit || MAX_TEXT_RESPONSE;
    if (s.length <= max) return s;
    return s.slice(0, max) + '\n\n…[响应过大，已截断：仅保留前 ' +
      formatSize(max) + ' / 共 ' + formatSize(s.length) + ']';
  }

  function escapeRegExp(s) {
    return String(s).split('').map(function (c) {
      return '.*+?^${}()|[]\\'.indexOf(c) !== -1 ? '\\' + c : c;
    }).join('');
  }

  /* ---------- 导出脱敏（面板内始终保留完整内容，仅导出文件默认脱敏） ---------- */
  const SENSITIVE_HEADERS = ['authorization', 'proxy-authorization', 'cookie', 'set-cookie',
    'x-api-key', 'api-key', 'x-auth-token'];
  const SENSITIVE_KEYS = ['password', 'passwd', 'pwd', 'secret', 'token', 'access_token',
    'refresh_token', 'api_key', 'apikey', 'session_id'];
  const SENSITIVE_QUERY_KEYS = SENSITIVE_KEYS.concat(['key', 'sig', 'signature']);

  function maskDeep(value) {
    if (Array.isArray(value)) return value.map(maskDeep);
    if (value && typeof value === 'object') {
      const out = {};
      Object.keys(value).forEach(function (k) {
        out[k] = SENSITIVE_KEYS.indexOf(k.toLowerCase()) !== -1
          ? MASK_PLACEHOLDER : maskDeep(value[k]);
      });
      return out;
    }
    return value;
  }

  function maskUrl(u) {
    if (!u || typeof u !== 'string') return u;
    try {
      const url = new URL(u, location.href);
      let changed = false;
      SENSITIVE_QUERY_KEYS.forEach(function (k) {
        if (url.searchParams.has(k)) { url.searchParams.set(k, MASK_PLACEHOLDER); changed = true; }
      });
      return changed ? url.href : u;
    } catch (e) { return u; }
  }

  function maskText(text) {
    if (!text) return text;
    const s = String(text);
    if (s.indexOf(':') !== -1 && s.indexOf('{') === -1) {
      return s.split('\n').map(function (line) {
        const idx = line.indexOf(':');
        if (idx < 0) return line;
        const name = line.slice(0, idx).trim().toLowerCase();
        return SENSITIVE_HEADERS.indexOf(name) !== -1
          ? line.slice(0, idx + 1) + ' ' + MASK_PLACEHOLDER : line;
      }).join('\n');
    }
    try {
      const parsed = JSON.parse(s);
      return JSON.stringify(maskDeep(parsed), null, 2);
    } catch (e) {
      /* 查询串 / 表单：token=xxx&a=1（params 字段常是这个形态） */
      if (s.indexOf('=') !== -1 && s.indexOf('{') === -1 && s.indexOf('<') === -1) {
        return s.split('&').map(function (pair) {
          const idx = pair.indexOf('=');
          if (idx < 0) return pair;
          const k = pair.slice(0, idx);
          return SENSITIVE_QUERY_KEYS.indexOf(k.toLowerCase()) !== -1
            ? k + '=' + MASK_PLACEHOLDER : pair;
        }).join('&');
      }
      return s;
    }
  }

  function downloadFile(filename, text, mime) {
    const blob = new Blob([text], { type: mime || 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.style.display = 'none';
    (document.body || document.documentElement).appendChild(a);
    a.click();
    setTimeout(function () {
      a.remove();
      try { URL.revokeObjectURL(url); } catch (e) {}
    }, 0);
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

  /* ---------- GM_cookie：异步读取（含 HttpOnly） ---------- */

  function gmListCookies() {
    return new Promise(function (resolve) {
      let settled = false;
      function done(value) {
        if (settled) return;
        settled = true;
        resolve(value);
      }
      try {
        let api = null;
        if (typeof GM_cookie !== 'undefined' && GM_cookie) api = GM_cookie;
        else if (typeof GM !== 'undefined' && GM && GM.cookie) api = GM.cookie;
        if (!api || typeof api.list !== 'function') { done(null); return; }
        const ret = api.list({}, function (cookies, error) {
          done(error ? null : (Array.isArray(cookies) ? cookies : null));
        });
        if (ret && typeof ret.then === 'function') {
          ret.then(function (cookies) { done(Array.isArray(cookies) ? cookies : null); })
            .catch(function () { done(null); });
        }
      } catch (e) { done(null); }
    });
  }

  function requestGmCookies(force) {
    if (gmCookiesBusy) return;
    if (!force && gmCookies && Date.now() - gmCookiesAt < GM_COOKIE_TTL) return;
    gmCookiesBusy = true;
    gmListCookies().then(function (list) {
      gmCookiesBusy = false;
      gmCookies = list;
      gmCookiesAt = Date.now();
      if (storeSubTab === 'cookie' && currentTab === TAB_STORAGE) renderStorage();
    });
  }

  /* ---------- Set-Cookie 还原（含 HttpOnly） ---------- */

  function parseSetCookieLine(line, fallbackDomain, fromUrl) {
    if (!line) return null;
    const segments = String(line).split(';');
    const kv = segments.shift();
    const eq = kv.indexOf('=');
    if (eq < 1) return null;
    const name = kv.slice(0, eq).trim();
    if (!name) return null;

    const out = {
      name: name,
      value: kv.slice(eq + 1).trim(),
      domain: fallbackDomain || '',
      path: '/',
      httpOnly: false,
      secure: false,
      sameSite: '',
      expires: 0,
      deleted: false,
      from: fromUrl || '',
      time: Date.now()
    };
    let hasMaxAge = false;
    let maxAge = 0;

    segments.forEach(function (seg) {
      const i = seg.indexOf('=');
      const key = (i < 0 ? seg : seg.slice(0, i)).trim().toLowerCase();
      const val = i < 0 ? '' : seg.slice(i + 1).trim();
      if (key === 'httponly') out.httpOnly = true;
      else if (key === 'secure') out.secure = true;
      else if (key === 'domain') { if (val) out.domain = val.replace(/^\./, '').toLowerCase(); }
      else if (key === 'path') { if (val) out.path = val; }
      else if (key === 'samesite') out.sameSite = val;
      else if (key === 'expires') {
        const t = Date.parse(val);
        if (!isNaN(t)) out.expires = t;
      } else if (key === 'max-age') {
        hasMaxAge = true;
        maxAge = parseInt(val, 10);
        if (isNaN(maxAge)) maxAge = 0;
      }
    });

    if (hasMaxAge) out.expires = maxAge <= 0 ? 1 : Date.now() + maxAge * 1000;
    /* Max-Age<=0 或过期时间是过去，表示浏览器应删除该 Cookie */
    if (hasMaxAge && maxAge <= 0) out.deleted = true;
    else if (!hasMaxAge && out.expires && out.expires <= Date.now()) out.deleted = true;
    return out;
  }

  function captureSetCookies(rec) {
    if (!rec || rec.imported) return;
    const raw = rec.respHeaders;
    if (!raw || typeof raw !== 'string') return;
    let host = '';
    try { host = new URL(rec.url).hostname; } catch (e) { /* ignore */ }

    const lines = raw.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const idx = line.indexOf(':');
      if (idx < 0) continue;
      if (line.slice(0, idx).trim().toLowerCase() !== 'set-cookie') continue;
      const c = parseSetCookieLine(line.slice(idx + 1).trim(), host, rec.url);
      if (!c) continue;
      const key = c.name + '|' + c.domain + '|' + c.path;
      if (c.deleted) { delete setCookieStore[key]; continue; }
      setCookieStore[key] = c;
    }

    const keys = Object.keys(setCookieStore);
    if (keys.length > MAX_SET_COOKIE_ENTRIES) {
      const extras = keys.sort(function (a, b) {
        return setCookieStore[a].time - setCookieStore[b].time;
      }).slice(0, keys.length - MAX_SET_COOKIE_ENTRIES);
      extras.forEach(function (k) { delete setCookieStore[k]; });
    }
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

  /* 空格分词：普通词需全部命中，以 - 开头的词表示排除 */
  function matchesTerms(hay, terms) {
    for (let i = 0; i < terms.length; i++) {
      const t = terms[i];
      if (t.charAt(0) === '-' && t.length > 1) {
        if (hay.indexOf(t.slice(1)) !== -1) return false;
      } else if (hay.indexOf(t) === -1) return false;
    }
    return true;
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
    return matchesTerms(hay, terms);
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
  const MSG_TAG_WS = '__NRP_WS__';
  const MSG_TAG_WS_UPDATE = '__NRP_WS_UPDATE__';
  const MSG_TAG_CONSOLE = '__NRP_CONSOLE__';

  function nextStreamId() {
    return 's' + (++streamSeq) + '-' + Date.now().toString(36) + '-' +
      Math.random().toString(36).slice(2, 8);
  }

  /* 记录被淘汰/清除时释放关联的流式映射与图片预览 Blob URL */
  function releaseRecord(rec) {
    if (!rec) return;
    if (rec.streamId) delete streamMap[rec.streamId];
    if (rec.previewUrl && rec.previewUrl.indexOf('blob:') === 0) {
      try { URL.revokeObjectURL(rec.previewUrl); } catch (e) { /* ignore */ }
    }
  }

  function pushRecord(rec, force) {
    if (capturePaused && !force) return;
    rec.id = ++seq;
    if (!rec.time) rec.time = Date.now();
    if (!rec.frameUrl && !IS_TOP) {
      try { rec.frameUrl = location.href; } catch (e) { rec.frameUrl = ''; }
    }
    try { captureSetCookies(rec); } catch (e) { /* ignore */ }
    if (rec.streamId) streamMap[rec.streamId] = rec;
    records.push(rec);

    const cap = rec.kind === 'resource' ? maxResourceRecords : maxRecords;
    const wantRes = rec.kind === 'resource';
    let count = 0;
    for (let i = records.length - 1; i >= 0; i--) {
      if ((records[i].kind === 'resource') !== wantRes) continue;
      count++;
      if (count > cap) {
        releaseRecord(records.splice(i, 1)[0]);
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
      win.top.postMessage({ tag: MSG_TAG_UPDATE, streamId: streamId, patch: patch }, location.origin);
    } catch (e) { /* ignore */ }
  }

  function addRecord(rec) {
    if (IS_TOP) {
      pushRecord(rec);
    } else {
      try {
        rec.frameUrl = location.href;
        win.top.postMessage({ tag: MSG_TAG, record: rec }, location.origin);
      } catch (e) {
        pushRecord(rec);
      }
    }
  }

  function installMessageListener() {
    if (!IS_TOP) return;
    win.addEventListener('message', function (ev) {
      try {
        /* 只接受同源帧上报，避免跨源页面伪造记录污染调试数据 */
        if (ev.origin !== location.origin) return;
        const data = ev.data;
        if (!data) return;
        if (data.tag === MSG_TAG && data.record) {
          pushRecord(data.record);
        } else if (data.tag === MSG_TAG_UPDATE && data.streamId) {
          updateRecord(data.streamId, data.patch);
        } else if (data.tag === MSG_TAG_WS && data.record) {
          addWsRecord(data.record);
        } else if (data.tag === MSG_TAG_WS_UPDATE && data.wsId) {
          updateWsRecord(data.wsId, data.patch);
        } else if (data.tag === MSG_TAG_CONSOLE && data.record) {
          pushConsoleRecord(data.record);
        }
      } catch (e) { /* ignore */ }
    }, false);
  }

  /* ========================== Console 捕获 ========================== */

  function truncConsoleText(s, limit) {
    const str = String(s == null ? '' : s);
    const max = limit || MAX_CONSOLE_TEXT;
    return str.length <= max ? str : str.slice(0, max) + '\n…[已截断，共 ' + str.length + ' 字符]';
  }

  function consoleArgToString(v, depth, seen) {
    depth = depth || 0;
    if (v === null) return 'null';
    if (v === undefined) return 'undefined';
    const t = typeof v;
    if (t === 'string') return v;
    if (t === 'number' || t === 'boolean' || t === 'bigint' || t === 'symbol') return String(v);
    if (t === 'function') return '[Function ' + (v.name || 'anonymous') + ']';
    try { if (v instanceof Error) return v.stack || (v.name + ': ' + v.message); } catch (e) { /* ignore */ }
    try {
      if (v && v.nodeType) {
        if (v.nodeType === 1) return '<' + String(v.tagName).toLowerCase() + (v.id ? '#' + v.id : '') + '>';
        if (v.nodeType === 9) return '#document';
        return '[Node ' + v.nodeType + ']';
      }
    } catch (e) { /* ignore */ }

    seen = seen || [];
    if (seen.indexOf(v) !== -1) return '[Circular]';
    if (depth >= MAX_CONSOLE_DEPTH) return Array.isArray(v) ? '[Array]' : '[Object]';
    const next = seen.concat([v]);
    try {
      if (Array.isArray(v)) {
        const parts = [];
        const n = Math.min(v.length, MAX_CONSOLE_KEYS);
        for (let i = 0; i < n; i++) parts.push(consoleArgToString(v[i], depth + 1, next));
        if (v.length > n) parts.push('… 另有 ' + (v.length - n) + ' 项');
        return '[' + parts.join(', ') + ']';
      }
      const keys = Object.keys(v);
      const parts2 = [];
      const n2 = Math.min(keys.length, MAX_CONSOLE_KEYS);
      for (let i = 0; i < n2; i++) {
        let val;
        try { val = v[keys[i]]; } catch (e) { val = '[?]'; }
        parts2.push(keys[i] + ': ' + consoleArgToString(val, depth + 1, next));
      }
      if (keys.length > n2) parts2.push('… 另有 ' + (keys.length - n2) + ' 项');
      return '{' + parts2.join(', ') + '}';
    } catch (e) {
      try { return String(v); } catch (e2) { return '[unserializable]'; }
    }
  }

  function consoleFormatArgs(args) {
    const arr = Array.prototype.slice.call(args);
    if (!arr.length) return { text: '', args: [] };
    const allArgs = arr.map(function (v) { return truncConsoleText(consoleArgToString(v, 0, []), MAX_CONSOLE_ARG_TEXT); });
    let out = '';
    const first = arr[0];
    if (typeof first === 'string' && /%[sdifjoOc%]/.test(first)) {
      let consumed = 1;
      out = first.replace(/%[sdifjoOc%]/g, function (m) {
        if (m === '%%') return '%';
        if (consumed >= arr.length) return m;
        const v = arr[consumed++];
        if (m === '%c') return '';
        if (m === '%s') return typeof v === 'string' ? v : consoleArgToString(v, 0, []);
        if (m === '%d' || m === '%i') return String(parseInt(v, 10) || 0);
        if (m === '%f') return String(parseFloat(v) || 0);
        return consoleArgToString(v, 0, []);
      });
      for (; consumed < arr.length; consumed++) {
        out += ' ' + consoleArgToString(arr[consumed], 0, []);
      }
    } else {
      out = allArgs.join(' ');
    }
    return { text: out, args: allArgs };
  }

  function consoleCallerSource() {
    try {
      const lines = (new Error().stack || '').split('\n');
      for (let i = 1; i < lines.length; i++) {
        const l = lines[i].trim();
        if (!l || l.indexOf('network-debuger') !== -1 || l.indexOf('nrpConsole') !== -1) continue;
        return l.length > 240 ? l.slice(0, 240) : l;
      }
    } catch (e) { /* ignore */ }
    return '';
  }

  function consoleLevelGroup(level) {
    if (level === 'log') return 'log';
    if (level === 'info') return 'info';
    if (level === 'warn') return 'warn';
    if (level === 'error' || level === 'assert' || level === 'uncaught') return 'error';
    if (level === 'debug' || level === 'trace') return 'debug';
    return 'other';
  }

  function pushConsoleRecord(rec) {
    if (!rec) return;
    if (capturePaused) return;
    if (!rec.id) rec.id = ++consoleSeq;
    if (!rec.time) rec.time = Date.now();
    if (!rec.frameUrl && !IS_TOP) {
      try { rec.frameUrl = location.href; } catch (e) { rec.frameUrl = ''; }
    }
    consoleRecords.push(rec);
    if (consoleRecords.length > MAX_CONSOLE_RECORDS) {
      consoleRecords.splice(0, consoleRecords.length - MAX_CONSOLE_RECORDS);
    }
    scheduleRender();
  }

  function captureConsole(level, args, extra) {
    if (capturePaused || consoleCapturing) return;
    consoleCapturing = true;
    try {
      const f = consoleFormatArgs(args);
      const rec = {
        level: level,
        text: truncConsoleText(f.text, MAX_CONSOLE_TEXT),
        args: f.args,
        time: Date.now(),
        frameUrl: IS_TOP ? '' : location.href,
        source: extra && extra.source ? extra.source : ''
      };
      if (IS_TOP) pushConsoleRecord(rec);
      else {
        try { win.top.postMessage({ tag: MSG_TAG_CONSOLE, record: rec }, location.origin); } catch (e) { /* ignore */ }
      }
    } catch (e) { /* ignore */ }
    finally { consoleCapturing = false; }
  }

  function installConsoleInterceptor() {
    const target = win.console;
    if (!target) return;
    const levels = ['log', 'info', 'warn', 'error', 'debug', 'trace', 'dir', 'table', 'assert', 'clear'];
    levels.forEach(function (level) {
      const orig = target[level];
      if (typeof orig !== 'function') return;
      try {
        const patched = function () {
          const args = arguments;
          if (level === 'assert') {
            if (args.length && !args[0]) {
              captureConsole('error', Array.prototype.slice.call(args, 1), { source: consoleCallerSource() });
            }
          } else {
            captureConsole(level === 'clear' ? 'clear' : level, args,
              (level === 'error' || level === 'warn') ? { source: consoleCallerSource() } : null);
          }
          return orig.apply(this, args);
        };
        patched.__nrpOriginal = orig;
        target[level] = patched;
      } catch (e) { /* ignore */ }
    });

    try {
      win.addEventListener('error', function (e) {
        if (capturePaused || consoleCapturing) return;
        if (e && e.target && e.target !== win && e.target !== document) return;
        const msg = e && e.message ? e.message : 'Uncaught error';
        const stack = e && e.error && e.error.stack ? '\n' + e.error.stack : '';
        const src = e && e.filename ? (e.filename + ':' + e.lineno + ':' + e.colno) : '';
        captureConsole('uncaught', [msg + stack], { source: src });
      }, true);
      win.addEventListener('unhandledrejection', function (e) {
        if (capturePaused || consoleCapturing) return;
        let reason = e && e.reason;
        if (reason && reason.stack) reason = reason.stack;
        captureConsole('uncaught', ['Unhandled promise rejection:', reason], { source: consoleCallerSource() });
      }, true);
    } catch (e) { /* ignore */ }
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
      bodyPromise.then(function (b) { updateRecord(streamId, { body: truncateText(b) }); }, function () {});
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

    /* 增量统计 data: 行，避免每个 chunk 都对整个缓冲区做 O(n) 扫描 */
    let eventCount = 0;
    let lineCarry = '';
    function countIncremental(text) {
      const lines = (lineCarry + text).split('\n');
      lineCarry = lines.pop() || '';
      for (let i = 0; i < lines.length; i++) {
        if (/^data:/i.test(lines[i].trim())) eventCount++;
      }
    }

    let lastPushAt = 0;
    function push() {
      const now = Date.now();
      if (now - lastPushAt < 200) return;   /* 高频流节流，结束时由 finish 补齐 */
      lastPushAt = now;
      updateRecord(streamId, {
        response: acc + tailNote(),
        sseEvents: eventCount,
        sseTruncated: truncated
      });
    }

    function finish(note) {
      if (finished) return;
      finished = true;
      updateRecord(streamId, {
        response: acc + tailNote() + (note ? '\n\n' + note : ''),
        sseEvents: eventCount,
        sseTruncated: truncated,
        sseDone: true
      });
    }

    function pump() {
      reader.read().then(function (result) {
        if (result.done) { finish('[stream closed]'); return; }
        const chunk = result.value;
        if (chunk) {
          let decoded = '';
          try { decoded = decoder.decode(chunk, { stream: true }); }
          catch (e) { decoded = String(chunk); }
          acc += decoded;
          countIncremental(decoded);
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
    if (seenResourceKeys.size > MAX_SEEN_RESOURCE_KEYS) seenResourceKeys.clear();
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
    if (capturePaused) return;
    if (!IS_TOP) {
      try { win.top.postMessage({ tag: MSG_TAG_WS, record: rec }, location.origin); }
      catch (e) { /* ignore */ }
      return;
    }
    /* 不要覆盖 installWebSocketInterceptor 里生成的 wsId（wsMap 以它为键） */
    if (!rec.id) rec.id = 'ws' + (++wsSeq);
    if (!rec.time) rec.time = Date.now();
    if (!rec.frameUrl && !IS_TOP) {
      try { rec.frameUrl = location.href; } catch (e) { rec.frameUrl = ''; }
    }
    /* 跨帧上报时顶层没有 interceptor 建的映射，这里统一补上 */
    wsMap[rec.id] = rec;
    wsRecords.push(rec);
    if (wsRecords.length > MAX_WS_RECORDS) {
      const removed = wsRecords.splice(0, wsRecords.length - MAX_WS_RECORDS);
      removed.forEach(function (r) { if (wsMap[r.id]) delete wsMap[r.id]; });
    }
    scheduleRender();
  }

  function updateWsRecord(wsId, patch) {
    if (!IS_TOP) {
      try { win.top.postMessage({ tag: MSG_TAG_WS_UPDATE, wsId: wsId, patch: patch }, location.origin); }
      catch (e) { /* ignore */ }
      return;
    }
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
    try { win.WebSocket = PatchedWS; } catch (e) {}
  }

  /* ========================== 请求拦截 ========================== */

  function installInterceptors() {
    /* ---------------- XMLHttpRequest ---------------- */
    const XHRProto = win.XMLHttpRequest && win.XMLHttpRequest.prototype;
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

        try { meta.bodyStr = truncateText(bodyToString(body)); }
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
              if (txt.length > SSE_MAX_BUFFER) txt = txt.slice(-SSE_MAX_BUFFER);

              if (!meta.sseRecorded) {
                meta.sseRecorded = true;
                addRecord({
                  kind: 'xhr', method: meta.method, url: absUrl(meta.url),
                  params: extractQuery(meta.url), body: meta.bodyStr,
                  reqHeaders: headersToString(meta.reqHeaders),
                  respHeaders: sseHeaders, status: xhr.status,
                  response: truncateText(txt), responseKind: 'sse',
                  mimeType: sseMime, binarySize: 0,
                  duration: null, time: meta.startTime || Date.now(),
                  streamId: meta.streamId, sseDone: false,
                  sseEvents: countSseEvents(txt)
                });
              } else {
                /* readystatechange 触发非常频繁，节流后再全量扫描 */
                const now = Date.now();
                if (now - (meta.lastSsePush || 0) < 150) return;
                meta.lastSsePush = now;
                updateRecord(meta.streamId, {
                  response: truncateText(txt), respHeaders: sseHeaders,
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
              if (sseText.length > SSE_MAX_BUFFER) sseText = sseText.slice(-SSE_MAX_BUFFER);
              updateRecord(meta.streamId, {
                status: xhr.status, response: truncateText(sseText), respHeaders: respHeaders,
                sseEvents: countSseEvents(sseText), sseDone: true, duration: duration
              });
              return;
            }

            addRecord({
              kind: 'xhr', method: meta.method, url: absUrl(meta.url),
              params: extractQuery(meta.url), body: meta.bodyStr,
              reqHeaders: headersToString(meta.reqHeaders),
              respHeaders: respHeaders, status: xhr.status,
              response: truncateText(text), responseKind: responseKind,
              mimeType: mime, binarySize: binarySize,
              duration: duration, time: meta.startTime || Date.now()
            });
          }, { once: true });
        } catch (e) { /* ignore */ }

        return origSend.apply(this, arguments);
      };
    }

    /* ---------------- fetch ---------------- */
    const nativeFetch = win.fetch;
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
                body: truncateText(bodyStr), reqHeaders: reqHeadersStr, respHeaders: respHeadersStr,
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

          /* 声明体积过大的二进制响应直接跳过读取，避免整块载入内存 */
          let declaredLen = NaN;
          try {
            if (res.headers && res.headers.get) {
              declaredLen = parseInt(res.headers.get('content-length') || '', 10);
            }
          } catch (e) {}
          if ((isImg || !isText) && isFinite(declaredLen) && declaredLen > MAX_BINARY_READ) {
            finalize('[' + (mime || 'binary') + ' ' + formatSize(declaredLen) +
              '，超过读取上限，未缓存内容]', isImg ? 'image' : 'binary', declaredLen, '');
            return res;
          }

          try {
            if (isImg) {
              const clone = res.clone();
              clone.arrayBuffer().then(function (buf) {
                let previewUrl = '';
                const text = '[Image ' + formatSize(buf.byteLength) + ', type=' + (mime || 'unknown') + ']';
                if (buf.byteLength <= MAX_IMAGE_PREVIEW) {
                  try {
                    const type = (mime || 'image/png').split(';')[0].trim();
                    previewUrl = URL.createObjectURL(new Blob([buf], { type: type }));
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
              clone.text().then(function (text) { finalize(truncateText(text), 'text', 0, ''); },
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
              body: truncateText(bodyStr), reqHeaders: reqHeadersStr, respHeaders: '',
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
      win.fetch = patched;
    }

    /* ---------------- EventSource ---------------- */
    const OrigES = win.EventSource;
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
      try { win.EventSource = PatchedES; } catch (e) {}
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


  /* ====================== 移动端触摸滚动守卫 ======================
   * 不少宿主页面为禁用橡皮筋会在 document 上 touchmove preventDefault()。
   * 滚轮不受影响，但会连带禁掉我们浮层内部的原生触摸滚动 —— 这正是
   * 「桌面能滚、移动端滚不动」的典型原因。
   *  1) #nrp-root 在冒泡路径上且先于 document：截断冒泡，宿主在 document
   *     冒泡阶段的监听器就不会触发；
   *  2) 若宿主用的是 document 捕获阶段（我们挡不住），在 root 捕获阶段
   *     检测到 defaultPrevented 时，改为手动更新 scrollTop 兜底。
   * 全程 passive，不自己调用 preventDefault。
   */
  function installTouchScrollGuard(root) {
    if (!root || !root.addEventListener) return;
    const SCROLL_SEL = '.nrp-modal-content, .nrp-store-view-body, .nrp-store-view-hl, .nrp-overlay';
    let startY = 0;
    let startTop = 0;
    let scroller = null;

    function bind(type, fn, capture) {
      try { root.addEventListener(type, fn, { passive: true, capture: !!capture }); }
      catch (e) { root.addEventListener(type, fn, !!capture); }
    }
    function inOverlay(t) {
      return !!(t && t.closest && t.closest('.nrp-overlay.nrp-open'));
    }
    function findScroller(node) {
      let el = node && node.nodeType === 1 ? node : (node ? node.parentNode : null);
      while (el && el !== root && el && el.nodeType === 1) {
        if (el.matches && el.matches(SCROLL_SEL) && el.scrollHeight > el.clientHeight + 1) return el;
        el = el.parentNode;
      }
      return null;
    }
    function pointY(e) {
      return (e.touches && e.touches[0] ? e.touches[0].clientY : e.clientY) || 0;
    }
    function stopBubble(e) {
      if (inOverlay(e.target)) e.stopPropagation();
    }
    function onStart(e) {
      if (!inOverlay(e.target)) { scroller = null; return; }
      startY = pointY(e);
      scroller = findScroller(e.target);
      startTop = scroller ? scroller.scrollTop : 0;
    }
    function onMoveCapture(e) {
      /* 仅在宿主已取消默认滚动时接管，避免和原生滚动叠加 */
      if (!scroller || !e.defaultPrevented) return;
      scroller.scrollTop = startTop - (pointY(e) - startY);
    }

    bind('touchstart', onStart, true);
    bind('touchmove', onMoveCapture, true);
    bind('touchstart', stopBubble, false);
    bind('touchmove', stopBubble, false);
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
  min-width: 360px;
  resize: horizontal;   /* 拖右下角可调整面板宽度，列宽按百分比自适应 */
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
  resize: none;
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
#nrp-root .nrp-actions { display: flex; gap: 4px; flex-wrap: wrap; justify-content: flex-end; }
#nrp-root .nrp-response-mode {
  display: flex; align-items: center; gap: 6px; margin-bottom: 6px; flex-wrap: wrap;
}
#nrp-root .nrp-tree-search { flex: 1 1 120px; max-width: 260px; font-size: 11px; }
#nrp-root .nrp-json-tree mark {
  background: #9e6a03; color: #fff; border-radius: 2px; padding: 0 1px;
}

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
#nrp-root .nrp-cookie-badge {
  display: inline-block; margin-left: 6px; padding: 0 5px;
  font-size: 10px; line-height: 16px; border-radius: 3px;
  color: #e3b341; background: #272005; border: 1px solid #6e5313;
  vertical-align: middle; font-weight: 600;
}
#nrp-root .nrp-cookie-ro { color: #8b949e; font-size: 11px; }
#nrp-root .nrp-btn:disabled { opacity: .45; cursor: not-allowed; }
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
#nrp-root .nrp-chip-clevel-log.nrp-chip-active {
  background: rgba(139,148,158,.2); color: #c9d1d9; border-color: rgba(139,148,158,.6);
}
#nrp-root .nrp-chip-clevel-info.nrp-chip-active {
  background: rgba(56,139,253,.2); color: #79c0ff; border-color: rgba(56,139,253,.6);
}
#nrp-root .nrp-chip-clevel-warn.nrp-chip-active {
  background: rgba(210,153,34,.2); color: #d29922; border-color: rgba(210,153,34,.6);
}
#nrp-root .nrp-chip-clevel-error.nrp-chip-active {
  background: rgba(248,81,73,.2); color: #f85149; border-color: rgba(248,81,73,.6);
}
#nrp-root .nrp-chip-clevel-debug.nrp-chip-active {
  background: rgba(210,168,255,.2); color: #d2a8ff; border-color: rgba(210,168,255,.6);
}
#nrp-root .nrp-chip-clevel-other.nrp-chip-active {
  background: rgba(86,211,100,.2); color: #56d364; border-color: rgba(86,211,100,.6);
}

#nrp-root .nrp-console-tools {
  display: flex; align-items: center; gap: 8px;
  padding: 4px 8px; border-bottom: 1px solid #21262d;
  background: #0d1117; flex-shrink: 0;
}
#nrp-root .nrp-console-tools-spacer { flex: 1 1 auto; }
#nrp-root .nrp-console-toggle {
  appearance: none; -webkit-appearance: none;
  display: inline-flex; align-items: center; gap: 4px;
  border: 1px solid #30363d; background: #161b22; color: #8b949e;
  font-family: inherit; font-size: 11px; line-height: 1.2;
  padding: 2px 8px; border-radius: 10px; cursor: pointer; white-space: nowrap;
}
#nrp-root .nrp-console-toggle.nrp-console-toggle-on {
  background: rgba(63,185,80,.15); color: #3fb950; border-color: rgba(63,185,80,.5);
}
#nrp-root .nrp-console-lv {
  display: inline-block; min-width: 44px; text-align: center;
  padding: 1px 6px; border-radius: 9px;
  font-size: 10px; font-weight: 700; text-transform: uppercase;
}
#nrp-root .nrp-console-lv-log   { background: rgba(139,148,158,.15); color: #c9d1d9; }
#nrp-root .nrp-console-lv-info  { background: rgba(56,139,253,.15); color: #79c0ff; }
#nrp-root .nrp-console-lv-warn  { background: rgba(210,153,34,.15); color: #d29922; }
#nrp-root .nrp-console-lv-error { background: rgba(248,81,73,.15); color: #f85149; }
#nrp-root .nrp-console-lv-debug { background: rgba(210,168,255,.15); color: #d2a8ff; }
#nrp-root .nrp-console-lv-other { background: rgba(86,211,100,.15); color: #56d364; }
#nrp-root .nrp-console-msg {
  white-space: pre-wrap; word-break: break-word;
  max-height: 60px; overflow: hidden;
  font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
}
#nrp-root .nrp-console-source { color: #8b949e; font-size: 11px; }
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
  position: fixed; right: 16px; bottom: 16px;
  width: 46px; height: 46px; border-radius: 50%;
  border: 1px solid #30363d; background: #161b22; color: #3fb950;
  font-family: inherit; font-size: 11px; font-weight: 700;
  cursor: grab; align-items: center; justify-content: center;
  box-shadow: 0 6px 20px rgba(0,0,0,.6);
  user-select: none; -webkit-user-select: none;
  touch-action: none;
}
#nrp-root .nrp-fab:hover { background: #21262d; color: #56d364; }
#nrp-root .nrp-fab.nrp-fab-dragging {
  cursor: grabbing;
  background: #21262d; color: #56d364;
  border-color: #1f6feb;
  box-shadow: 0 10px 28px rgba(0,0,0,.75);
  transform: scale(1.06);
}

/* ============ 通用模态框：可复用 head / body / footer ============ */
#nrp-root .nrp-overlay {
  display: none;
  position: fixed; inset: 0;
  z-index: ${OVERLAY_Z};
  background: rgba(1,4,9,.72);
  align-items: center; justify-content: center;
  padding: 24px;
  pointer-events: auto;
  /* 兜底滚动层：内层滚动被宿主页面限制时，仍可整体滚动看到全部内容 */
  overflow-y: auto;
  -webkit-overflow-scrolling: touch;
  overscroll-behavior: contain;
  touch-action: pan-y;
  touch-action: manipulation;  /* 支持时额外允许横向平移与双指缩放 */
}
#nrp-root .nrp-overlay.nrp-open { display: flex; }

#nrp-root .nrp-modal {
  width: 920px; max-width: 92vw;
  max-height: 82vh;
  max-height: 82dvh;   /* 移动端动态视口，避免地址栏把底部顶出屏幕 */
  margin: auto;        /* auto 边距在空间不足时退化为 0，不会把顶部裁在屏幕外 */
  background: #0d1117;
  border: 1px solid #30363d;
  border-radius: 8px;
  box-shadow: 0 20px 60px rgba(0,0,0,.7);
  display: flex; flex-direction: column;
  min-height: 0;
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
  -webkit-overflow-scrolling: touch;  /* 旧版 iOS / WebView 需要显式开启惯性滚动 */
  overscroll-behavior-y: contain;     /* 滚到边界不把滚动传给宿主页面 */
  touch-action: pan-y;                /* 对抗宿主页面的 touch-action:none */
  touch-action: manipulation;
  display: flex;
  flex-direction: column;
  min-height: 0;
  max-height: 100%;
  padding-bottom: env(safe-area-inset-bottom);
}
/* flex 列 + 可滚动容器：子元素若可被压缩，内容高度会被算错，表现为"滚不动" */
#nrp-root .nrp-modal-content > * { flex-shrink: 0; }
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
  #nrp-root .nrp-fab { right: 8px; bottom: 8px; }
  #nrp-root .nrp-panel {
    right: 0;
    width: 100vw;
    max-width: 100vw;
    min-width: 0;
    resize: none;
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
    max-height: calc(100dvh - 220px);
    overflow-y: auto;
    -webkit-overflow-scrolling: touch;
  }

  /* ---- 模态框：移动端纵向滚动 ---- */
  #nrp-root .nrp-overlay {
    padding: 8px;
    padding: max(8px, env(safe-area-inset-top)) 8px max(8px, env(safe-area-inset-bottom));
  }
  #nrp-root .nrp-modal {
    width: 100%;
    max-width: 100%;
    /* vh 在移动端包含地址栏，dvh 才是真实可视高度；两条按顺序回退 */
    max-height: calc(100vh - 16px);
    max-height: calc(100dvh - 16px);
  }
  #nrp-root .nrp-modal.nrp-store-add-modal,
  #nrp-root .nrp-modal.nrp-store-view-modal,
  #nrp-root .nrp-modal.nrp-settings-modal { width: 100%; max-width: 100%; }
  #nrp-root .nrp-modal.nrp-store-view-modal {
    height: auto;
    max-height: calc(100vh - 16px);
    max-height: calc(100dvh - 16px);
  }
  #nrp-root .nrp-modal-head,
  #nrp-root .nrp-modal-footer { flex-wrap: wrap; }
  #nrp-root .nrp-modal-content,
  #nrp-root .nrp-store-view-body { -webkit-overflow-scrolling: touch; }
  #nrp-root textarea,
  #nrp-root pre {
    touch-action: pan-y;
    touch-action: manipulation;
    -webkit-overflow-scrolling: touch;
  }
  #nrp-root .nrp-store-view-split,
  #nrp-root .nrp-store-view-col { flex: 0 0 auto; }
  #nrp-root .nrp-settings-row { flex-wrap: wrap; }
  #nrp-root .nrp-settings-info { flex: 1 1 100%; }
}

/* ---------------- 列宽拖拽 ---------------- */
#nrp-root th { position: sticky; }
#nrp-root .nrp-col-resizer {
  position: absolute; top: 0; right: -3px;
  width: 7px; height: 100%;
  cursor: col-resize; z-index: 3;
  user-select: none; touch-action: none;
  background: transparent;
}
#nrp-root .nrp-col-resizer::after {
  content: ''; position: absolute; left: 3px; top: 20%;
  width: 1px; height: 60%; background: #30363d;
}
#nrp-root .nrp-col-resizer:hover { background: rgba(56,139,253,.55); }
#nrp-root .nrp-col-resizer:hover::after { background: transparent; }
body.nrp-col-resizing #nrp-root * { cursor: col-resize !important; user-select: none !important; }

/* ---------------- 请求耗时瀑布图 ---------------- */
#nrp-root .nrp-wf {
  flex: 1 1 auto; display: flex; flex-direction: column;
  min-height: 0; overflow: hidden;
}
#nrp-root .nrp-wf-head {
  display: flex; align-items: center; gap: 8px; flex-wrap: wrap;
  padding: 5px 8px; border-bottom: 1px solid #21262d;
  background: #0d1117; flex: 0 0 auto;
}
#nrp-root .nrp-wf-summary { color: #8b949e; font-size: 11px; flex: 1 1 auto; min-width: 150px; }
#nrp-root .nrp-wf-select {
  background: #010409; border: 1px solid #30363d; color: #c9d1d9;
  font-family: inherit; font-size: 11px; border-radius: 5px;
  padding: 3px 5px; outline: none;
}
#nrp-root .nrp-wf-legend {
  display: flex; align-items: center; gap: 8px; flex-wrap: wrap;
  font-size: 10px; color: #8b949e; flex: 0 0 100%;
}
#nrp-root .nrp-wf-key { display: inline-flex; align-items: center; gap: 4px; }
#nrp-root .nrp-wf-swatch { display: inline-block; width: 9px; height: 9px; border-radius: 2px; }
#nrp-root .nrp-wf-axis-row,
#nrp-root .nrp-wf-row { display: flex; align-items: stretch; }
#nrp-root .nrp-wf-axis-row {
  position: sticky; top: 0; z-index: 2;
  height: 22px;
  border-bottom: 1px solid #30363d; background: #161b22;
}
#nrp-root .nrp-wf-label-head,
#nrp-root .nrp-wf-label { flex: 0 0 38%; min-width: 0; box-sizing: border-box; padding: 2px 8px; }
#nrp-root .nrp-wf-label-head {
  display: flex; align-items: center;
  color: #8b949e; font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: .5px;
}
#nrp-root .nrp-wf-axis,
#nrp-root .nrp-wf-track { flex: 1 1 auto; position: relative; min-width: 0; }
#nrp-root .nrp-wf-axis { color: #6e7681; font-size: 10px; }
#nrp-root .nrp-wf-tick { position: absolute; top: 4px; transform: translateX(-50%); white-space: nowrap; }
#nrp-root .nrp-wf-tick.nrp-wf-tick-first { transform: none; }
#nrp-root .nrp-wf-tick.nrp-wf-tick-last { transform: translateX(-100%); }
#nrp-root .nrp-wf-rows { flex: 1 1 auto; min-height: 0; overflow: auto; }
#nrp-root .nrp-wf-row { height: 24px; border-bottom: 1px solid #1b222b; cursor: pointer; }
#nrp-root .nrp-wf-row:nth-child(even) { background: #10161d; }
#nrp-root .nrp-wf-row:hover { background: #1c2733; }
#nrp-root .nrp-wf-label {
  display: flex; align-items: center; gap: 6px;
  overflow: hidden; white-space: nowrap; color: #c9d1d9; font-size: 11px;
}
#nrp-root .nrp-wf-method { flex: 0 0 auto; color: #79c0ff; font-weight: 700; }
#nrp-root .nrp-wf-url { flex: 1 1 auto; min-width: 0; overflow: hidden; text-overflow: ellipsis; }
#nrp-root .nrp-wf-dur { flex: 0 0 auto; color: #8b949e; font-size: 10px; }
#nrp-root .nrp-wf-track {
  overflow: hidden;   /* 固定时间窗时裁掉窗口外的请求条 */
  background-image: linear-gradient(to right, rgba(48,54,61,.7) 1px, transparent 1px);
  background-size: 25% 100%;
}
#nrp-root .nrp-wf-bar {
  position: absolute; top: 6px; height: 12px; min-width: 2px;
  display: flex; overflow: hidden; border-radius: 2px;
  box-shadow: 0 0 0 1px rgba(0,0,0,.3);
}
#nrp-root .nrp-wf-bar:hover { filter: brightness(1.3); }
#nrp-root .nrp-wf-ok { background: #3fb950; }
#nrp-root .nrp-wf-redirect { background: #d29922; }
#nrp-root .nrp-wf-err { background: #f85149; }
#nrp-root .nrp-wf-pending { background: #6e7681; }
#nrp-root .nrp-wf-sse { background: #d2a8ff; }
#nrp-root .nrp-wf-res { background: #58a6ff; }
#nrp-root .nrp-wf-seg { height: 100%; flex: 0 0 auto; }
#nrp-root .nrp-wf-seg-blocked { background: #484f58; }
#nrp-root .nrp-wf-seg-dns { background: #d29922; }
#nrp-root .nrp-wf-seg-tcp { background: #a371f7; }
#nrp-root .nrp-wf-seg-wait { background: #58a6ff; }
#nrp-root .nrp-wf-seg-download { background: #3fb950; }
#nrp-root .nrp-wf-empty { padding: 28px 8px; text-align: center; color: #6e7681; font-style: italic; }

/* ---------------- 集中设置面板 ---------------- */
#nrp-root .nrp-settings-modal { width: 620px; max-width: calc(100vw - 32px); }
#nrp-root .nrp-settings { display: flex; flex-direction: column; }
#nrp-root .nrp-settings-group {
  margin: 8px 0 2px; padding-bottom: 4px;
  border-bottom: 1px solid #21262d;
  color: #79c0ff; font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: .6px;
}
#nrp-root .nrp-settings-row { display: flex; align-items: center; gap: 10px; padding: 5px 2px; }
#nrp-root .nrp-settings-row:hover { background: #10161d; }
#nrp-root .nrp-settings-info { flex: 1 1 auto; min-width: 0; }
#nrp-root .nrp-settings-name { color: #e6edf3; font-size: 12px; }
#nrp-root .nrp-settings-desc { color: #6e7681; font-size: 10px; margin-top: 1px; }
#nrp-root .nrp-settings-ctl { flex: 0 0 auto; display: flex; align-items: center; gap: 5px; }
#nrp-root .nrp-settings-input {
  width: 92px; background: #010409; border: 1px solid #30363d;
  color: #e6edf3; border-radius: 5px; font-family: inherit;
  font-size: 11px; padding: 4px 6px; outline: none; text-align: right;
}
#nrp-root .nrp-settings-select {
  background: #010409; border: 1px solid #30363d; color: #e6edf3;
  border-radius: 5px; font-family: inherit; font-size: 11px;
  padding: 4px 6px; outline: none;
}
#nrp-root .nrp-settings-unit { color: #8b949e; font-size: 10px; min-width: 18px; }
#nrp-root .nrp-settings-check { width: 15px; height: 15px; accent-color: #1f6feb; cursor: pointer; }
#nrp-root .nrp-settings-actions { display: flex; flex-wrap: wrap; gap: 6px; padding: 8px 0 2px; }
#nrp-root .nrp-settings-note { color: #6e7681; font-size: 10px; line-height: 1.6; padding: 6px 2px 2px; }
#nrp-root .nrp-settings-status { color: #3fb950; font-size: 10px; min-height: 14px; padding: 2px; }

/* ---------------- 紧凑行高 ---------------- */
#nrp-root.nrp-dense td { padding: 2px 8px; }
#nrp-root.nrp-dense th { padding: 3px 8px; }
#nrp-root.nrp-dense .nrp-wf-row { height: 19px; }
#nrp-root.nrp-dense .nrp-wf-bar { top: 4px; height: 11px; }

@media (max-width: 768px) {
  #nrp-root .nrp-wf-label-head, #nrp-root .nrp-wf-label { flex-basis: 46%; }
  #nrp-root .nrp-wf-legend { display: none; }
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
      try { win.localStorage.setItem(LS_KEY_SLOW, String(v)); } catch (e) {}
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
    largeResInputEl = input;
    wrap.appendChild(input);
    wrap.appendChild(h('span', { class: 'nrp-slow-unit' }, 'KB'));

    function commit() {
      const v = parseFloat(input.value);
      if (isNaN(v) || v < 0) return;
      largeResThreshold = Math.round(v * 1024);
      try { win.localStorage.setItem(LS_KEY_LARGE_RES, String(largeResThreshold)); } catch (e) {}
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
    resSlowInputEl = input;
    wrap.appendChild(input);
    wrap.appendChild(h('span', { class: 'nrp-slow-unit' }, 'ms'));

    input.addEventListener('input', function () {
      const v = parseInt(input.value, 10);
      if (isNaN(v) || v < 0) return;
      resSlowThreshold = v;
      try { win.localStorage.setItem(LS_KEY_RES_SLOW, String(v)); } catch (e) {}
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
        try { win.localStorage.setItem(LS_KEY_GROUP, groupBy); } catch (e) {}
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
    if (wfTabBtnEl) {
      wfTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_WATERFALL);
      const c = wfTabBtnEl.querySelector('.nrp-tab-count');
      if (c) c.textContent = String(records.length);
    }
    if (consoleTabBtnEl) {
      consoleTabBtnEl.classList.toggle('nrp-tab-active', currentTab === TAB_CONSOLE);
      const cc = consoleTabBtnEl.querySelector('.nrp-tab-count');
      if (cc) cc.textContent = String(consoleRecords.length);
    }
  }

  function switchTab(tab) {
    if (tab === currentTab) return;
    if (tab !== TAB_NETWORK && tab !== TAB_RESOURCE && tab !== TAB_STORAGE &&
        tab !== TAB_WS && tab !== TAB_WATERFALL && tab !== TAB_CONSOLE) return;

    const isTableView = function (t) {
      return t !== TAB_STORAGE && t !== TAB_WS && t !== TAB_WATERFALL && t !== TAB_CONSOLE;
    };

    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    const st = tabState[currentTab];
    st.search = searchEl ? searchEl.value : '';
    if (isTableView(currentTab)) {
      st.groupBy = groupBy;
      st.collapsed = collapsedGroups;
    }

    currentTab = tab;
    if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
    const next = tabState[currentTab];
    if (isTableView(tab)) {
      groupBy = next.groupBy || '';
      collapsedGroups = next.collapsed || Object.create(null);
    }

    if (searchEl) {
      searchEl.value = next.search || '';
      searchEl.placeholder = tab === TAB_RESOURCE
        ? 'Search url / type / source (cache/network) / protocol …（-word 排除）'
        : (tab === TAB_STORAGE
          ? 'Search name / value …（-word 排除）'
          : (tab === TAB_WATERFALL
            ? 'Search 接口 + 资源：url / method / status / type / headers …（-word 排除）'
            : (tab === TAB_CONSOLE
              ? 'Search console 日志内容 / 级别 / 来源 …（-word 排除）'
              : 'Search url / method / params / body / headers / status / response / mime …（-word 排除）')));
    }
    fillGroupOptions();

    if (groupWrapEl) groupWrapEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (netTableWrapEl) netTableWrapEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (resTableWrapEl) resTableWrapEl.style.display = tab === TAB_RESOURCE ? '' : 'none';
    if (typeof wsTableWrapEl !== 'undefined' && wsTableWrapEl) wsTableWrapEl.style.display = tab === TAB_WS ? '' : 'none';
    if (waterfallWrapEl) waterfallWrapEl.style.display = tab === TAB_WATERFALL ? '' : 'none';
    if (storeWrapEl) storeWrapEl.style.display = tab === TAB_STORAGE ? '' : 'none';
    if (consoleTableWrapEl) consoleTableWrapEl.style.display = tab === TAB_CONSOLE ? '' : 'none';
    if (consoleToolsWrapEl) consoleToolsWrapEl.style.display = tab === TAB_CONSOLE ? '' : 'none';
    if (consoleChipsWrapEl) consoleChipsWrapEl.style.display = tab === TAB_CONSOLE ? '' : 'none';
    if (chipsEl) chipsEl.style.display = tab === TAB_NETWORK ? '' : 'none';
    if (chipsResEl) chipsResEl.style.display = tab === TAB_RESOURCE ? '' : 'none';
    const isNet = tab === TAB_NETWORK;
    const isVisualOnly = tab === TAB_STORAGE || tab === TAB_WS || tab === TAB_WATERFALL || tab === TAB_CONSOLE;
    /* WS 页签的 Clear 用于清空 WebSocket 记录，需保留 */
    if (clearBtnEl) clearBtnEl.style.display = (tab === TAB_STORAGE || tab === TAB_WATERFALL) ? 'none' : '';
    if (exportBtnEl) exportBtnEl.style.display = (isVisualOnly && tab !== TAB_CONSOLE) ? 'none' : '';
    if (harBtnEl) harBtnEl.style.display = isNet ? '' : 'none';
    if (importBtnEl) importBtnEl.style.display = isNet ? '' : 'none';
    if (maskBtnEl) maskBtnEl.style.display = isVisualOnly ? 'none' : '';
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


  /* ============================ 悬浮图标拖拽 ============================ */

  function clampNum(v, min, max) {
    return Math.max(min, Math.min(max, v));
  }

  function fabBounds() {
    return {
      min: FAB_EDGE,
      maxLeft: Math.max(FAB_EDGE, win.innerWidth - FAB_SIZE - FAB_EDGE),
      maxTop: Math.max(FAB_EDGE, win.innerHeight - FAB_SIZE - FAB_EDGE)
    };
  }

  /* 把保存的坐标应用到图标：从 right/bottom 切换为 left/top，并限制在可视区域内 */
  function applyFabPos(fab, pos) {
    if (!fab || !pos) return;
    const b = fabBounds();
    fab.style.left = clampNum(pos.left, b.min, b.maxLeft) + 'px';
    fab.style.top = clampNum(pos.top, b.min, b.maxTop) + 'px';
    fab.style.right = 'auto';
    fab.style.bottom = 'auto';
  }

  function saveFabPos(pos) {
    fabPos = pos;
    try { win.localStorage.setItem(LS_KEY_FAB_POS, JSON.stringify(pos)); }
    catch (e) { /* ignore */ }
  }

  function resetFabPos(fab) {
    fabPos = null;
    try { win.localStorage.removeItem(LS_KEY_FAB_POS); } catch (e) { /* ignore */ }
    fab.style.left = '';
    fab.style.top = '';
    fab.style.right = '';
    fab.style.bottom = '';
    syncPanelSide();
  }

  /* 图标被拖到左半屏时把面板锚点翻到左侧，避免宽面板溢出屏幕 */
  function syncPanelSide() {
    if (!rootEl) return;
    if (!fabPos) { rootEl.style.left = ''; rootEl.style.right = ''; return; }
    const leftSide = fabPos.left + FAB_SIZE / 2 < win.innerWidth / 2;
    rootEl.style.left = leftSide ? '16px' : '';
    rootEl.style.right = leftSide ? 'auto' : '';
  }

  /**
   * 让悬浮图标可拖拽定位：
   * - Pointer Events 统一鼠标 / 触摸，pointer capture 保证指针移出后仍能拖
   * - 位移超过阈值才算拖拽，拖拽结束不会误触发「打开面板」
   * - 松手后写入 localStorage；视口变化时重新约束回屏幕内
   */
  function makeFabDraggable(fab, onClick) {
    let dragging = false;
    let moved = false;
    let ignoreClick = false;
    let startX = 0, startY = 0, originLeft = 0, originTop = 0;

    fab.addEventListener('pointerdown', function (e) {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      ignoreClick = false;
      const rect = fab.getBoundingClientRect();
      dragging = true;
      moved = false;
      startX = e.clientX;
      startY = e.clientY;
      originLeft = rect.left;
      originTop = rect.top;
      try { fab.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    });

    fab.addEventListener('pointermove', function (e) {
      if (!dragging) return;
      const dx = e.clientX - startX;
      const dy = e.clientY - startY;
      if (!moved) {
        if (Math.abs(dx) + Math.abs(dy) < FAB_DRAG_THRESHOLD) return;
        moved = true;
        /* 首次真正拖动时才固定为 left/top：纯点击后图标仍跟随默认右下角 */
        fab.style.right = 'auto';
        fab.style.bottom = 'auto';
        fab.classList.add('nrp-fab-dragging');
      }
      e.preventDefault();
      const b = fabBounds();
      fab.style.left = clampNum(originLeft + dx, b.min, b.maxLeft) + 'px';
      fab.style.top = clampNum(originTop + dy, b.min, b.maxTop) + 'px';
    });

    function endDrag(e) {
      if (!dragging) return;
      dragging = false;
      try { fab.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
      fab.classList.remove('nrp-fab-dragging');
      if (!moved) return;
      ignoreClick = true;
      const left = parseFloat(fab.style.left) || 0;
      const top = parseFloat(fab.style.top) || 0;
      saveFabPos({ left: left, top: top });
    }

    fab.addEventListener('pointerup', endDrag);
    fab.addEventListener('pointercancel', endDrag);
    fab.addEventListener('lostpointercapture', function () {
      if (!dragging) return;
      dragging = false;
      fab.classList.remove('nrp-fab-dragging');
      if (moved) ignoreClick = true;
    });
    fab.addEventListener('dragstart', function (e) { e.preventDefault(); });

    fab.addEventListener('click', function (e) {
      if (ignoreClick) { ignoreClick = false; e.preventDefault(); return; }
      onClick();
    });

    /* 右键复位到默认右下角，不与单击/双击抢事件 */
    fab.addEventListener('contextmenu', function (e) {
      e.preventDefault();
      resetFabPos(fab);
    });

    win.addEventListener('resize', function () {
      applyFabPos(fab, fabPos);
      syncPanelSide();
    });
  }


  /* ============================ 表格列宽拖拽 ============================ */

  function loadColumnWidths() {
    const out = Object.create(null);
    try {
      const raw = win.localStorage.getItem(LS_KEY_COL_WIDTHS);
      if (!raw) return out;
      const obj = JSON.parse(raw);
      if (!obj || typeof obj !== 'object') return out;
      COL_WIDTH_KEYS.forEach(function (key) {
        const def = COL_DEFAULTS[key];
        if (!Array.isArray(obj[key]) || obj[key].length !== def.length) return;
        const arr = [];
        let total = 0;
        for (let i = 0; i < obj[key].length; i++) {
          const n = Number(obj[key][i]);
          if (!isFinite(n) || n < 1 || n > 100) return;
          arr.push(Math.round(n * 100) / 100);
          total += n;
        }
        /* 列宽始终在相邻两列间此消彼长，合计应接近 100%；异常数据直接忽略 */
        if (Math.abs(total - 100) > 5) return;
        out[key] = arr;
      });
    } catch (e) { /* ignore */ }
    return out;
  }

  function saveColumnWidths() {
    try {
      /* 没有任何自定义列宽时移除键，避免「恢复默认」后又留下空对象 */
      if (!Object.keys(columnWidths).length) {
        win.localStorage.removeItem(LS_KEY_COL_WIDTHS);
        return;
      }
      win.localStorage.setItem(LS_KEY_COL_WIDTHS, JSON.stringify(columnWidths));
    } catch (e) { /* ignore */ }
  }

  /* 列宽统一用百分比保存：表始终 100% 宽，拖拽只与右侧相邻列互换宽度 */
  function readColPercents(cols, key) {
    const out = [];
    for (let i = 0; i < cols.length; i++) {
      const v = parseFloat(cols[i].style.width);
      out.push(isFinite(v) && v > 0 ? v : ((COL_DEFAULTS[key] || [])[i] || 10));
    }
    return out;
  }

  function writeColPercents(cols, percents) {
    for (let i = 0; i < cols.length && i < percents.length; i++) {
      cols[i].style.width = (Math.max(1, Math.round(percents[i] * 100) / 100)) + '%';
    }
  }

  function applySavedColWidths(table, key) {
    const cols = table.querySelectorAll('colgroup col');
    if (!cols.length) return;
    const saved = columnWidths[key];
    writeColPercents(cols, saved && saved.length === cols.length ? saved : COL_DEFAULTS[key]);
  }

  function resetColWidths(key) {
    delete columnWidths[key];
    saveColumnWidths();
    if (colTableRefs[key]) applySavedColWidths(colTableRefs[key], key);
  }

  function resetAllColWidths() {
    COL_WIDTH_KEYS.forEach(resetColWidths);
  }

  function tablePixelWidth(table) {
    try {
      if (table.getBoundingClientRect) {
        const w = table.getBoundingClientRect().width;
        if (w && isFinite(w)) return w;
      }
    } catch (e) { /* ignore */ }
    return table.offsetWidth || 1180;
  }

  function setResizingCursor(on) {
    try {
      if (document.body && document.body.classList) {
        document.body.classList.toggle('nrp-col-resizing', !!on);
      }
    } catch (e) { /* ignore */ }
  }

  function addColResizeHandle(table, cols, th, index, key) {
    const handle = h('span', {
      class: 'nrp-col-resizer', title: '拖拽调整列宽 · 双击复位'
    });
    th.appendChild(handle);

    let dragging = false;
    let startX = 0;
    let base = null;
    let minPct = 4;

    handle.addEventListener('pointerdown', function (e) {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      e.preventDefault();
      e.stopPropagation();
      base = readColPercents(cols, key);
      minPct = Math.max(1, MIN_COL_WIDTH / tablePixelWidth(table) * 100);
      startX = e.clientX;
      dragging = true;
      setResizingCursor(true);
      try { handle.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    });

    handle.addEventListener('pointermove', function (e) {
      if (!dragging || !base) return;
      e.preventDefault();
      const delta = (e.clientX - startX) / tablePixelWidth(table) * 100;
      let a = base[index] + delta;
      let b = base[index + 1] - delta;
      if (a < minPct) { b -= (minPct - a); a = minPct; }
      if (b < minPct) { a -= (minPct - b); b = minPct; }
      if (a < minPct) a = minPct;
      if (b < minPct) b = minPct;
      const next = base.slice();
      next[index] = a;
      next[index + 1] = b;
      writeColPercents(cols, next);
    });

    function commit() {
      columnWidths[key] = readColPercents(cols, key);
      saveColumnWidths();
    }
    function endDrag(e) {
      if (!dragging) return;
      dragging = false;
      setResizingCursor(false);
      try { handle.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
      commit();
    }
    handle.addEventListener('pointerup', endDrag);
    handle.addEventListener('pointercancel', endDrag);
    handle.addEventListener('lostpointercapture', function () {
      if (!dragging) return;
      dragging = false;
      setResizingCursor(false);
      commit();
    });
    handle.addEventListener('dblclick', function (e) {
      e.preventDefault();
      e.stopPropagation();
      resetColWidths(key);
    });
    return handle;
  }

  function installColumnResizers(table, key) {
    if (!table) return;
    colTableRefs[key] = table;
    const cols = table.querySelectorAll('colgroup col');
    const ths = table.querySelectorAll('thead th');
    if (!cols.length || !ths.length) return;
    applySavedColWidths(table, key);
    for (let i = 0; i < ths.length - 1 && i < cols.length - 1; i++) {
      addColResizeHandle(table, cols, ths[i], i, key);
    }
  }


  /* ============================ 请求耗时瀑布图 ============================ */

  function wfFmt(ms) {
    return formatDuration(Math.round(ms || 0));
  }

  function wfShortUrl(url) {
    const s = String(url || '');
    let p;
    try {
      const u = new URL(s, location.href);
      p = (u.pathname || '/') + (u.search || '');
    } catch (e) { p = s; }
    return p.length > 160 ? p.slice(0, 157) + '…' : p;
  }

  function wfColorClass(r) {
    if (r.kind === 'resource') return 'nrp-wf-res';
    if (r.responseKind === 'sse') return 'nrp-wf-sse';
    if (r.duration == null) return 'nrp-wf-pending';
    const s = r.status || 0;
    if (s >= 200 && s < 300) return 'nrp-wf-ok';
    if (s >= 300 && s < 400) return 'nrp-wf-redirect';
    return 'nrp-wf-err';
  }

  /* PerformanceEntry 的 ttfb 覆盖 dns+tcp，减去后得到近似的 waiting 段 */
  function wfPhases(r) {
    const t = r && r.timing;
    if (!t) return null;
    const blocked = Math.max(0, t.blocked || 0);
    const dns = Math.max(0, t.dns || 0);
    const tcp = Math.max(0, t.tcp || 0);
    const wait = Math.max(0, (t.ttfb || 0) - dns - tcp);
    const download = Math.max(0, t.download || 0);
    const parts = [
      ['Blocked', blocked, 'nrp-wf-seg-blocked'],
      ['DNS', dns, 'nrp-wf-seg-dns'],
      ['TCP', tcp, 'nrp-wf-seg-tcp'],
      ['Waiting', wait, 'nrp-wf-seg-wait'],
      ['Download', download, 'nrp-wf-seg-download']
    ].filter(function (p) { return p[1] > 0; });
    let total = 0;
    parts.forEach(function (p) { total += p[1]; });
    return total > 0 ? { parts: parts, total: total } : null;
  }

  function wfTooltip(r, startMs, phases) {
    const lines = [
      (r.method || 'GET') + '  ' + (r.status || (r.kind === 'resource' ? 'resource' : 'pending')),
      String(r.url || ''),
      '开始偏移  ' + wfFmt(startMs),
      '总耗时    ' + (r.duration == null ? '进行中…' : wfFmt(r.duration))
    ];
    if (phases) {
      lines.push('— 阶段（近似拆分）—');
      phases.parts.forEach(function (p) { lines.push(p[0] + '  ' + wfFmt(p[1])); });
    }
    if (r.size) lines.push('传输大小  ' + formatSize(r.size));
    lines.push('点击查看详情');
    return lines.join('\n');
  }

  /* 瀑布图同时展示接口请求与静态资源；搜索框复用 Network 的 -word 排除语法 */
  function getWaterfallRecords() {
    const raw = searchEl && searchEl.value ? searchEl.value.trim().toLowerCase() : '';
    const terms = raw ? raw.split(/\s+/).filter(Boolean) : [];
    const out = [];
    for (let i = 0; i < records.length; i++) {
      const r = records[i];
      if (terms.length) {
        const hay = (
          (r.url || '') + ' ' + (r.method || '') + ' ' + (r.status || '') + ' ' +
          (r.resType || '') + ' ' + resTypeLabel(r.resType) + ' ' +
          (r.mimeType || '') + ' ' + (r.params || '') + ' ' +
          (r.body || '') + ' ' + (r.reqHeaders || '') + ' ' +
          (r.respHeaders || '') + ' ' + String(r.response || '').slice(0, 400)
        ).toLowerCase();
        if (!matchesTerms(hay, terms)) continue;
      }
      out.push(r);
    }
    return out;
  }

  function buildWaterfallRow(r, t0, span) {
    const start = (r.time || 0) - t0;
    const dur = r.duration == null ? 0 : Math.max(0, r.duration);
    const leftPct = clampNum(start / span * 100, 0, 100);
    const widthPct = clampNum(dur / span * 100, WF_BAR_MIN_PCT,
      Math.max(WF_BAR_MIN_PCT, 100 - leftPct));
    const phases = wfPhases(r);

    const bar = h('div', {
      class: 'nrp-wf-bar ' + wfColorClass(r),
      style: 'left:' + leftPct + '%;width:' + widthPct + '%',
      title: wfTooltip(r, start, phases)
    });
    if (phases) {
      phases.parts.forEach(function (p) {
        bar.appendChild(h('div', {
          class: 'nrp-wf-seg ' + p[2],
          style: 'width:' + (p[1] / phases.total * 100) + '%',
          title: p[0] + ' ' + wfFmt(p[1])
        }));
      });
    }

    const isRes = r.kind === 'resource';
    const durText = r.duration == null ? '…' : wfFmt(r.duration);
    const label = h('div', { class: 'nrp-wf-label' }, [
      h('span', { class: 'nrp-wf-method' }, isRes ? resTypeLabel(r.resType) : (r.method || 'GET')),
      h('span', { class: 'nrp-wf-url', title: r.url }, wfShortUrl(r.url)),
      h('span', {
        class: 'nrp-wf-dur' + (r.duration != null && r.duration >= slowThreshold ? ' nrp-st-err' : '')
      }, durText)
    ]);
    const track = h('div', { class: 'nrp-wf-track' }, bar);
    return h('div', {
      class: 'nrp-wf-row', 'data-nrp-wf-id': String(r.id)
    }, [label, track]);
  }

  function renderWaterfall() {
    if (!wfRowsEl) return;
    updateTabButtons();

    const list = getWaterfallRecords();
    if (statsEl) statsEl.textContent = list.length + ' / ' + records.length;
    if (wfSortMode === 'slow') {
      list.sort(function (a, b) { return (b.duration || 0) - (a.duration || 0) || a.time - b.time; });
    } else if (wfSortMode === 'latest') {
      list.sort(function (a, b) { return b.time - a.time || b.id - a.id; });
    } else {
      list.sort(function (a, b) { return a.time - b.time || a.id - b.id; });
    }

    wfRowMap = Object.create(null);
    let t0 = Infinity;
    let tEnd = 0;
    for (let i = 0; i < list.length; i++) {
      const r = list[i];
      const start = r.time || 0;
      if (start < t0) t0 = start;
      const end = start + (r.duration == null ? 0 : Math.max(0, r.duration));
      if (end > tEnd) tEnd = end;
    }
    if (!isFinite(t0)) t0 = Date.now();
    const span = Math.max(1, wfScaleMs > 0 ? wfScaleMs : (tEnd - t0));

    let slowest = 0;
    let sum = 0;
    let counted = 0;
    const frag = document.createDocumentFragment();
    for (let i = 0; i < list.length; i++) {
      const r = list[i];
      wfRowMap[r.id] = r;
      if (r.duration != null) {
        sum += r.duration;
        counted++;
        if (r.duration > slowest) slowest = r.duration;
      }
      frag.appendChild(buildWaterfallRow(r, t0, span));
    }

    if (wfSummaryEl) {
      wfSummaryEl.textContent = list.length + ' 条 · 窗口 0–' + wfFmt(span) +
        ' · 最慢 ' + wfFmt(slowest) + ' · 平均 ' + wfFmt(counted ? sum / counted : 0);
    }
    if (wfAxisEl) {
      clearEl(wfAxisEl);
      for (let k = 0; k <= 4; k++) {
        wfAxisEl.appendChild(h('div', {
          class: 'nrp-wf-tick' + (k === 0 ? ' nrp-wf-tick-first' : '') +
            (k === 4 ? ' nrp-wf-tick-last' : ''),
          style: 'left:' + (k * 25) + '%'
        }, wfFmt(span * k / 4)));
      }
    }

    clearEl(wfRowsEl);
    if (wfAxisRowEl) wfRowsEl.appendChild(wfAxisRowEl);
    if (!list.length) {
      wfRowsEl.appendChild(h('div', { class: 'nrp-wf-empty' },
        records.length ? 'No records match the current filter.' : 'Waiting for requests…'));
    } else {
      wfRowsEl.appendChild(frag);
    }
  }


  /* ============================ 集中设置面板 ============================ */

  function settingsStatus(msg) {
    if (settingsStatusEl) settingsStatusEl.textContent = msg || '';
  }

  function settingsGroup(title) {
    return h('div', { class: 'nrp-settings-group' }, title);
  }

  function settingsRow(name, desc, control) {
    return h('div', { class: 'nrp-settings-row' }, [
      h('div', { class: 'nrp-settings-info' }, [
        h('div', { class: 'nrp-settings-name' }, name),
        h('div', { class: 'nrp-settings-desc' }, desc)
      ]),
      h('div', { class: 'nrp-settings-ctl' }, control)
    ]);
  }

  function settingsCheckbox(ref, onChange) {
    const input = h('input', { class: 'nrp-settings-check', type: 'checkbox' });
    settingsCtl[ref] = input;
    input.addEventListener('change', function () { onChange(!!input.checked); });
    return [input];
  }

  function settingsNumber(ref, min, max, unit, onChange) {
    const input = h('input', {
      class: 'nrp-settings-input', type: 'number',
      min: String(min), max: String(max), step: '1'
    });
    settingsCtl[ref] = input;
    input.addEventListener('change', function () {
      const v = parseInt(input.value, 10);
      if (isNaN(v) || v < min || v > max) { syncSettingsUI(); return; }
      onChange(v);
      settingsStatus('已保存');
    });
    return [input, h('span', { class: 'nrp-settings-unit' }, unit)];
  }

  function settingsScaleSelect() {
    const sel = h('select', { class: 'nrp-settings-select' });
    WF_SCALE_OPTIONS.forEach(function (o) {
      sel.appendChild(h('option', { value: String(o.value) }, o.label));
    });
    settingsCtl.wfScale = sel;
    sel.addEventListener('change', function () {
      wfScaleMs = parseInt(sel.value, 10) || 0;
      writeSetting(LS_KEY_WF_SCALE, wfScaleMs);
      if (wfScaleSelectEl) wfScaleSelectEl.value = String(wfScaleMs);
      scheduleRender();
      settingsStatus('瀑布图时间窗已保存');
    });
    return [sel];
  }

  function syncToolbarControls() {
    if (slowInputEl) slowInputEl.value = String(slowThreshold);
    if (resSlowInputEl) resSlowInputEl.value = String(resSlowThreshold);
    if (largeResInputEl) largeResInputEl.value = String(Math.round(largeResThreshold / 1024));
    if (pauseBtnEl) {
      pauseBtnEl.textContent = capturePaused ? 'Resume' : 'Pause';
      pauseBtnEl.classList.toggle('nrp-btn-active', capturePaused);
      pauseBtnEl.title = capturePaused ? '已暂停记录，点击恢复' : '暂停记录';
    }
    if (maskBtnEl) {
      maskBtnEl.classList.toggle('nrp-btn-active', maskOnExport);
      maskBtnEl.title = '导出时对敏感字段脱敏（当前：' + (maskOnExport ? '开启' : '关闭') + '）';
    }
    if (wfScaleSelectEl) wfScaleSelectEl.value = String(wfScaleMs);
  }

  function applyDenseMode() {
    if (rootEl) rootEl.classList.toggle('nrp-dense', !!denseRows);
  }

  function syncSettingsUI() {
    if (settingsCtl.paused) settingsCtl.paused.checked = capturePaused;
    if (settingsCtl.mask) settingsCtl.mask.checked = maskOnExport;
    if (settingsCtl.dense) settingsCtl.dense.checked = denseRows;
    if (settingsCtl.slow) settingsCtl.slow.value = String(slowThreshold);
    if (settingsCtl.resSlow) settingsCtl.resSlow.value = String(resSlowThreshold);
    if (settingsCtl.largeRes) settingsCtl.largeRes.value = String(Math.round(largeResThreshold / 1024));
    if (settingsCtl.maxRecords) settingsCtl.maxRecords.value = String(maxRecords);
    if (settingsCtl.maxResRecords) settingsCtl.maxResRecords.value = String(maxResourceRecords);
    if (settingsCtl.wfScale) settingsCtl.wfScale.value = String(wfScaleMs);
    settingsStatus('');
  }

  function openSettingsModal() {
    syncSettingsUI();
    if (settingsModal) settingsModal.open();
  }

  function resetAllSettings() {
    try {
      if (typeof win.confirm === 'function' &&
          !win.confirm('恢复所有设置为默认值？已捕获的记录不会被清除。')) return;
    } catch (e) { /* ignore */ }

    capturePaused = false;
    maskOnExport = true;
    denseRows = false;
    slowThreshold = DEFAULT_SLOW_THRESHOLD;
    largeResThreshold = DEFAULT_LARGE_RES_THRESHOLD;
    resSlowThreshold = DEFAULT_RES_SLOW_THRESHOLD;
    maxRecords = DEFAULT_MAX_RECORDS;
    maxResourceRecords = DEFAULT_MAX_RESOURCE_RECORDS;
    wfScaleMs = 0;
    groupBy = '';
    collapsedGroups = Object.create(null);
    if (tabState.network) { tabState.network.groupBy = ''; tabState.network.collapsed = collapsedGroups; }

    [LS_KEY_PAUSED, LS_KEY_MASK_EXPORT, LS_KEY_SLOW, LS_KEY_LARGE_RES,
      LS_KEY_RES_SLOW, LS_KEY_DENSE, LS_KEY_MAX_RECORDS, LS_KEY_MAX_RES_RECORDS,
      LS_KEY_WF_SCALE, LS_KEY_COL_WIDTHS, LS_KEY_FAB_POS, LS_KEY_GROUP].forEach(function (k) {
      try { win.localStorage.removeItem(k); } catch (e) { /* ignore */ }
    });

    columnWidths = Object.create(null);
    resetAllColWidths();
    if (fabEl) resetFabPos(fabEl);
    applyDenseMode();
    syncToolbarControls();
    fillGroupOptions();
    syncSettingsUI();
    scheduleRender();
    settingsStatus('已恢复全部默认设置');
  }

  function buildSettingsModal() {
    const resetColsBtn = h('button', { class: 'nrp-btn', type: 'button' }, '复位所有列宽');
    const resetFabBtn = h('button', { class: 'nrp-btn', type: 'button' }, '复位悬浮图标');
    const resetAllBtn = h('button', { class: 'nrp-btn nrp-btn-danger', type: 'button' }, '恢复全部默认');
    const doneBtn = h('button', { class: 'nrp-btn nrp-btn-primary', type: 'button' }, '完成');
    settingsStatusEl = h('div', { class: 'nrp-settings-status' }, '');

    const rows = [
      settingsGroup('捕获与隐私'),
      settingsRow('暂停记录', '暂停后不再采集新请求、WebSocket、静态资源与 console 日志（含跨帧上报）',
        settingsCheckbox('paused', function (v) {
          capturePaused = v;
          writeSetting(LS_KEY_PAUSED, v ? '1' : '0');
          syncToolbarControls();
          settingsStatus(v ? '已暂停记录' : '已恢复记录');
        })),
      settingsRow('导出脱敏', 'JSON / HAR 导出时遮蔽 Authorization、Cookie、token、密码等字段',
        settingsCheckbox('mask', function (v) {
          maskOnExport = v;
          writeSetting(LS_KEY_MASK_EXPORT, v ? '1' : '0');
          syncToolbarControls();
          settingsStatus('导出脱敏已' + (v ? '开启' : '关闭'));
        })),

      settingsGroup('阈值与容量'),
      settingsRow('慢请求阈值', 'Network 列表与瀑布图中超过该耗时的记录标红',
        settingsNumber('slow', 0, 600000, 'ms', function (v) {
          slowThreshold = v;
          writeSetting(LS_KEY_SLOW, v);
          syncToolbarControls();
          scheduleRender();
        })),
      settingsRow('资源慢请求阈值', 'Resources 页签 slow 快捷过滤的阈值',
        settingsNumber('resSlow', 0, 600000, 'ms', function (v) {
          resSlowThreshold = v;
          writeSetting(LS_KEY_RES_SLOW, v);
          syncToolbarControls();
          scheduleRender();
        })),
      settingsRow('大资源阈值', 'Resources 页签 large 快捷过滤的阈值',
        settingsNumber('largeRes', 0, 102400, 'KB', function (v) {
          largeResThreshold = v * 1024;
          writeSetting(LS_KEY_LARGE_RES, largeResThreshold);
          syncToolbarControls();
          scheduleRender();
        })),
      settingsRow('最大接口记录数', '超出后淘汰最旧的 XHR / fetch / SSE 记录',
        settingsNumber('maxRecords', 50, 10000, '条', function (v) {
          maxRecords = v;
          writeSetting(LS_KEY_MAX_RECORDS, v);
        })),
      settingsRow('最大资源记录数', '超出后淘汰最旧的静态资源记录',
        settingsNumber('maxResRecords', 50, 20000, '条', function (v) {
          maxResourceRecords = v;
          writeSetting(LS_KEY_MAX_RES_RECORDS, v);
        })),

      settingsGroup('视图'),
      settingsRow('紧凑行高', '缩小表格与瀑布图行高，一屏显示更多请求',
        settingsCheckbox('dense', function (v) {
          denseRows = v;
          writeSetting(LS_KEY_DENSE, v ? '1' : '0');
          applyDenseMode();
          settingsStatus(v ? '已启用紧凑行高' : '已恢复标准行高');
        })),
      settingsRow('瀑布图时间窗', '固定横向时间刻度，便于对比多批请求', settingsScaleSelect()),
      h('div', { class: 'nrp-settings-actions' }, [resetColsBtn, resetFabBtn, resetAllBtn]),
      h('div', { class: 'nrp-settings-note' },
        '表头右侧竖线可拖拽调整列宽，双击该竖线复位；列宽、图标位置等设置会分别保存。' +
        '设置保存在当前站点（origin）的 localStorage，换站点后需重新配置。'),
      h('div', { class: 'nrp-settings-note' }, 'Network Debugger v' + SCRIPT_VERSION),
      settingsStatusEl
    ];

    settingsBodyEl = h('div', { class: 'nrp-settings' }, rows);
    settingsModal = createModal({
      modalClass: 'nrp-settings-modal',
      title: 'Settings',
      body: [settingsBodyEl],
      footer: [doneBtn],
      onOpen: syncSettingsUI
    });

    doneBtn.addEventListener('click', function () { settingsModal.close(); });
    resetColsBtn.addEventListener('click', function () {
      resetAllColWidths();
      settingsStatus('所有列宽已复位');
    });
    resetFabBtn.addEventListener('click', function () {
      if (fabEl) resetFabPos(fabEl);
      settingsStatus('悬浮图标已复位到右下角');
    });
    resetAllBtn.addEventListener('click', resetAllSettings);

    return settingsModal;
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
    harBtnEl = h('button', { class: 'nrp-btn', type: 'button', title: 'Export filtered network records as HAR' }, 'HAR');
    fsBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Fullscreen' }, '⤢');
    const hideBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Hide panel' }, '×');
    pauseBtnEl = h('button', {
      class: 'nrp-btn' + (capturePaused ? ' nrp-btn-active' : ''),
      type: 'button', title: capturePaused ? '已暂停记录，点击恢复' : '暂停记录'
    }, capturePaused ? 'Resume' : 'Pause');
    importBtnEl = h('button', {
      class: 'nrp-btn', type: 'button', title: '导入此前导出的 JSON 会话'
    }, 'Import');
    maskBtnEl = h('button', {
      class: 'nrp-btn' + (maskOnExport ? ' nrp-btn-active' : ''),
      type: 'button',
      title: '导出时对敏感字段脱敏（当前：' + (maskOnExport ? '开启' : '关闭') + '）'
    }, 'Mask');
    settingsBtnEl = h('button', {
      class: 'nrp-btn', type: 'button', title: '集中设置：阈值 / 容量 / 隐私 / 视图'
    }, '⚙');
    importFileEl = h('input', { type: 'file', accept: '.json,application/json' });
    importFileEl.style.display = 'none';

    searchEl = h('input', {
      class: 'nrp-search', type: 'text',
      placeholder: 'Search url / method / params / body / headers / status / response / mime …（-word 排除）',
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

    /* ---------------- Console 子页 ---------------- */
    const consoleTbodyEl = h('tbody');
    const consoleTable = h('table', null, [
      h('colgroup', null, [
        h('col', { style: 'width:11%' }), h('col', { style: 'width:8%' }),
        h('col', { style: 'width:65%' }), h('col', { style: 'width:16%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', null, 'Time'), h('th', null, 'Level'),
        h('th', null, 'Message'), h('th', null, 'Source')
      ])),
      consoleTbodyEl
    ]);
    consoleTableWrapEl = h('div', { class: 'nrp-table-wrap' }, consoleTable);
    consoleTableWrapEl.style.display = 'none';
    const consoleChipsEl = buildChipsFrom(CONSOLE_LEVEL_GROUPS, consoleFilter, '清除日志级别过滤');
    consoleChipsEl.id = 'nrp-console-chips';
    consoleChipsEl.style.display = 'none';
    consoleChipsWrapEl = consoleChipsEl;
    consoleAutoScrollEl = h('button', {
      class: 'nrp-console-toggle nrp-console-toggle-on', type: 'button',
      title: '开启后新日志自动滚动到底部'
    }, '⤓ Auto-scroll');
    consoleAutoScrollEl.addEventListener('click', function () {
      consoleAutoScroll = !consoleAutoScroll;
      consoleAutoScrollEl.classList.toggle('nrp-console-toggle-on', consoleAutoScroll);
    });
    const consoleClearBtn = h('button', {
      class: 'nrp-btn nrp-btn-sm', type: 'button',
      title: '清空所有已捕获的 console 日志（不影响页面本身）'
    }, 'Clear');
    consoleClearBtn.addEventListener('click', function () {
      consoleRecords = [];
      render();
    });
    consoleToolsWrapEl = h('div', { class: 'nrp-console-tools' }, [
      consoleAutoScrollEl,
      h('span', { class: 'nrp-console-tools-spacer' }),
      consoleClearBtn
    ]);
    consoleToolsWrapEl.style.display = 'none';

    installColumnResizers(netTable, 'network');
    installColumnResizers(resTable, 'resource');
    installColumnResizers(wsTable, 'websocket');

    /* ---------------- Waterfall 子页 ---------------- */
    wfSummaryEl = h('span', { class: 'nrp-wf-summary' }, '0 条');
    wfScaleSelectEl = h('select', { class: 'nrp-wf-select', title: '横向时间窗' });
    WF_SCALE_OPTIONS.forEach(function (o) {
      wfScaleSelectEl.appendChild(h('option', { value: String(o.value) }, o.label));
    });
    wfScaleSelectEl.value = String(wfScaleMs);
    wfSortSelectEl = h('select', { class: 'nrp-wf-select', title: '排序方式' }, [
      h('option', { value: 'start' }, '按开始时间'),
      h('option', { value: 'latest' }, '最新在前'),
      h('option', { value: 'slow' }, '耗时降序')
    ]);
    wfSortSelectEl.value = wfSortMode;
    wfAxisEl = h('div', { class: 'nrp-wf-axis' });
    /* 刻度行放进滚动容器内并 sticky 置顶，保证与条形共用同一宽度（不受滚动条影响） */
    wfAxisRowEl = h('div', { class: 'nrp-wf-axis-row' }, [
      h('div', { class: 'nrp-wf-label-head' }, 'Request / Duration'),
      wfAxisEl
    ]);
    wfRowsEl = h('div', { class: 'nrp-wf-rows' }, wfAxisRowEl);

    function wfLegend(color, label) {
      return h('span', { class: 'nrp-wf-key' }, [
        h('i', { class: 'nrp-wf-swatch ' + color }), label
      ]);
    }
    const wfLegendEl = h('div', { class: 'nrp-wf-legend' }, [
      wfLegend('nrp-wf-ok', '2xx'),
      wfLegend('nrp-wf-redirect', '3xx'),
      wfLegend('nrp-wf-err', '4xx/5xx/失败'),
      wfLegend('nrp-wf-res', '静态资源'),
      wfLegend('nrp-wf-sse', 'SSE'),
      wfLegend('nrp-wf-pending', '进行中'),
      h('span', { class: 'nrp-wf-key' }, '阶段：'),
      wfLegend('nrp-wf-seg-blocked', 'Blocked'),
      wfLegend('nrp-wf-seg-dns', 'DNS'),
      wfLegend('nrp-wf-seg-tcp', 'TCP'),
      wfLegend('nrp-wf-seg-wait', 'Waiting'),
      wfLegend('nrp-wf-seg-download', 'Download')
    ]);

    waterfallWrapEl = h('div', { class: 'nrp-wf' }, [
      h('div', { class: 'nrp-wf-head' }, [wfSummaryEl, wfScaleSelectEl, wfSortSelectEl, wfLegendEl]),
      wfRowsEl
    ]);
    waterfallWrapEl.style.display = 'none';

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
    consoleTabBtnEl = makeTabButton('Console', 'nrp-tab-count-console', '页面 console 日志（log/warn/error 等）', false);
    storeTabBtnEl = makeTabButton('Storage', 'nrp-tab-count-storage', '查看 / 编辑 Cookies、LocalStorage、SessionStorage', false);
    wfTabBtnEl = makeTabButton('Waterfall', 'nrp-tab-count-waterfall', '请求耗时瀑布图：按时间轴查看并发与耗时', false);

    const header = h('div', { class: 'nrp-header' }, [
      h('div', { class: 'nrp-title' }, [h('span', { class: 'nrp-dot' }), 'Network Debugger']),
      h('div', { class: 'nrp-tabs' }, [netTabBtnEl, resTabBtnEl, wfTabBtnEl, wsTabBtnEl, consoleTabBtnEl, storeTabBtnEl]),
      h('div', { class: 'nrp-actions' }, [
        collapseBtn, clearBtnEl, pauseBtnEl, exportBtnEl, importBtnEl,
        harBtnEl, maskBtnEl, settingsBtnEl, fsBtn, hideBtn, importFileEl
      ])
    ]);

    const body = h('div', { class: 'nrp-body' }, [
      h('div', { class: 'nrp-toolbar' }, [searchEl, groupWrapEl, statsEl]),
      chipsEl, chipsResEl, netTableWrapEl, resTableWrapEl, wsTableWrapEl,
      waterfallWrapEl, storeWrapEl,
      consoleToolsWrapEl, consoleChipsWrapEl, consoleTableWrapEl
    ]);

    panelEl = h('div', { class: 'nrp-panel' }, [header, body]);

    const fab = h('button', {
      class: 'nrp-fab', type: 'button',
      title: '点击打开面板 · 拖动移动位置 · 右键复位'
    }, 'NET');
    applyFabPos(fab, fabPos);
    makeFabDraggable(fab, function () {
      panelEl.style.display = '';
      fab.style.display = 'none';
      syncPanelSide();
      if (needsRender) { needsRender = false; render(); }
    });

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
    storeViewDeleteBtnEl = h('button', {
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
      footer: [storeViewDeleteBtnEl, storeViewCloseEl, storeViewSaveEl],
      showClose: false
    });
    storeViewOverlayEl = storeViewModal.overlay;

    /* ---------- 集中设置面板 ---------- */
    const settingsHandle = buildSettingsModal();

    rootEl = h('div', { id: 'nrp-root' }, [
      panelEl, fab,
      netModal.overlay,
      storeAddModal.overlay,
      storeViewModal.overlay,
      settingsHandle.overlay
    ]);
    (document.documentElement || document.body).appendChild(rootEl);
    installTouchScrollGuard(rootEl);
    fabEl = fab;
    applyDenseMode();

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
    wfTabBtnEl.addEventListener('click', function () { switchTab(TAB_WATERFALL); });
    consoleTabBtnEl.addEventListener('click', function () { switchTab(TAB_CONSOLE); });
    settingsBtnEl.addEventListener('click', openSettingsModal);

    wfScaleSelectEl.addEventListener('change', function () {
      wfScaleMs = parseInt(wfScaleSelectEl.value, 10) || 0;
      writeSetting(LS_KEY_WF_SCALE, wfScaleMs);
      if (settingsCtl.wfScale) settingsCtl.wfScale.value = String(wfScaleMs);
      scheduleRender(0);
    });
    wfSortSelectEl.addEventListener('change', function () {
      wfSortMode = wfSortSelectEl.value || 'start';
      scheduleRender(0);
    });
    /* 瀑布图行点击统一委托，避免每条请求挂一个监听器 */
    wfRowsEl.addEventListener('click', function (e) {
      let node = e.target;
      while (node && node !== wfRowsEl) {
        if (node.getAttribute && node.getAttribute('data-nrp-wf-id')) break;
        node = node.parentNode;
      }
      if (!node || node === wfRowsEl) return;
      const rec = wfRowMap[node.getAttribute('data-nrp-wf-id')];
      if (!rec) return;
      if (rec.kind === 'resource') openResourceModal(rec);
      else openModal(rec);
    });

    Array.prototype.forEach.call(storeTabsEl.children, function (btn) {
      btn.addEventListener('click', function () {
        storeSubTab = btn.getAttribute('data-store') || 'local';
        updateStoreSubTabButtons();
        if (currentTab === TAB_STORAGE) renderStorage();
      });
    });
    storeToolsEl.children[0].addEventListener('click', addStorageEntry);
    storeToolsEl.children[1].addEventListener('click', function () {
      if (currentTab !== TAB_STORAGE) return;
      if (storeSubTab === 'cookie') requestGmCookies(true);
      renderStorage();
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
    storeViewDeleteBtnEl.addEventListener('click', deleteFromViewModal);
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
    win.addEventListener('resize', function () { applyStoreViewTab(); });

    clearBtnEl.addEventListener('click', function () {
      if (currentTab === TAB_WS) {
        wsRecords = [];
        Object.keys(wsMap).forEach(function (k) { delete wsMap[k]; });
        render();
        return;
      }
      if (currentTab === TAB_CONSOLE) {
        consoleRecords = [];
        render();
        return;
      }
      if (currentTab === TAB_RESOURCE) seenResourceKeys.clear();
      const wantRes = currentTab === TAB_RESOURCE;
      const kept = [];
      for (let i = 0; i < records.length; i++) {
        const r = records[i];
        if ((r.kind === 'resource') === wantRes) {
          releaseRecord(r);
          continue;
        }
        kept.push(r);
      }
      records = kept;
      collapsedGroups = Object.create(null);
      if (!tabState[currentTab]) tabState[currentTab] = { search: '' };
      tabState[currentTab].collapsed = collapsedGroups;
      render();
    });

    exportBtnEl.addEventListener('click', exportJSON);
    if (harBtnEl) harBtnEl.addEventListener('click', exportHAR);
    fsBtn.addEventListener('click', toggleFullscreen);

    pauseBtnEl.addEventListener('click', function () {
      capturePaused = !capturePaused;
      try { win.localStorage.setItem(LS_KEY_PAUSED, capturePaused ? '1' : '0'); } catch (e) {}
      pauseBtnEl.textContent = capturePaused ? 'Resume' : 'Pause';
      pauseBtnEl.classList.toggle('nrp-btn-active', capturePaused);
      pauseBtnEl.title = capturePaused ? '已暂停记录，点击恢复' : '暂停记录';
    });
    maskBtnEl.addEventListener('click', function () {
      maskOnExport = !maskOnExport;
      try { win.localStorage.setItem(LS_KEY_MASK_EXPORT, maskOnExport ? '1' : '0'); } catch (e) {}
      maskBtnEl.classList.toggle('nrp-btn-active', maskOnExport);
      maskBtnEl.title = '导出时对敏感字段脱敏（当前：' + (maskOnExport ? '开启' : '关闭') + '）';
    });
    importBtnEl.addEventListener('click', function () { importFileEl.click(); });
    importFileEl.addEventListener('change', function () {
      importSession(importFileEl.files && importFileEl.files[0]);
      importFileEl.value = '';
    });

    hideBtn.addEventListener('click', function () {
      panelEl.style.display = 'none';
      fab.style.display = 'flex';
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
    /* 面板隐藏时不建 DOM、不启定时器；打开面板时再补一次渲染 */
    if (panelEl && panelEl.style.display === 'none') { needsRender = true; return; }
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
    return matchesTerms(hay, terms);
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

  function cell(text, cls, title, field) {
    const td = document.createElement('td');
    td.textContent = text;
    if (cls) td.className = cls;
    if (title) td.title = title;
    if (field) td.setAttribute('data-nrp-field', field);
    return td;
  }

  /* 单元格点击统一由所在行代理，避免每行挂 6~7 个监听器 */
  function fieldOfEvent(e) {
    let node = e.target;
    if (node && node.nodeType !== 1) node = node.parentNode;
    const td = node && node.closest ? node.closest('td[data-nrp-field]') : null;
    return td ? td.getAttribute('data-nrp-field') : null;
  }

  function buildRow(r) {
    const tr = document.createElement('tr');
    tr.className = 'nrp-data-row';

    tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
    tr.appendChild(cell(r.method, 'nrp-cell-method', r.method));

    const st = statusInfo(r);
    tr.appendChild(cell(st.text, st.cls, 'Status: ' + st.text));

    tr.appendChild(cell(r.url, 'nrp-cell-clickable', r.url, 'url'));

    const reqHeaderPreview = r.reqHeaders ? r.reqHeaders.split('\n').filter(Boolean).slice(0, 2).join('; ') : '';
    tr.appendChild(cell(reqHeaderPreview, 'nrp-cell-clickable nrp-cell-headers',
      r.reqHeaders || '(no request headers)', 'req-headers'));

    const params = r.params || '';
    tr.appendChild(cell(params, 'nrp-cell-clickable nrp-cell-query', params, 'params'));

    const bodyStr = r.body || '';
    tr.appendChild(cell(bodyStr, 'nrp-cell-clickable nrp-cell-body', bodyStr, 'body'));

    const respHeaderPreview = r.respHeaders ? r.respHeaders.split('\n').filter(Boolean).slice(0, 2).join('; ') : '';
    tr.appendChild(cell(respHeaderPreview, 'nrp-cell-clickable nrp-cell-headers',
      r.respHeaders || '(no response headers)', 'resp-headers'));

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
    tr.appendChild(cell(preview, 'nrp-cell-clickable ' + previewCls,
      preview.slice(0, 2000), 'response'));

    const durText = r.duration != null ? formatDuration(r.duration) : '';
    const durCls = 'nrp-dim' + (r.duration != null && r.duration >= slowThreshold ? ' nrp-st-err' : '');
    tr.appendChild(cell(durText, durCls, durText));

    tr.addEventListener('click', function (e) {
      const field = fieldOfEvent(e);
      if (field) { e.stopPropagation(); openFieldModal(r, field); }
      else openModal(r);
    });
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

    tr.appendChild(cell(r.url, 'nrp-cell-clickable', r.url));

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
      try { win.open(r.url, '_blank'); } catch (e) {}
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
    const groups = Object.create(null);
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
    if (panelEl && panelEl.style.display === 'none') { needsRender = true; return; }
    if (currentTab === TAB_STORAGE) { renderStorage(); return; }
    if (currentTab === TAB_WS) { renderWS(); updateTabButtons(); return; }
    if (currentTab === TAB_WATERFALL) { renderWaterfall(); return; }
    if (currentTab === TAB_CONSOLE) { renderConsole(); updateTabButtons(); return; }
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

    const wrap = isRes ? resTableWrapEl : netTableWrapEl;
    const keepTop = wrap ? wrap.scrollTop : 0;
    const keepLeft = wrap ? wrap.scrollLeft : 0;
    clearEl(tbodyEl);
    tbodyEl.appendChild(frag);
    /* 全量重建会重置滚动位置，重绘后还原，避免高频请求时列表跳动 */
    if (wrap) { wrap.scrollTop = keepTop; wrap.scrollLeft = keepLeft; }
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
        const byName = Object.create(null);
        const byKey = Object.create(null);
        const hasGm = Array.isArray(gmCookies);

        const src = document.cookie || '';
        const pairs = src.split(';');
        for (let i = 0; i < pairs.length; i++) {
          const pair = pairs[i];
          if (!pair) continue;
          const idx = pair.indexOf('=');
          const name = (idx < 0 ? pair : pair.slice(0, idx)).trim();
          const value = idx < 0 ? '' : pair.slice(idx + 1).trim();
          if (!name) continue;
          const entry = {
            name: name, value: value, httpOnly: false,
            domain: '', path: '', secure: false, sameSite: '',
            expires: 0, session: true,
            from: '', time: 0, source: 'document.cookie'
          };
          byName[name] = entry;
          out.push(entry);
        }

        /* 兜底：从拦截到的响应头还原（浏览器通常会过滤 Set-Cookie，故多数环境为空） */
        Object.keys(setCookieStore).forEach(function (key) {
          const c = setCookieStore[key];
          if (c.deleted || (c.expires && c.expires <= Date.now())) return;
          if (hasGm) return; /* GM_cookie 已就绪，以浏览器存储为准，不再用响应头快照 */
          const same = byName[c.name];
          if (same && !c.httpOnly) {
            same.domain = c.domain;
            same.path = c.path;
            same.secure = c.secure;
            same.sameSite = c.sameSite;
            same.from = c.from;
            same.time = c.time;
            same.source = 'set-cookie';
            return;
          }
          if (byKey[key]) return;
          const item = {
            name: c.name, value: c.value, httpOnly: !!c.httpOnly,
            domain: c.domain, path: c.path, secure: c.secure,
            sameSite: c.sameSite, expires: c.expires, session: false,
            from: c.from, time: c.time, source: 'set-cookie'
          };
          byKey[key] = item;
          out.push(item);
        });

        /* 主数据源：GM_cookie 能读到 HttpOnly，值以浏览器 Cookie 存储为准 */
        if (hasGm) {
          gmCookies.forEach(function (c) {
            if (!c || !c.name) return;
            const key = c.name + '|' + (c.domain || '') + '|' + (c.path || '');
            const domain = c.domain || '';
            const path = c.path || '/';
            const secure = !!c.secure;
            const sameSite = c.sameSite || '';
            const expires = c.expirationDate ? c.expirationDate * 1000 : 0;
            const session = !!c.session;
            const doc = byName[c.name];
            if (doc && !c.httpOnly) {
              doc.domain = domain;
              doc.path = path;
              doc.secure = secure;
              doc.sameSite = sameSite;
              doc.expires = expires;
              doc.session = session;
              doc.source = 'gm_cookie';
              byKey[key] = doc;
              return;
            }
            if (byKey[key]) return;
            const item = {
              name: c.name,
              value: c.value == null ? '' : String(c.value),
              httpOnly: !!c.httpOnly,
              domain: domain, path: path, secure: secure,
              sameSite: sameSite, expires: expires, session: session,
              from: '', time: 0, source: 'gm_cookie'
            };
            byKey[key] = item;
            out.push(item);
          });
        }
        return out;
      }
      const store = storeSubTab === 'local' ? win.localStorage : win.sessionStorage;
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

  function setStorageEntry(name, value, entry) {
    try {
      if (storeSubTab === 'cookie') {
        const path = (entry && entry.path) || '/';
        let str = name + '=' + encodeURIComponent(value) + '; path=' + path;
        if (entry && entry.secure) str += '; secure';
        if (entry && entry.sameSite) str += '; SameSite=' + entry.sameSite;
        document.cookie = str;
        gmCookies = null;
      } else {
        const store = storeSubTab === 'local' ? win.localStorage : win.sessionStorage;
        store.setItem(name, value);
      }
    } catch (e) { /* ignore */ }
  }

  function deleteStorageEntry(name, entry) {
    try {
      if (storeSubTab === 'cookie') {
        const expired = '=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=';
        document.cookie = name + expired + ((entry && entry.path) || '/');
        document.cookie = name + expired + '/';
        gmCookies = null;
      } else {
        const store = storeSubTab === 'local' ? win.localStorage : win.sessionStorage;
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
    try { return win.matchMedia('(max-width: 768px)').matches; }
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
    const readOnly = !!(storeSubTab === 'cookie' && entry.httpOnly);
    storeViewModal.setTitle((readOnly ? '查看 · HttpOnly Cookie' : '查看 / 编辑 · ') +
      STORE_SUB_LABELS[storeSubTab]);
    storeViewKeyEl.value = entry.name;
    storeViewValueEl.value = entry.value;
    storeViewKeyEl.readOnly = readOnly;
    storeViewValueEl.readOnly = readOnly;
    storeViewSaveEl.disabled = readOnly;
    if (storeViewDeleteBtnEl) storeViewDeleteBtnEl.disabled = readOnly;
    const tip = readOnly
      ? 'HttpOnly Cookie 无法通过 document.cookie 读取/修改，此处展示 GM_cookie 读取的快照（只读）'
      : '';
    storeViewKeyEl.title = tip;
    storeViewValueEl.title = tip;
    updateStoreViewHighlight();
    storeViewModal.open();
    storeViewValueEl.focus();
  }

  function closeViewStorageModal() {
    if (storeViewModal) storeViewModal.close();
  }

  function saveViewStorageModal() {
    if (!storeViewEntry) return;
    if (storeSubTab === 'cookie' && storeViewEntry.httpOnly) return;
    const n = (storeViewKeyEl.value || '').trim();
    if (!n) { storeViewKeyEl.focus(); return; }
    if (n !== storeViewEntry.name) deleteStorageEntry(storeViewEntry.name, storeViewEntry);
    setStorageEntry(n, storeViewValueEl.value || '', storeViewEntry);
    closeViewStorageModal();
    renderStorage();
  }

  function deleteFromViewModal() {
    if (!storeViewEntry) return;
    if (storeSubTab === 'cookie' && storeViewEntry.httpOnly) return;
    deleteStorageEntry(storeViewEntry.name, storeViewEntry);
    closeViewStorageModal();
    renderStorage();
  }

  function buildStorageRow(entry) {
    const tr = document.createElement('tr');
    tr.className = 'nrp-store-row';

    const tdName = document.createElement('td');
    tdName.className = 'nrp-store-td nrp-store-name';
    tdName.textContent = entry.name;
    if (storeSubTab === 'cookie') {
      const meta = [];
      if (entry.domain) meta.push('Domain: ' + entry.domain);
      if (entry.path) meta.push('Path: ' + entry.path);
      if (entry.secure) meta.push('Secure');
      if (entry.sameSite) meta.push('SameSite=' + entry.sameSite);
      if (entry.from) meta.push('来源: ' + entry.from);
      if (entry.source === 'gm_cookie') meta.push('由 GM_cookie 读取');
      else if (entry.source === 'set-cookie') meta.push('由响应头 Set-Cookie 还原');
      if (entry.expires) meta.push('Expires: ' + new Date(entry.expires).toLocaleString());
      tdName.title = meta.length ? meta.join('\n') : entry.name;
      if (entry.httpOnly) {
        tdName.appendChild(h('span', {
          class: 'nrp-cookie-badge',
          title: 'HttpOnly：页面 JS 无法读取或修改，值由 GM_cookie 从浏览器 Cookie 存储读取'
        }, 'HttpOnly'));
      }
    } else {
      tdName.title = entry.name;
    }
    tr.appendChild(tdName);

    const tdVal = document.createElement('td');
    tdVal.className = 'nrp-store-td nrp-store-value';
    const valText = document.createElement('div');
    valText.className = 'nrp-store-value-text';
    valText.textContent = entry.value;
    valText.title = entry.httpOnly ? '点击查看完整内容（HttpOnly，只读）' : '点击查看 / 编辑完整内容';
    valText.addEventListener('click', function () { openViewStorageModal(entry); });
    tdVal.appendChild(valText);
    tr.appendChild(tdVal);

    const tdAct = document.createElement('td');
    tdAct.className = 'nrp-store-td nrp-store-actions';
    if (entry.httpOnly) {
      tdAct.appendChild(h('span', {
        class: 'nrp-cookie-ro',
        title: 'HttpOnly Cookie 无法通过 document.cookie 修改或删除'
      }, '只读'));
    } else {
      const delBtn = h('button', { class: 'nrp-btn nrp-btn-sm', type: 'button', title: '删除该条目' }, 'Delete');
      delBtn.addEventListener('click', function () {
        deleteStorageEntry(entry.name, entry);
        renderStorage();
      });
      tdAct.appendChild(delBtn);
    }
    tr.appendChild(tdAct);

    return tr;
  }

  function renderStorage() {
    if (!storeTableWrapEl) return;
    if (storeSubTab === 'cookie') requestGmCookies(false);

    const q = (searchEl && searchEl.value ? searchEl.value : '').trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];

    let entries;
    try { entries = getStorageEntries(); } catch (e) { entries = []; }

    const filtered = entries.filter(function (e) {
      if (!terms.length) return true;
      const hay = (e.name + ' ' + e.value + ' ' + (e.domain || '') + ' ' +
        (e.path || '') + ' ' + (e.httpOnly ? 'httponly' : '')).toLowerCase();
      return matchesTerms(hay, terms);
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
        : (storeSubTab === 'cookie'
          ? '当前 Cookies 为空。HttpOnly Cookie 需要通过 GM_cookie 读取；请确认脚本已被授权 Cookie 权限。'
          : ('当前 ' + STORE_SUB_LABELS[storeSubTab] + ' 为空。'));
      tr.appendChild(td);
      tbody.appendChild(tr);
    } else {
      filtered.forEach(function (e) { tbody.appendChild(buildStorageRow(e)); });
    }

    table.appendChild(tbody);

    const keepTop = storeTableWrapEl.scrollTop;
    const keepLeft = storeTableWrapEl.scrollLeft;
    clearEl(storeTableWrapEl);
    storeTableWrapEl.appendChild(table);
    storeTableWrapEl.scrollTop = keepTop;
    storeTableWrapEl.scrollLeft = keepLeft;
  }


  function renderWS() {
    if (!wsTableWrapEl) return;
    const q = (searchEl && searchEl.value ? searchEl.value : '').trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];
    let list = wsRecords.slice();
    if (terms.length) {
      list = list.filter(function (r) {
        const hay = (r.url + ' ' + (r.state || '')).toLowerCase();
        return matchesTerms(hay, terms);
      });
    }
    if (statsEl) statsEl.textContent = list.length + ' / ' + wsRecords.length;
    const tbody = wsTableWrapEl.querySelector('tbody');
    if (!tbody) return;
    const keepTop = wsTableWrapEl.scrollTop;
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
      wsTableWrapEl.scrollTop = keepTop;
      return;
    }
    for (let i = list.length - 1; i >= 0; i--) {
      const r = list[i];
      const tr = document.createElement('tr');
      tr.className = 'nrp-data-row';
      tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
      tr.appendChild(cell(r.state || '', 'nrp-cell-method'));
      tr.appendChild(cell(r.url, 'nrp-cell-clickable'));
      tr.appendChild(cell(String((r.messages && r.messages.length) || 0), 'nrp-cell-method'));
      const info = r.state === 'closed' ? ('closed' + (r.closeCode != null ? ' ' + r.closeCode : '')) : (r.state || '');
      tr.appendChild(cell(info, 'nrp-dim'));
      tr.addEventListener('click', function () { openWSModal(r); });
      tbody.appendChild(tr);
    }
    wsTableWrapEl.scrollTop = keepTop;
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


  function getFilteredConsole() {
    const raw = searchEl && searchEl.value ? searchEl.value : '';
    const q = raw.trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];
    return consoleRecords.filter(function (r) {
      if (consoleFilter.level.size && !consoleFilter.level.has(consoleLevelGroup(r.level))) return false;
      if (!terms.length) return true;
      const hay = (r.level + ' ' + r.text + ' ' + (r.source || '') + ' ' + (r.frameUrl || '')).toLowerCase();
      return matchesTerms(hay, terms);
    });
  }

  function renderConsole() {
    if (!consoleTableWrapEl) return;
    const list = getFilteredConsole();
    if (statsEl) statsEl.textContent = list.length + ' / ' + consoleRecords.length;
    const tbody = consoleTableWrapEl.querySelector('tbody');
    if (!tbody) return;
    const atBottom = consoleAutoScroll &&
      (consoleTableWrapEl.scrollHeight - consoleTableWrapEl.scrollTop - consoleTableWrapEl.clientHeight < 40);
    clearEl(tbody);

    if (!list.length) {
      const tr = document.createElement('tr');
      tr.className = 'nrp-empty-row';
      const td = document.createElement('td');
      td.className = 'nrp-empty';
      td.colSpan = 4;
      td.textContent = consoleRecords.length
        ? '没有匹配当前搜索或级别过滤的日志。'
        : '等待页面 console 输出…（log / info / warn / error / debug 等）';
      tr.appendChild(td);
      tbody.appendChild(tr);
      return;
    }

    for (let i = list.length - 1; i >= 0; i--) {
      const r = list[i];
      const tr = document.createElement('tr');
      tr.className = 'nrp-data-row';
      tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
      const lv = document.createElement('td');
      lv.className = 'nrp-store-td';
      const badge = h('span', { class: 'nrp-console-lv nrp-console-lv-' + consoleLevelGroup(r.level) }, r.level);
      lv.appendChild(badge);
      tr.appendChild(lv);
      const tdMsg = document.createElement('td');
      tdMsg.className = 'nrp-console-msg';
      tdMsg.textContent = r.text || '(empty)';
      tdMsg.title = r.text || '';
      tr.appendChild(tdMsg);
      const src = r.source || r.frameUrl || '';
      tr.appendChild(cell(src ? (src.length > 90 ? src.slice(0, 90) + '…' : src) : '', 'nrp-console-source', src));
      tr.addEventListener('click', function () { openConsoleModal(r); });
      tbody.appendChild(tr);
    }
    if (atBottom) consoleTableWrapEl.scrollTop = consoleTableWrapEl.scrollHeight;
  }

  function openConsoleModal(r) {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    currentModalRecord = null;
    currentModalExtra = null;
    clearEl(modalHeadlineEl);
    modalHeadlineEl.appendChild(h('span', {
      class: 'nrp-badge nrp-badge-' + (r.level === 'error' || r.level === 'uncaught' || r.level === 'assert'
        ? 'err' : (r.level === 'warn' ? 'time' : 'other'))
    }, r.level));
    modalHeadlineEl.appendChild(h('span', {
      class: 'nrp-modal-url', title: formatFullTime(r.time)
    }, formatTime(r.time)));
    clearEl(modalParamsEl);
    modalParamsEl.style.display = 'none';
    clearEl(modalHeadersEl);
    modalHeadersEl.style.display = '';
    const info = [
      'Level: ' + r.level,
      'Time: ' + formatFullTime(r.time),
      r.frameUrl ? ('Frame: ' + r.frameUrl) : '',
      r.source ? ('Source: ' + r.source) : ''
    ].filter(Boolean).join('\n');
    const sec = makeSection('Info', info);
    if (sec) modalHeadersEl.appendChild(sec);
    if (r.args && r.args.length > 1) {
      const argSec = makeSection('Arguments (' + r.args.length + ')', r.args.map(function (a, i) {
        return '[' + i + '] ' + a;
      }).join('\n'));
      if (argSec) modalHeadersEl.appendChild(argSec);
    }
    clearEl(modalResponseEl);
    modalResponseEl.style.display = '';
    currentCopyText = r.text || '';
    const msec = makeSection('Message', r.text || '(empty)', 'nrp-section-response');
    if (msec) modalResponseEl.appendChild(msec);
    copyBtn.textContent = 'Copy';
    if (netModal) netModal.open();
  }


  /* ============================ 弹窗逻辑 ============================ */

  function buildHeadline(r, extraLabel) {
    clearEl(modalHeadlineEl);
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-method' }, r.method));

    const isSse = r.kind === 'sse';
    modalHeadlineEl.appendChild(h('span', {
      class: 'nrp-badge ' + (isSse ? 'nrp-badge-sse' : 'nrp-badge-other'),
      title: 'Request type'
    }, isSse ? 'SSE' : (r.kind === 'fetch' ? 'fetch' : 'XHR')));

    const st = statusInfo(r);
    const stCls = st.cls === 'nrp-st-ok' ? 'nrp-badge-ok'
      : (st.cls === 'nrp-st-err' ? 'nrp-badge-err' : 'nrp-badge-other');
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge ' + stCls }, st.text));

    if (r.responseKind === 'sse' && !r.sseDone) {
      modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-live', title: '流尚未结束' }, '● LIVE'));
    }

    modalHeadlineEl.appendChild(
      h('span', { class: 'nrp-badge nrp-badge-time', title: formatFullTime(r.time) }, formatTime(r.time))
    );

    if (r.duration != null) {
      modalHeadlineEl.appendChild(
        h('span', { class: 'nrp-badge nrp-badge-dur', title: 'Duration' }, formatDuration(r.duration))
      );
    }

    if (r.mimeType) {
      modalHeadlineEl.appendChild(
        h('span', { class: 'nrp-badge nrp-badge-mime', title: 'MIME: ' + r.mimeType }, r.mimeType.split(';')[0].trim())
      );
    }

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

    if (extraLabel) {
      modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-other' }, extraLabel));
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
    let nodeCount = 0;
    let truncated = false;
    function renderNode(val, key, depth) {
      /* 大 JSON 会递归出海量节点，超过上限立即停手 */
      if (nodeCount >= MAX_TREE_NODES) { truncated = true; return null; }
      nodeCount++;
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
        let html = escapeHTML(val);
        if (search && val.toLowerCase().indexOf(search.toLowerCase()) !== -1) {
          try {
            const re = new RegExp('(' + escapeRegExp(search) + ')', 'ig');
            html = val.split(re).map(function (part, i) {
              return i % 2 ? '<mark>' + escapeHTML(part) + '</mark>' : escapeHTML(part);
            }).join('');
          } catch (e) { /* ignore */ }
        }
        wrap.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') +
          '<span class="nrp-hl-str">"' + html + '"</span>';
        return wrap;
      }
      if (Array.isArray(val)) {
        const details = document.createElement('details');
        details.open = depth < 2;
        const summary = document.createElement('summary');
        summary.innerHTML = (key != null ? '<span class="nrp-hl-key">' + escapeHTML(String(key)) + '</span>: ' : '') + '[Array(' + val.length + ')]';
        details.appendChild(summary);
        for (let i = 0; i < val.length && !truncated; i++) {
          const child = renderNode(val[i], i, depth + 1);
          if (child) details.appendChild(child);
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
        for (let i = 0; i < keys.length && !truncated; i++) {
          const child = renderNode(val[keys[i]], keys[i], depth + 1);
          if (child) details.appendChild(child);
        }
        wrap.appendChild(details);
        return wrap;
      }
      wrap.textContent = String(val);
      return wrap;
    }
    const root = renderNode(obj, null, 0);
    if (root) container.appendChild(root);
    if (truncated) {
      const note = document.createElement('div');
      note.className = 'nrp-json-node';
      note.textContent = '…[节点数超过 ' + MAX_TREE_NODES + '，已截断显示]';
      container.appendChild(note);
    }
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
      /* prettyJSONText 内部会吞掉解析异常，必须显式判断是否为合法 JSON */
      const pretty = trimmed.length <= MAX_TEXT_RESPONSE ? formatJSONOrNull(trimmed) : null;
      if (pretty != null) { formatted = pretty; isJson = true; }
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
    const treeSearchEl = h('input', {
      class: 'nrp-search nrp-tree-search', type: 'text',
      placeholder: 'Search in JSON…', spellcheck: 'false'
    });
    treeSearchEl.value = responseSearchTerm;
    treeSearchEl.style.display = responseViewMode === 'tree' ? '' : 'none';
    treeSearchEl.addEventListener('input', function () {
      responseSearchTerm = treeSearchEl.value;
      renderBody();
    });
    modeWrap.appendChild(rawBtn);
    modeWrap.appendChild(treeBtn);
    modeWrap.appendChild(treeSearchEl);
    container.appendChild(modeWrap);

    const bodyWrap = document.createElement('div');
    bodyWrap.className = 'nrp-response-body-wrap';

    function renderBody() {
      clearEl(bodyWrap);
      if (responseViewMode === 'tree' && isJson && r.responseKind !== 'sse') {
        try {
          const parsed = tryParseJSON(formatted) || tryParseJSON(trimmed);
          if (parsed != null) {
            const tree = buildJSONTree(parsed, responseSearchTerm);
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
      treeSearchEl.style.display = 'none';
      renderBody();
    });
    treeBtn.addEventListener('click', function () {
      responseViewMode = 'tree';
      treeBtn.classList.add('nrp-btn-active');
      rawBtn.classList.remove('nrp-btn-active');
      treeSearchEl.style.display = '';
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

  function openModal(r) {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    responseSearchTerm = '';

    currentModalRecord = r;
    currentModalExtra = null;

    buildHeadline(r, null);
    fillParamsBlock(r);
    fillHeadersBlock(r);
    fillResponseBlock(r);

    openNetworkModal();
  }

  function openFieldModal(r, field) {
    if (modalContentEl) modalContentEl.scrollTop = 0;
    responseSearchTerm = '';

    if (field === 'response') {
      currentModalRecord = r;
      currentModalExtra = 'Response';
      buildHeadline(r, 'Response');
      modalParamsEl.style.display = 'none';
      clearEl(modalParamsEl);
      clearEl(modalHeadersEl);
      modalHeadersEl.style.display = 'none';
      fillResponseBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'req-headers') {
      currentModalRecord = r;
      currentModalExtra = 'Request Headers';
      buildHeadline(r, 'Request Headers');
      modalParamsEl.style.display = 'none';
      clearEl(modalParamsEl);
      clearEl(modalResponseEl);
      modalResponseEl.style.display = 'none';
      currentCopyText = r.reqHeaders || '';
      fillReqHeadersBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'resp-headers') {
      currentModalRecord = r;
      currentModalExtra = 'Response Headers';
      buildHeadline(r, 'Response Headers');
      modalParamsEl.style.display = 'none';
      clearEl(modalParamsEl);
      clearEl(modalResponseEl);
      modalResponseEl.style.display = 'none';
      currentCopyText = r.respHeaders || '';
      fillRespHeadersBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'headers') {
      currentModalRecord = r;
      currentModalExtra = 'Headers';
      buildHeadline(r, 'Headers');
      modalParamsEl.style.display = 'none';
      clearEl(modalParamsEl);

      clearEl(modalHeadersEl);
      const parts = [];
      if (r.reqHeaders) parts.push('Request Headers:\n' + r.reqHeaders);
      if (r.respHeaders) parts.push('Response Headers:\n' + r.respHeaders);
      const content = parts.length ? parts.join('\n\n') : '(no headers)';
      currentCopyText = content;
      const sec = makeSection('Headers', content);
      if (sec) modalHeadersEl.appendChild(sec);
      modalHeadersEl.style.display = '';

      fillResponseBlock(r);
      openNetworkModal();
      return;
    }

    if (field === 'params' || field === 'body') {
      currentModalRecord = r;
      currentModalExtra = field === 'params' ? 'Params' : 'Body';
      currentCopyText = (field === 'params' ? r.params : r.body) || '';
      buildHeadline(r, field === 'params' ? 'Params' : 'Body');
      fillParamsBlock(r, field);

      clearEl(modalHeadersEl);
      modalHeadersEl.style.display = 'none';
      clearEl(modalResponseEl);
      modalResponseEl.style.display = 'none';

      openNetworkModal();
      return;
    }

    currentModalRecord = r;
    currentModalExtra = 'URL';
    const contentText = r.url || '(empty url)';
    currentCopyText = contentText;

    buildHeadline(r, 'URL');

    modalParamsEl.style.display = 'none';
    clearEl(modalParamsEl);
    clearEl(modalHeadersEl);
    modalHeadersEl.style.display = 'none';
    clearEl(modalResponseEl);

    const sec = makeSection('URL', contentText);
    if (sec) modalResponseEl.appendChild(sec);
    modalResponseEl.style.display = '';

    openNetworkModal();
  }

  /* ============================ 复制 / 导出 ============================ */



  function replayRequest(r) {
    try {
      if (!r) return;
      const method = r.method || 'GET';
      const url = r.url || '';
      if (!url) return;

      const hasCred = /authorization|cookie/i.test(r.reqHeaders || '');
      const sideEffect = method !== 'GET' && method !== 'HEAD';
      const tip = 'Replay 会真实重发一次请求' +
        (sideEffect ? '（可能重复提交、产生副作用）' : '') +
        (hasCred ? '，并携带原请求中的 Authorization / Cookie 凭据' : '') +
        '。\n\n' + method + ' ' + url + '\n\n确定继续？';
      if (!win.confirm(tip)) return;
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
          if (win.nrpLog) win.nrpLog('Replayed', method, url, '->', res.status);
        } catch (e) {}
        alert('Replay: ' + method + ' ' + url + '\nStatus: ' + res.status);
      }).catch(function (e) {
        alert('Replay failed: ' + (e && e.message ? e.message : e));
      });
    } catch (e) {
      alert('Replay failed');
    }
  }

  function shellQuote(s) {
    return "'" + String(s).replace(/'/g, "'\\''") + "'";
  }

  /* body 含换行/制表符时改用 ANSI-C 引号 $'...' 正确保留转义（bash / zsh） */
  function shellDataQuote(s) {
    const str = String(s);
    if (!/[\r\n\t]/.test(str)) return shellQuote(str);
    return "$'" + str
      .replace(/\\/g, '\\\\')
      .replace(/'/g, "\\'")
      .replace(/\n/g, '\\n')
      .replace(/\r/g, '\\r')
      .replace(/\t/g, '\\t') + "'";
  }

  function buildCurlCommand(r) {
    try {
      const url = r.url || '';
      if (!url) return '';
      let cmd = 'curl -X ' + (r.method || 'GET') + ' ' + shellQuote(url);
      const reqHeaders = r.reqHeaders || '';
      let compressed = false;
      reqHeaders.split(/\r?\n/).forEach(function (line) {
        if (!line.trim()) return;
        const idx = line.indexOf(':');
        if (idx === -1) return;
        const k = line.slice(0, idx).trim();
        const v = line.slice(idx + 1).trim();
        if (!k) return;
        const lk = k.toLowerCase();
        if (lk === 'content-length' || lk === 'host') return;
        if (lk === 'accept-encoding' && /gzip|br|deflate/i.test(v)) compressed = true;
        cmd += ' -H ' + shellQuote(k + ': ' + v);
      });
      if (compressed) cmd += ' --compressed';
      const body = r.body || '';
      if (body) cmd += ' --data-raw ' + shellDataQuote(body);
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


  const HTTP_STATUS_TEXT = {
    200: 'OK', 201: 'Created', 202: 'Accepted', 204: 'No Content', 206: 'Partial Content',
    301: 'Moved Permanently', 302: 'Found', 304: 'Not Modified', 307: 'Temporary Redirect',
    308: 'Permanent Redirect', 400: 'Bad Request', 401: 'Unauthorized', 403: 'Forbidden',
    404: 'Not Found', 405: 'Method Not Allowed', 408: 'Request Timeout', 409: 'Conflict',
    422: 'Unprocessable Entity', 429: 'Too Many Requests',
    500: 'Internal Server Error', 501: 'Not Implemented', 502: 'Bad Gateway',
    503: 'Service Unavailable', 504: 'Gateway Timeout'
  };

  function parseHeaderLines(text, mask) {
    const out = [];
    (text || '').split(/\r?\n/).forEach(function (line) {
      if (!line.trim()) return;
      const idx = line.indexOf(':');
      if (idx === -1) return;
      const name = line.slice(0, idx).trim();
      const value = line.slice(idx + 1).trim();
      out.push({
        name: name,
        value: mask && SENSITIVE_HEADERS.indexOf(name.toLowerCase()) !== -1 ? MASK_PLACEHOLDER : value
      });
    });
    return out;
  }

  /* Cookie 名称保留，值一律不导出（即使关闭脱敏） */
  function cookieNames(text) {
    const out = [];
    (text || '').split(/\r?\n/).forEach(function (line) {
      const idx = line.indexOf(':');
      if (idx < 0) return;
      const n = line.slice(0, idx).trim().toLowerCase();
      if (n !== 'cookie' && n !== 'set-cookie') return;
      line.slice(idx + 1).split(';').forEach(function (pair) {
        const eq = pair.indexOf('=');
        if (eq > 0) out.push({ name: pair.slice(0, eq).trim(), value: MASK_PLACEHOLDER });
      });
    });
    return out;
  }

  function queryPairs(url) {
    const out = [];
    try {
      new URL(url || '', location.href).searchParams.forEach(function (v, k) {
        out.push({
          name: k,
          value: maskOnExport && SENSITIVE_QUERY_KEYS.indexOf(k.toLowerCase()) !== -1
            ? MASK_PLACEHOLDER : v
        });
      });
    } catch (e) { /* ignore */ }
    return out;
  }

  function exportHAR() {
    const mask = maskOnExport;
    const mx = function (v) { return mask ? maskText(v) : v; };
    const entries = getFiltered().filter(function (r) { return r.kind !== 'resource'; }).map(function (r) {
      const started = r.time || Date.now();
      const bodySize = r.binarySize || (r.response ? r.response.length : 0);
      return {
        pageref: 'page_1',
        startedDateTime: new Date(started).toISOString(),
        time: r.duration != null ? r.duration : 0,
        request: {
          method: r.method || 'GET',
          url: mask ? maskUrl(r.url) : (r.url || ''),
          httpVersion: 'HTTP/1.1',
          cookies: cookieNames(r.reqHeaders),
          headers: parseHeaderLines(r.reqHeaders, mask),
          queryString: queryPairs(r.url),
          postData: r.body ? { mimeType: r.mimeType || 'text/plain', text: mx(r.body) } : undefined,
          headersSize: -1,
          bodySize: r.body ? r.body.length : -1
        },
        response: {
          status: r.status || 0,
          statusText: HTTP_STATUS_TEXT[r.status] || '',
          httpVersion: 'HTTP/1.1',
          cookies: cookieNames(r.respHeaders),
          headers: parseHeaderLines(r.respHeaders, mask),
          content: {
            size: bodySize,
            mimeType: r.mimeType || 'text/plain',
            text: mx(r.response || '')
          },
          redirectURL: '',
          headersSize: -1,
          bodySize: r.response ? bodySize : -1
        },
        cache: {},
        timings: {
          blocked: -1, dns: -1, connect: -1, send: 0,
          wait: r.duration != null ? r.duration : -1, receive: 0, ssl: -1
        }
      };
    });
    const har = {
      log: {
        version: '1.2',
        creator: { name: 'Network Debugger', version: SCRIPT_VERSION },
        pages: [{
          startedDateTime: new Date().toISOString(),
          id: 'page_1',
          title: document.title || location.hostname || '',
          pageTimings: {}
        }],
        entries: entries
      }
    };
    downloadFile('network-' + new Date().toISOString().replace(/[:.]/g, '-') + '.har',
      JSON.stringify(har, null, 2), 'application/json');
  }

  function exportJSON() {
    if (currentTab === TAB_CONSOLE) {
      const list = getFilteredConsole();
      const data = list.map(function (r) {
        return {
          id: r.id, level: r.level, message: maskOnExport ? maskText(r.text) : r.text,
          args: maskOnExport ? r.args.map(maskText) : r.args,
          source: r.source || '', frameUrl: r.frameUrl || '',
          time: formatFullTime(r.time)
        };
      });
      downloadFile('console-' + new Date().toISOString().replace(/[:.]/g, '-') + '.json',
        JSON.stringify(data, null, 2));
      return;
    }
    const isRes = currentTab === TAB_RESOURCE;
    const mask = maskOnExport;
    const mx = function (v) { return mask ? maskText(v) : v; };
    const mu = function (u) { return mask ? maskUrl(u) : u; };

    const data = getFiltered().map(function (r) {
      if (r.kind === 'resource') {
        return {
          id: r.id, type: 'resource', resType: r.resType,
          initiatorType: r.initiatorType, url: mu(r.url),
          transferSize: r.size, encodedBodySize: r.encodedSize,
          decodedBodySize: r.decodedSize, cache: r.cache,
          protocol: r.protocol || '', duration: r.duration,
          timing: r.timing, frameUrl: r.frameUrl || '',
          time: formatFullTime(r.time)
        };
      }
      return {
        id: r.id, type: r.kind, method: r.method, url: mu(r.url),
        params: mx(r.params), body: mx(r.body),
        reqHeaders: mx(r.reqHeaders), respHeaders: mx(r.respHeaders),
        status: r.status,
        responseKind: r.responseKind || 'text',
        sseEvents: r.sseEvents || 0, sseDone: !!r.sseDone,
        mimeType: r.mimeType || '', binarySize: r.binarySize || 0,
        response: mx(r.response), duration: r.duration,
        frameUrl: r.frameUrl || '', time: formatFullTime(r.time)
      };
    });

    downloadFile((isRes ? 'resources-' : 'network-requests-') +
      new Date().toISOString().replace(/[:.]/g, '-') + '.json',
      JSON.stringify(data, null, 2));
  }

  /* 导入 Export / HAR 之外的自有 JSON 会话，便于复现与归档 */
  function importSession(file) {
    if (!file) return;
    const reader = new FileReader();
    reader.onload = function () {
      let parsed;
      try { parsed = JSON.parse(String(reader.result)); }
      catch (e) { alert('Import failed: invalid JSON'); return; }
      if (!Array.isArray(parsed)) { alert('Import failed: expected an array of records'); return; }
      let n = 0;
      parsed.forEach(function (item) {
        if (!item || typeof item !== 'object') return;
        const time = item.time ? (Date.parse(item.time) || Date.now()) : Date.now();
        if (item.type === 'resource') {
          pushRecord({
            kind: 'resource', method: 'GET', url: item.url || '',
            params: '', body: '', reqHeaders: '', respHeaders: '',
            status: 0, response: '', responseKind: 'resource', mimeType: '',
            initiatorType: item.initiatorType || '', resType: item.resType || 'other',
            size: item.transferSize || 0, encodedSize: item.encodedBodySize || 0,
            decodedSize: item.decodedBodySize || 0, cache: item.cache || 'unknown',
            protocol: item.protocol || '', duration: item.duration || 0,
            timing: item.timing || null, time: time, imported: true
          }, true);
        } else {
          pushRecord({
            kind: item.type || 'fetch', method: item.method || 'GET', url: item.url || '',
            params: item.params || '', body: item.body || '',
            reqHeaders: item.reqHeaders || '', respHeaders: item.respHeaders || '',
            status: item.status || 0, response: item.response || '',
            responseKind: item.responseKind || 'text',
            mimeType: item.mimeType || '', binarySize: item.binarySize || 0,
            duration: item.duration == null ? null : item.duration, time: time,
            imported: true
          }, true);
        }
        n++;
      });
      render();
      alert('Imported ' + n + ' records');
    };
    reader.onerror = function () { alert('Import failed: cannot read file'); };
    reader.readAsText(file);
  }

  /* ============================== 启动 ============================== */

  installInterceptors();
  installMessageListener();
  installResourceObserver();
  try { installWebSocketInterceptor(); } catch (e) {}
  try { installConsoleInterceptor(); } catch (e) {}

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
