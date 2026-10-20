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
// ==/UserScript==

(function () {
  'use strict';

  /* ============================== 配置 ============================== */
  const MAX_RECORDS = 1000;
  const PANEL_Z = 2147483600;
  const OVERLAY_Z = 2147483640;
  const RENDER_DELAY = 50;

  /* ============================== 状态 ============================== */
  let records = [];
  let seq = 0;
  let renderTimer = null;
  let currentCopyText = '';

  let rootEl = null;
  let panelEl = null;
  let tbodyEl = null;
  let statsEl = null;
  let searchEl = null;
  let overlayEl = null;
  let modalBodyEl = null;
  let modalHeadlineEl = null;
  let modalParamsEl = null;
  let modalHeadersEl = null;
  let copyBtn = null;

  /* ============================ 工具函数 ============================ */

  function absUrl(u) {
    try { return new URL(String(u), location.href).href; }
    catch (e) { return String(u); }
  }

  function bodyToString(b) {
    if (b == null) return '';
    try {
      if (typeof b === 'string') return b;
      if (typeof URLSearchParams !== 'undefined' && b instanceof URLSearchParams) {
        return b.toString();
      }
      if (typeof FormData !== 'undefined' && b instanceof FormData) {
        const out = [];
        b.forEach(function (v, k) {
          if (typeof v === 'string') {
            out.push(k + '=' + v);
          } else if (v && typeof v === 'object' && 'name' in v && 'size' in v) {
            out.push(k + '=[File ' + v.name + ', ' + v.size + ' bytes]');
          } else {
            out.push(k + '=' + String(v));
          }
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
      if (typeof Headers !== 'undefined' && h instanceof Headers) {
        h.forEach(function (v, k) { lines.push(k + ': ' + v); });
      } else if (Array.isArray(h)) {
        h.forEach(function (pair) {
          if (Array.isArray(pair) && pair.length >= 2) {
            lines.push(String(pair[0]) + ': ' + String(pair[1]));
          }
        });
      } else if (typeof h === 'object') {
        Object.keys(h).forEach(function (k) {
          lines.push(k + ': ' + String(h[k]));
        });
      } else {
        lines.push(String(h));
      }
      return lines.join('\n');
    } catch (e) {
      return '';
    }
  }

  function rawHeadersToLines(raw) {
    if (!raw) return '';
    const out = [];
    raw.split(/\r?\n/).forEach(function (line) {
      const s = line.trim();
      if (!s) return;
      const idx = s.indexOf(':');
      if (idx === -1) {
        out.push(s);
      } else {
        out.push(s.slice(0, idx).trim() + ': ' + s.slice(idx + 1).trim());
      }
    });
    return out.join('\n');
  }

  function headersSummary(reqHeaders, respHeaders) {
    const parts = [];
    if (reqHeaders) {
      const firstLines = reqHeaders.split('\n').filter(Boolean).slice(0, 2);
      if (firstLines.length) parts.push('Req: ' + firstLines.join('; '));
    }
    if (respHeaders) {
      const firstLines = respHeaders.split('\n').filter(Boolean).slice(0, 2);
      if (firstLines.length) parts.push('Resp: ' + firstLines.join('; '));
    }
    return parts.join(' | ');
  }

  function matchRecord(r, terms) {
    const hay = (
      r.method + ' ' +
      r.url + ' ' +
      (r.params || '') + ' ' +
      (r.body || '') + ' ' +
      (r.reqHeaders || '') + ' ' +
      (r.respHeaders || '') + ' ' +
      (r.status == null ? '' : r.status) + ' ' +
      (r.response || '').slice(0, 5000)
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

  /* ========================== 请求拦截部分 ========================== */

  function addRecord(rec) {
    rec.id = ++seq;
    if (!rec.time) rec.time = Date.now();
    records.push(rec);
    if (records.length > MAX_RECORDS) {
      records.splice(0, records.length - MAX_RECORDS);
    }
    scheduleRender();
  }

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
            bodyStr: '',
            reqHeaders: []
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
        const meta = xhr.__nrpMeta || { method: 'GET', url: '', bodyStr: '', reqHeaders: [] };

        try {
          meta.bodyStr = bodyToString(body);
        } catch (e) {
          meta.bodyStr = '[unreadable body]';
        }

        try {
          xhr.addEventListener('loadend', function () {
            let text = '';
            try {
              const rt = xhr.responseType;
              if (rt === '' || rt === 'text') {
                text = xhr.responseText || '';
              } else if (rt === 'json') {
                text = xhr.response == null ? '' : JSON.stringify(xhr.response);
              } else if (rt === 'document') {
                text = xhr.responseXML
                  ? new XMLSerializer().serializeToString(xhr.responseXML)
                  : '';
              } else {
                text = '[binary response: ' + rt + ']';
              }
            } catch (e) {
              text = '[unreadable response]';
            }

            let respHeaders = '';
            try {
              respHeaders = rawHeadersToLines(xhr.getAllResponseHeaders());
            } catch (e) { /* ignore */ }

            addRecord({
              kind: 'xhr',
              method: meta.method,
              url: absUrl(meta.url),
              params: extractQuery(meta.url),
              body: meta.bodyStr,
              reqHeaders: headersToString(meta.reqHeaders),
              respHeaders: respHeaders,
              status: xhr.status,
              response: text
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
            try {
              reqHeadersStr = headersToString(input.headers);
            } catch (e) { /* ignore */ }
          }

          if (init && init.body != null) {
            bodyPromise = Promise.resolve(bodyToString(init.body));
          } else if (isRequest && input.body != null) {
            try {
              if (typeof input.clone === 'function' && !input.bodyUsed) {
                const cloned = input.clone();
                bodyPromise = cloned.text().then(function (t) {
                  return t;
                }, function () {
                  return '[unreadable body]';
                });
              } else if (typeof input.text === 'function') {
                bodyPromise = input.text().then(function (t) { return t; }, function () {
                  return '[unreadable body]';
                });
              } else {
                bodyPromise = Promise.resolve('[stream body]');
              }
            } catch (e) {
              bodyPromise = Promise.resolve('[unreadable body]');
            }
          } else if (!isRequest && input && typeof input === 'object' && input.body != null) {
            try {
              bodyPromise = Promise.resolve(bodyToString(input.body));
            } catch (e) {
              bodyPromise = Promise.resolve('[unreadable body]');
            }
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
          let respHeadersStr = '';
          try {
            respHeadersStr = headersToString(res.headers);
          } catch (e) { /* ignore */ }

          bodyPromise.then(function (bodyStr) {
            try {
              const clone = res.clone();
              clone.text().then(function (text) {
                addRecord({
                  kind: 'fetch',
                  method: upperMethod,
                  url: finalUrl,
                  params: queryStr,
                  body: bodyStr,
                  reqHeaders: reqHeadersStr,
                  respHeaders: respHeadersStr,
                  status: res.status,
                  response: text,
                  time: reqTime
                });
              }, function () {
                addRecord({
                  kind: 'fetch',
                  method: upperMethod,
                  url: finalUrl,
                  params: queryStr,
                  body: bodyStr,
                  reqHeaders: reqHeadersStr,
                  respHeaders: respHeadersStr,
                  status: res.status,
                  response: '[unreadable response]',
                  time: reqTime
                });
              });
            } catch (e) {
              addRecord({
                kind: 'fetch',
                method: upperMethod,
                url: finalUrl,
                params: queryStr,
                body: bodyStr,
                reqHeaders: reqHeadersStr,
                respHeaders: respHeadersStr,
                status: res.status,
                response: '[unreadable response]',
                time: reqTime
              });
            }
          }).catch(function () {
            try {
              const clone = res.clone();
              clone.text().then(function (text) {
                addRecord({
                  kind: 'fetch',
                  method: upperMethod,
                  url: finalUrl,
                  params: queryStr,
                  body: '',
                  reqHeaders: reqHeadersStr,
                  respHeaders: respHeadersStr,
                  status: res.status,
                  response: text,
                  time: reqTime
                });
              }, function () { /* ignore */ });
            } catch (e) { /* ignore */ }
          });
          return res;
        }, function (err) {
          bodyPromise.then(function (bodyStr) {
            addRecord({
              kind: 'fetch',
              method: upperMethod,
              url: finalUrl,
              params: queryStr,
              body: bodyStr,
              reqHeaders: reqHeadersStr,
              respHeaders: '',
              status: 0,
              response: '[network error] ' + (err && err.message ? err.message : ''),
              time: reqTime
            });
          }).catch(function () {
            addRecord({
              kind: 'fetch',
              method: upperMethod,
              url: finalUrl,
              params: queryStr,
              body: '',
              reqHeaders: reqHeadersStr,
              respHeaders: '',
              status: 0,
              response: '[network error] ' + (err && err.message ? err.message : ''),
              time: reqTime
            });
          });
          throw err;
        });
      };

      patched.__nrpPatched = true;
      window.fetch = patched;
    }
  }

  /* ============================ UI 构建 ============================ */

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
  width: 1100px;
  max-width: calc(100vw - 32px);
  background: #0d1117;
  border: 1px solid #30363d;
  border-radius: 8px;
  box-shadow: 0 10px 40px rgba(0,0,0,.65);
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

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

#nrp-root .nrp-body {
  display: flex; flex-direction: column;
  height: 380px; max-height: 62vh;
}
#nrp-root .nrp-panel.nrp-collapsed .nrp-body { display: none; }

#nrp-root .nrp-toolbar {
  display: flex; align-items: center; gap: 8px;
  padding: 6px 8px; border-bottom: 1px solid #21262d;
  background: #0d1117;
}
#nrp-root .nrp-search {
  flex: 1 1 auto; min-width: 0;
  background: #010409; border: 1px solid #30363d; color: #e6edf3;
  border-radius: 5px; padding: 4px 8px;
  font-family: inherit; font-size: 12px; outline: none;
}
#nrp-root .nrp-search:focus {
  border-color: #1f6feb;
  box-shadow: 0 0 0 2px rgba(31,111,235,.25);
}
#nrp-root .nrp-search::placeholder { color: #6e7681; }
#nrp-root .nrp-stats { color: #8b949e; font-size: 11px; white-space: nowrap; }

#nrp-root .nrp-table-wrap { flex: 1 1 auto; overflow: auto; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar { width: 10px; height: 10px; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-track { background: #0d1117; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-thumb { background: #30363d; border-radius: 5px; }
#nrp-root .nrp-table-wrap::-webkit-scrollbar-thumb:hover { background: #484f58; }

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
#nrp-root tbody tr:nth-child(even) { background: #10161d; }
#nrp-root tbody tr:hover { background: #1c2733; }

#nrp-root .nrp-cell-method { color: #79c0ff; font-weight: 600; }
#nrp-root .nrp-cell-time { color: #8b949e; }
#nrp-root .nrp-dim { color: #8b949e; }
#nrp-root .nrp-cell-query { color: #d29922; }
#nrp-root .nrp-cell-body { color: #a5d6ff; }
#nrp-root .nrp-cell-headers { color: #d2a8ff; }
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
  flex-shrink: 0;                       /* 头部不收缩 */
}
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

#nrp-root .nrp-modal-url {
  color: #c9d1d9; font-size: 12px; line-height: 1.5;
  word-break: break-all; min-width: 0;
}
#nrp-root .nrp-modal-tools { display: flex; gap: 6px; flex-shrink: 0; }

/* Params/Body 区块：不收缩，允许内部滚动 */
#nrp-root .nrp-modal-params {
  padding: 6px 12px; font-size: 12px; color: #8b949e;
  border-bottom: 1px solid #21262d; background: #0d1117;
  word-break: break-all; white-space: pre-wrap;
  max-height: 180px; overflow: auto;
  flex-shrink: 0;
}
#nrp-root .nrp-modal-params .nrp-k { color: #6e7681; font-weight: 700; }
#nrp-root .nrp-modal-params .nrp-v { color: #d29922; }
#nrp-root .nrp-modal-params .nrp-v-body { color: #a5d6ff; }

/* Headers 区块：不收缩 */
#nrp-root .nrp-headers {
  flex-shrink: 0;
}
#nrp-root .nrp-headers-section {
  border-bottom: 1px solid #21262d;
  background: #0d1117;
}
#nrp-root .nrp-headers-title {
  display: flex; align-items: center; gap: 6px;
  padding: 6px 12px; cursor: pointer;
  color: #8b949e; font-size: 11px; font-weight: 700;
  user-select: none;
}
#nrp-root .nrp-headers-title:hover { color: #c9d1d9; }
#nrp-root .nrp-headers-title .nrp-caret {
  display: inline-block; width: 10px; text-align: center;
  transition: transform .12s;
}
#nrp-root .nrp-headers-title.nrp-collapsed .nrp-caret { transform: rotate(-90deg); }
#nrp-root .nrp-headers-content {
  padding: 0 12px 8px 12px;
  font-size: 12px; color: #a5d6ff;
  white-space: pre-wrap; word-break: break-all;
  max-height: 120px; overflow: auto;
}
#nrp-root .nrp-headers-title.nrp-collapsed + .nrp-headers-content { display: none; }

/* 响应体：占据剩余空间，可滚动 */
#nrp-root .nrp-modal-body {
  margin: 0; padding: 12px;
  flex: 1 1 auto; overflow: auto;
  min-height: 60px;
  font-family: inherit; font-size: 12px; line-height: 1.6;
  color: #c9d1d9; background: #010409;
  white-space: pre-wrap; word-break: break-word;
}
`;

  function buildUI() {
    if (rootEl) return;

    const styleEl = document.createElement('style');
    styleEl.id = 'nrp-style';
    styleEl.textContent = CSS;
    (document.head || document.documentElement).appendChild(styleEl);

    const collapseBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Minimize / Maximize' }, '—');
    const clearBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Clear all records' }, 'Clear');
    const exportBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Export filtered records as JSON' }, 'Export');
    const hideBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Hide panel' }, '×');

    searchEl = h('input', {
      class: 'nrp-search',
      type: 'text',
      placeholder: 'Search url / method / params / body / headers / status / response …',
      spellcheck: 'false'
    });
    statsEl = h('span', { class: 'nrp-stats' }, '0 / 0');

    tbodyEl = h('tbody');

    const table = h('table', null, [
      h('colgroup', null, [
        h('col', { style: 'width:9%' }),
        h('col', { style: 'width:6%' }),
        h('col', { style: 'width:5%' }),
        h('col', { style: 'width:18%' }),
        h('col', { style: 'width:13%' }),
        h('col', { style: 'width:13%' }),
        h('col', { style: 'width:18%' }),
        h('col', { style: 'width:18%' })
      ]),
      h('thead', null, h('tr', null, [
        h('th', null, 'Time'),
        h('th', null, 'Method'),
        h('th', null, 'Status'),
        h('th', null, 'URL'),
        h('th', null, 'Params'),
        h('th', null, 'Body'),
        h('th', null, 'Headers'),
        h('th', null, 'Response')
      ])),
      tbodyEl
    ]);

    const header = h('div', { class: 'nrp-header' }, [
      h('div', { class: 'nrp-title' }, [h('span', { class: 'nrp-dot' }), 'Network Debugger']),
      h('div', { class: 'nrp-actions' }, [collapseBtn, clearBtn, exportBtn, hideBtn])
    ]);

    const body = h('div', { class: 'nrp-body' }, [
      h('div', { class: 'nrp-toolbar' }, [searchEl, statsEl]),
      h('div', { class: 'nrp-table-wrap' }, table)
    ]);

    panelEl = h('div', { class: 'nrp-panel' }, [header, body]);

    const fab = h('button', { class: 'nrp-fab', type: 'button', title: 'Show Network Debugger' }, 'NET');

    const modalCloseBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Close' }, '×');
    copyBtn = h('button', { class: 'nrp-btn', type: 'button', title: 'Copy' }, 'Copy');
    modalHeadlineEl = h('div', { class: 'nrp-headline' });
    modalParamsEl = h('div', { class: 'nrp-modal-params' });
    modalHeadersEl = h('div', { class: 'nrp-headers' });
    modalBodyEl = h('pre', { class: 'nrp-modal-body' });

    const modal = h('div', { class: 'nrp-modal' }, [
      h('div', { class: 'nrp-modal-head' }, [
        modalHeadlineEl,
        h('div', { class: 'nrp-modal-tools' }, [copyBtn, modalCloseBtn])
      ]),
      modalParamsEl,
      modalHeadersEl,
      modalBodyEl
    ]);

    overlayEl = h('div', { class: 'nrp-overlay' }, modal);

    rootEl = h('div', { id: 'nrp-root' }, [panelEl, fab, overlayEl]);
    (document.documentElement || document.body).appendChild(rootEl);

    collapseBtn.addEventListener('click', function () {
      const collapsed = panelEl.classList.toggle('nrp-collapsed');
      collapseBtn.textContent = collapsed ? '□' : '—';
      collapseBtn.title = collapsed ? 'Maximize' : 'Minimize';
    });

    clearBtn.addEventListener('click', function () {
      records = [];
      render();
    });

    exportBtn.addEventListener('click', exportJSON);

    hideBtn.addEventListener('click', function () {
      panelEl.style.display = 'none';
      fab.style.display = 'flex';
    });
    fab.addEventListener('click', function () {
      panelEl.style.display = '';
      fab.style.display = 'none';
    });

    searchEl.addEventListener('input', scheduleRender);

    modalCloseBtn.addEventListener('click', closeModal);
    overlayEl.addEventListener('click', function (e) {
      if (e.target === overlayEl) closeModal();
    });
    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape' && overlayEl.classList.contains('nrp-open')) closeModal();
    });

    copyBtn.addEventListener('click', function () {
      copyText(currentCopyText).then(function () {
        copyBtn.textContent = 'Copied!';
        setTimeout(function () { copyBtn.textContent = 'Copy'; }, 1500);
      }, function () {
        copyBtn.textContent = 'Failed';
        setTimeout(function () { copyBtn.textContent = 'Copy'; }, 1500);
      });
    });

    render();
  }

  /* ============================ 渲染逻辑 ============================ */

  function scheduleRender() {
    if (renderTimer) return;
    renderTimer = setTimeout(function () {
      renderTimer = null;
      render();
    }, RENDER_DELAY);
  }

  function getFiltered() {
    const raw = searchEl && searchEl.value ? searchEl.value : '';
    const q = raw.trim().toLowerCase();
    const terms = q ? q.split(/\s+/).filter(Boolean) : [];
    if (!terms.length) return records.slice();
    return records.filter(function (r) { return matchRecord(r, terms); });
  }

  function cell(text, cls, title) {
    const td = document.createElement('td');
    td.textContent = text;
    if (cls) td.className = cls;
    if (title) td.title = title;
    return td;
  }

  function statusClass(status) {
    if (status >= 200 && status < 300) return 'nrp-st-ok';
    if (status === 0 || status >= 400) return 'nrp-st-err';
    return 'nrp-st-other';
  }

  function buildRow(r) {
    const tr = document.createElement('tr');

    tr.appendChild(cell(formatTime(r.time), 'nrp-cell-time', formatFullTime(r.time)));
    tr.appendChild(cell(r.method, 'nrp-cell-method', r.method));

    const stText = r.status ? String(r.status) : 'ERR';
    tr.appendChild(cell(stText, statusClass(r.status), 'Status: ' + stText));

    const urlTd = cell(r.url, 'nrp-cell-clickable', r.url);
    urlTd.addEventListener('click', function (e) {
      e.stopPropagation();
      openFieldModal(r, 'url');
    });
    tr.appendChild(urlTd);

    const params = r.params || '';
    const paramsTd = cell(params, 'nrp-cell-clickable nrp-cell-query', params);
    paramsTd.addEventListener('click', function (e) {
      e.stopPropagation();
      openFieldModal(r, 'params');
    });
    tr.appendChild(paramsTd);

    const bodyStr = r.body || '';
    const bodyTd = cell(bodyStr, 'nrp-cell-clickable nrp-cell-body', bodyStr);
    bodyTd.addEventListener('click', function (e) {
      e.stopPropagation();
      openFieldModal(r, 'body');
    });
    tr.appendChild(bodyTd);

    const headersSum = headersSummary(r.reqHeaders, r.respHeaders);
    const headersTd = cell(headersSum, 'nrp-cell-clickable nrp-cell-headers', headersSum);
    headersTd.addEventListener('click', function (e) {
      e.stopPropagation();
      openFieldModal(r, 'headers');
    });
    tr.appendChild(headersTd);

    const preview = (r.response || '').replace(/\s+/g, ' ').slice(0, 400);
    const respTd = cell(preview, 'nrp-cell-clickable nrp-dim', preview.slice(0, 2000));
    respTd.addEventListener('click', function (e) {
      e.stopPropagation();
      openFieldModal(r, 'response');
    });
    tr.appendChild(respTd);

    tr.addEventListener('click', function () { openModal(r); });
    return tr;
  }

  function render() {
    if (!tbodyEl) return;

    const filtered = getFiltered();

    if (statsEl) statsEl.textContent = filtered.length + ' / ' + records.length;

    const frag = document.createDocumentFragment();
    for (let i = filtered.length - 1; i >= 0; i--) {
      frag.appendChild(buildRow(filtered[i]));
    }

    if (!filtered.length) {
      const tr = document.createElement('tr');
      tr.className = 'nrp-empty-row';
      const td = document.createElement('td');
      td.className = 'nrp-empty';
      td.colSpan = 8;
      td.textContent = records.length
        ? 'No records match the current filter.'
        : 'Waiting for network requests…';
      tr.appendChild(td);
      frag.appendChild(tr);
    }

    while (tbodyEl.firstChild) tbodyEl.removeChild(tbodyEl.firstChild);
    tbodyEl.appendChild(frag);
  }

  /* ============================ 弹窗逻辑 ============================ */

  function buildHeadline(r, extraLabel) {
    while (modalHeadlineEl.firstChild) {
      modalHeadlineEl.removeChild(modalHeadlineEl.firstChild);
    }
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-method' }, r.method));

    const stText = r.status ? String(r.status) : 'ERR';
    let stCls = 'nrp-badge-other';
    if (r.status >= 200 && r.status < 300) stCls = 'nrp-badge-ok';
    else if (r.status === 0 || r.status >= 400) stCls = 'nrp-badge-err';
    modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge ' + stCls }, stText));

    modalHeadlineEl.appendChild(
      h('span', { class: 'nrp-badge nrp-badge-time', title: formatFullTime(r.time) }, formatTime(r.time))
    );

    if (extraLabel) {
      modalHeadlineEl.appendChild(h('span', { class: 'nrp-badge nrp-badge-other' }, extraLabel));
    }

    modalHeadlineEl.appendChild(h('span', { class: 'nrp-modal-url', title: r.url }, r.url));
  }

  function fillParamsBlock(r) {
    while (modalParamsEl.firstChild) {
      modalParamsEl.removeChild(modalParamsEl.firstChild);
    }

    const hasQuery = !!r.params;
    const hasBody = !!r.body;

    if (!hasQuery && !hasBody) {
      modalParamsEl.style.display = 'none';
      return;
    }

    modalParamsEl.style.display = '';
    if (hasQuery) {
      modalParamsEl.appendChild(h('span', { class: 'nrp-k' }, 'Params: '));
      modalParamsEl.appendChild(h('span', { class: 'nrp-v' }, r.params));
    }
    if (hasQuery && hasBody) {
      modalParamsEl.appendChild(document.createTextNode('\n'));
    }
    if (hasBody) {
      modalParamsEl.appendChild(h('span', { class: 'nrp-k' }, 'Body: '));
      modalParamsEl.appendChild(h('span', { class: 'nrp-v-body' }, r.body));
    }
  }

  function makeHeadersSection(title, content) {
    if (!content) return null;

    const titleEl = h('div', { class: 'nrp-headers-title' }, [
      h('span', { class: 'nrp-caret' }, '▾'),
      title + ' (' + content.split('\n').filter(Boolean).length + ')'
    ]);
    const contentEl = h('div', { class: 'nrp-headers-content' }, content);

    titleEl.addEventListener('click', function () {
      titleEl.classList.toggle('nrp-collapsed');
    });

    return h('div', { class: 'nrp-headers-section' }, [titleEl, contentEl]);
  }

  function fillHeadersBlock(r) {
    while (modalHeadersEl.firstChild) {
      modalHeadersEl.removeChild(modalHeadersEl.firstChild);
    }

    const reqSec = makeHeadersSection('Request Headers', r.reqHeaders);
    if (reqSec) modalHeadersEl.appendChild(reqSec);

    const respSec = makeHeadersSection('Response Headers', r.respHeaders);
    if (respSec) modalHeadersEl.appendChild(respSec);

    if (!reqSec && !respSec) {
      modalHeadersEl.style.display = 'none';
    } else {
      modalHeadersEl.style.display = '';
    }
  }

  function openModal(r) {
    const raw = r.response == null ? '' : String(r.response);
    const trimmed = raw.trim();

    let formatted;
    if (!trimmed) {
      formatted = '(empty response)';
    } else {
      formatted = raw;
      try {
        formatted = JSON.stringify(JSON.parse(trimmed), null, 2);
      } catch (e) { /* 非 JSON，原样展示 */ }
    }

    currentCopyText = formatted;

    buildHeadline(r, null);
    fillParamsBlock(r);
    fillHeadersBlock(r);

    modalBodyEl.textContent = formatted;

    copyBtn.textContent = 'Copy';
    overlayEl.classList.add('nrp-open');
  }

  function openFieldModal(r, field) {
    let titleText = '';
    let contentText = '';

    if (field === 'url') {
      titleText = 'URL';
      contentText = r.url || '(empty url)';
    } else if (field === 'params') {
      titleText = 'Params';
      contentText = r.params || '(no params)';
    } else if (field === 'body') {
      titleText = 'Body';
      contentText = r.body || '(no body)';
    } else if (field === 'headers') {
      titleText = 'Headers';
      const parts = [];
      if (r.reqHeaders) parts.push('[Request Headers]\n' + r.reqHeaders);
      if (r.respHeaders) parts.push('[Response Headers]\n' + r.respHeaders);
      contentText = parts.length ? parts.join('\n\n') : '(no headers)';
    } else if (field === 'reqHeaders') {
      titleText = 'Request Headers';
      contentText = r.reqHeaders || '(no request headers)';
    } else if (field === 'respHeaders') {
      titleText = 'Response Headers';
      contentText = r.respHeaders || '(no response headers)';
    } else {
      titleText = 'Response';
      const raw = r.response == null ? '' : String(r.response);
      const trimmed = raw.trim();
      if (!trimmed) {
        contentText = '(empty response)';
      } else {
        contentText = raw;
        try {
          contentText = JSON.stringify(JSON.parse(trimmed), null, 2);
        } catch (e) { /* 非 JSON，原样展示 */ }
      }
    }

    currentCopyText = contentText;

    buildHeadline(r, titleText);

    modalParamsEl.style.display = 'none';
    while (modalParamsEl.firstChild) modalParamsEl.removeChild(modalParamsEl.firstChild);

    while (modalHeadersEl.firstChild) modalHeadersEl.removeChild(modalHeadersEl.firstChild);
    modalHeadersEl.style.display = 'none';

    modalBodyEl.textContent = contentText;

    copyBtn.textContent = 'Copy';
    overlayEl.classList.add('nrp-open');
  }

  function closeModal() {
    if (overlayEl) overlayEl.classList.remove('nrp-open');
  }

  /* ============================ 复制 / 导出 ============================ */

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

  function exportJSON() {
    const data = getFiltered().map(function (r) {
      return {
        id: r.id,
        type: r.kind,
        method: r.method,
        url: r.url,
        params: r.params,
        body: r.body,
        reqHeaders: r.reqHeaders,
        respHeaders: r.respHeaders,
        status: r.status,
        response: r.response,
        time: formatFullTime(r.time)
      };
    });

    const json = JSON.stringify(data, null, 2);
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);

    const a = document.createElement('a');
    a.href = url;
    a.download = 'network-records-' +
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

  function bootstrap() {
    if (!document.documentElement) {
      setTimeout(bootstrap, 10);
      return;
    }
    buildUI();
  }

  bootstrap();
})();
