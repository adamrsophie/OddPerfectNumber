// Sky map of the library (cluster view of the map component). Plain canvas 2D; data from assets/map-data.js.
(function () {
  "use strict";
  var root = document.getElementById("sky");
  if (!root) return;
  var D = window.OPN_MAP;
  if (!D) return;
  function nm(n) { return n.replace(/^OddPerfect\./, ""); }
  var cv = document.getElementById("sky-canvas"), ctx = cv.getContext("2d");
  var mini = document.getElementById("sky-mini"), mctx = mini.getContext("2d");
  var tip = document.getElementById("sky-tip");
  var panel = document.getElementById("sky-panel"), body = document.getElementById("sky-panel-body");
  var box = document.getElementById("sky-q"), results = document.getElementById("sky-results");
  var css = getComputedStyle(document.documentElement);
  var SANS = css.getPropertyValue("--sans") || "sans-serif", MONO = css.getPropertyValue("--mono") || "monospace";
  var reduce = window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches;

  // dots
  var N = D.t.length, X = new Float32Array(N), Y = new Float32Array(N), DM = new Int32Array(N);
  var DG = new Int32Array(N), ring = new Uint8Array(N), hit = new Uint8Array(N);
  for (var i = 0; i < N; i++) { X[i] = D.p[2 * i] / 10; Y[i] = D.p[2 * i + 1] / 10; }
  D.m.forEach(function (m, k) { for (var j = m[6]; j < m[6] + m[7]; j++) { DM[j] = k; DG[j] = m[1]; } });
  D.ring.forEach(function (j) { ring[j] = 1; });

  // world bounds (discs, label plates, targets)
  var bx0 = Infinity, by0 = Infinity, bx1 = -Infinity, by1 = -Infinity;
  D.g.forEach(function (g) {
    bx0 = Math.min(bx0, g[4] - g[6]); bx1 = Math.max(bx1, g[4] + g[6]);
    by0 = Math.min(by0, g[5] - g[6]); by1 = Math.max(by1, g[5] + g[6] + 66 / D.s0);
  });
  D.o.forEach(function (t) {
    bx0 = Math.min(bx0, t[3] - (24 + t[0].length * 6.6) / D.s0); bx1 = Math.max(bx1, t[3] + (24 + t[0].length * 6.6) / D.s0);
    by0 = Math.min(by0, t[4] - 6); by1 = Math.max(by1, t[4] + 8);
  });

  // spatial grid for hit testing
  var CELL = 3, grid = new Map();
  function cellKey(cx, cy) { return cx * 100003 + cy; }
  for (i = 0; i < N; i++) {
    var k = cellKey(Math.floor(X[i] / CELL), Math.floor(Y[i] / CELL));
    if (!grid.has(k)) grid.set(k, []);
    grid.get(k).push(i);
  }

  var W = 0, H = 0, dpr = 1, view = { x: 0, y: 0, s: 1 }, sMin = 0.2, sMax = 60;
  var hover = -1, selMod = -1, selDot = -1, selGroup = -1, query = "", plates = [];

  function sx(x) { return (x - view.x) * view.s + W / 2; }
  function sy(y) { return (y - view.y) * view.s + H / 2; }
  function wx(px) { return (px - W / 2) / view.s + view.x; }
  function wy(py) { return (py - H / 2) / view.s + view.y; }

  function insets() {
    var head = root.querySelector(".sky-top"), foot = root.querySelector(".sky-legend");
    return { top: head.offsetHeight + 8, bottom: foot.offsetHeight + 16 };
  }
  function fitView() {
    var ins = insets(), h = Math.max(H - ins.top - ins.bottom, 120);
    var s = Math.min((W - 32) / (bx1 - bx0), h / (by1 - by0));
    sMin = s * 0.6;
    return { x: (bx0 + bx1) / 2, y: (by0 + by1) / 2 - (ins.top - ins.bottom) / 2 / s, s: s };
  }

  var frame = 0;
  function draw() { if (!frame) frame = requestAnimationFrame(paint); }

  function paint() {
    frame = 0;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = "#0b0c0f";
    ctx.fillRect(0, 0, W, H);
    var s = view.s;
    // links between groups, rim to rim
    ctx.strokeStyle = "rgba(170,174,184,0.22)";
    ctx.lineWidth = 1;
    ctx.setLineDash([]);
    ctx.beginPath();
    D.links.forEach(function (e) {
      var a = D.g[e[0]], b = D.g[e[1]], dx = b[4] - a[4], dy = b[5] - a[5], d = Math.hypot(dx, dy);
      if (d <= a[6] + b[6]) return;
      ctx.moveTo(sx(a[4] + dx / d * a[6]), sy(a[5] + dy / d * a[6]));
      ctx.lineTo(sx(b[4] - dx / d * b[6]), sy(b[5] - dy / d * b[6]));
    });
    ctx.stroke();
    // group bounds
    ctx.setLineDash([3, 5]);
    D.g.forEach(function (g) {
      ctx.strokeStyle = g[3] + "59";
      ctx.beginPath(); ctx.arc(sx(g[4]), sy(g[5]), g[6] * s, 0, 7); ctx.stroke();
    });
    // research targets and their dashed tethers
    D.o.forEach(function (t) {
      var g = D.g[t[2]], dx = t[3] - g[4], dy = t[4] - g[5], d = Math.hypot(dx, dy);
      var tr = Math.max(7, 2.2 * s);
      ctx.strokeStyle = "rgba(200,204,212,0.45)";
      ctx.setLineDash([2, 4]);
      ctx.beginPath();
      ctx.moveTo(sx(g[4] + dx / d * g[6]), sy(g[5] + dy / d * g[6]));
      ctx.lineTo(sx(t[3]) - dx / d * tr, sy(t[4]) - dy / d * tr);
      ctx.stroke();
      ctx.strokeStyle = "#e9e6df";
      ctx.setLineDash([3, 3]);
      ctx.beginPath(); ctx.arc(sx(t[3]), sy(t[4]), tr, 0, 7); ctx.stroke();
      ctx.setLineDash([]);
      ctx.fillStyle = "#b9b5ac";
      ctx.font = "11.5px " + SANS;
      ctx.textAlign = dx < 0 ? "right" : "left";
      ctx.textBaseline = "middle";
      if (W >= 600) ctx.fillText(t[0], sx(t[3]) + (dx < 0 ? -1 : 1) * (tr + 6), sy(t[4]));
    });
    ctx.setLineDash([]);
    // module bounds and names once they are large enough
    var showMods = s > 2.6;
    if (showMods) {
      ctx.lineWidth = 1;
      ctx.font = "11px " + MONO;
      ctx.textAlign = "center";
      ctx.textBaseline = "bottom";
      D.m.forEach(function (m, k) {
        var r = m[5] * s, x = sx(m[3]), y = sy(m[4]);
        if (x + r < 0 || x - r > W || y + r < 0 || y - r > H) return;
        ctx.strokeStyle = k === selMod ? D.g[m[1]][3] : "rgba(233,230,223,0.13)";
        ctx.lineWidth = k === selMod ? 2 : 1;
        ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.stroke();
        if (r > 34) {
          var name = m[0].split(".").pop();
          if (ctx.measureText(name).width < 1.7 * r) {
            ctx.fillStyle = "rgba(233,230,223,0.72)";
            ctx.fillText(name, x, y - r - 2);
          }
        }
      });
    }
    // dots
    var dr = Math.max(0.75, Math.min(s * 0.36, 7));
    var dim = query !== "";
    for (var g = 0; g < D.g.length; g++) {
      ctx.fillStyle = D.g[g][3];
      for (var pass = 0; pass < (dim ? 2 : 1); pass++) {
        // without a query one pass draws every dot; with a query, misses first and faint, then hits
        ctx.globalAlpha = dim ? (pass === 0 ? 0.13 : 1) : 0.88;
        ctx.beginPath();
        for (var j = 0; j < N; j++) {
          if (DG[j] !== g || (dim && hit[j] !== pass)) continue;
          var x = sx(X[j]), y = sy(Y[j]);
          if (x < -8 || x > W + 8 || y < -8 || y > H + 8) continue;
          if (dr < 1.6) { ctx.rect(x - dr, y - dr, 2 * dr, 2 * dr); }
          else { ctx.moveTo(x + dr, y); ctx.arc(x, y, dr, 0, 7); }
        }
        ctx.fill();
      }
    }
    ctx.globalAlpha = 1;
    // rings: theorems restated by the statement gate
    ctx.strokeStyle = "#ffffff";
    ctx.lineWidth = Math.max(0.9, Math.min(dr * 0.35, 1.6));
    ctx.beginPath();
    D.ring.forEach(function (j) {
      if (dim && !hit[j]) return;
      var x = sx(X[j]), y = sy(Y[j]), rr = dr + 1.8;
      ctx.moveTo(x + rr, y); ctx.arc(x, y, rr, 0, 7);
    });
    ctx.stroke();
    [hover, selDot].forEach(function (j) {
      if (j < 0) return;
      ctx.strokeStyle = "#ffffff"; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(sx(X[j]), sy(Y[j]), dr + 4, 0, 7); ctx.stroke();
    });
    // label plates under each group; plates are drawn largest group first, a plate that would
    // cover one already drawn is left out until the view is large enough
    plates = [];
    var fs = Math.max(0.8, Math.min(1.25, s / D.s0));  // plates follow the zoom a little, as the layout assumes
    ctx.textBaseline = "alphabetic";
    D.g.map(function (g, k) { return k; }).sort(function (a, b) { return D.g[b][7] - D.g[a][7]; }).forEach(function (k) {
      var g = D.g[k], x = sx(g[4]), top = sy(g[5]) + g[6] * s + 8 * fs;
      var count = g[7].toLocaleString("en-US") + " theorems · " + g[8] + " modules · " + g[9] + " in gate";
      ctx.font = 10.5 * fs + "px " + MONO;
      var cw = ctx.measureText(count).width, limit = Math.max(cw, 200 * fs);
      ctx.font = "600 " + 12 * fs + "px " + SANS;
      var lines = [], cur = "";
      g[1].toUpperCase().split(" ").forEach(function (w) {
        var next = cur ? cur + " " + w : w;
        if (cur && spaced(next, 0, 0, false) > limit) { lines.push(cur); cur = w; } else cur = next;
      });
      lines.push(cur);
      var tw = Math.max.apply(null, lines.map(function (l) { return spaced(l, 0, 0, false); }));
      var w = Math.max(tw, cw) + 24 * fs, h = (16 * lines.length + 30) * fs;
      x = Math.min(Math.max(x, w / 2 + 4), W - w / 2 - 4);  // keep the plate inside the canvas
      var box = [x - w / 2, top, w, h, k], hitp = function (p) { return box[0] < p[0] + p[2] && p[0] < box[0] + w && box[1] < p[1] + p[3] && p[1] < box[1] + h; };
      for (var tries = 0, o; tries < 3 && (o = plates.filter(hitp)[0]); tries++) box[1] = o[1] + o[3] + 3;  // slide below a plate in the way
      if (plates.some(hitp)) return;
      top = box[1];
      ctx.fillStyle = "rgba(11,12,15,0.84)";
      ctx.fillRect(box[0], top, w, h);
      if (k === selGroup) { ctx.strokeStyle = g[3]; ctx.lineWidth = 1; ctx.strokeRect(box[0] + 0.5, top + 0.5, w - 1, h - 1); }
      ctx.fillStyle = g[3];
      lines.forEach(function (l, n) { spaced(l, x - spaced(l, 0, 0, false) / 2, top + (20 + 16 * n) * fs, true); });
      ctx.fillStyle = "#aeaaa1";
      ctx.font = 10.5 * fs + "px " + MONO;
      ctx.textAlign = "center";
      ctx.fillText(count, x, top + (16 * lines.length + 20) * fs);
      plates.push(box);
    });
    paintMini();
  }

  // small capitals with letter spacing, drawn one character at a time; returns the width
  function spaced(text, x, y, paint) {
    var w = 0, gap = 1.6 * parseFloat(ctx.font.replace(/^\d+ /, "")) / 12;
    for (var c = 0; c < text.length; c++) {
      var cw = ctx.measureText(text[c]).width;
      if (paint) { ctx.textAlign = "left"; ctx.fillText(text[c], x + w, y); }
      w += cw + gap;
    }
    ctx.textAlign = "center";
    return w - gap;
  }

  function paintMini() {
    var mw = mini.clientWidth, mh = mini.clientHeight, md = window.devicePixelRatio || 1;
    if (mini.width !== Math.round(mw * md)) { mini.width = Math.round(mw * md); mini.height = Math.round(mh * md); }
    mctx.setTransform(md, 0, 0, md, 0, 0);
    mctx.fillStyle = "#14161b";
    mctx.fillRect(0, 0, mw, mh);
    var ms = Math.min((mw - 8) / (bx1 - bx0), (mh - 8) / (by1 - by0));
    var ox = mw / 2 - (bx0 + bx1) / 2 * ms, oy = mh / 2 - (by0 + by1) / 2 * ms;
    mini._map = [ms, ox, oy];
    D.g.forEach(function (g) {
      mctx.fillStyle = g[3] + "99";
      mctx.beginPath(); mctx.arc(ox + g[4] * ms, oy + g[5] * ms, Math.max(g[6] * ms, 1.5), 0, 7); mctx.fill();
    });
    mctx.strokeStyle = "#ffffff";
    mctx.lineWidth = 1;
    var x0 = ox + wx(0) * ms, y0 = oy + wy(0) * ms, x1 = ox + wx(W) * ms, y1 = oy + wy(H) * ms;
    mctx.strokeRect(Math.max(x0, 0.5), Math.max(y0, 0.5), Math.min(x1, mw - 0.5) - Math.max(x0, 0.5), Math.min(y1, mh - 0.5) - Math.max(y0, 0.5));
  }

  // hit testing
  function dotAt(px, py) {
    var x = wx(px), y = wy(py), r = Math.max(7 / view.s, 0.7), best = -1, bd = r * r;
    var c0 = Math.floor((x - r) / CELL), c1 = Math.floor((x + r) / CELL), d0 = Math.floor((y - r) / CELL), d1 = Math.floor((y + r) / CELL);
    for (var a = c0; a <= c1; a++) for (var b = d0; b <= d1; b++) {
      var list = grid.get(cellKey(a, b));
      if (!list) continue;
      for (var q = 0; q < list.length; q++) {
        var j = list[q], dd = (X[j] - x) * (X[j] - x) + (Y[j] - y) * (Y[j] - y);
        if (dd < bd) { bd = dd; best = j; }
      }
    }
    return best;
  }
  function moduleAt(px, py) {
    var x = wx(px), y = wy(py), best = -1, br = Infinity;
    D.m.forEach(function (m, k) {
      if (m[5] < br && Math.hypot(m[3] - x, m[4] - y) <= m[5]) { best = k; br = m[5]; }
    });
    return best;
  }
  function plateAt(px, py) {
    for (var q = 0; q < plates.length; q++) {
      var p = plates[q];
      if (px >= p[0] && px <= p[0] + p[2] && py >= p[1] && py <= p[1] + p[3]) return p[4];
    }
    return -1;
  }
  function targetAt(px, py) {
    for (var q = 0; q < D.o.length; q++) {
      if (Math.hypot(sx(D.o[q][3]) - px, sy(D.o[q][4]) - py) < Math.max(12, 2.2 * view.s + 4)) return q;
    }
    return -1;
  }

  // view changes
  var anim = 0;
  function go(to, now) {
    cancelAnimationFrame(anim);
    to.s = Math.max(sMin, Math.min(sMax, to.s));
    if (reduce || now) { view = to; draw(); return; }
    var from = { x: view.x, y: view.y, s: view.s }, t0 = performance.now();
    function step(t) {
      var u = Math.min(1, (t - t0) / 320), e = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2;
      var ls = Math.log(from.s) + (Math.log(to.s) - Math.log(from.s)) * e;
      view = { x: from.x + (to.x - from.x) * e, y: from.y + (to.y - from.y) * e, s: Math.exp(ls) };
      paint();
      if (u < 1) anim = requestAnimationFrame(step);
    }
    anim = requestAnimationFrame(step);
  }
  function zoomAt(f, px, py, now) {
    var x = wx(px), y = wy(py), s = Math.max(sMin, Math.min(sMax, view.s * f));
    go({ x: x - (px - W / 2) / s, y: y - (py - H / 2) / s, s: s }, now);
  }
  function focusCircle(x, y, r) {
    var wide = W >= 720, open = !panel.hidden;
    var w = W - (wide && open ? 360 : 0), h = H * (!wide && open ? 0.5 : 1);
    var s = Math.min(w, h) / (2.6 * r);
    go({ x: x + (wide && open ? 180 : 0) / s, y: y + (!wide && open ? H * 0.25 : 0) / s, s: s });
  }

  // panel
  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function open() { panel.hidden = false; root.classList.add("panel-open"); }
  function close() {
    panel.hidden = true; root.classList.remove("panel-open");
    selMod = selDot = selGroup = -1; draw();
  }
  function kicker(g) {
    var p = el("p", "sky-kicker", g[1]);
    p.style.color = g[3];
    return p;
  }
  function showModule(k, dot) {
    var m = D.m[k], g = D.g[m[1]];
    selMod = k; selDot = dot; selGroup = -1;
    body.innerHTML = "";
    body.appendChild(kicker(g));
    var h = el("h2"); h.appendChild(el("code", null, m[0])); body.appendChild(h);
    body.appendChild(el("p", "sky-meta", D.l[m[2]][0] + " · " + m[7] + (m[7] === 1 ? " public theorem" : " public theorems")));
    if (D.s[k]) { var p = el("p", "sky-sum"); p.innerHTML = D.s[k]; body.appendChild(p); }
    var a = el("a", "sky-ref", "Open in the Reference");
    a.href = "reference.html#" + m[8];
    body.appendChild(a);
    if (m[7]) {
      body.appendChild(el("h3", null, "Public theorems"));
      var ul = el("ul", "sky-thms");
      for (var j = m[6]; j < m[6] + m[7]; j++) {
        var li = el("li"), link = el("a");
        link.href = "reference.html#" + encodeURIComponent(D.t[j]);
        link.appendChild(el("code", null, nm(D.t[j])));
        li.appendChild(link);
        if (ring[j]) li.appendChild(el("span", "sky-tag", "restated by the statement gate"));
        if (j === dot) { li.className = "cur"; li.setAttribute("aria-current", "true"); }
        ul.appendChild(li);
      }
      body.appendChild(ul);
    }
    open(); draw();
    var cur = body.querySelector(".cur");
    if (cur) cur.scrollIntoView({ block: "nearest" });
  }
  function showGroup(k, lineIdx) {
    var g = D.g[k];
    selGroup = k; selMod = selDot = -1;
    body.innerHTML = "";
    body.appendChild(kicker(g));
    body.appendChild(el("h2", null, g[1]));
    body.appendChild(el("p", "sky-meta", g[7].toLocaleString("en-US") + " theorems · " + g[8] + " modules · " + g[9] + " in gate"));
    if (g[2]) { var p = el("p", "sky-sum"); p.innerHTML = g[2]; body.appendChild(p); }
    body.appendChild(el("h3", null, "Lines"));
    var ul = el("ul", "sky-lines");
    g[10].forEach(function (li) {
      var l = D.l[li], item = el("li"), b = el("button", null, l[0]);
      b.type = "button";
      if (li === lineIdx) item.className = "cur";
      b.addEventListener("click", function () { focusCircle(l[2], l[3], l[4]); });
      item.appendChild(b);
      item.appendChild(el("span", "sky-n", " " + l[5].length + (l[5].length === 1 ? " module" : " modules")));
      ul.appendChild(item);
    });
    body.appendChild(ul);
    open(); draw();
  }
  function showTarget(q) {
    var t = D.o[q];
    selMod = selDot = selGroup = -1;
    body.innerHTML = "";
    body.appendChild(el("p", "sky-kicker", "Research target"));
    body.appendChild(el("h2", null, t[0]));
    var p = el("p", "sky-sum"); p.innerHTML = t[1]; body.appendChild(p);
    var a = el("a", "sky-ref", "See the status page");
    a.href = "roadmap.html#open";
    body.appendChild(a);
    open(); draw();
  }
  document.getElementById("sky-close").addEventListener("click", close);

  // pointer input: drag to pan, pinch and wheel to zoom, click to select
  var pts = new Map(), moved = false, last = null, pinch = 0;
  cv.addEventListener("pointerdown", function (e) {
    cv.setPointerCapture(e.pointerId);
    pts.set(e.pointerId, [e.offsetX, e.offsetY]);
    moved = false; last = [e.offsetX, e.offsetY];
    if (pts.size === 2) { var v = Array.from(pts.values()); pinch = Math.hypot(v[0][0] - v[1][0], v[0][1] - v[1][1]); }
  });
  cv.addEventListener("pointermove", function (e) {
    if (pts.has(e.pointerId)) {
      pts.set(e.pointerId, [e.offsetX, e.offsetY]);
      if (pts.size === 2) {
        var v = Array.from(pts.values()), d = Math.hypot(v[0][0] - v[1][0], v[0][1] - v[1][1]);
        if (pinch) zoomAt(d / pinch, (v[0][0] + v[1][0]) / 2, (v[0][1] + v[1][1]) / 2, true);
        pinch = d; moved = true; return;
      }
      var dx = e.offsetX - last[0], dy = e.offsetY - last[1];
      if (!moved && Math.hypot(dx, dy) < 4) return;
      if (!moved) { dx = e.offsetX - last[0]; dy = e.offsetY - last[1]; }
      moved = true;
      view.x -= dx / view.s; view.y -= dy / view.s;
      last = [e.offsetX, e.offsetY];
      tip.hidden = true;
      draw();
      return;
    }
    var j = dotAt(e.offsetX, e.offsetY);
    if (j !== hover) { hover = j; draw(); }
    if (j >= 0) {
      tip.textContent = "";
      tip.appendChild(el("code", null, nm(D.t[j])));
      tip.appendChild(el("span", null, D.m[DM[j]][0] + (ring[j] ? " · restated by the statement gate" : "")));
      tip.hidden = false;
      var tx = Math.min(e.offsetX + 14, W - tip.offsetWidth - 8), ty = e.offsetY + 16;
      if (ty + tip.offsetHeight > H - 8) ty = e.offsetY - tip.offsetHeight - 10;
      tip.style.left = Math.max(8, tx) + "px"; tip.style.top = ty + "px";
      cv.style.cursor = "pointer";
    } else {
      tip.hidden = true;
      cv.style.cursor = plateAt(e.offsetX, e.offsetY) >= 0 || targetAt(e.offsetX, e.offsetY) >= 0 ? "pointer" : "grab";
    }
  });
  function up(e) {
    if (!pts.has(e.pointerId)) return;
    pts.delete(e.pointerId);
    pinch = 0;
    if (pts.size || moved || e.type === "pointercancel") return;
    var px = e.offsetX, py = e.offsetY, k;
    if ((k = plateAt(px, py)) >= 0) { showGroup(k); var g = D.g[k]; focusCircle(g[4], g[5], g[6]); return; }
    if ((k = targetAt(px, py)) >= 0) { showTarget(k); return; }
    if ((k = dotAt(px, py)) >= 0) { showModule(DM[k], k); return; }
    if ((k = moduleAt(px, py)) >= 0 && view.s > 2.6) { showModule(k, -1); return; }
  }
  cv.addEventListener("pointerup", up);
  cv.addEventListener("pointercancel", up);
  cv.addEventListener("pointerleave", function () { if (hover >= 0) { hover = -1; tip.hidden = true; draw(); } });
  cv.addEventListener("wheel", function (e) {
    e.preventDefault();
    zoomAt(Math.exp(-e.deltaY * (e.deltaMode ? 0.05 : 0.0018)), e.offsetX, e.offsetY, true);
  }, { passive: false });
  cv.addEventListener("keydown", function (e) {
    var step = 60 / view.s, map = { ArrowLeft: [-step, 0], ArrowRight: [step, 0], ArrowUp: [0, -step], ArrowDown: [0, step] };
    if (map[e.key]) { view.x += map[e.key][0]; view.y += map[e.key][1]; draw(); e.preventDefault(); }
    else if (e.key === "+" || e.key === "=") { zoomAt(1.5, W / 2, H / 2); e.preventDefault(); }
    else if (e.key === "-") { zoomAt(1 / 1.5, W / 2, H / 2); e.preventDefault(); }
  });
  document.getElementById("sky-in").addEventListener("click", function () { zoomAt(1.6, W / 2, H / 2); });
  document.getElementById("sky-out").addEventListener("click", function () { zoomAt(1 / 1.6, W / 2, H / 2); });
  document.getElementById("sky-fit").addEventListener("click", function () { go(fitView()); });
  mini.addEventListener("click", function (e) {
    var m = mini._map;
    go({ x: (e.offsetX - m[1]) / m[0], y: (e.offsetY - m[2]) / m[0], s: view.s });
  });

  // search
  var found = [], active = -1;
  function search() {
    var q = box.value.trim().toLowerCase();
    query = q.length >= 2 ? q : "";
    found = [];
    hit.fill(0);
    if (query) {
      var lineHit = D.l.map(function (l) { return l[0].toLowerCase().indexOf(query) >= 0; });
      var modHit = D.m.map(function (m) { return m[0].toLowerCase().indexOf(query) >= 0; });
      for (var j = 0; j < N; j++) {
        var m = D.m[DM[j]];
        if (lineHit[m[2]] || modHit[DM[j]] || D.t[j].toLowerCase().indexOf(query) >= 0) hit[j] = 1;
      }
      D.l.forEach(function (l, k) { if (lineHit[k] && found.length < 12) found.push(["line", k, l[0], l[5].length + " modules"]); });
      D.m.forEach(function (m, k) { if (modHit[k] && found.length < 12) found.push(["module", k, m[0], "module"]); });
      for (j = 0; j < N && found.length < 12; j++) {
        if (D.t[j].toLowerCase().indexOf(query) >= 0) found.push(["theorem", j, nm(D.t[j]), D.m[DM[j]][0]]);
      }
    }
    results.innerHTML = "";
    active = found.length ? 0 : -1;
    found.forEach(function (f, n) {
      var li = el("li");
      li.id = "sky-r" + n;
      li.setAttribute("role", "option");
      li.appendChild(el("code", null, f[2]));
      li.appendChild(el("span", null, f[3]));
      li.addEventListener("mousedown", function (e) { e.preventDefault(); choose(n); });
      results.appendChild(li);
    });
    if (query && !found.length) results.appendChild(el("li", "none", "No match"));
    results.hidden = !query;
    box.setAttribute("aria-expanded", query ? "true" : "false");
    mark();
    draw();
  }
  function mark() {
    Array.prototype.forEach.call(results.children, function (li, n) { li.setAttribute("aria-selected", n === active ? "true" : "false"); });
    if (active >= 0) box.setAttribute("aria-activedescendant", "sky-r" + active); else box.removeAttribute("aria-activedescendant");
  }
  function choose(n) {
    var f = found[n];
    if (!f) return;
    results.hidden = true;
    box.setAttribute("aria-expanded", "false");
    if (f[0] === "theorem") { var m = D.m[DM[f[1]]]; showModule(DM[f[1]], f[1]); focusCircle(m[3], m[4], Math.max(m[5], 10)); }
    else if (f[0] === "module") { var mm = D.m[f[1]]; showModule(f[1], -1); focusCircle(mm[3], mm[4], Math.max(mm[5], 10)); }
    else { var l = D.l[f[1]]; showGroup(l[1], f[1]); focusCircle(l[2], l[3], l[4]); }
  }
  box.addEventListener("input", search);
  box.addEventListener("keydown", function (e) {
    if (e.key === "ArrowDown" && found.length) { active = (active + 1) % found.length; mark(); e.preventDefault(); }
    else if (e.key === "ArrowUp" && found.length) { active = (active + found.length - 1) % found.length; mark(); e.preventDefault(); }
    else if (e.key === "Enter") { choose(active); e.preventDefault(); }
    else if (e.key === "Escape") { box.value = ""; search(); e.preventDefault(); }
  });
  box.addEventListener("blur", function () { results.hidden = true; });
  box.addEventListener("focus", function () { if (query) results.hidden = false; });
  document.addEventListener("keydown", function (e) {
    var t = e.target.tagName;
    if (e.key === "/" && t !== "INPUT" && t !== "TEXTAREA") { box.focus(); e.preventDefault(); }
    else if (e.key === "Escape" && !panel.hidden && t !== "INPUT") close();
  });

  // size
  var fitted = false;
  function resize() {
    var r = cv.getBoundingClientRect();
    if (!r.width || !r.height) return;
    dpr = window.devicePixelRatio || 1;
    W = r.width; H = r.height;
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    var f = fitView();
    if (!fitted) { view = f; fitted = true; }
    paint();
  }
  if (window.ResizeObserver) new ResizeObserver(resize).observe(cv);
  else window.addEventListener("resize", resize);
  root.classList.add("ready");
  resize();
})();
