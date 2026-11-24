// Lines view of the map component and the switch between the two views. Data from assets/map-data.js.
(function () {
  "use strict";
  var D = window.OPN_MAP, comp = document.getElementById("mapc");
  if (!D || !comp) return;

  // view switch, remembered per viewer
  var views = comp.querySelectorAll(".mapc-view"), switches = comp.querySelectorAll(".mapc-switch button");
  function show(name) {
    views.forEach(function (v) { v.hidden = v.getAttribute("data-view") !== name; });
    switches.forEach(function (b) { b.setAttribute("aria-pressed", b.getAttribute("data-view") === name ? "true" : "false"); });
    try { localStorage.setItem("opn-map-view", name); } catch (e) { }
    if (name === "lines") fit();
  }
  switches.forEach(function (b) { b.addEventListener("click", function () { show(b.getAttribute("data-view")); }); });

  var view = document.getElementById("dm-view"), stage = document.getElementById("dm-stage");
  var laneBox = document.getElementById("dm-lanes"), panel = document.getElementById("dm-panel");
  var box = document.getElementById("dm-q"), count = document.getElementById("dm-count");
  var pbody = document.getElementById("dm-panel-body"), MW = D.lsize[0], MH = D.lsize[1];
  var t = { x: 0, y: 0, s: 1 }, sFit = 1;

  // lane titles drawn at a fixed size over the scaled map
  var titles = D.lanes.map(function (l) {
    var d = document.createElement("div");
    d.className = "dm-lane";
    d.innerHTML = l[0];
    laneBox.appendChild(d);
    return d;
  });

  // lane titles live in a left gutter that no card enters at the fitted scale
  function gutter() { return view.clientWidth < 600 ? 88 : 156; }
  function clamp() {
    var G = gutter(), vw = view.clientWidth - G, vh = view.clientHeight, w = MW * t.s, h = MH * t.s, m = 60;
    t.x = w <= vw ? G + (vw - w) / 2 : Math.min(G + m, Math.max(G + vw - w - m, t.x));
    t.y = h <= vh ? (vh - h) / 2 : Math.min(m, Math.max(vh - h - m, t.y));
  }
  function apply() {
    clamp();
    stage.style.transform = "translate(" + t.x + "px," + t.y + "px) scale(" + t.s + ")";
    laneBox.style.width = gutter() + "px";
    D.lanes.forEach(function (l, k) {
      var top = Math.max(t.y + l[1] * t.s, 0), bottom = Math.min(t.y + (l[1] + l[2]) * t.s, view.clientHeight);
      titles[k].style.top = top + 4 + "px";
      var fit = Math.floor((bottom - top - 6) / 16);  // whole lines only
      titles[k].style.maxHeight = fit * 16 + "px";
      titles[k].hidden = fit < 1;
    });
  }
  function fit() {
    if (!view.clientWidth) return;
    var vw = view.clientWidth - gutter(), s = vw / MW;
    var cap = Math.round(window.innerHeight * 0.8);
    view.style.height = Math.min(Math.ceil(MH * s), cap) + (view.offsetHeight - view.clientHeight) + "px";
    if (MH * s > cap) s = Math.min(s, cap / MH);
    sFit = s;
    t = { x: 0, y: 0, s: s };
    apply();
  }
  function zoomAt(f, px, py) {
    var s = Math.max(sFit, Math.min(2.5, t.s * f));
    t.x = px - (px - t.x) * s / t.s;
    t.y = py - (py - t.y) * s / t.s;
    t.s = s;
    apply();
  }
  function centerZoom(f) { zoomAt(f, view.clientWidth / 2, view.clientHeight / 2); }

  view.addEventListener("wheel", function (e) {
    e.preventDefault();
    var r = view.getBoundingClientRect();
    zoomAt(Math.exp(-e.deltaY * (e.deltaMode ? 0.05 : 0.0018)), e.clientX - r.left, e.clientY - r.top);
  }, { passive: false });
  view.addEventListener("dblclick", function (e) {
    var r = view.getBoundingClientRect();
    zoomAt(1.6, e.clientX - r.left, e.clientY - r.top);
    e.preventDefault();
  });

  // drag to pan; pinch to zoom. The pointer is captured only after it moves, so cards still get clicks.
  var pts = new Map(), start = null, dragged = false, pinch = 0;
  view.addEventListener("pointerdown", function (e) {
    pts.set(e.pointerId, [e.clientX, e.clientY]);
    start = [e.clientX, e.clientY, t.x, t.y];
    dragged = false;
    if (pts.size === 2) { var v = Array.from(pts.values()); pinch = Math.hypot(v[0][0] - v[1][0], v[0][1] - v[1][1]); }
  });
  view.addEventListener("pointermove", function (e) {
    if (!pts.has(e.pointerId)) return;
    pts.set(e.pointerId, [e.clientX, e.clientY]);
    var r = view.getBoundingClientRect();
    if (pts.size === 2) {
      var v = Array.from(pts.values()), d = Math.hypot(v[0][0] - v[1][0], v[0][1] - v[1][1]);
      if (pinch) zoomAt(d / pinch, (v[0][0] + v[1][0]) / 2 - r.left, (v[0][1] + v[1][1]) / 2 - r.top);
      pinch = d; dragged = true; return;
    }
    var dx = e.clientX - start[0], dy = e.clientY - start[1];
    if (!dragged && Math.hypot(dx, dy) < 5) return;
    if (!dragged) { dragged = true; view.setPointerCapture(e.pointerId); view.classList.add("dragging"); }
    t.x = start[2] + dx; t.y = start[3] + dy;
    apply();
  });
  function up(e) {
    pts.delete(e.pointerId);
    pinch = 0;
    view.classList.remove("dragging");
    if (pts.size === 1) { var v = Array.from(pts.values())[0]; start = [v[0], v[1], t.x, t.y]; }
  }
  view.addEventListener("pointerup", up);
  view.addEventListener("pointercancel", up);
  view.addEventListener("click", function (e) { if (dragged) { e.stopPropagation(); e.preventDefault(); dragged = false; } }, true);
  view.addEventListener("keydown", function (e) {
    var step = 80, map = { ArrowLeft: [step, 0], ArrowRight: [-step, 0], ArrowUp: [0, step], ArrowDown: [0, -step] };
    if (e.target !== view && !map[e.key] && "+=-0".indexOf(e.key) < 0) return;
    if (map[e.key] && e.target === view) { t.x += map[e.key][0]; t.y += map[e.key][1]; apply(); }
    else if (e.key === "+" || e.key === "=") centerZoom(1.4);
    else if (e.key === "-") centerZoom(1 / 1.4);
    else if (e.key === "0") fit();
    else return;
    e.preventDefault();
  });
  document.getElementById("dm-in").addEventListener("click", function () { centerZoom(1.4); });
  document.getElementById("dm-out").addEventListener("click", function () { centerZoom(1 / 1.4); });
  document.getElementById("dm-fit").addEventListener("click", fit);
  // refit only when the width changes
  var lastW = 0;
  if (window.ResizeObserver) new ResizeObserver(function () {
    if (view.clientWidth && view.clientWidth !== lastW) { lastW = view.clientWidth; fit(); }
  }).observe(view.parentNode);

  // cards: highlight neighbors, select to open the panel
  var cards = Array.prototype.slice.call(stage.querySelectorAll(".dm-card"));
  var paths = Array.prototype.slice.call(stage.querySelectorAll(".dm-edges .e"));
  var near = D.l.map(function (l, i) { return [i]; }), users = D.l.map(function () { return []; });
  D.le.forEach(function (e) { near[e[0]].push(e[1]); near[e[1]].push(e[0]); });
  D.ld.forEach(function (deps, c) { deps.forEach(function (d) { users[d].push(c); }); });
  var selected = null, dm = document.getElementById("dm");

  function light(id) {
    dm.classList.toggle("hl", id !== null);
    cards.forEach(function (c, i) { c.classList.toggle("on", id !== null && near[id].indexOf(i) >= 0); });
    paths.forEach(function (p) {
      var on = id !== null && (+p.getAttribute("data-from") === id || +p.getAttribute("data-to") === id);
      p.classList.toggle("on", on);
      if (on) p.parentNode.appendChild(p);
    });
  }
  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function list(title, ids) {
    if (!ids.length) return;
    pbody.appendChild(el("h4", null, title));
    var ul = el("ul", "dm-links");
    ids.forEach(function (id) {
      var li = el("li"), b = el("button", "dm-jump", D.l[id][0]);
      b.type = "button";
      b.addEventListener("click", function () { select(id); cards[id].focus({ preventScroll: true }); });
      li.appendChild(b); ul.appendChild(li);
    });
    pbody.appendChild(ul);
  }
  function detail(i) {
    var l = D.l[i], mods = l[5], thms = 0, gate = [];
    mods.forEach(function (mi) {
      var m = D.m[mi];
      thms += m[7];
      for (var j = m[6]; j < m[6] + m[7]; j++) if (ringed[j]) gate.push(D.t[j]);
    });
    pbody.innerHTML = "";
    pbody.appendChild(el("h3", null, l[0]));
    pbody.appendChild(el("p", "dm-meta", D.g[l[1]][1] + ". " + mods.length + (mods.length === 1 ? " module, " : " modules, ") +
      thms + (thms === 1 ? " public theorem" : " public theorems") + (gate.length ? ", " + gate.length + " restated by the statement gate" : "")));
    pbody.appendChild(el("h4", null, "Modules"));
    var ul = el("ul", "dm-mods");
    mods.forEach(function (mi) {
      var li = el("li"), a = el("a");
      a.href = "reference.html#" + D.m[mi][8];
      a.appendChild(el("code", null, "OddPerfect." + D.m[mi][0]));
      li.appendChild(a);
      if (D.s[mi]) { var p = el("p"); p.innerHTML = D.s[mi]; li.appendChild(p); }
      ul.appendChild(li);
    });
    pbody.appendChild(ul);
    if (gate.length) {
      pbody.appendChild(el("h4", null, "Restated by the statement gate"));
      var gl = el("ul", "dm-gate");
      gate.forEach(function (n) {
        var li = el("li"), a = el("a");
        a.href = "reference.html#" + encodeURIComponent(n);
        a.appendChild(el("code", null, n.replace(/^OddPerfect\./, "")));
        li.appendChild(a); gl.appendChild(li);
      });
      pbody.appendChild(gl);
    }
    list("Imports from", D.ld[i]);
    list("Imported by", users[i]);
  }
  var ringed = new Uint8Array(D.t.length);
  D.ring.forEach(function (j) { ringed[j] = 1; });
  function select(id) {
    if (selected !== null) cards[selected].setAttribute("aria-pressed", "false");
    selected = id;
    panel.hidden = id === null;
    if (id !== null) {
      cards[id].setAttribute("aria-pressed", "true");
      detail(id);
      panel.scrollTop = 0;
    }
    light(id);
  }
  cards.forEach(function (b, i) {
    b.setAttribute("aria-pressed", "false");
    b.addEventListener("mouseenter", function () { light(i); });
    b.addEventListener("mouseleave", function () { light(selected); });
    b.addEventListener("focus", function () { light(i); });
    b.addEventListener("blur", function () { light(selected); });
    b.addEventListener("click", function () { select(i); });
  });
  document.getElementById("dm-clear").addEventListener("click", function () { select(null); });
  document.getElementById("dm-close").addEventListener("click", function () {
    var was = selected;
    select(null);
    if (was !== null) cards[was].focus({ preventScroll: true });
  });
  dm.addEventListener("keydown", function (e) {
    if (e.key === "Escape" && selected !== null) { document.getElementById("dm-close").click(); e.preventDefault(); }
  });

  var text = D.l.map(function (l) {
    var parts = [l[0]];
    l[5].forEach(function (mi) { var m = D.m[mi]; parts.push(m[0]); for (var j = m[6]; j < m[6] + m[7]; j++) parts.push(D.t[j]); });
    return parts.join(" ").toLowerCase();
  });
  function filter() {
    var q = box.value.trim().toLowerCase(), hits = 0;
    cards.forEach(function (c, i) {
      var hit = q === "" || text[i].indexOf(q) >= 0;
      c.classList.toggle("miss", !hit);
      if (hit) hits++;
    });
    count.textContent = q === "" ? cards.length + " lines" : hits + " of " + cards.length + " lines match";
  }
  box.addEventListener("input", filter);
  filter();

  var saved = null;
  try { saved = localStorage.getItem("opn-map-view"); } catch (e) { }
  show(saved === "lines" ? "lines" : "clusters");
})();
