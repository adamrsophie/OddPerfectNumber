(function () {
  var root = document.documentElement;
  root.classList.remove("no-js");
  root.classList.add("js");

  function stored() {
    try { return localStorage.getItem("theme"); } catch (e) { return null; }
  }
  function save(v) {
    try { localStorage.setItem("theme", v); } catch (e) { }
  }
  var param = /[?&]theme=(light|dark)\b/.exec(location.search);
  var theme = param ? param[1] : stored();
  if (theme === "light" || theme === "dark") root.setAttribute("data-theme", theme);

  function current() {
    var t = root.getAttribute("data-theme");
    if (t) return t;
    return window.matchMedia && matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  }

  document.addEventListener("DOMContentLoaded", function () {
    var nav = document.querySelector(".navbar");
    var end = document.querySelector(".nav-end");
    var tabs = document.getElementById("site-tabs");

    var toggle = document.createElement("button");
    toggle.type = "button";
    toggle.className = "icon-btn theme-btn";
    function label() {
      var dark = current() === "dark";
      toggle.textContent = dark ? "Light" : "Dark";
      toggle.setAttribute("aria-label", dark ? "Switch to light theme" : "Switch to dark theme");
    }
    label();
    toggle.addEventListener("click", function () {
      var next = current() === "dark" ? "light" : "dark";
      root.setAttribute("data-theme", next);
      save(next);
      label();
    });
    end.appendChild(toggle);

    var menu = document.createElement("button");
    menu.type = "button";
    menu.className = "icon-btn menu-btn";
    menu.textContent = "Menu";
    menu.setAttribute("aria-expanded", "false");
    menu.setAttribute("aria-controls", "site-tabs");
    menu.addEventListener("click", function () {
      var open = nav.classList.toggle("open");
      menu.setAttribute("aria-expanded", open ? "true" : "false");
    });
    end.appendChild(menu);
    tabs.addEventListener("click", function (e) {
      if (e.target.closest("a")) nav.classList.remove("open");
    });

    // sections: open on click, Enter or Space, and on hover where a pointer can hover
    var secs = Array.prototype.slice.call(tabs.querySelectorAll(".sec"));
    var narrow = window.matchMedia ? matchMedia("(max-width: 900px)") : { matches: false };
    var hoverable = window.matchMedia ? matchMedia("(hover: hover)") : { matches: false };
    var timer = 0;
    function setOpen(sec, on) {
      sec.classList.toggle("open", on);
      sec.querySelector(".sec-btn").setAttribute("aria-expanded", on ? "true" : "false");
    }
    function closeAll(except) { secs.forEach(function (s) { if (s !== except) setOpen(s, false); }); }
    secs.forEach(function (sec) {
      var btn = sec.querySelector(".sec-btn");
      var links = function () { return Array.prototype.slice.call(sec.querySelectorAll(".sec-list a")); };
      btn.addEventListener("click", function () {
        var on = !sec.classList.contains("open");
        closeAll(sec);
        setOpen(sec, on);
      });
      sec.addEventListener("keydown", function (e) {
        var ls = links(), i = ls.indexOf(document.activeElement);
        if (e.key === "Escape" && sec.classList.contains("open")) { setOpen(sec, false); btn.focus(); e.preventDefault(); }
        else if (e.key === "ArrowDown") {
          if (i < 0) { closeAll(sec); setOpen(sec, true); ls[0].focus(); }
          else ls[Math.min(i + 1, ls.length - 1)].focus();
          e.preventDefault();
        } else if (e.key === "ArrowUp" && i >= 0) { (i === 0 ? btn : ls[i - 1]).focus(); e.preventDefault(); }
      });
      sec.addEventListener("focusout", function (e) { if (!sec.contains(e.relatedTarget) && !narrow.matches) setOpen(sec, false); });
      sec.addEventListener("pointerenter", function (e) {
        if (e.pointerType !== "mouse" || !hoverable.matches || narrow.matches) return;
        clearTimeout(timer);
        closeAll(sec);
        setOpen(sec, true);
      });
      sec.addEventListener("pointerleave", function (e) {
        if (e.pointerType !== "mouse" || narrow.matches) return;
        clearTimeout(timer);
        timer = setTimeout(function () { setOpen(sec, false); }, 280);
      });
    });
    document.addEventListener("click", function (e) { if (!e.target.closest(".tabs .sec")) closeAll(null); });

    var toc = document.querySelector("details.toc");
    if (toc && window.matchMedia && !matchMedia("(min-width: 1040px)").matches) toc.open = false;

    document.querySelectorAll("pre").forEach(function (pre) {
      if (!navigator.clipboard) return;
      var b = document.createElement("button");
      b.type = "button";
      b.className = "copy";
      b.textContent = "Copy";
      b.setAttribute("aria-label", "Copy code to clipboard");
      b.addEventListener("click", function () {
        var code = pre.querySelector("code") || pre;
        navigator.clipboard.writeText(code.textContent).then(function () {
          b.textContent = "Copied";
          setTimeout(function () { b.textContent = "Copy"; }, 1500);
        }, function () { b.textContent = "Failed"; });
      });
      pre.appendChild(b);
    });

    var box = document.getElementById("filter");
    if (box) {
      var wrap = box.closest(".filter");
      wrap.hidden = false;
      var out = document.getElementById("filter-count");
      var decls = Array.prototype.slice.call(document.querySelectorAll("[data-decl]"));
      var mods = Array.prototype.slice.call(document.querySelectorAll("[data-module]"));
      var groups = Array.prototype.slice.call(document.querySelectorAll("[data-group]"));
      var text = new Map();
      decls.concat(mods).forEach(function (el) { text.set(el, el.textContent.toLowerCase()); });
      function run() {
        var q = box.value.trim().toLowerCase();
        var shown = 0;
        mods.forEach(function (m) {
          var head = m.querySelector("h3").textContent.toLowerCase() + " " + (m.querySelector(".summary") || m).textContent.toLowerCase();
          var modHit = q === "" || head.indexOf(q) >= 0;
          var any = false;
          m.querySelectorAll("[data-decl]").forEach(function (d) {
            var hit = q === "" || modHit || text.get(d).indexOf(q) >= 0;
            d.hidden = !hit;
            if (hit) { any = true; shown++; }
          });
          m.hidden = !(modHit || any);
          var det = m.querySelector("details.decls");
          if (det) det.open = q !== "" && any;
        });
        groups.forEach(function (g) {
          g.hidden = !g.querySelector("[data-module]:not([hidden])");
        });
        out.textContent = q === "" ? decls.length + " theorems" : shown + " of " + decls.length + " theorems match";
      }
      box.addEventListener("input", run);
      run();
    }

    if (location.hash) {
      var target = document.getElementById(decodeURIComponent(location.hash.slice(1)));
      var det = target && target.closest("details.decls");
      if (det) det.open = true;
      if (target) target.scrollIntoView();
    }
  });
})();
