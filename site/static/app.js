(function () {
  var root = document.documentElement;

  var theme = document.querySelector(".theme");
  if (theme) theme.addEventListener("click", function () {
    var dark = root.getAttribute("data-theme") === "dark" ||
      (!root.getAttribute("data-theme") && window.matchMedia("(prefers-color-scheme: dark)").matches);
    var next = dark ? "light" : "dark";
    root.setAttribute("data-theme", next);
    try { localStorage.setItem("sfrl-theme", next); } catch (e) { /* ignore */ }
  });

  var toggle = document.querySelector(".toc-toggle");
  if (toggle) toggle.addEventListener("click", function () {
    document.body.classList.toggle("toc-open");
  });
  document.querySelectorAll(".toc a").forEach(function (a) {
    a.addEventListener("click", function () { document.body.classList.remove("toc-open"); });
  });

  // Results page: text search plus one status filter.
  var q = document.getElementById("q");
  var chips = document.querySelectorAll(".chip");
  var rows = document.querySelectorAll("table.results tbody tr[data-status]");
  var filter = "";
  function apply() {
    var text = q ? q.value.trim().toLowerCase() : "";
    var shown = {};
    rows.forEach(function (r) {
      var ok = (!filter || (" " + r.dataset.status + " ").indexOf(" " + filter + " ") >= 0) &&
        (!text || r.dataset.search.indexOf(text) >= 0);
      r.hidden = !ok;
    });
    document.querySelectorAll("table.results tr.ch-row").forEach(function (h) {
      var n = h.nextElementSibling, any = false;
      while (n && !n.classList.contains("ch-row")) { if (!n.hidden) { any = true; break; } n = n.nextElementSibling; }
      h.hidden = !any;
    });
  }
  if (q) {
    var params = new URLSearchParams(location.search);
    if (params.get("q")) q.value = params.get("q");
    q.addEventListener("input", apply);
  }
  chips.forEach(function (c) {
    c.addEventListener("click", function () {
      filter = c.dataset.filter;
      chips.forEach(function (x) { x.classList.toggle("on", x === c); });
      apply();
    });
  });
  if (rows.length) apply();

  // Open the Lean card or TeX disclosure that a link points at.
  function reveal() {
    if (!location.hash) return;
    var el = document.getElementById(decodeURIComponent(location.hash.slice(1)));
    if (el && el.tagName === "ARTICLE") el.querySelectorAll("details").forEach(function (d) { d.open = true; });
  }
  window.addEventListener("hashchange", reveal);
  reveal();
})();
