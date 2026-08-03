/* vaelii — the browser's one hand-written script (docs/web.md).  htmx carries the
   declarative interactivity; this carries the five things it cannot express:

     1. selection over the `.sx-item[data-h]` sentex rows, by every route a reader
        expects: click the row (or its checkbox) to toggle, shift-click for a
        contiguous range from the last row touched, arrows/space/enter from the
        keyboard, escape to clear, a select-all control per index group, and the
        press-drag marquee for a sweep across many rows at once.  A click on a *link*
        inside a row still navigates, so the row is selectable without becoming a
        dead zone.  The action bar's Edit / Retract buttons act on the selection.
     2. the header's two colour dots — the palette and the light/dark theme — held as
        data-* on <html> and persisted.  The pre-paint <head> script applies the saved
        values; this wires the dots and keeps what they say about themselves current.
     3. marking the menubar link for the current path active.
     4. the `/kbs` page's option sliders, which show their own value as it moves.
     5. the proposal review's keys — j/k to move, a/x to accept or reject, 1-9 to pick
        a shape — holding a decision per row *index*, since choosing a shape swaps the
        row out from under the element that held it.

   The rows are a single-column ARIA **grid**: each `<li>` is a `role="row"` carrying
   `aria-selected`, and the one row that holds the keyboard's place carries
   `tabindex="0"` while the rest carry `-1` (a roving tabindex), so Tab reaches the
   list once and arrows move inside it.  A grid — unlike a listbox — admits the links
   each row is made of.  The selection count is a live region, so a change announces.

   All of it re-syncs after an htmx swap: a boosted navigation replaces #main, so the
   selection is void, and a save swaps individual rows out of band, so a handle whose
   row has left the page is dropped from it. */
(function () {
  "use strict";

  const $ = (s) => document.querySelector(s);
  const $$ = (s) => document.querySelectorAll(s);

  // localStorage throws outright in a locked-down browser, and one we cannot reach
  // just means the defaults.  A key reads; a key and a value writes.
  const stored = (k, v) => {
    try { return v === undefined ? localStorage.getItem(k) : localStorage.setItem(k, v); }
    catch (e) { return null; }
  };
  const saved = (k, dflt) => stored("vaelii-" + k) || dflt;

  // ---- selection ---------------------------------------------------------

  let selected = new Set();          // handle strings, e.g. "42"
  let anchor = null;                 // handle a shift-range extends from
  let active = null;                 // handle holding the keyboard's place
  const rows = () => Array.from($$(".sx-item[data-h]"));
  const handles = () => rows().map((el) => el.dataset.h);
  const rowFor = (h) => document.querySelector(".sx-item[data-h='" + h + "']");

  function render() {
    const all = rows();
    // a row can leave the page under us — a save swaps the rows it changed out of band,
    // replacing or deleting them — and a handle with no row left is not a selection, so
    // the count and the bar follow the page rather than drifting from it
    const present = new Set(all.map((el) => el.dataset.h));
    selected.forEach((h) => { if (!present.has(h)) selected.delete(h); });
    if (anchor && !present.has(anchor)) anchor = null;
    if (active && !present.has(active)) active = null;
    if (!active && all.length) active = all[0].dataset.h;
    all.forEach((el) => {
      const on = selected.has(el.dataset.h);
      el.classList.toggle("selected", on);
      el.setAttribute("aria-selected", on ? "true" : "false");
      el.tabIndex = el.dataset.h === active ? 0 : -1;
    });
    // each group's select-all control says whether it is currently all-selected, so
    // the same button clears what it selected
    $$(".sx-group").forEach((g) => {
      const btn = g.querySelector("[data-select-all]");
      if (!btn) return;
      const hs = Array.from(g.querySelectorAll(".sx-item[data-h]"), (el) => el.dataset.h);
      const on = hs.length > 0 && hs.every((h) => selected.has(h));
      btn.setAttribute("aria-pressed", on ? "true" : "false");
      btn.textContent = on ? "Clear group" : "Select all";
    });
    const input = $("#sx-handles"), count = $("#sx-count"), bar = $("#sx-bar");
    if (input) input.value = Array.from(selected).join(",");
    if (count) count.textContent = selected.size + " selected";
    if (bar) bar.classList.toggle("hidden", selected.size === 0);
  }

  const clearSelection = () => { selected = new Set(); anchor = null; render(); };
  const closeEditor = () => { const e = $("#editor"); if (e) e.innerHTML = ""; clearSelection(); };

  function toggle(h) {
    if (selected.has(h)) selected.delete(h); else selected.add(h);
    anchor = h;
    render();
  }

  // a contiguous run in document order, from the last row touched to this one — the
  // rows between two groups included, since the flat order is what the reader sees
  function selectRange(h) {
    const hs = handles();
    const from = hs.indexOf(anchor === null ? h : anchor), to = hs.indexOf(h);
    if (from < 0 || to < 0) return toggle(h);
    for (let i = Math.min(from, to); i <= Math.max(from, to); i++) selected.add(hs[i]);
    render();
  }

  function setActive(h, focus) {
    active = h;
    render();
    const el = rowFor(h);
    if (el && focus) el.focus();
  }

  function toggleGroup(group) {
    const hs = Array.from(group.querySelectorAll(".sx-item[data-h]"), (el) => el.dataset.h);
    const on = hs.length > 0 && hs.every((h) => selected.has(h));
    hs.forEach((h) => { if (on) selected.delete(h); else selected.add(h); });
    if (hs.length) anchor = hs[hs.length - 1];
    render();
  }

  // ---- keyboard ----------------------------------------------------------
  // Arrows move the active row (shift extends the selection as it goes), space and
  // enter toggle it, escape clears.  Everything but escape is scoped to a focused
  // row, so the page still scrolls and the search box still takes its own keys.

  document.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape") {
      const ed = $("#editor");
      if (selected.size || (ed && ed.innerHTML)) { closeEditor(); ev.preventDefault(); }
      return;
    }
    const row = ev.target.closest && ev.target.closest(".sx-item[data-h]");
    if (!row || ev.metaKey || ev.ctrlKey || ev.altKey) return;
    const hs = handles(), i = hs.indexOf(row.dataset.h);
    let next = null;
    if (ev.key === "ArrowDown") next = hs[Math.min(i + 1, hs.length - 1)];
    else if (ev.key === "ArrowUp") next = hs[Math.max(i - 1, 0)];
    else if (ev.key === "Home") next = hs[0];
    else if (ev.key === "End") next = hs[hs.length - 1];
    else if (ev.key === " " || ev.key === "Enter") {
      ev.preventDefault();
      if (ev.shiftKey) selectRange(row.dataset.h); else toggle(row.dataset.h);
      return;
    } else return;
    ev.preventDefault();
    if (next === undefined || next === null) return;
    if (ev.shiftKey) {
      // the run grows from where the reader started, so a shift-arrow reversed
      // shrinks it back rather than painting over what it already covered
      if (anchor === null) anchor = row.dataset.h;
      selected.add(row.dataset.h);
      selectRange(next);
    }
    setActive(next, true);
  });

  // ---- marquee drag ------------------------------------------------------

  const THRESHOLD = 5;               // px of movement before a press becomes a drag
  let start = null;                  // {x, y} of the press
  let base = null;                   // the selection to extend (shift) or replace
  let marquee = null;                // the rubber-band element
  let dragging = false;              // moved past THRESHOLD this press
  let swallow = false;               // suppress the click a drag would otherwise fire

  document.addEventListener("pointerdown", (ev) => {
    swallow = false;
    // no marquee from a real control, from inside the bar/editor, or on a page with
    // nothing selectable.  A link (a term, a badge) is fine — a press on one still
    // clicks unless it turns into a drag.
    if (ev.button !== 0 || !$(".sx-item") ||
        ev.target.closest("button, input, textarea, select, .sx-check, #sx-bar, #editor")) return;
    start = { x: ev.clientX, y: ev.clientY };
    dragging = false;
    base = ev.shiftKey ? new Set(selected) : new Set();
  });

  document.addEventListener("pointermove", (ev) => {
    if (!start || (!dragging && Math.hypot(ev.clientX - start.x, ev.clientY - start.y) < THRESHOLD)) return;
    if (!dragging) {
      dragging = true;
      marquee = document.body.appendChild(document.createElement("div"));
      marquee.className = "sx-marquee";
      document.body.classList.add("sx-dragging");
    }
    ev.preventDefault();
    const l = Math.min(start.x, ev.clientX), t = Math.min(start.y, ev.clientY),
          r = Math.max(start.x, ev.clientX), b = Math.max(start.y, ev.clientY);
    marquee.style.cssText = `left:${l}px;top:${t}px;width:${r - l}px;height:${b - t}px`;
    selected = new Set(base);
    rows().forEach((el) => {
      const q = el.getBoundingClientRect();
      if (!(q.right < l || q.left > r || q.bottom < t || q.top > b)) selected.add(el.dataset.h);
    });
    render();
  });

  document.addEventListener("pointerup", () => {
    if (marquee) marquee.remove();
    document.body.classList.remove("sx-dragging");
    swallow = dragging;              // the click after a drag must not navigate
    start = base = marquee = null;
    dragging = false;
  });

  // a link or image under the press must not start a native drag while we marquee
  document.addEventListener("dragstart", (ev) => { if (start) ev.preventDefault(); });

  // ---- palette, theme, menubar -------------------------------------------

  const PALETTES = ["violet", "red", "green", "rainbow"];

  // what the OS is asking for, which is what an unpinned page is showing
  const osTheme = () => {
    try { return matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light"; }
    catch (e) { return "light"; }
  };

  // Both readers **validate**, because localStorage is shared ground that anything can
  // have written: a value outside the set is not a preference, it is noise, and reading
  // it back would pin the page to a value no rule matches — which strands it off the OS
  // default rather than following it.  An unrecognised palette is the default one, and
  // an unrecognised theme is no pin at all.
  const palette = () => {
    const p = stored("vaelii-palette");
    return PALETTES.indexOf(p) < 0 ? "violet" : p;
  };
  const pinnedTheme = () => {
    const t = stored("vaelii-theme");
    return t === "light" || t === "dark" ? t : null;
  };

  // mirror what localStorage and the URL already say — each dot's title, the active
  // nav link.  Everything that changes one of them ends here.  The dots need no
  // state class: each is painted in the variables it sets, so it already shows it.
  function reflect() {
    const pal = $("#palette-dot"), thm = $("#theme-dot"), pinned = pinnedTheme();
    if (pal) pal.title = "Colour palette: " + palette() + " (click to change)";
    if (thm) {
      thm.title = pinned
        ? "Theme: " + pinned + " (click to flip)"
        : "Theme: " + osTheme() + ", following the system (click to pin one)";
    }
    $$(".menubar a").forEach((a) => a.classList.toggle("active", a.getAttribute("href") === location.pathname));
  }

  // data-palette picks the accent pair, data-theme pins light or dark over the OS
  // preference — and a page that has never pinned one carries no data-theme at all,
  // which is what leaves the stylesheet's media query in charge
  const apply = (k, v) => {
    document.documentElement.setAttribute("data-" + k, v);
    stored("vaelii-" + k, v);
    reflect();
  };

  // the OS flipping under an open page moves it too, until a click pins one; the CSS
  // does the recolouring on its own, so this is only the theme dot's title catching up
  try {
    matchMedia("(prefers-color-scheme: dark)").addEventListener("change", reflect);
  } catch (e) { /* no matchMedia: the page just never follows a live change */ }

  // ---- wiring ------------------------------------------------------------

  document.addEventListener("click", (ev) => {
    if (swallow) { swallow = false; ev.preventDefault(); ev.stopPropagation(); return; }
    const all = ev.target.closest("[data-select-all]");
    if (ev.target.closest("#sx-clear, #sx-cancel")) return closeEditor();
    if (ev.target.closest("#palette-dot")) {
      const i = PALETTES.indexOf(palette());
      return apply("palette", PALETTES[(i + 1) % PALETTES.length]);
    }
    // flip whichever theme is on screen, pinned or OS-chosen, and the flip is what
    // turns it into a pinned one
    if (ev.target.closest("#theme-dot")) {
      return apply("theme", (pinnedTheme() || osTheme()) === "dark" ? "light" : "dark");
    }
    if (all) {
      ev.preventDefault(); ev.stopPropagation();
      const group = all.closest(".sx-group");
      if (group) toggleGroup(group);
      return;
    }
    // a row: the checkbox and the row's own body toggle it, a shift-click anywhere in
    // it extends the range, and a plain click on a link still navigates
    const row = ev.target.closest(".sx-item[data-h]");
    if (!row || ev.target.closest("#sx-bar, #editor")) return;
    const onControl = ev.target.closest("a, button, input, textarea, select");
    if (ev.shiftKey || !onControl || ev.target.closest(".sx-check")) {
      ev.preventDefault(); ev.stopPropagation();
      if (ev.shiftKey) selectRange(row.dataset.h); else toggle(row.dataset.h);
      setActive(row.dataset.h, false);
    }
  }, true);                          // capture, so the swallow beats an <a>'s navigation

  // an #main swap (navigation / active search) invalidates the selection; any other
  // swap — the editor loading, a continuation page of rows — just re-applies the
  // highlights over whatever rows are now on the page
  document.addEventListener("htmx:afterSwap", (ev) => {
    if (ev.target && ev.target.id === "main") clearSelection(); else render();
    reflect();
  });

  const init = () => { render(); reflect(); };
  const setPalette = (p) => apply("palette", p);
  const setTheme = (t) => apply("theme", t);
  window.vaelii = { clearSelection, closeEditor, setPalette, setTheme };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init);
  else init();
})();

// ---- the KB catalog's sliders (/kbs) ------------------------------------
// A knob is three elements: the range input the reader drags (0–1000, a position,
// not a value), the <output> that shows what that position means, and the hidden
// field the form actually submits.  The mapping lives here and in `slider-pos`
// server-side, and the two agree: linear for the small knobs, logarithmic for the
// counts that run to millions, where every interesting value would otherwise sit in
// the first few pixels of a linear track.
//
// Only a drag syncs.  The server renders the default's position, its readout, and
// its exact value together, so leaving them alone until the reader moves something
// keeps a default exactly the number the generator documents rather than whatever
// the position happens to round back to.
(() => {
  const valueAt = (r) => {
    const lo = +r.dataset.min, hi = +r.dataset.max, step = +r.dataset.step || 1;
    const t = (+r.value) / 1000;
    const raw = r.dataset.log === "1"
      ? Math.expm1(Math.log1p(lo) + t * (Math.log1p(hi) - Math.log1p(lo)))
      : lo + t * (hi - lo);
    return Math.min(hi, Math.max(lo, Math.round(raw / step) * step));
  };

  document.addEventListener("input", (ev) => {
    const r = ev.target.closest && ev.target.closest(".knob-r");
    if (!r) return;
    const v = valueAt(r);
    const knob = r.closest(".knob");
    const out = knob && knob.querySelector(".knob-v");
    const hid = knob && knob.querySelector("[data-knob-value]");
    if (out) out.textContent = v.toLocaleString() + (r.dataset.unit || "");
    if (hid) hid.value = v;
  });
})();

// ---- reviewing a proposal (/propose) ------------------------------------
// Ten proposed lines have to be reviewable without the mouse, so the review list is a
// second ARIA grid with its own keys: j/k move, a/x decide and step on, 1–9 pick which
// shape of the line to store.  Everything else is htmx and the browser:
//
//   * picking a shape is the numbered button's own hx-post — this only clicks it, so
//     the round-trip that re-checks the sentence is declarative like every other one.
//   * accepting **enables the row's hidden field**, and the form submits exactly the
//     enabled ones.  No payload is assembled here; a decision is one `disabled` flag.
//
// Decisions are held by row index rather than by element, because choosing a shape
// swaps the row out from under them — the server re-renders it undecided and this puts
// the reader's decision back.  A whole new proposal clears them.
(() => {
  "use strict";

  const decisions = new Map();       // data-i -> "accept" | "reject"
  const list = () => document.querySelector("#propose-result .propose-lines");
  const rows = () => Array.from(document.querySelectorAll("#propose-result .p-line"));
  const at = (i) => document.querySelector("#propose-result .p-line[data-i='" + i + "']");

  // The consequence preview listens for this on <body>; its own hx-trigger carries the
  // `delay:` that debounces it, so holding `a` down the list costs one preview and not
  // one per row.  A plain CustomEvent, so nothing here needs htmx's own API — the
  // request stays declarative, in the markup, like every other one on this page.
  let lastAccepted = "";                                 // a fresh list has nothing accepted
  function announce(accepted) {
    const key = accepted.join(" ");
    if (key === lastAccepted) return;                    // a move or a re-render is not a change
    lastAccepted = key;
    document.body.dispatchEvent(new CustomEvent("accepted-changed"));
  }

  function sync(focusIndex) {
    const all = rows();
    // the roving tabindex follows the reader: deciding a line must not send Tab back to
    // the top of a list they are halfway down
    const here = document.activeElement && document.activeElement.closest
      ? document.activeElement.closest("#propose-result .p-line") : null;
    all.forEach((el, k) => {
      const state = decisions.get(el.dataset.i) || "undecided";
      const on = state === "accept";
      el.dataset.state = state;
      el.classList.toggle("p-accepted", on);
      el.classList.toggle("p-rejected", state === "reject");
      el.setAttribute("aria-selected", on ? "true" : "false");
      el.tabIndex = (here ? el === here : k === 0) ? 0 : -1;
      // the accept mechanism, in one line: a disabled field is not submitted, so the
      // form posts the accepted rows and nothing else
      const field = el.querySelector("input[name='line']");
      if (field) field.disabled = !on;
    });
    const accepted = all.filter((el) => decisions.get(el.dataset.i) === "accept");
    const n = accepted.length;
    const count = document.querySelector("#p-count");
    if (count) count.textContent = n + " accepted";
    const commit = document.querySelector(".propose-apply button[type='submit']");
    if (commit) commit.disabled = n === 0;
    // the *lines*, not the count: re-choosing a shape on an accepted row changes what
    // would be stored without changing how many rows are accepted
    announce(accepted.map((el) => {
      const f = el.querySelector("input[name='line']");
      return f ? f.value : "";
    }));
    if (focusIndex !== undefined) {
      const el = at(focusIndex);
      if (el) { el.tabIndex = 0; el.focus(); }
    }
  }

  const decide = (row, state) => {
    const i = row.dataset.i;
    if (decisions.get(i) === state) decisions.delete(i); else decisions.set(i, state);
    sync();
  };

  function move(row, delta) {
    const all = rows(), i = all.indexOf(row);
    const next = all[Math.min(Math.max(i + delta, 0), all.length - 1)];
    if (next) { all.forEach((el) => { el.tabIndex = -1; }); next.tabIndex = 0; next.focus(); }
  }

  document.addEventListener("keydown", (ev) => {
    if (ev.metaKey || ev.ctrlKey || ev.altKey) return;
    const t = ev.target;
    // the instruction box and the search field keep their own keys
    if (t.closest && t.closest("input, textarea, select")) return;
    const row = t.closest && t.closest("#propose-result .p-line");
    if (!row) return;
    const k = ev.key;
    if (k === "j" || k === "ArrowDown") move(row, 1);
    else if (k === "k" || k === "ArrowUp") move(row, -1);
    else if (k === "a" || k === "x") {
      // a row the correction cannot repair has no field to enable, so it has no decision
      if (row.querySelector("input[name='line']")) decide(row, k === "a" ? "accept" : "reject");
      move(row, 1);
    } else if (/^[1-9]$/.test(k)) {
      const b = row.querySelector(".p-opt[data-n='" + k + "']");
      if (!b) return;                                    // a shape this line does not have
      b.click();
    } else return;
    ev.preventDefault();
  });

  document.addEventListener("click", (ev) => {
    const btn = ev.target.closest && ev.target.closest("[data-accept], [data-reject]");
    if (!btn) return;
    const row = btn.closest(".p-line");
    if (row) { ev.preventDefault(); decide(row, btn.hasAttribute("data-accept") ? "accept" : "reject"); }
  });

  // A new proposal is a new review: the old decisions are about lines that no longer
  // exist.  A row swapped in place (a shape choice) is the same line, so its decision
  // survives and the keyboard's place goes back where it was.
  document.addEventListener("htmx:afterSwap", (ev) => {
    const t = ev.target;
    if (!t || !t.closest) return;
    if (t.id === "propose-result") {
      decisions.clear();
      lastAccepted = "";                                 // a new proposal, so a new baseline
      sync();
      const first = rows()[0];
      if (first) first.focus();                          // the reader typed; now they read
    } else if (t.closest("#propose-result") || (list() && t.contains(list()))) {
      const row = t.closest(".p-line") || t.querySelector(".p-line");
      sync(row ? row.dataset.i : undefined);
    }
  });
})();
