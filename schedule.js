/* Live schedule engine for the Paris walking map (no DOM; also loaded by Node tests).
 *
 * The day's plan in data.js is a chain over day.stops (ordered, incl. "via" routing points and
 * "view from afar" stops): arrive_k = depart_(k-1) + leg_min_k; fixed times wait; depart = arrive + stay.
 * This file re-runs that chain from where you really are (GPS or "I'm here") and the real clock.
 *
 *   locate(day, fix, p)        -> where on the route a GPS fix is (p = index of the last stop passed)
 *   forecast(day, anchor, opt) -> expected times for every stop after the anchor + warnings
 *   suggestSkips(day, fc)      -> which stops to drop to keep a buffer before the next fixed time
 */
(function (root) {
  'use strict';
  const PACE = 75;            // m per minute, same as build_routes.py
  const AT_M = 60;            // within this distance you are "at" a stop
  const NEAR_M = 120;         // a route leg counts as yours within this (+ GPS accuracy)
  const OFF_M = 150;          // further than this from every candidate leg = off the route
  const WINDOW = 8;           // look this many stops ahead before allowing a jump further on
  const BUFFER = 10;          // minutes of slack we want before a fixed time

  const toMin = s => { const [h, m] = String(s).split(':').map(Number); return h * 60 + m; };
  const fmt = m => {
    m = Math.round(m); m = ((m % 1440) + 1440) % 1440;
    return String(Math.floor(m / 60)).padStart(2, '0') + ':' + String(m % 60).padStart(2, '0');
  };
  function parseHours(h) {
    if (!h) return null;
    const [a, b] = h.split('-');
    return { open: a ? toMin(a) : null, close: b ? toMin(b) : null };
  }

  // ---- geometry (local flat projection, metres) -------------------------------------------
  function xy(p, lat0) { return [p[1] * 111320 * Math.cos(lat0 * Math.PI / 180), p[0] * 110540]; }
  function distM(a, b) { const A = xy(a, a[0]), B = xy(b, a[0]); return Math.hypot(A[0] - B[0], A[1] - B[1]); }
  // distance from p to a polyline and how far along it (0..1) the closest point is
  function projLine(p, line) {
    const lat0 = p[0], P = xy(p, lat0);
    let best = { d: Infinity, along: 0 }, run = 0;
    const seg = [];
    for (let i = 1; i < line.length; i++) {
      const A = xy(line[i - 1], lat0), B = xy(line[i], lat0);
      const dx = B[0] - A[0], dy = B[1] - A[1], L2 = dx * dx + dy * dy, L = Math.sqrt(L2);
      let t = L2 ? ((P[0] - A[0]) * dx + (P[1] - A[1]) * dy) / L2 : 0;
      t = Math.max(0, Math.min(1, t));
      const d = Math.hypot(P[0] - (A[0] + t * dx), P[1] - (A[1] + t * dy));
      if (d < best.d) best = { d, along: run + t * L };
      run += L; seg.push(L);
    }
    return { d: best.d, frac: run ? best.along / run : 1 };
  }

  const isVia = s => s.kind === 'via';
  const isView = s => !!s.view;
  const isRouted = s => !isView(s);
  const isPoint = s => !isVia(s);            // something you would call a "stop"

  // Per routed stop i: its leg (geometry from the previous routed stop) and the stops on it.
  function legs(day) {
    if (day._legs) return day._legs;
    const S = day.stops, out = [];
    let prev = -1;
    S.forEach((s, i) => {
      if (!isRouted(s)) return;
      if (prev >= 0 && s.leg_geom && s.leg_geom.length > 1) {
        const members = [];               // view stops between + i itself, with cumulative minutes
        let cum = 0;
        for (let k = prev + 1; k <= i; k++) { cum += S[k].leg_min || 0; members.push({ k, cum }); }
        out.push({ i, from: prev, geom: s.leg_geom, total: cum, members });
      }
      prev = i;
    });
    Object.defineProperty(day, '_legs', { value: out, enumerable: false });
    return out;
  }

  // ---- where am I -------------------------------------------------------------------------
  // fix = {lat, lon, acc}; p = last stop index passed (-1 before the start)
  function locate(day, fix, p) {
    const S = day.stops, pt = [fix.lat, fix.lon], acc = Math.min(fix.acc || 0, 100);
    p = p == null ? -1 : p;
    const atR = Math.max(AT_M, acc * 0.6);
    const nextStop = S.findIndex((s, i) => i > p && isPoint(s) && !isView(s));
    // nearest point stop within atR among indexes [lo, hi]
    const atStop = (lo, hi) => {
      let best = null;
      S.forEach((s, i) => {
        if (i < lo || i > hi || !isPoint(s) || isView(s)) return;
        const d = distM(pt, [s.lat, s.lon]);
        if (d <= atR && (!best || d < best.d)) best = { i, d };
      });
      return best && { kind: 'at', i: best.i, p: best.i, d: Math.round(best.d) };
    };
    // 1) at the current or the very next stop
    const here = atStop(Math.max(p, 0), nextStop < 0 ? S.length - 1 : nextStop);
    if (here) return here;
    // 2) on a leg ahead: the earliest leg (ending after p) within reach. This comes before stops
    //    further ahead, so passing a later stop on the way (e.g. the metro entrance on the walk to
    //    dinner) does not make the plan jump past the stops in between.
    const R = NEAR_M + acc;
    let on = null, nearest = Infinity;
    for (const L of legs(day)) {
      if (L.i <= p) continue;
      const pr = projLine(pt, L.geom);
      nearest = Math.min(nearest, pr.d);
      if (pr.d <= R) { on = { L, pr }; break; }
    }
    if (on) {
      const pos = on.pr.frac * on.L.total;
      let passed = on.L.from;
      for (const m of on.L.members) if (m.cum <= pos && m.k !== on.L.i) passed = m.k;
      return { kind: 'leg', i: on.L.i, frac: on.pr.frac, p: Math.max(p, passed), d: Math.round(on.pr.d) };
    }
    // 3) at a stop further ahead (you took a shortcut): the nearest one within the next few stops
    const ahead = atStop(nextStop + 1, p + WINDOW) || atStop(p + WINDOW + 1, S.length - 1);
    if (ahead) return ahead;
    // 4) off the route: head by straight line for the nearest of the next few stops
    //    (the ones before it count as passed: you are already beyond them)
    if (nextStop < 0) return { kind: 'done', p };
    let tgt = nextStop, td = distM(pt, [S[nextStop].lat, S[nextStop].lon]);
    S.forEach((s, i) => {
      if (i <= nextStop || i > p + WINDOW || !isPoint(s) || isView(s)) return;
      const d = distM(pt, [s.lat, s.lon]);
      if (d < td) { tgt = i; td = d; }
    });
    return { kind: 'off', i: tgt, p: tgt === nextStop ? p : tgt - 1, walk: td * 1.3 / PACE, d: Math.round(Math.min(td, nearest)) };
  }

  // ---- forecast -----------------------------------------------------------------------------
  // anchor: {kind:'at', i, since}, {kind:'leg', i, frac}, {kind:'off', i, walk}, {kind:'start'}
  // opt: {now, skips: Set of stop ids, visited: Set of stop ids}
  function forecast(day, anchor, opt) {
    const S = day.stops, now = opt.now, skips = opt.skips || new Set(), visited = opt.visited || new Set();
    // a stop you marked as visited but that is still ahead (you went there out of order) is not
    // walked to or stayed at again: it counts like a skipped one, flagged `visited`
    const gone = id => skips.has(id) || visited.has(id);
    const rows = new Array(S.length).fill(null);
    let t, from;

    const step = (k, arrive) => {           // arrive at stop k at time `arrive`; returns departure
      const s = S[k], plan = toMin(s.arrive), r = { k, eta: arrive, plan, delay: arrive - plan };
      let tt = arrive;
      if (gone(s.id)) {
        if (visited.has(s.id)) r.visited = true; else r.skipped = true;
        tt -= s.skip_walk_min || 0;             // the shortcut prev -> next
      } else {
        const h = parseHours(s.hours);
        if (h && h.open != null && tt < h.open && s.stay > 0) { r.wait = h.open - tt; tt = h.open; }
        if (s.fixed) { const f = toMin(s.fixed); r.fixed = f; r.slack = f - tt; if (tt < f) tt = f; }
        if (h && h.close != null) {
          if (tt >= h.close) r.closed = h.close;
          else if (s.stay > 0 && tt + s.stay > h.close) r.short = h.close - tt;
        }
        tt += s.stay || 0;
      }
      r.etd = tt; rows[k] = r;
      return tt;
    };

    if (anchor.kind === 'start' || (anchor.kind === 'at' && anchor.i === 0)) {
      // before leaving: you leave at the planned start or now, whichever is later
      const start = Math.max(now, toMin(day.start));
      rows[0] = { k: 0, eta: start, plan: toMin(S[0].arrive), delay: start - toMin(S[0].depart), etd: start, here: true };
      t = start; from = 1;
    } else if (anchor.kind === 'at') {
      const k = anchor.i, s = S[k];
      const since = anchor.since == null ? now : Math.min(anchor.since, now);
      const r = { k, eta: since, plan: toMin(s.arrive), here: true };
      r.delay = since - r.plan;
      let dep = since;
      const h = parseHours(s.hours);
      if (h && h.open != null && dep < h.open && s.stay > 0) { r.wait = h.open - dep; dep = h.open; }
      if (s.fixed) { const f = toMin(s.fixed); r.fixed = f; r.slack = f - since; if (dep < f) dep = f; }
      if (h && h.close != null && since >= h.close) r.closed = h.close;
      dep = Math.max(now, dep + (gone(s.id) ? 0 : (s.stay || 0)));
      r.etd = dep; rows[k] = r;
      t = dep; from = k + 1;
    } else if (anchor.kind === 'leg') {
      const L = legs(day).find(x => x.i === anchor.i);
      const pos = anchor.frac * L.total;
      const first = L.members.find(m => m.cum > pos) || L.members[L.members.length - 1];
      t = step(first.k, now + Math.max(0, first.cum - pos));
      from = first.k + 1;
    } else {                                   // off route
      t = step(anchor.i, now + anchor.walk);
      from = anchor.i + 1;
    }
    for (let k = from; k < S.length; k++) t = step(k, t + (S[k].leg_min || 0));

    // summary
    const ahead = rows.filter(Boolean);
    const next = ahead.find(r => !r.here && isPoint(S[r.k]) && !r.skipped && !r.visited) || null;
    const fixedAhead = ahead.filter(r => r.fixed != null && !r.skipped && !r.visited);
    const issues = ahead.filter(r => (r.closed != null || r.short != null) && !r.skipped && !r.visited && !r.here);
    const last = ahead[ahead.length - 1];
    return { rows, next, fixed: fixedAhead, issues, finish: last ? last.etd : null, now };
  }

  // ---- what could be skipped ----------------------------------------------------------------
  function skippable(s) {
    return isPoint(s) && !isView(s) && !s.fixed && !['hotel', 'metro', 'restaurant', 'brunch'].includes(s.kind)
      && s.src !== 'mine' && s.mode !== 'metro';
  }
  function suggestSkips(day, fc, buffer) {
    buffer = buffer == null ? BUFFER : buffer;
    const target = fc.fixed.find(r => r.slack < buffer);
    if (!target) return null;
    const need = buffer - target.slack;
    const S = day.stops;
    const cands = fc.rows.filter(r => r && !r.here && !r.skipped && !r.visited && r.k < target.k && skippable(S[r.k]))
      .map(r => ({ k: r.k, id: S[r.k].id, gain: (S[r.k].stay || 0) + (S[r.k].skip_walk_min || 0), closed: r.closed != null }))
      .filter(c => c.gain > 0)
      .sort((a, b) => (b.closed - a.closed) || (b.gain - a.gain));
    const picks = [];
    let sum = 0;
    for (const c of cands) { if (sum >= need) break; picks.push(c); sum += c.gain; }
    return { target: target.k, slack: target.slack, need, picks, gain: sum, enough: sum >= need };
  }

  const api = { toMin, fmt, parseHours, distM, projLine, legs, locate, forecast, suggestSkips, skippable, BUFFER };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.Sched = api;
})(typeof window !== 'undefined' ? window : globalThis);
