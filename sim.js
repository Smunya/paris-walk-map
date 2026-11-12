/* Simulated walker for the Paris map: used by the Node tests and by the fast-forward demo (?sim=0).
 *
 * build(day, scenario) -> { at(t), arrive, depart, end }: walks the day's real route geometry,
 *   stays at stops, waits for opening hours and fixed times, goes dark (no GPS) in the metro.
 * scenario: { late: min, pace: m/min (75 = plan), stays: factor for every stay, extra: {stopId: min},
 *             pass: [stopIds walked past without stopping], noise: GPS error in m, seed }
 *
 * Demo in the browser: index.html?sim=0&speed=60&late=20&pace=70&extra=jozi:15&stays=1.2
 *   speed = how many times faster than real time (60: one minute of the day per second).
 */
(function (root) {
  'use strict';
  const Sched = root.Sched || (typeof require !== 'undefined' ? require('./schedule.js') : null);
  const toMin = Sched.toMin;

  function cumul(g) {
    const c = [0];
    for (let i = 1; i < g.length; i++) c.push(c[i - 1] + Sched.distM(g[i - 1], g[i]));
    return c;
  }
  function pointAt(g, c, d) {
    if (d <= 0) return g[0];
    for (let i = 1; i < g.length; i++) {
      if (c[i] >= d) {
        const f = (d - c[i - 1]) / ((c[i] - c[i - 1]) || 1);
        return [g[i - 1][0] + f * (g[i][0] - g[i - 1][0]), g[i - 1][1] + f * (g[i][1] - g[i - 1][1])];
      }
    }
    return g[g.length - 1];
  }
  function rng(seed) {               // small deterministic PRNG + gaussian
    let s = seed >>> 0 || 1;
    const u = () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return ((s >>> 0) % 1e9) / 1e9; };
    return () => Math.sqrt(-2 * Math.log(u() || 1e-9)) * Math.cos(2 * Math.PI * u());
  }

  function build(day, sc) {
    sc = sc || {};
    const S = day.stops, pace = sc.pace || 75, segs = [], arrive = {}, depart = {};
    const pass = new Set(sc.pass || []), extra = sc.extra || {}, stays = sc.stays == null ? 1 : sc.stays;
    const stayOf = s => pass.has(s.id) ? 0 : Math.max(0, (s.stay || 0) * stays + (extra[s.id] || 0));
    const openOf = s => { const h = Sched.parseHours(s.hours); return h && h.open != null && !pass.has(s.id) && (s.stay || 0) > 0 ? h.open : null; };
    let t = toMin(day.start) + (sc.late || 0);
    segs.push({ type: 'stay', t0: -1e9, t1: t, pos: [S[0].lat, S[0].lon], k: 0 });
    arrive[0] = toMin(S[0].arrive); depart[0] = t;
    const walk = (geom, c, d0, d1) => {
      const dur = (d1 - d0) / pace;
      if (dur > 0) segs.push({ type: 'walk', t0: t, t1: t + dur, geom, c, d0, d1 });
      t += Math.max(0, dur);
    };
    const stopAt = (k, pos) => {
      const s = S[k];
      arrive[k] = t;
      const o = openOf(s); if (o != null && t < o) t = o;
      if (s.fixed && !pass.has(s.id)) t = Math.max(t, toMin(s.fixed));
      t += stayOf(s);
      segs.push({ type: 'stay', t0: arrive[k], t1: t, pos, k });
      depart[k] = t;
    };
    let prev = 0;
    S.forEach((s, i) => {
      if (i === 0 || s.view) return;
      const geom = s.leg_geom && s.leg_geom.length > 1 ? s.leg_geom : [[S[prev].lat, S[prev].lon], [s.lat, s.lon]];
      const c = cumul(geom), L = c[c.length - 1];
      if (s.mode === 'metro') {
        const dur = s.metro_min || s.leg_min || 0;
        segs.push({ type: 'metro', t0: t, t1: t + dur, geom, c, d0: 0, d1: L });
        t += dur;
      } else {
        const views = [];
        for (let k = prev + 1; k < i; k++) if (S[k].view) views.push({ k, at: Sched.projLine(S[k].view_pt || [S[k].lat, S[k].lon], geom).frac * L });
        views.sort((a, b) => a.at - b.at);
        let pos = 0;
        for (const v of views) { walk(geom, c, pos, v.at); pos = Math.max(pos, v.at); stopAt(v.k, pointAt(geom, c, pos)); }
        walk(geom, c, pos, L);
      }
      if (s.kind !== 'via') stopAt(i, [s.lat, s.lon]);
      else arrive[i] = depart[i] = t;
      prev = i;
    });
    const last = S[S.length - 1];
    segs.push({ type: 'stay', t0: t, t1: 1e9, pos: [last.lat, last.lon], k: S.length - 1 });
    const noise = sc.noise || 0, g = rng(sc.seed || 7);
    let cur = 0;
    function at(tt) {
      if (tt < segs[cur].t0) cur = 0;
      while (cur < segs.length - 1 && tt >= segs[cur].t1) cur++;
      const sg = segs[cur];
      let p = sg.type === 'stay' ? sg.pos : pointAt(sg.geom, sg.c, sg.d0 + (sg.d1 - sg.d0) * Math.min(1, (tt - sg.t0) / ((sg.t1 - sg.t0) || 1)));
      if (noise) p = [p[0] + g() * noise / 110540, p[1] + g() * noise / (111320 * Math.cos(p[0] * Math.PI / 180))];
      return { lat: p[0], lon: p[1], acc: Math.max(5, noise * 1.5), gps: sg.type !== 'metro', state: sg.type, k: sg.k };
    }
    return { at, arrive, depart, end: t, segs };
  }

  // ---- fast-forward demo on the map (browser only; uses the page's globals) --------------------
  function demo() {
    const qs = new URLSearchParams(location.search), di = +qs.get('sim') || 0, day = P.days[di];
    const extra = {};
    (qs.get('extra') || '').split(',').filter(Boolean).forEach(x => { const [id, m] = x.split(':'); extra[id] = +m || 0; });
    const sc = { late: +qs.get('late') || 0, pace: +qs.get('pace') || 75, stays: qs.has('stays') ? +qs.get('stays') : 1,
      extra, pass: (qs.get('pass') || '').split(',').filter(Boolean), noise: qs.has('noise') ? +qs.get('noise') : 8, seed: 7 };
    const W = build(day, sc);
    const t0 = toMin(day.start) - 5;
    window.SIM = { now: t0, speed: +qs.get('speed') || 60, run: true };
    const fresh = () => {          // a clean demo day (only the demo's own storage)
      try { Object.keys(localStorage).filter(k => k.startsWith('paris-sim-')).forEach(k => localStorage.removeItem(k)); } catch (e) {}
      LIVE.st = { p: -1, arrived: {}, skips: new Set(), manual: null }; LIVE.anchor = null; LIVE.lastFixMin = -1e9;
      VISITED[di].clear();
    };
    fresh();
    const css = document.createElement('style');
    css.textContent = `#simbar{position:fixed;z-index:1050;left:8px;bottom:calc(env(safe-area-inset-bottom,0px) + 26px);display:flex;gap:6px;align-items:center;
      padding:6px 8px;border-radius:12px;background:#1f2430;color:#fff;font:600 13px/1 system-ui,sans-serif;box-shadow:0 2px 10px rgba(0,0,0,.3)}
      #simbar button{min-width:36px;height:32px;border:0;border-radius:8px;background:#ffffff22;color:#fff;font:inherit;cursor:pointer}
      #simbar .tm{font-variant-numeric:tabular-nums;min-width:62px;text-align:center}`;
    document.head.appendChild(css);
    const bar = document.createElement('div');
    bar.id = 'simbar';
    bar.innerHTML = '<span>Демо</span><span class="tm"></span><button data-a="run">⏸</button><button data-a="speed"></button><button data-a="restart">⟲</button>';
    document.body.appendChild(bar);
    const tm = bar.querySelector('.tm'), bRun = bar.querySelector('[data-a=run]'), bSp = bar.querySelector('[data-a=speed]');
    const SPEEDS = [10, 60, 300];
    const paint = () => { tm.textContent = Sched.fmt(SIM.now) + (W.at(SIM.now).gps ? '' : ' 🚇'); bRun.textContent = SIM.run ? '⏸' : '▶'; bSp.textContent = '×' + SIM.speed; };
    bar.onclick = e => {
      const a = e.target.dataset.a;
      if (a === 'run') SIM.run = !SIM.run;
      if (a === 'speed') SIM.speed = SPEEDS[(SPEEDS.indexOf(SIM.speed) + 1) % SPEEDS.length] || 60;
      if (a === 'restart') { SIM.now = t0; fresh(); liveRecalc(); }
      paint();
    };
    L.DomEvent.disableClickPropagation(bar);
    let last = performance.now();
    const step = () => {
      const nowR = performance.now(), dt = (nowR - last) / 1000; last = nowR;
      if (SIM.run && SIM.now < W.end + 15) {
        // a real phone gets a fix every few seconds: at high speed feed the map in 30 s steps
        const dmin = Math.min(SIM.speed * dt / 60, 30), n = Math.max(1, Math.ceil(dmin / 0.5));
        for (let j = 0; j < n; j++) {
          SIM.now += dmin / n;
          const p = W.at(SIM.now);
          if (p.gps) onPos({ coords: { latitude: p.lat, longitude: p.lon, accuracy: p.acc } });
        }
        if (!W.at(SIM.now).gps) liveRecalc();
      }
      paint();
    };
    setInterval(step, 200);
    toast(`Демо ${day.label.split(/[,:]/)[0]}: старт ${sc.late ? 'на ' + sc.late + ' хв пізніше' : 'вчасно'}, ×${SIM.speed}. Кнопки внизу: пауза, швидкість, заново.`, 6000);
    paint();
  }

  const api = { build, cumul, pointAt };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else { root.Sim = api; root.Sim.demo = demo; }
})(typeof window !== 'undefined' ? window : globalThis);
