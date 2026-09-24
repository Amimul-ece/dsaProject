'use strict';
/* =====================================================================
   Shortest Path Finder – Dijkstra's Algorithm (DSA Project)
   Part 1: MinHeap (priority queue)
   Part 2: dijkstra() – the algorithm, records every step
   Part 3: Graph editor + visualizer (canvas & DOM)
   ===================================================================== */

/* ---- MIN-HEAP START ---- */
// Priority queue. Each item is [priority, nodeId]; smallest priority comes out first.
class MinHeap {
  constructor() { this.a = []; }
  isEmpty() { return this.a.length === 0; }

  push(item) {                       // O(log n)
    this.a.push(item);
    this._up(this.a.length - 1);
  }
  pop() {                            // O(log n)
    const a = this.a;
    if (a.length === 0) return undefined;
    const top = a[0];
    const last = a.pop();
    if (a.length > 0) { a[0] = last; this._down(0); }
    return top;
  }
  _up(i) {                           // move item up while it is smaller than its parent
    const a = this.a;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p][0] <= a[i][0]) break;
      [a[p], a[i]] = [a[i], a[p]];
      i = p;
    }
  }
  _down(i) {                         // move item down while a child is smaller
    const a = this.a, n = a.length;
    while (true) {
      const l = 2 * i + 1, r = l + 1;
      let m = i;
      if (l < n && a[l][0] < a[m][0]) m = l;
      if (r < n && a[r][0] < a[m][0]) m = r;
      if (m === i) break;
      [a[m], a[i]] = [a[i], a[m]];
      i = m;
    }
  }
}
/* ---- MIN-HEAP END ---- */

/* ---- DIJKSTRA START ---- */
// nodes: [{id,label,x,y}]   edges: [{a,b,w}] (undirected)   src/dst: node ids
// Returns {steps, path, distance}. "steps" is a list of snapshots used to animate.
function dijkstra(nodes, edges, src, dst) {
  const label = id => nodes.find(n => n.id === id).label;

  // 1. Build adjacency list
  const adj = {};
  nodes.forEach(n => { adj[n.id] = []; });
  edges.forEach(e => {
    adj[e.a].push({ to: e.b, w: e.w });
    adj[e.b].push({ to: e.a, w: e.w });
  });

  // 2. Initialise distances (∞), previous nodes (null) and visited set
  const dist = {}, prev = {}, visited = new Set();
  nodes.forEach(n => { dist[n.id] = Infinity; prev[n.id] = null; });
  dist[src] = 0;

  const heap = new MinHeap();
  heap.push([0, src]);

  const steps = [];
  const snap = (current, edge, msg) =>
    steps.push({ dist: { ...dist }, prev: { ...prev }, visited: [...visited], current, edge, msg, path: null });

  snap(null, null, `Start: distance to ${label(src)} is 0, all other nodes are ∞.`);

  // 3. Main loop
  while (!heap.isEmpty()) {
    const [d, u] = heap.pop();          // node with the smallest known distance
    if (visited.has(u)) continue;       // outdated heap entry, ignore it
    visited.add(u);
    snap(u, null, `Pick ${label(u)} (smallest distance so far = ${d}). Mark it visited.`);

    if (u === dst) {                    // early exit: destination distance is final
      snap(u, null, `Destination ${label(dst)} reached. Its distance is final, so we stop.`);
      break;
    }

    for (const { to, w } of adj[u]) {   // relax every edge leaving u
      if (visited.has(to)) continue;
      const nd = d + w;
      if (nd < dist[to]) {
        const old = dist[to];
        dist[to] = nd;
        prev[to] = u;
        heap.push([nd, to]);
        snap(u, [u, to], `Relax ${label(u)}→${label(to)}: ${d} + ${w} = ${nd} < ${old === Infinity ? '∞' : old}. Update ${label(to)}.`);
      } else {
        snap(u, [u, to], `Check ${label(u)}→${label(to)}: ${d} + ${w} = ${nd}, not better than ${dist[to]}. No change.`);
      }
    }
  }

  // 4. Rebuild the path by walking back through prev[]
  const path = [];
  if (dist[dst] !== Infinity) {
    for (let v = dst; v !== null; v = prev[v]) path.push(v);
    path.reverse();
  }
  snap(null, null, path.length
    ? `Shortest path: ${path.map(label).join(' → ')}  (total distance ${dist[dst]}).`
    : `No path exists from ${label(src)} to ${label(dst)}.`);
  steps[steps.length - 1].path = path;

  return { steps, path, distance: dist[dst] };
}
/* ---- DIJKSTRA END ---- */

/* =====================  UI / VISUALIZER  ===================== */
const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
const R = 22;                                    // node radius

let nodes = [], edges = [], nextId = 1;
let tool = 'node', pending = null, drag = null;  // editor state
let steps = [], stepIdx = -1, result = null, timer = null;  // run state

const $ = id => document.getElementById(id);
const nodeById = id => nodes.find(n => n.id === id);
const labelOf = id => (nodeById(id) || {}).label;
const fmt = v => (v === Infinity ? '∞' : v);

const hints = {
  node:   'Click on an empty area of the canvas to add a node.',
  edge:   'Click one node, then another node to connect them (uses the edge weight above).',
  move:   'Drag a node to move it.',
  delete: 'Click a node or an edge to delete it.'
};
function setHint(text, isError = false) {
  const h = $('hint');
  h.textContent = text;
  h.classList.toggle('error', isError);
}

/* ---------- editing ---------- */
function newLabel() {
  const used = new Set(nodes.map(n => n.label));
  for (let i = 0; i < 26; i++) {
    const c = String.fromCharCode(65 + i);
    if (!used.has(c)) return c;
  }
  return 'N' + nextId;
}
function addNode(x, y) {
  nodes.push({ id: nextId++, label: newLabel(), x, y });
  graphChanged();
}
function addEdge(a, b, w) {
  const old = edges.find(e => (e.a === a && e.b === b) || (e.a === b && e.b === a));
  if (old) old.w = w; else edges.push({ a, b, w });
  graphChanged();
}
function removeNode(id) {
  nodes = nodes.filter(n => n.id !== id);
  edges = edges.filter(e => e.a !== id && e.b !== id);
  graphChanged();
}
function removeEdge(e) { edges = edges.filter(x => x !== e); graphChanged(); }

function graphChanged() { resetRun(); refreshSelects(); }

function refreshSelects() {
  for (const sel of [$('src'), $('dst')]) {
    const keep = Number(sel.value);
    sel.innerHTML = nodes.map(n => `<option value="${n.id}">${n.label}</option>`).join('');
    if (nodes.some(n => n.id === keep)) sel.value = keep;
  }
  if (nodes.length > 1 && $('src').value === $('dst').value) $('dst').selectedIndex = nodes.length - 1;
  draw();
}

function loadSample() {
  nodes = []; edges = []; nextId = 1;
  const pos = { A: [110, 210], B: [280, 90], C: [300, 270], D: [560, 120], E: [680, 330], F: [420, 430] };
  for (const k in pos) nodes.push({ id: nextId++, label: k, x: pos[k][0], y: pos[k][1] });
  const id = l => nodes.find(n => n.label === l).id;
  [['A','B',7],['A','C',9],['A','F',14],['B','C',10],['B','D',15],['C','D',11],['C','F',2],['D','E',6],['E','F',9]]
    .forEach(([a, b, w]) => edges.push({ a: id(a), b: id(b), w }));
  resetRun();
  refreshSelects();
  $('src').value = id('A');
  $('dst').value = id('E');
  setHint('Sample graph loaded (source A, destination E). Press Step or Play.');
}

/* ---------- mouse / touch ---------- */
function pointer(e) {
  const r = canvas.getBoundingClientRect();
  return { x: (e.clientX - r.left) * canvas.width / r.width, y: (e.clientY - r.top) * canvas.height / r.height };
}
const nodeAt = p => nodes.find(n => Math.hypot(n.x - p.x, n.y - p.y) <= R);
function edgeAt(p) {                              // point-to-segment distance
  return edges.find(e => {
    const A = nodeById(e.a), B = nodeById(e.b);
    const dx = B.x - A.x, dy = B.y - A.y;
    const t = Math.max(0, Math.min(1, ((p.x - A.x) * dx + (p.y - A.y) * dy) / (dx * dx + dy * dy)));
    return Math.hypot(p.x - (A.x + t * dx), p.y - (A.y + t * dy)) < 8;
  });
}

canvas.addEventListener('pointerdown', ev => {
  const p = pointer(ev), hit = nodeAt(p);
  if (tool === 'node') {
    if (!hit) { addNode(Math.max(R, Math.min(canvas.width - R, p.x)), Math.max(R, Math.min(canvas.height - R, p.y))); setHint(hints.node); }
  } else if (tool === 'edge') {
    if (!hit) { pending = null; }
    else if (pending === null) { pending = hit.id; setHint(`Now click the second node to connect with ${labelOf(hit.id)}.`); }
    else if (pending !== hit.id) {
      const w = Number($('weight').value);
      if (!(w > 0)) { setHint('Edge weight must be a positive number.', true); }
      else { addEdge(pending, hit.id, w); setHint(hints.edge); }
      pending = null;
    }
  } else if (tool === 'move') {
    if (hit) { drag = hit; canvas.setPointerCapture(ev.pointerId); }
  } else if (tool === 'delete') {
    if (hit) removeNode(hit.id);
    else { const e = edgeAt(p); if (e) removeEdge(e); }
  }
  draw();
});
canvas.addEventListener('pointermove', ev => {
  if (!drag) return;
  const p = pointer(ev);
  drag.x = Math.max(R, Math.min(canvas.width - R, p.x));
  drag.y = Math.max(R, Math.min(canvas.height - R, p.y));
  draw();
});
canvas.addEventListener('pointerup', () => { drag = null; });

/* ---------- running the algorithm ---------- */
function resetRun() {
  clearTimeout(timer); timer = null;
  steps = []; stepIdx = -1; result = null; pending = null;
  $('btnPlay').textContent = 'Play';
  render();
}
function prepare() {                              // run dijkstra() once, then just animate its steps
  if (steps.length) return true;
  const src = Number($('src').value), dst = Number($('dst').value);
  if (nodes.length < 2) { setHint('Add at least two nodes first.', true); return false; }
  if (!nodeById(src) || !nodeById(dst)) { setHint('Choose a source and a destination.', true); return false; }
  result = dijkstra(nodes, edges, src, dst);
  steps = result.steps; stepIdx = -1;
  setHint(hints[tool]);
  return true;
}
function stepForward() {
  if (!prepare()) return false;
  if (stepIdx < steps.length - 1) { stepIdx++; render(); return true; }
  return false;
}
function play() {
  if (timer) { clearTimeout(timer); timer = null; $('btnPlay').textContent = 'Play'; return; }
  if (!prepare()) return;
  if (stepIdx >= steps.length - 1) { stepIdx = -1; }
  $('btnPlay').textContent = 'Pause';
  const tick = () => {
    if (stepForward()) timer = setTimeout(tick, 1100 - $('speed').value * 100);
    else { timer = null; $('btnPlay').textContent = 'Play'; }
  };
  tick();
}
function finish() {
  if (!prepare()) return;
  clearTimeout(timer); timer = null; $('btnPlay').textContent = 'Play';
  stepIdx = steps.length - 1; render();
}

/* ---------- drawing ---------- */
const edgeKey = (a, b) => Math.min(a, b) + '-' + Math.max(a, b);

function draw() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  const view = stepIdx >= 0 ? steps[stepIdx] : null;
  const path = view && view.path ? view.path : [];
  const pathEdges = new Set(path.slice(1).map((v, i) => edgeKey(path[i], v)));
  const src = Number($('src').value), dst = Number($('dst').value);

  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';

  edges.forEach(e => {
    const A = nodeById(e.a), B = nodeById(e.b);
    const onPath = pathEdges.has(edgeKey(e.a, e.b));
    const active = view && view.edge && edgeKey(view.edge[0], view.edge[1]) === edgeKey(e.a, e.b);
    ctx.strokeStyle = onPath ? '#2563eb' : active ? '#f59e0b' : '#94a3b8';
    ctx.lineWidth = onPath ? 6 : active ? 5 : 2.5;
    ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke();

    const mx = (A.x + B.x) / 2, my = (A.y + B.y) / 2;   // weight label with white background
    ctx.font = 'bold 14px Segoe UI, Arial';
    const tw = ctx.measureText(e.w).width + 10;
    ctx.fillStyle = '#fff'; ctx.fillRect(mx - tw / 2, my - 10, tw, 20);
    ctx.fillStyle = '#0f172a'; ctx.fillText(e.w, mx, my);
  });

  nodes.forEach(n => {
    let fill = '#fff';
    if (view) {
      if (path.includes(n.id)) fill = '#93c5fd';
      else if (view.current === n.id) fill = '#fbbf24';
      else if (view.visited.includes(n.id)) fill = '#bbf7d0';
    }
    ctx.beginPath(); ctx.arc(n.x, n.y, R, 0, Math.PI * 2);
    ctx.fillStyle = fill; ctx.fill();
    ctx.lineWidth = 3;
    ctx.strokeStyle = n.id === pending ? '#7c3aed' : n.id === src ? '#16a34a' : n.id === dst ? '#dc2626' : '#475569';
    ctx.stroke();

    ctx.fillStyle = '#0f172a'; ctx.font = 'bold 16px Segoe UI, Arial';
    ctx.fillText(n.label, n.x, n.y);
    if (view) {                                   // current distance under the node
      ctx.font = '12px Segoe UI, Arial'; ctx.fillStyle = '#475569';
      ctx.fillText('d=' + fmt(view.dist[n.id]), n.x, n.y + R + 12);
    }
  });
}

function render() {
  draw();
  const view = stepIdx >= 0 ? steps[stepIdx] : null;

  // distance table
  $('table').tBodies[0].innerHTML = nodes.map(n => {
    const d = view ? view.dist[n.id] : Infinity;
    const p = view && view.prev[n.id] !== null ? labelOf(view.prev[n.id]) : '–';
    const status = !view ? '–' : view.current === n.id ? 'Current' : view.visited.includes(n.id) ? 'Visited' : 'Waiting';
    const cls = status === 'Current' ? 'current' : status === 'Visited' ? 'visited' : '';
    return `<tr class="${cls}"><td><b>${n.label}</b></td><td>${fmt(d)}</td><td>${p}</td><td>${status}</td></tr>`;
  }).join('');

  // step log
  $('log').innerHTML = steps.slice(0, stepIdx + 1)
    .map((s, i) => `<li class="${i === stepIdx ? 'now' : ''}">${s.msg}</li>`).join('');
  $('log').scrollTop = $('log').scrollHeight;

  // result box
  if (view && view.path) {
    $('result').textContent = view.path.length
      ? `Shortest path: ${view.path.map(labelOf).join(' → ')}   |   Total distance: ${result.distance}`
      : `No path exists between the selected nodes.`;
  } else if (view) {
    $('result').textContent = `Running… step ${stepIdx + 1} of ${steps.length}`;
  } else {
    $('result').textContent = 'Build a graph, choose source & destination, then press Step or Play.';
  }
}

/* ---------- wire up buttons ---------- */
document.querySelectorAll('.tool').forEach(b => b.addEventListener('click', () => {
  tool = b.dataset.tool; pending = null;
  document.querySelectorAll('.tool').forEach(x => x.classList.toggle('active', x === b));
  setHint(hints[tool]); draw();
}));
$('btnSample').addEventListener('click', loadSample);
$('btnClear').addEventListener('click', () => { nodes = []; edges = []; nextId = 1; graphChanged(); setHint(hints[tool]); });
$('btnStep').addEventListener('click', () => { clearTimeout(timer); timer = null; $('btnPlay').textContent = 'Play'; stepForward(); });
$('btnPlay').addEventListener('click', play);
$('btnFinish').addEventListener('click', finish);
$('btnReset').addEventListener('click', resetRun);
$('src').addEventListener('change', resetRun);
$('dst').addEventListener('change', resetRun);

loadSample();
