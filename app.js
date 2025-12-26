// app.js  (FULL FILE)
// - Fixes Chrome SVG variable issue by using NUMBERS for SVG geometry attrs
// - Keeps CSS variables only for colors (stroke/fill)
// - Computes isomorphism via brute-force perms (n<=8) and prints ONE mapping
// - Uses palette CSS vars --c1..--c8 (so dark mode can darken them in CSS)

let ISO_DB = null;

const title = document.getElementById("title");
const nLabel = document.getElementById("nLabel");
const slider = document.getElementById("nSlider");

const svgLeft  = document.getElementById("vizLeft");
const svgRight = document.getElementById("vizRight");

const edgeCount = document.getElementById("edgeCount");
const isoText = document.getElementById("isoText");
const isoKey  = document.getElementById("isoKey");
const mapText = document.getElementById("mapText");

let n = parseInt(slider.value, 10);
let selected = null;
const edges = new Set(); // "a-b" added edges (non-cycle)

// geometry per panel
const L = { cx: 260, cy: 220, R: 165 };
const Rg = { cx: 260, cy: 220, R: 165 };

// IMPORTANT: Chrome does NOT reliably support CSS vars in SVG geometry attributes.
// So keep these numeric:
const RIM_W = 8;
const EDGE_W = 6;
const V_R = 18;
const V_STROKE_W = 2.2;
const LABEL_FONT = 14;

function getPalette(){
  const cs = getComputedStyle(document.body);
  return [
    cs.getPropertyValue("--c1").trim(),
    cs.getPropertyValue("--c2").trim(),
    cs.getPropertyValue("--c3").trim(),
    cs.getPropertyValue("--c4").trim(),
    cs.getPropertyValue("--c5").trim(),
    cs.getPropertyValue("--c6").trim(),
    cs.getPropertyValue("--c7").trim(),
    cs.getPropertyValue("--c8").trim(),
  ];
}

function el(name, attrs = {}){
  const e = document.createElementNS("http://www.w3.org/2000/svg", name);
  for (const [k,v] of Object.entries(attrs)) e.setAttribute(k, String(v));
  return e;
}

function keyOf(a,b){ return `${Math.min(a,b)}-${Math.max(a,b)}`; }
function parseKey(k){ const [a,b]=k.split("-").map(Number); return {a,b}; }

function isCycleEdge(a,b,n){
  const d = Math.abs(a-b);
  return d===1 || d===n-1;
}

function polar(i, n, G){
  const ang = (-90 + (360*(i-1)/n)) * Math.PI/180;
  return { x: G.cx + G.R*Math.cos(ang), y: G.cy + G.R*Math.sin(ang) };
}

// build adjacency dict for (cycle + added edges)
function buildAdjFromEdges(edgeSet){
  const adj = {};
  for (let i=1;i<=n;i++) adj[String(i)] = [];

  // cycle edges
  for (let i=1;i<=n;i++){
    const j = (i % n) + 1;
    adj[String(i)].push(String(j));
    adj[String(j)].push(String(i));
  }

  // added edges
  for (const k of edgeSet){
    const {a,b} = parseKey(k);
    adj[String(a)].push(String(b));
    adj[String(b)].push(String(a));
  }

  // normalize
  for (let i=1;i<=n;i++){
    const v = String(i);
    adj[v] = Array.from(new Set(adj[v]))
      .map(String)
      .sort((x,y)=>Number(x)-Number(y));
  }
  return adj;
}

function drawGraph(svg, G, edgeSet, selectedVertex=null, clickable=false){
  svg.replaceChildren();
  const pts = Array.from({length:n}, (_,k)=>polar(k+1, n, G));
  const palette = getPalette();

  // rim
  svg.appendChild(el("circle",{
    cx: G.cx, cy: G.cy, r: G.R,
    fill: "none",
    stroke: "var(--rim)",
    "stroke-width": RIM_W
  }));

  // added edges
  for (const k of edgeSet){
    const {a,b} = parseKey(k);
    const A = pts[a-1], B = pts[b-1];
    svg.appendChild(el("line",{
      x1:A.x, y1:A.y, x2:B.x, y2:B.y,
      stroke:"var(--edge)",
      "stroke-width": EDGE_W,
      "stroke-linecap":"round"
    }));
  }

  // vertices
  for (let i=1;i<=n;i++){
    const p = pts[i-1];
    const g = el("g", {
      class: `${clickable ? "clickHint" : ""}${selectedVertex===i ? " selected" : ""}`
    });

    g.appendChild(el("circle",{
      class:"vCircle",
      cx:p.x, cy:p.y, r: V_R,
      fill: palette[(i-1) % palette.length],
      stroke:"var(--vStroke)",
      "stroke-width": V_STROKE_W
    }));

    // keep text centered even when circle scales (Chrome-safe)
    const t = el("text",{
      x:p.x, y:p.y,
      "text-anchor":"middle",
      "dominant-baseline":"middle",
      "font-size": LABEL_FONT,
      "font-weight":"850",
      fill:"var(--fg)",
      style:"pointer-events:none;"
    });
    t.textContent = String(i);
    g.appendChild(t);

    if (clickable){
      g.addEventListener("click", ()=>handleVertexClick(i));
    }

    svg.appendChild(g);
  }
}

// ---------- ISOMORPHISM (brute-force perms; n<=8) + RETURN ONE MAPPING ----------

function edgeCountFromAdj(adj){
  let sum = 0;
  for (const u of Object.keys(adj)){
    sum += (adj[u] || []).length;
  }
  return sum / 2;
}

function adjToMatrix(adj, n){
  const M = Array.from({length:n+1}, ()=>Array(n+1).fill(false));
  for (let u=1; u<=n; u++){
    const nbrs = adj[String(u)] || [];
    for (const vStr of nbrs){
      const v = Number(vStr);
      M[u][v] = true;
    }
  }
  return M;
}

function partialOk(p, idx, A, B){
  const k = idx + 1;
  for (let u=1; u<=k; u++){
    for (let v=1; v<=k; v++){
      if (A[u][v] !== B[p[u-1]][p[v-1]]) return false;
    }
  }
  return true;
}

// returns perm array if found, else null
function permuteFind(p, idx, A, B){
  const n = p.length;

  if (idx === n){
    for (let u=1; u<=n; u++){
      for (let v=1; v<=n; v++){
        if (A[u][v] !== B[p[u-1]][p[v-1]]) return null;
      }
    }
    return p.slice();
  }

  for (let i=idx; i<n; i++){
    [p[idx], p[i]] = [p[i], p[idx]];

    if (partialOk(p, idx, A, B)){
      const got = permuteFind(p, idx+1, A, B);
      if (got) return got;
    }

    [p[idx], p[i]] = [p[i], p[idx]];
  }
  return null;
}

// returns perm (length n) or null
function isomorphicMapping(adj1, adj2){
  const n1 = Object.keys(adj1).length;
  const n2 = Object.keys(adj2).length;
  if (n1 !== n2) return null;

  const e1 = edgeCountFromAdj(adj1);
  const e2 = edgeCountFromAdj(adj2);
  if (e1 !== e2) return null;

  const A = adjToMatrix(adj1, n1);
  const B = adjToMatrix(adj2, n1);

  const perm = Array.from({length:n1}, (_,i)=>i+1);
  return permuteFind(perm, 0, A, B);
}

function formatMapping(perm){
  if (!perm) return "";
  const parts = [];
  for (let i=1;i<=perm.length;i++){
    parts.push(`${i} ↦ ${perm[i-1]}`);
  }
  return parts.join(", ");
}

// build a Set of non-cycle edges "a-b" from an adjacency dict (to draw on the right)
function edgeSetFromAdj(adj){
  const s = new Set();
  const seen = new Set();
  for (const uStr of Object.keys(adj)){
    const u = Number(uStr);
    for (const vStr of (adj[uStr] || [])){
      const v = Number(vStr);
      const k = keyOf(u,v);
      if (seen.has(k)) continue;
      seen.add(k);
      if (!isCycleEdge(u, v, n)) s.add(k);
    }
  }
  return s;
}

// returns {matchIndex, matchedEdgeSet, perm} OR null (no edges)
function classify(){
  const k = edges.size;
  if (k === 0) return null;

  const nKey = String(n);
  const kKey = String(k);

  const bucket = ISO_DB?.[nKey]?.[kKey] || [];
  const curAdj = buildAdjFromEdges(edges);

  for (let i=0; i<bucket.length; i++){
    const candAdj = bucket[i];
    const perm = isomorphicMapping(curAdj, candAdj);
    if (perm){
      return {
        matchIndex: i,
        matchedEdgeSet: edgeSetFromAdj(candAdj),
        perm
      };
    }
  }

  return { matchIndex: -1, matchedEdgeSet: new Set(), perm: null };
}

function render(){
  title.textContent = `Cycle (outer rim) — n = ${n}`;
  nLabel.textContent = `n=${n}`;
  edgeCount.textContent = `${edges.size} edge${edges.size===1 ? "" : "s"}`;

  drawGraph(svgLeft, L, edges, selected, true);

  const res = classify();

  if (res === null){
    isoText.textContent = "";
    isoKey.textContent = "";
    svgRight.replaceChildren();
    mapText.textContent = "";
    return;
  }

  isoKey.textContent = `n=${n}, edges=${edges.size}`;

  if (res.matchIndex === -1){
    isoText.textContent = "None — new class found.";
    svgRight.replaceChildren();
    mapText.textContent = "";
    return;
  }

  isoText.textContent = `Class ${res.matchIndex + 1}`;
  drawGraph(svgRight, Rg, res.matchedEdgeSet, null, false);
  mapText.textContent = formatMapping(res.perm);
}

function handleVertexClick(i){
  if (selected === null){
    selected = i;
    render();
    return;
  }

  const a = selected, b = i;
  selected = null;

  if (a === b){ render(); return; }
  if (isCycleEdge(a, b, n)){ render(); return; }

  const k = keyOf(a,b);
  edges.has(k) ? edges.delete(k) : edges.add(k);
  render();
}

slider.addEventListener("input", (e)=>{
  n = parseInt(e.target.value, 10);

  for (const k of Array.from(edges)){
    const {a,b} = parseKey(k);
    if (a > n || b > n) edges.delete(k);
  }
  if (selected !== null && selected > n) selected = null;

  render();
});

document.getElementById("clearEdges").addEventListener("click", ()=>{
  edges.clear();
  selected = null;
  render();
});

document.getElementById("toggleTheme").addEventListener("click", ()=>{
  const root = document.body;
  root.dataset.theme = (root.dataset.theme === "dark") ? "light" : "dark";
  render(); // redraw so palette updates immediately
});

window.addEventListener("keydown", (e)=>{
  if (e.key === "Escape"){
    selected = null;
    render();
  }
});

async function loadDb(){
  try{
    const res = await fetch("./iso_db.json", { cache: "no-store" });
    if (!res.ok) throw new Error("Failed to load iso_db.json");
    ISO_DB = await res.json();
  }catch(_){
    ISO_DB = {};
  }
}

(async ()=>{
  await loadDb();
  render();
})();
