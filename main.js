// ═══════════════════════════════════════════════════════════════
// Canvas setup
// ═══════════════════════════════════════════════════════════════
const canvas = document.getElementById('c');
const ctx = canvas.getContext('2d');
let W = 600, H = 440;

function resize() {
  const wrap = document.getElementById('canvas-wrap');
  W = wrap.clientWidth || 600;
  H = wrap.clientHeight || 440;
  canvas.width = W;
  canvas.height = H;
  draw();
}
window.addEventListener('resize', () => resize());

// ═══════════════════════════════════════════════════════════════
// Graph topology — SCC, 9 nodes A–I, edges with raw weights
// ═══════════════════════════════════════════════════════════════
let nodes = [], edges = [];

function initGraph() {
  // Relative positions (rx, ry) normalized to canvas size
  nodes = [
    { id:0, label:'A', rx:.50, ry:.12, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:1, label:'B', rx:.18, ry:.34, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:2, label:'C', rx:.82, ry:.28, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:3, label:'D', rx:.10, ry:.62, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:4, label:'E', rx:.42, ry:.52, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:5, label:'F', rx:.72, ry:.58, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:6, label:'G', rx:.24, ry:.84, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:7, label:'H', rx:.56, ry:.83, state:'idle', blockchain:[], color:'#4a4a4e' },
    { id:8, label:'I', rx:.88, ry:.78, state:'idle', blockchain:[], color:'#4a4a4e' },
  ];

  // [from, to, rawWeight]  — w ∈ {1…9}
  // Forward edges (main propagation)
  const fwd = [
    [0,1,3],[0,2,7],[0,4,8],
    [1,3,2],[1,4,5],
    [2,4,4],[2,5,6],[2,8,9],
    [3,6,1],
    [4,5,3],[4,6,4],[4,7,5],
    [5,8,6],
    [6,7,2],
    [7,8,3],
  ];
  // Back edges (SCC closure — leaf nodes feed back to ensure full coverage from any origin)
  const back = [
    [8,5,4],[8,2,5],   // I→F, I→C
    [7,4,3],[7,0,6],   // H→E, H→A
    [6,3,2],[6,1,4],   // G→D, G→B
    [5,2,2],[5,4,3],   // F→C, F→E
    [3,1,3],           // D→B
    [4,0,5],           // E→A
    [1,0,4],           // B→A
  ];

  const all = [...fwd, ...back];
  const seen = new Set();
  edges = [];
  for (const [f,t,w] of all) {
    const key = `${f}-${t}`;
    if (!seen.has(key) && f !== t) {
      seen.add(key);
      edges.push({ from:f, to:t, raw:w, active:false, anim:0 });
    }
  }

  // Pre-compute peers (out-neighbors) for each node
  nodes.forEach(n => {
    n.peers = edges.filter(e => e.from === n.id).map(e => e.to);
  });
}

// Pixel positions
const NR = 22; // node radius
function nx(n) { return n.rx * W; }
function ny(n) { return n.ry * H; }

// ═══════════════════════════════════════════════════════════════
// Cryptography — Generalized Caesar Cipher
// F = B⁻¹[(B(A') + N' + M×P) mod 26]
// ═══════════════════════════════════════════════════════════════
function charCode(c)   { return c.charCodeAt(0) - 65; }
function fromCode(n)   { return String.fromCharCode(((n % 26) + 26) % 26 + 65); }

function encryptChar(c, nShift, M, P) {
  return fromCode(charCode(c) + nShift + M * P);
}
function decryptChar(c, nShift, M, P) {
  return fromCode(charCode(c) - nShift - M * P);
}
function encrypt(msg, nShift, M, P) {
  return msg.toUpperCase().replace(/[^A-Z]/g,'')
    .split('').map(c => encryptChar(c, nShift, M, P)).join('');
}
function decrypt(enc, nShift, M, P) {
  return enc.toUpperCase().replace(/[^A-Z]/g,'')
    .split('').map(c => decryptChar(c, nShift, M, P)).join('');
}

// ═══════════════════════════════════════════════════════════════
// Blockchain
// hashData(str) = (Σ B(cᵢ) for A–Z chars) mod 10
// hash_k = hash_{k-1} + hashData(data_k)
// ═══════════════════════════════════════════════════════════════
function hashData(str) {
  let s = 0;
  for (const c of str.toUpperCase()) {
    if (c >= 'A' && c <= 'Z') s += charCode(c);
  }
  return s % 10;
}

function mineBlock(chain, plain, encData, originId, hop) {
  const prev = chain.length > 0 ? chain[chain.length-1] : { hash: 0 };
  const h = prev.hash + hashData(plain);
  chain.push({
    index: chain.length,
    data: plain,
    encData,
    origin: originId,
    hop,
    prevHash: prev.hash,
    hash: h,
  });
}

// ═══════════════════════════════════════════════════════════════
// State
// ═══════════════════════════════════════════════════════════════
let msgCount = 0;
let selectedNode = null;
let activeTab = 'chain';
let logs = [];
let running = false;

// ═══════════════════════════════════════════════════════════════
// Logging
// ═══════════════════════════════════════════════════════════════
function logMsg(msg, type = 'ok') {
  const ts = new Date().toLocaleTimeString('pt-BR', { hour12: false });
  logs.unshift({ msg, type, ts });
  if (logs.length > 80) logs.pop();
  if (activeTab === 'log') renderLog();
}

// ═══════════════════════════════════════════════════════════════
// Dissemination — BFS with greedy out-degree priority
// delay(e) = ln(w(e)+1) × Δt  (ms)
// ═══════════════════════════════════════════════════════════════
const DT = 400; // Δt in ms — time scale constant

function disseminate(originId, plain, nShift, M, P) {
  running = true;
  document.getElementById('btn-send').disabled = true;

  msgCount++;
  const enc = encrypt(plain, nShift, M, P);
  const visited = new Set([originId]);

  const origin = nodes[originId];
  origin.state = 'origin';
  origin.color = '#1D9E75';
  mineBlock(origin.blockchain, plain, enc, originId, 0);
  logMsg(`Origem Nó ${origin.label} | plain="${plain}" enc="${enc}" key=(N'=${nShift} M=${M} P=${P})`, 'ok');
  updateStatus(visited.size);

  // Returns unvisited out-edges sorted by neighbor out-degree (desc)
  function sortedNeighbors(nid) {
    return edges
      .filter(e => e.from === nid && !visited.has(e.to))
      .sort((a,b) => nodes[b.to].peers.length - nodes[a.to].peers.length);
  }

  // BFS queue: { fromId, toId, edge, accDelay, hop }
  const queue = [];
  let baseDelay = 0;
  for (const e of sortedNeighbors(originId)) {
    visited.add(e.to);
    const d = Math.log(e.raw + 1) * DT;
    queue.push({ fromId: originId, toId: e.to, edge: e, accDelay: baseDelay + d, hop: 1 });
    baseDelay += d;
  }

  let qi = 0;
  let finalTime = 0;

  function processNext() {
    if (qi >= queue.length) return;
    const item = queue[qi++];
    const { fromId, toId, edge, accDelay, hop } = item;
    if (accDelay > finalTime) finalTime = accDelay;

    setTimeout(() => {
      const src = nodes[fromId];
      const dst = nodes[toId];

      edge.active = true;
      edge.anim = 0;

      if (src.state !== 'origin') { src.state = 'sending'; src.color = '#EF9F27'; }
      logMsg(`${src.label}→${dst.label} | enc="${enc}" ln(${edge.raw}+1)=${Math.log(edge.raw+1).toFixed(2)} hop=${hop}`, 'tx');

      // Animate packet along edge
      const duration = Math.log(edge.raw + 1) * DT * 0.85;
      let startTs = null;
      function animStep(ts) {
        if (!startTs) startTs = ts;
        edge.anim = Math.min((ts - startTs) / duration, 1);
        draw();
        if (edge.anim < 1) {
          requestAnimationFrame(animStep);
        } else {
          edge.active = false;
          edge.anim = 0;
          dst.state = 'received';
          dst.color = '#378ADD';
          mineBlock(dst.blockchain, plain, enc, originId, hop);
          const blk = dst.blockchain[dst.blockchain.length-1];
          logMsg(`Nó ${dst.label} ← bloco #${blk.index} | hash=${blk.hash} prevHash=${blk.prevHash}`, 'relay');
          updateStatus(visited.size);
          if (activeTab === 'chain' && selectedNode?.id === dst.id) renderChain(dst);
          if (activeTab === 'node'  && selectedNode?.id === dst.id) renderNode(dst);
          draw();
        }
      }
      requestAnimationFrame(animStep);

      // Enqueue unvisited neighbors of dst
      let localBase = accDelay;
      for (const ne of sortedNeighbors(toId)) {
        visited.add(ne.to);
        const nd = Math.log(ne.raw + 1) * DT;
        queue.push({ fromId: toId, toId: ne.to, edge: ne, accDelay: localBase + nd, hop: hop + 1 });
        localBase += nd;
        if (localBase > finalTime) finalTime = localBase;
      }
    }, item.accDelay);
  }

  // Drain queue (including dynamically added items)
  function drainQueue() {
    while (qi < queue.length) processNext();
    if (visited.size < nodes.length || qi < queue.length) {
      setTimeout(drainQueue, 60);
    } else {
      // Wait for animations to finish then re-enable button
      const remaining = Math.max(0, finalTime - Date.now() + performance.now()) + 1000;
      setTimeout(() => {
        running = false;
        document.getElementById('btn-send').disabled = false;
        logMsg(`Disseminação concluída — ${visited.size}/${nodes.length} nós cobertos`, 'sys');
        if (activeTab === 'log') renderLog();
      }, remaining);
    }
  }
  drainQueue();
}

// ═══════════════════════════════════════════════════════════════
// Drawing
// ═══════════════════════════════════════════════════════════════
function bezierPt(p0, p1, p2, t) {
  return (1-t)*(1-t)*p0 + 2*(1-t)*t*p1 + t*t*p2;
}

function draw() {
  ctx.clearRect(0, 0, W, H);

  // ── Edges ──
  for (const e of edges) {
    const f = nodes[e.from], t = nodes[e.to];
    const x1 = nx(f), y1 = ny(f), x2 = nx(t), y2 = ny(t);
    const dx = x2-x1, dy = y2-y1, len = Math.sqrt(dx*dx + dy*dy);
    if (len < 1) continue;
    const ux = dx/len, uy = dy/len;
    const sx = x1+ux*NR, sy = y1+uy*NR;
    const ex = x2-ux*(NR+4), ey = y2-uy*(NR+4);
    const cpx = (sx+ex)/2 - uy*18, cpy = (sy+ey)/2 + ux*18;

    const active = e.active;
    const edgeColor = active ? '#EF9F27' : 'rgba(136,135,128,0.20)';
    const lw = active ? 2 : Math.log(e.raw+1)*0.55 + 0.3;

    ctx.beginPath();
    ctx.moveTo(sx, sy);
    ctx.quadraticCurveTo(cpx, cpy, ex, ey);
    ctx.strokeStyle = edgeColor;
    ctx.lineWidth = lw;
    ctx.stroke();

    // Arrowhead
    const angle = Math.atan2(ey-cpy, ex-cpx);
    ctx.save();
    ctx.translate(ex, ey);
    ctx.rotate(angle);
    ctx.beginPath();
    ctx.moveTo(0,0); ctx.lineTo(-8,-3); ctx.lineTo(-8,3);
    ctx.closePath();
    ctx.fillStyle = edgeColor;
    ctx.fill();
    ctx.restore();

    // Weight label (ln(w+1))
    const mlx = bezierPt(sx, cpx, ex, 0.5) - uy*12;
    const mly = bezierPt(sy, cpy, ey, 0.5) + ux*12;
    ctx.fillStyle = active ? 'rgba(239,159,39,0.85)' : 'rgba(136,135,128,0.45)';
    ctx.font = '8px monospace';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(Math.log(e.raw+1).toFixed(1), mlx, mly);

    // Animated packet
    if (active && e.anim > 0 && e.anim < 1) {
      const px = bezierPt(sx, cpx, ex, e.anim);
      const py = bezierPt(sy, cpy, ey, e.anim);
      // Glow
      ctx.beginPath(); ctx.arc(px, py, 11, 0, Math.PI*2);
      ctx.fillStyle = 'rgba(239,159,39,0.15)'; ctx.fill();
      // Inner ring
      ctx.beginPath(); ctx.arc(px, py, 7, 0, Math.PI*2);
      ctx.fillStyle = 'rgba(239,159,39,0.30)'; ctx.fill();
      // Core
      ctx.beginPath(); ctx.arc(px, py, 4.5, 0, Math.PI*2);
      ctx.fillStyle = '#EF9F27'; ctx.fill();
    }
  }

  // ── Nodes ──
  for (const n of nodes) {
    const x = nx(n), y = ny(n);
    const isSel = selectedNode?.id === n.id;
    const r = NR + (isSel ? 3 : 0);

    // Shadow for selected
    if (isSel) {
      ctx.beginPath(); ctx.arc(x, y, r+6, 0, Math.PI*2);
      ctx.fillStyle = 'rgba(216,90,48,0.18)'; ctx.fill();
    }
    // Node body
    ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI*2);
    ctx.fillStyle = isSel ? '#D85A30' : n.color;
    ctx.fill();
    // Border
    ctx.strokeStyle = isSel ? '#993C1D' : 'rgba(255,255,255,0.12)';
    ctx.lineWidth = isSel ? 2 : 0.8;
    ctx.stroke();

    // Label
    ctx.fillStyle = '#fff';
    ctx.font = 'bold 13px monospace';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(n.label, x, y - 5);
    // Out-degree hint
    ctx.font = '8px monospace';
    ctx.fillStyle = 'rgba(255,255,255,0.55)';
    ctx.fillText(`${n.peers.length}→`, x, y + 7);

    // Blockchain block count badge
    if (n.blockchain.length > 0) {
      const bx = x + NR - 2, by = y - NR + 2;
      ctx.beginPath(); ctx.arc(bx, by, 9, 0, Math.PI*2);
      ctx.fillStyle = '#1D9E75'; ctx.fill();
      ctx.strokeStyle = 'rgba(0,0,0,0.5)'; ctx.lineWidth = 1; ctx.stroke();
      ctx.fillStyle = '#fff';
      ctx.font = 'bold 8px monospace';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(n.blockchain.length, bx, by);
    }
  }
}

// ═══════════════════════════════════════════════════════════════
// Panel rendering
// ═══════════════════════════════════════════════════════════════
function switchTab(t) {
  activeTab = t;
  document.querySelectorAll('.tab').forEach(el => {
    el.classList.toggle('active', el.dataset.tab === t);
  });
  renderPanel();
}

function renderPanel() {
  if (activeTab === 'chain') renderChain(selectedNode);
  else if (activeTab === 'node') renderNode(selectedNode);
  else renderLog();
}

function renderChain(node) {
  const pb = document.getElementById('panel-body');
  if (!node) {
    pb.innerHTML = '<div class="empty">Clique em um nó para ver sua blockchain.</div>';
    return;
  }
  const chain = node.blockchain;
  if (!chain.length) {
    pb.innerHTML = `<div class="empty">Nó ${node.label}: nenhum bloco ainda.</div>`;
    return;
  }
  let html = `<div style="font-weight:bold;font-size:11px;margin-bottom:8px">Nó ${node.label} — ${chain.length} bloco(s)</div>`;
  for (let i = 0; i < chain.length; i++) {
    const b = chain[i];
    const originLabel = nodes[b.origin]?.label ?? b.origin;
    html += `<div class="block-card">
      <div class="block-title">#${b.index}${i===0?' — genesis':''}</div>
      <div class="kv"><span class="k">plain</span><span class="v">${b.data}</span></div>
      <div class="kv"><span class="k">enc</span><span class="v">${b.encData}</span></div>
      <div class="kv"><span class="k">origem</span><span class="v">Nó ${originLabel}</span></div>
      <div class="kv"><span class="k">hop</span><span class="v">${b.hop}</span></div>
      <div class="kv"><span class="k">prevHash</span><span class="v prev">${b.prevHash}</span></div>
      <div class="kv"><span class="k">hash</span><span class="v hash">${b.hash}</span></div>
    </div>`;
    if (i < chain.length-1) html += '<div class="chain-link">↓ encadeado</div>';
  }
  pb.innerHTML = html;
}

function renderNode(node) {
  const pb = document.getElementById('panel-body');
  if (!node) {
    pb.innerHTML = '<div class="empty">Clique em um nó para inspecioná-lo.</div>';
    return;
  }
  const out = edges.filter(e => e.from === node.id);
  const inp = edges.filter(e => e.to === node.id);
  let html = `<div class="node-title">Nó ${node.label}</div>
    <div class="kv"><span class="k">estado</span><span class="v">${node.state}</span></div>
    <div class="kv"><span class="k">out-degree</span><span class="v">${out.length}</span></div>
    <div class="kv"><span class="k">in-degree</span><span class="v">${inp.length}</span></div>
    <div class="kv"><span class="k">blocos</span><span class="v">${node.blockchain.length}</span></div>`;

  if (out.length) {
    html += '<div class="section-label">Saídas</div>';
    for (const e of out) {
      html += `<div class="edge-row">
        <span class="edge-from">→ ${nodes[e.to].label}</span>
        <span class="edge-val">w=${e.raw} &nbsp; ln=${Math.log(e.raw+1).toFixed(2)}</span>
      </div>`;
    }
  }
  if (inp.length) {
    html += '<div class="section-label">Entradas</div>';
    for (const e of inp) {
      html += `<div class="edge-row">
        <span class="edge-from">← ${nodes[e.from].label}</span>
        <span class="edge-val">w=${e.raw} &nbsp; ln=${Math.log(e.raw+1).toFixed(2)}</span>
      </div>`;
    }
  }
  pb.innerHTML = html;
}

function renderLog() {
  const pb = document.getElementById('panel-body');
  if (!logs.length) {
    pb.innerHTML = '<div class="empty">Nenhum evento ainda.</div>';
    return;
  }
  let html = '';
  for (const l of logs) {
    html += `<div class="log-entry ${l.type}">[${l.ts}] ${l.msg}</div>`;
  }
  pb.innerHTML = html;
}

function updateStatus(covered) {
  const selEl = document.getElementById('s-sel');
  const covEl = document.getElementById('s-cov');
  const blkEl = document.getElementById('s-blocks');
  const msgEl = document.getElementById('s-msgs');
  selEl.textContent = selectedNode ? `Nó ${selectedNode.label}` : '—';
  const total = nodes.reduce((s,n) => s + n.blockchain.length, 0);
  blkEl.textContent = total;
  msgEl.textContent = msgCount;
  if (covered !== undefined) covEl.textContent = `${covered}/${nodes.length}`;
}

// ═══════════════════════════════════════════════════════════════
// Interaction
// ═══════════════════════════════════════════════════════════════
canvas.addEventListener('click', ev => {
  const r = canvas.getBoundingClientRect();
  const scaleX = canvas.width / r.width;
  const scaleY = canvas.height / r.height;
  const mx = (ev.clientX - r.left) * scaleX;
  const my = (ev.clientY - r.top)  * scaleY;
  let hit = null;
  for (const n of nodes) {
    const dx = nx(n) - mx, dy = ny(n) - my;
    if (Math.sqrt(dx*dx + dy*dy) < NR + 8) { hit = n; break; }
  }
  selectedNode = hit;
  updateStatus();
  renderPanel();
  draw();
});

document.querySelectorAll('.tab').forEach(btn => {
  btn.addEventListener('click', () => switchTab(btn.dataset.tab));
});

document.getElementById('btn-send').addEventListener('click', () => {
  if (!selectedNode) {
    alert('Selecione um nó de origem clicando no grafo.');
    return;
  }
  const rawMsg = document.getElementById('msg-input').value.toUpperCase().replace(/[^A-Z]/g,'');
  if (!rawMsg) {
    alert('Mensagem inválida — use apenas letras A–Z.');
    return;
  }
  const nShift = ((parseInt(document.getElementById('n-shift').value) || 0) % 26 + 26) % 26;
  const P = Math.max(1, parseInt(document.getElementById('p-key').value) || 1);
  const M = ((parseInt(document.getElementById('m-key').value) || 0) % 26 + 26) % 26;
  disseminate(selectedNode.id, rawMsg, nShift, M, P);
});

document.getElementById('btn-reset').addEventListener('click', () => {
  msgCount = 0;
  logs = [];
  selectedNode = null;
  running = false;
  document.getElementById('btn-send').disabled = false;
  initGraph();
  renderPanel();
  updateStatus(0);
  draw();
  logMsg('Sistema reiniciado.', 'sys');
  if (activeTab === 'log') renderLog();
});

// Input: force uppercase and strip non-alpha
document.getElementById('msg-input').addEventListener('input', function() {
  const pos = this.selectionStart;
  this.value = this.value.toUpperCase().replace(/[^A-Z]/g,'');
  this.setSelectionRange(pos, pos);
});

// ═══════════════════════════════════════════════════════════════
// Boot
// ═══════════════════════════════════════════════════════════════
initGraph();
setTimeout(resize, 0);
renderPanel();
updateStatus(0);
