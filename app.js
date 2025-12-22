
/* Minimal Online Client (server-authoritative)
   - Server steuert: Turn, Roll, Legals, Path, Barrikaden, Turnwechsel
   - Client: Zeichnen + UI + Animation
*/
const $ = (s)=>document.querySelector(s);

const canvas = $("#board");
const ctx = canvas.getContext("2d");

const ui = {
  btnRoll: $("#btnRoll"),
  dice: $("#dice"),
  turnLabel: $("#turnLabel"),
  hint: $("#hint"),

  serverUrl: $("#serverUrl"),
  roomCode: $("#roomCode"),
  playerName: $("#playerName"),
  btnHost: $("#btnHost"),
  btnJoin: $("#btnJoin"),
  btnLeave: $("#btnLeave"),
  btnStart: $("#btnStart"),

  netHint: $("#netHint"),
  playersList: $("#playersList"),
  netDebug: $("#netDebug"),
  netLog: $("#netLog"),
  btnCopyDiag: $("#btnCopyDiag"),
  btnClearLog: $("#btnClearLog"),
};

const SESSION_TOKEN_KEY = "barikade_session_v2";
function getSessionToken(){
  let t = localStorage.getItem(SESSION_TOKEN_KEY);
  if(!t){
    t = (crypto?.randomUUID?.() || (Math.random().toString(36).slice(2)+Date.now().toString(36))).slice(0,40);
    localStorage.setItem(SESSION_TOKEN_KEY, t);
  }
  return t;
}

const STATE = {
  board: null,
  nodes: new Map(),
  edges: [],
  adj: new Map(),
  view: { scale: 1, tx: 0, ty: 0, dpr: 1, min: 0.2, max: 3.0 },
  pointer: { dragging:false, lastX:0, lastY:0 },

  // synced from server
  started: false,
  paused: false,
  turnColor: "red",
  phase: "need_roll",   // need_roll | need_move | place_barricade
  rolled: null,
  pieces: [],
  barricades: new Set(),
  carrying: null, // color holding a barricade or null

  // local selection
  myColor: null,
  clientId: null,
  selectedPieceId: null,
  legalTargets: new Set(),
  legalPaths: new Map(), // nodeId -> path array
  anim: null, // {pieceId, pathIds, t0, i, a,b}
  net: { ws:null, url:"", room:"", name:"", connected:false, isHost:false },
};

const NET_LOG_MAX=80;
let NET_LOG=[];
function logNet(line){
  const ts = new Date().toLocaleTimeString();
  NET_LOG.push(`[${ts}] ${line}`);
  if(NET_LOG.length>NET_LOG_MAX) NET_LOG=NET_LOG.slice(-NET_LOG_MAX);
  ui.netLog.textContent = NET_LOG.join("\n") || "–";
}
function netHint(t){ ui.netHint.textContent = t; renderNetDebug(); }
function setHint(t){ ui.hint.textContent = t; }

function setDice(v){
  ui.dice.setAttribute("data-value", String(Number(v)||0));
}
function pill(color){
  const name = String(color||"").toUpperCase() || "–";
  return name;
}
function updateTurnLabel(){
  ui.turnLabel.textContent = `Dran: ${pill(STATE.turnColor)}`;
}
function renderPlayers(players){
  if(!players?.length){ ui.playersList.textContent="–"; return; }
  ui.playersList.innerHTML="";
  for(const p of players){
    const row=document.createElement("div");
    row.className="playerRow";
    const left=document.createElement("div");
    left.className="badge";
    const dot=document.createElement("span");
    dot.className="dotc "+(p.color||"red");
    const name=document.createElement("span");
    name.textContent = p.name || "Spieler";
    left.append(dot,name);

    const right=document.createElement("div");
    if(p.id===STATE.clientId){
      const me=document.createElement("span"); me.className="me"; me.textContent="DU";
      right.append(me);
    }else if(p.isHost){
      const h=document.createElement("span"); h.className="me"; h.textContent="HOST";
      right.append(h);
    }
    row.append(left,right);
    ui.playersList.append(row);
  }
}
function renderNetDebug(extra=""){
  ui.netDebug.textContent = [
    `connected: ${STATE.net.connected}`,
    `room: ${STATE.net.room||"-"}`,
    `meColor: ${STATE.myColor||"-"}`,
    `turn: ${STATE.turnColor||"-"}`,
    `phase: ${STATE.phase||"-"}`,
    `rolled: ${STATE.rolled ?? "-"}`,
    `paused: ${STATE.paused}`,
    extra
  ].filter(Boolean).join("\n");
}

function canAct(){
  if(!STATE.net.connected) return {ok:false, reason:"🔌 Nicht verbunden"};
  if(!STATE.started) return {ok:false, reason:"⏳ Nicht gestartet"};
  if(STATE.paused) return {ok:false, reason:"⏸️ pausiert"};
  if(!STATE.myColor) return {ok:false, reason:"👀 Zuschauer"};
  if(STATE.myColor !== STATE.turnColor) return {ok:false, reason:`⛔ Nicht dran (${pill(STATE.turnColor)})`};
  return {ok:true, reason:""};
}

// ---------- Board load ----------
async function loadBoard(){
  const res = await fetch("./board.json?v=FINAL", {cache:"no-store"});
  if(!res.ok) throw new Error("board.json load failed");
  const b = await res.json();
  STATE.board=b;
  STATE.nodes=new Map(); b.nodes.forEach(n=>STATE.nodes.set(n.id,n));
  STATE.edges=b.edges||[];
  STATE.adj=new Map();
  for(const [a,b2] of STATE.edges){
    if(!STATE.adj.has(a)) STATE.adj.set(a,new Set());
    if(!STATE.adj.has(b2)) STATE.adj.set(b2,new Set());
    STATE.adj.get(a).add(b2);
    STATE.adj.get(b2).add(a);
  }
}

// ---------- Render ----------
function resize(){
  const rect = canvas.getBoundingClientRect();
  const dpr = Math.max(1, Math.min(2, window.devicePixelRatio||1));
  STATE.view.dpr=dpr;
  canvas.width = Math.floor(rect.width*dpr);
  canvas.height = Math.floor(rect.height*dpr);
  draw();
}
function worldToScreen(x,y){
  const {scale,tx,ty,dpr}=STATE.view;
  return {x:(x*scale+tx)*dpr, y:(y*scale+ty)*dpr};
}
function screenToWorld(px,py){
  const {scale,tx,ty,dpr}=STATE.view;
  return {x:(px/dpr - tx)/scale, y:(py/dpr - ty)/scale};
}
function nodeR(){
  return 10;
}
function clear(){
  ctx.setTransform(1,0,0,1,0,0);
  ctx.clearRect(0,0,canvas.width,canvas.height);
}
function draw(){
  if(!STATE.board) return;
  clear();

  // edges
  ctx.lineWidth=2*STATE.view.dpr;
  ctx.strokeStyle="rgba(255,255,255,0.12)";
  for(const [a,b] of STATE.edges){
    const na=STATE.nodes.get(a), nb=STATE.nodes.get(b);
    if(!na||!nb) continue;
    const pa=worldToScreen(na.x,na.y), pb=worldToScreen(nb.x,nb.y);
    ctx.beginPath(); ctx.moveTo(pa.x,pa.y); ctx.lineTo(pb.x,pb.y); ctx.stroke();
  }

  // nodes
  for(const n of STATE.nodes.values()){
    const p=worldToScreen(n.x,n.y);
    const r=nodeR()*STATE.view.dpr;
    ctx.beginPath(); ctx.arc(p.x,p.y,r,0,Math.PI*2);
    let fill="rgba(255,255,255,0.06)";
    if(n.flags?.goal) fill="rgba(55,211,154,0.20)";
    if(n.flags?.startColor==="red") fill="rgba(255,77,109,0.22)";
    if(n.flags?.startColor==="blue") fill="rgba(90,167,255,0.22)";
    ctx.fillStyle=fill; ctx.fill();
    ctx.strokeStyle="rgba(255,255,255,0.18)"; ctx.stroke();
  }

  // legal target rings
  for(const id of STATE.legalTargets){
    const n=STATE.nodes.get(id); if(!n) continue;
    const p=worldToScreen(n.x,n.y);
    const r=(nodeR()+6)*STATE.view.dpr;
    ctx.beginPath(); ctx.arc(p.x,p.y,r,0,Math.PI*2);
    ctx.strokeStyle="rgba(90,167,255,0.85)";
    ctx.lineWidth=3*STATE.view.dpr;
    ctx.stroke();
  }

  // barricades
  for(const id of STATE.barricades){
    const n=STATE.nodes.get(id); if(!n) continue;
    const p=worldToScreen(n.x,n.y);
    const s=14*STATE.view.dpr;
    ctx.fillStyle="rgba(255,255,255,0.92)";
    ctx.fillRect(p.x - s/2, p.y - s/2, s, s);
    ctx.strokeStyle="rgba(0,0,0,0.35)";
    ctx.lineWidth=2*STATE.view.dpr;
    ctx.strokeRect(p.x - s/2, p.y - s/2, s, s);
  }

  // pieces (with animation override)
  for(const pc of STATE.pieces){
    let pos=null;
    if(STATE.anim && STATE.anim.pieceId===pc.id && STATE.anim.pos){
      pos=STATE.anim.pos;
    }else{
      pos=getPiecePos(pc);
    }
    if(!pos) continue;
    const p=worldToScreen(pos.x,pos.y);
    const r=11*STATE.view.dpr;
    ctx.beginPath(); ctx.arc(p.x,p.y,r,0,Math.PI*2);
    ctx.fillStyle = pc.color==="red" ? "rgba(255,77,109,1)" : "rgba(90,167,255,1)";
    ctx.fill();
    ctx.strokeStyle="rgba(0,0,0,0.4)"; ctx.lineWidth=2*STATE.view.dpr; ctx.stroke();

    // label
    ctx.fillStyle="rgba(0,0,0,0.75)";
    ctx.font=`${11*STATE.view.dpr}px ui-sans-serif`;
    ctx.textAlign="center"; ctx.textBaseline="middle";
    ctx.fillText(String(pc.label||""), p.x, p.y+0.5*STATE.view.dpr);
  }
}

function getPiecePos(pc){
  if(pc.posKind==="board" && pc.nodeId){
    const n=STATE.nodes.get(pc.nodeId); if(!n) return null;
    return {x:n.x,y:n.y};
  }
  // house: draw around its house node
  if(pc.posKind==="house" && pc.houseId){
    const h=STATE.nodes.get(pc.houseId); if(!h) return null;
    const idx=(pc.label||1)-1;
    const ang=(idx/5)*Math.PI*2;
    return {x:h.x + Math.cos(ang)*14, y:h.y + Math.sin(ang)*14};
  }
  return null;
}

// ---------- Input: pan/zoom + click ----------
function onWheel(ev){
  ev.preventDefault();
  const rect=canvas.getBoundingClientRect();
  const px=ev.clientX-rect.left, py=ev.clientY-rect.top;
  const before=screenToWorld(px*STATE.view.dpr, py*STATE.view.dpr);
  const factor=Math.exp(-ev.deltaY*0.0015);
  STATE.view.scale = Math.max(STATE.view.min, Math.min(STATE.view.max, STATE.view.scale*factor));
  const after=screenToWorld(px*STATE.view.dpr, py*STATE.view.dpr);
  STATE.view.tx += (after.x-before.x)*STATE.view.scale;
  STATE.view.ty += (after.y-before.y)*STATE.view.scale;
  draw();
}
function onPointerDown(ev){
  canvas.setPointerCapture?.(ev.pointerId);
  STATE.pointer.dragging=true;
  STATE.pointer.lastX=ev.clientX;
  STATE.pointer.lastY=ev.clientY;
}
function onPointerMove(ev){
  if(!STATE.pointer.dragging) return;
  const dx=ev.clientX-STATE.pointer.lastX;
  const dy=ev.clientY-STATE.pointer.lastY;
  STATE.pointer.lastX=ev.clientX; STATE.pointer.lastY=ev.clientY;
  STATE.view.tx += dx;
  STATE.view.ty += dy;
  draw();
}
function onPointerUp(){ STATE.pointer.dragging=false; }

function pickNode(world){
  let best=null, bestD=1e9;
  for(const n of STATE.nodes.values()){
    const dx=n.x-world.x, dy=n.y-world.y;
    const d=dx*dx+dy*dy;
    if(d<bestD){ bestD=d; best=n; }
  }
  const thr=(nodeR()*1.2); // world-ish, OK for your board scale
  if(best && bestD <= thr*thr) return best;
  return null;
}
function pickPiece(world){
  let best=null, bestD=1e9;
  for(const pc of STATE.pieces){
    if(pc.color!==STATE.myColor) continue;
    const pos=getPiecePos(pc); if(!pos) continue;
    const dx=pos.x-world.x, dy=pos.y-world.y;
    const d=dx*dx+dy*dy;
    if(d<bestD){ bestD=d; best=pc; }
  }
  const thr=(16); 
  if(best && bestD<=thr*thr) return best;
  return null;
}

async function onClick(ev){
  if(STATE.anim) return;
  const act=canAct();
  if(!act.ok){ setHint(act.reason); return; }

  const rect=canvas.getBoundingClientRect();
  const world=screenToWorld((ev.clientX-rect.left)*STATE.view.dpr, (ev.clientY-rect.top)*STATE.view.dpr);

  if(STATE.phase==="place_barricade"){
    const n=pickNode(world);
    if(!n){ setHint("Klick ein Feld"); return; }
    netSend({type:"place_barricade", nodeId:n.id});
    return;
  }

  if(STATE.phase!=="need_move"){
    setHint("Erst würfeln.");
    return;
  }

  // If click a piece -> request legals
  const pc=pickPiece(world);
  if(pc){
    STATE.selectedPieceId = pc.id;
    STATE.legalTargets.clear(); STATE.legalPaths.clear();
    draw();
    netSend({type:"legal_request", pieceId: pc.id});
    setHint("Legale Ziele laden…");
    return;
  }

  // If click on legal target -> move
  const n=pickNode(world);
  if(!n) return;
  if(!STATE.selectedPieceId){
    setHint("Klick zuerst eine Figur.");
    return;
  }
  if(!STATE.legalTargets.has(n.id)){
    setHint("Kein gültiges Ziel (blauer Ring).");
    return;
  }
  netSend({type:"move_request", pieceId: STATE.selectedPieceId, targetId: n.id});
  STATE.legalTargets.clear(); STATE.legalPaths.clear();
  draw();
}

// ---------- Networking ----------
function netSend(obj){
  const ws=STATE.net.ws;
  if(!ws || ws.readyState!==1) return;
  ws.send(JSON.stringify(obj));
  logNet(`→ ${obj.type}`);
}
function netConnect(){
  if(STATE.net.ws){ try{ STATE.net.ws.close(); }catch(_e){} }
  const url = STATE.net.url;
  netHint("Verbinde…");
  const ws = new WebSocket(url);
  STATE.net.ws=ws;

  ws.onopen=()=>{
    STATE.net.connected=true;
    ui.btnLeave.disabled=false;
    netHint("Verbunden.");
    logNet("ws open");
  };
  ws.onmessage=(ev)=>{
    try{
      const msg=JSON.parse(ev.data);
      logNet(`← ${msg.type}`);
      handleMsg(msg);
    }catch(e){
      logNet("bad message");
      console.warn(ev.data);
    }
  };
  ws.onclose=()=>{
    STATE.net.connected=false;
    STATE.started=false;
    STATE.myColor=null;
    ui.btnLeave.disabled=true;
    ui.btnStart.disabled=true;
    ui.btnRoll.disabled=true;
    netHint("Verbindung getrennt.");
    logNet("ws close");
  };
  ws.onerror=()=>{
    netHint("WS error");
    logNet("ws error");
  };
}

function applySnapshot(s){
  STATE.started=!!s.started;
  STATE.paused=!!s.paused;
  STATE.turnColor=s.turnColor||STATE.turnColor;
  STATE.phase=s.phase||STATE.phase;
  STATE.rolled = (s.rolled ?? null);
  STATE.carrying = s.carrying || null;
  STATE.pieces = Array.isArray(s.pieces) ? s.pieces : STATE.pieces;
  STATE.barricades = new Set(Array.isArray(s.barricades)?s.barricades:[]);
  updateTurnLabel();
  // roll button
  const act=canAct();
  ui.btnRoll.disabled = !(act.ok && STATE.phase==="need_roll");
  setHint(STATE.paused ? "⏸️ pausiert" : (act.ok ? "Du bist dran." : act.reason));
  draw();
}

function handleMsg(msg){
  if(msg.type==="hello"){
    STATE.clientId=msg.clientId;
    netHint("Verbunden. Raumcode eingeben → Host/Beitreten.");
    return;
  }
  if(msg.type==="room_update"){
    renderPlayers(msg.players||[]);
    const me = (msg.players||[]).find(p=>p.id===STATE.clientId);
    STATE.myColor = me?.color || null;
    STATE.net.isHost = !!me?.isHost;
    ui.btnStart.disabled = !(STATE.net.isHost && (msg.canStart===true));
    netHint(`Du bist ${STATE.myColor ? STATE.myColor.toUpperCase() : "ZUSCHAUER"}`);
    return;
  }
  if(msg.type==="snapshot"){
    applySnapshot(msg.state||{});
    return;
  }
  if(msg.type==="started"){
    applySnapshot(msg.state||{});
    netHint("Spiel gestartet.");
    return;
  }
  if(msg.type==="roll"){
    setDice(msg.value);
    applySnapshot(msg.state||{});
    return;
  }
  if(msg.type==="legal"){
    // {pieceId, targets:[id,...]}
    STATE.legalTargets = new Set(msg.targets||[]);
    setHint(STATE.legalTargets.size ? "Wähle ein Ziel (Ring)." : "Keine Ziele.");
    draw();
    return;
  }
  if(msg.type==="move"){
    // animate action.path then apply snapshot at end (server state already includes new positions)
    const action=msg.action||{};
    if(Array.isArray(action.path) && action.path.length>=1){
      startAnim(action.pieceId, action.path, msg.state);
      return;
    }
    applySnapshot(msg.state||{});
    return;
  }
  if(msg.type==="error"){
    setHint("Fehler: "+(msg.message||""));
    return;
  }
}

function startAnim(pieceId, pathIds, finalState){
  const pts = pathIds.map(id=>{
    const n=STATE.nodes.get(id);
    return n ? {x:n.x,y:n.y} : null;
  }).filter(Boolean);
  if(pts.length<1){ applySnapshot(finalState||{}); return; }

  const durStep = 220;
  let step=0;
  let from=pts[0];
  let to=pts[0];
  let t0=performance.now();
  if(pts.length>=2){ from=pts[0]; to=pts[1]; step=1; }

  STATE.anim = {pieceId, pts, step, from, to, t0, pos:{x:from.x,y:from.y}, finalState};
  function tick(){
    if(!STATE.anim) return;
    const a=STATE.anim;
    const now=performance.now();
    const tt=Math.min(1, (now-a.t0)/durStep);
    const e = tt<0.5 ? 4*tt*tt*tt : 1-Math.pow(-2*tt+2,3)/2;
    a.pos = {x: a.from.x + (a.to.x-a.from.x)*e, y: a.from.y + (a.to.y-a.from.y)*e};
    draw();
    if(tt>=1){
      if(a.step >= a.pts.length-1){
        STATE.anim=null;
        applySnapshot(a.finalState||{});
        return;
      }
      // next segment
      a.from=a.to;
      a.step++;
      a.to=a.pts[a.step];
      a.t0=performance.now();
    }
    requestAnimationFrame(tick);
  }
  requestAnimationFrame(tick);
}

// ---------- UI wiring ----------
async function copyDiag(){
  const diag={
    ts:new Date().toISOString(),
    url:location.href,
    ua:navigator.userAgent,
    net:{connected:STATE.net.connected, room:STATE.net.room, myColor:STATE.myColor, turn:STATE.turnColor, phase:STATE.phase, paused:STATE.paused, rolled:STATE.rolled},
    hint: ui.netHint.textContent,
    log: NET_LOG,
  };
  const txt=JSON.stringify(diag,null,2);
  try{ await navigator.clipboard.writeText(txt); netHint("✅ Debug kopiert"); }
  catch{ prompt("Kopieren:", txt); }
}

function initUI(){
  // defaults
  ui.serverUrl.value = window.BARIKADE_SERVER_URL || "wss://barikade-server.onrender.com";
  ui.playerName.value = localStorage.getItem("barikade_name") || "Christoph";
  ui.roomCode.value = localStorage.getItem("barikade_room") || "";

  ui.btnHost.onclick=()=>{
    STATE.net.url = ui.serverUrl.value.trim();
    STATE.net.room = ui.roomCode.value.trim().toUpperCase();
    STATE.net.name = ui.playerName.value.trim() || "Spieler";
    localStorage.setItem("barikade_room", STATE.net.room);
    localStorage.setItem("barikade_name", STATE.net.name);
    if(!STATE.net.url || !STATE.net.room){ netHint("Server + Raum nötig"); return; }
    netConnect();
    const send=()=>netSend({type:"join", room:STATE.net.room, name:STATE.net.name, asHost:true, sessionToken:getSessionToken()});
    setTimeout(send, 250);
  };
  ui.btnJoin.onclick=()=>{
    STATE.net.url = ui.serverUrl.value.trim();
    STATE.net.room = ui.roomCode.value.trim().toUpperCase();
    STATE.net.name = ui.playerName.value.trim() || "Spieler";
    localStorage.setItem("barikade_room", STATE.net.room);
    localStorage.setItem("barikade_name", STATE.net.name);
    if(!STATE.net.url || !STATE.net.room){ netHint("Server + Raum nötig"); return; }
    netConnect();
    const send=()=>netSend({type:"join", room:STATE.net.room, name:STATE.net.name, asHost:false, sessionToken:getSessionToken()});
    setTimeout(send, 250);
  };
  ui.btnLeave.onclick=()=>{
    try{ netSend({type:"leave"}); }catch(_e){}
    try{ STATE.net.ws?.close(); }catch(_e){}
  };
  ui.btnStart.onclick=()=>{ netSend({type:"start"}); };
  ui.btnRoll.onclick=()=>{
    const act=canAct();
    if(!act.ok){ setHint(act.reason); return; }
    netSend({type:"roll_request"});
  };
  ui.btnCopyDiag.onclick=copyDiag;
  ui.btnClearLog.onclick=()=>{ NET_LOG=[]; ui.netLog.textContent="–"; renderNetDebug(); };

  canvas.addEventListener("wheel", onWheel, {passive:false});
  canvas.addEventListener("pointerdown", onPointerDown);
  canvas.addEventListener("pointermove", onPointerMove);
  canvas.addEventListener("pointerup", onPointerUp);
  canvas.addEventListener("pointercancel", onPointerUp);
  canvas.addEventListener("click", onClick);

  window.addEventListener("resize", resize, {passive:true});
}

(async function main(){
  initUI();
  setHint("Lade board.json…");
  await loadBoard();
  resize();
  updateTurnLabel();
  setDice(0);
  setHint("Server eintragen → Host/Beitreten.");
  // ping
  setInterval(()=>{ if(STATE.net.ws?.readyState===1) netSend({type:"ping"}); }, 10000);
})();
