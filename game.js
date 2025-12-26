(() => {
  const $ = (id) => document.getElementById(id);

  // ===== UI refs =====
  const canvas = $("c");
  const ctx = canvas.getContext("2d");
  const toastEl = $("toast");
  const netBannerEl = $("netBanner");

  const rollBtn = $("rollBtn");
  const endBtn  = $("endBtn");
  const skipBtn = $("skipBtn");
  const resetBtn= $("resetBtn");
  const diceEl  = $("diceCube");
  const turnText= $("turnText");
  const turnDot = $("turnDot");
  const turnPill = document.querySelector(".turnPill");
  const boardInfo = $("boardInfo");
  const barrInfo  = $("barrInfo");

  // Online
  const serverLabel = $("serverLabel");
  const roomCodeInp = $("roomCode");
  const hostBtn = $("hostBtn");
  const joinBtn = $("joinBtn");
  const leaveBtn= $("leaveBtn");
  const netStatus = $("netStatus");
  const netPlayersEl = $("netPlayers");
  const myColorEl = $("myColor");

  // Color picker
  const colorPickWrap = $("colorPick");
  const btnPickRed = $("pickRed");
  const btnPickBlue = $("pickBlue");
  const btnPickGreen = $("pickGreen");
  const btnPickYellow = $("pickYellow");

  // Overlay
  const overlay = $("overlay");
  const overlayTitle = $("overlayTitle");
  const overlaySub = $("overlaySub");
  const overlayHint = $("overlayHint");
  const overlayOk = $("overlayOk");

  const CSS = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
  const COLORS = {
    node: CSS("--node"), stroke: CSS("--stroke"),
    edge: CSS("--edge"),
    goal: CSS("--goal"), run: CSS("--run"),
    red: CSS("--red"), blue: CSS("--blue"), green: CSS("--green"), yellow: CSS("--yellow"),
  };

  const DEFAULT_PLAYERS = ["red","blue","green","yellow"];
  const PLAYER_NAME = {red:"Rot", blue:"Blau", green:"Grün", yellow:"Gelb"};

  let PLAYERS = ["red","blue"];
  function setPlayers(arg){
    if(Array.isArray(arg)){
      const order = {red:0, blue:1, green:2, yellow:3};
      const uniq=[], seen=new Set();
      for(const c of arg){
        if(!order.hasOwnProperty(c)) continue;
        if(seen.has(c)) continue;
        seen.add(c); uniq.push(c);
      }
      uniq.sort((a,b)=>order[a]-order[b]);
      PLAYERS = uniq.length ? uniq : ["red","blue"];
      return;
    }
    const n = Math.max(2, Math.min(4, Number(arg)||2));
    PLAYERS = DEFAULT_PLAYERS.slice(0, n);
  }

  // ===== Board =====
  let board=null, nodeById=new Map(), adj=new Map(), runNodes=new Set();
  let goalNodeId=null, startNodeId={red:null,blue:null,green:null,yellow:null};

  // Camera
  let dpr=1, view={x:40,y:40,s:1,_fittedOnce:false};

  const AUTO_CENTER_ALWAYS = true; // immer beim Start zentrieren (überschreibt gespeicherte Ansicht)
  let pointerMap=new Map(), isPanning=false, panStart=null;

  // ===== View persistence (Tablet-safe) =====
  const VIEW_KEY = "barikade_view_v2";
  let lastTapTs = 0;
  let lastTapPos = null;

  function saveView(){
    try{
      const data = { x:view.x, y:view.y, s:view.s, ts:Date.now() };
      localStorage.setItem(VIEW_KEY, JSON.stringify(data));
    }catch(_e){}
  }
  function loadView(){
    try{
      const raw = localStorage.getItem(VIEW_KEY);
      if(!raw) return false;
      const v = JSON.parse(raw);
      if(!v || typeof v!=="object") return false;
      if(typeof v.x!=="number" || typeof v.y!=="number" || typeof v.s!=="number") return false;
      // sanity
      if(!(v.s>0.05 && v.s<20)) return false;
      view.x = v.x; view.y = v.y; view.s = v.s;
      view._fittedOnce = true; // we have an explicit view
      return true;
    }catch(_e){ return false; }
  }
  function clearView(){
    try{ localStorage.removeItem(VIEW_KEY); }catch(_e){}
    view._fittedOnce = false;
  }

  // ===== Game state =====
  let phase = "need_roll";            // need_roll | need_move | placing_barricade | game_over
  let legalTargets = [];
  let placingChoices = [];

  function setPhase(p){ phase=p; if(state) state.phase=p; }
  function setPlacingChoices(arr){
    placingChoices = Array.isArray(arr) ? arr : [];
    if(state) state.placingChoices = [...placingChoices];
  }

  let selected=null;
  let legalMovesAll=[];
  let legalMovesByPiece=new Map();
  let state=null;

  // ===== FX (safe, visual only) =====

  // Turn UI helpers (visual only)
  const TURN_EMOJI = { red:"🔴", blue:"🔵", green:"🟢", yellow:"🟡" };

  // Landing FX (visual only)
  let landFxs = [];
  let lastDiceFace = 0;
  let lastMoveFx = null;
  let moveGhostFx = null;

  // Smooth animation loop (visual only). Runs only while FX are active.
  let _rafId = 0;
  function _hasActiveFx(now){
    if(moveGhostFx && (now - moveGhostFx.t0) < moveGhostFx.dur) return true;
    if(lastMoveFx && (now - lastMoveFx.t0) < 900) return true;
    if(landFxs && landFxs.length) return true;
    return false;
  }
  function ensureAnimLoop(){
    if(_rafId) return;
    const raf = window.requestAnimationFrame || (cb=>setTimeout(()=>cb(performance.now()), 16));
    const caf = window.cancelAnimationFrame || (id=>clearTimeout(id));
    const tick = (tNow)=>{
      const now = (typeof tNow==="number") ? tNow : performance.now();
      if(!_hasActiveFx(now)){
        caf(_rafId);
        _rafId = 0;
        return;
      }
      try{ draw(); }catch(_e){}
      _rafId = raf(tick);
    };
    _rafId = raf(tick);
  }


  // ===== Online =====
  const SERVER_URL = "wss://serverfinal-9t39.onrender.com";
  if(serverLabel) serverLabel.textContent = SERVER_URL;

  let ws=null;
  let netMode="offline";    // offline | host | client
  let roomCode="";
  let clientId="";
  let lastNetPlayers=[];
  let rosterById=new Map();
  let myColor=null;

  let reconnectTimer=null;
  let reconnectAttempt=0;
  let pendingIntents=[];

  function randId(len=10){
    const chars="ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
    let s=""; for(let i=0;i<len;i++) s += chars[Math.floor(Math.random()*chars.length)];
    return s;
  }
  function normalizeRoomCode(s){
    return (s||"").toUpperCase().replace(/[^A-Z0-9]/g,"").slice(0,10);
  }
  function safeJsonParse(s){ try{ return JSON.parse(s); }catch(_e){ return null; } }

  function setNetStatus(text, good){
    if(!netStatus) return;
    netStatus.textContent = text;
    netStatus.style.color = good ? "var(--green)" : "var(--muted)";
  }

  function wsSend(obj){
    if(!ws || ws.readyState!==1) return false;
    try{ ws.send(JSON.stringify(obj)); return true; }catch(_e){ return false; }
  }

  function setNetPlayers(list){
    lastNetPlayers = Array.isArray(list) ? list : [];
    rosterById = new Map();
    for(const p of lastNetPlayers){ if(p && p.id) rosterById.set(p.id, p); }

    const me = rosterById.get(clientId);
    myColor = (me && me.color) ? me.color : null;

    if(myColorEl){
      myColorEl.textContent = myColor ? PLAYER_NAME[myColor] : "–";
      myColorEl.style.color = myColor ? COLORS[myColor] : "var(--muted)";
    }
    if(colorPickWrap){
      colorPickWrap.style.display = (netMode!=="offline" && !myColor) ? "block" : "none";
    }

    // Host: keep state players in sync with chosen colors
    if(netMode==="host" && state){
      const active = getActiveColors();
      const prev = Array.isArray(state.players) ? state.players : [];
      const same = prev.length===active.length && prev.every((c,i)=>c===active[i]);
      if(!same){
        setPlayers(active);
        state.players = [...PLAYERS];
        state.pieces = state.pieces || {};
        for(const c of PLAYERS){
          if(!state.pieces[c]) state.pieces[c] = Array.from({length:5},()=>({pos:"house"}));
        }
        if(!state.players.includes(state.currentPlayer)){
          state.currentPlayer = state.players[0];
          setPhase("need_roll");
          state.dice=null;
        }
        broadcastState("snapshot");
      }
    }

    if(netPlayersEl){
      if(!lastNetPlayers.length){ netPlayersEl.textContent="–"; return; }
      const parts = lastNetPlayers.map(p=>{
        const name = p.name || p.id || "Spieler";
        const role = p.role ? `(${p.role})` : "";
        const col  = p.color ? `· ${PLAYER_NAME[p.color]}` : "";
        const con  = (p.connected===false) ? " ✖" : " ✔";
        return `${name} ${role} ${col}${con}`;
      });
      netPlayersEl.textContent = parts.join(" · ");
    }
  }

  function scheduleReconnect(){
    if(reconnectTimer) return;
    reconnectAttempt++;
    const delay = Math.min(12000, 600 * Math.pow(1.6, reconnectAttempt));
    setNetStatus(`Reconnect in ${Math.round(delay/1000)}s…`, false);
    reconnectTimer = setTimeout(()=>{ reconnectTimer=null; connectWS(); }, delay);
  }
  function stopReconnect(){
    if(reconnectTimer){ clearTimeout(reconnectTimer); reconnectTimer=null; }
    reconnectAttempt = 0;
  }

  function connectWS(){
    if(!roomCode) return;
    if(ws && (ws.readyState===0 || ws.readyState===1)) return;

    setNetStatus("Verbinden…", false);
    
    view._fittedOnce = false;
try{ ws = new WebSocket(SERVER_URL); }
    catch(_e){ setNetStatus("WebSocket nicht möglich", false); scheduleReconnect(); return; }

    ws.onopen = () => {
      stopReconnect();
      hideNetBanner();
      setNetStatus("Verbunden – join…", true);

      const sessionToken = getSessionToken();
      wsSend({
        type: "join",
        room: roomCode,
        name: (netMode === "host" ? "Host" : "Client"),
        asHost: (netMode === "host"),
        sessionToken,
        ts: Date.now()
      });
    };

    ws.onmessage = (ev) => {
      const msg = (typeof ev.data==="string") ? safeJsonParse(ev.data) : null;
      if(!msg) return;
      const type = msg.type;

      if(type==="hello"){
        if(msg.clientId) clientId = msg.clientId;
        return;
      }
      if(type==="room_update"){
        if(Array.isArray(msg.players)) setNetPlayers(msg.players);
        // Auto-start when host and 2 players present
        if(netMode==="host" && msg.canStart){
          wsSend({type:"start", ts:Date.now()});
        }
        return;
      }
      if(type==="snapshot" || type==="started" || type==="place_barricade"){
        if(msg.state) applyRemoteState(msg.state);
        if(Array.isArray(msg.players)) setNetPlayers(msg.players);
        return;
      }
      if(type==="roll"){
        // (108/26) small suspense + particles
        if(typeof msg.value==="number") setDiceFaceAnimated(msg.value);
        if(msg.state) applyRemoteState(msg.state);
        if(Array.isArray(msg.players)) setNetPlayers(msg.players);
        return;
      }
      if(type==="move"){
        // (7/8/109) animate path + destination glow
        if(msg.action) queueMoveFx(msg.action);
        if(msg.state) applyRemoteState(msg.state);
        if(Array.isArray(msg.players)) setNetPlayers(msg.players);
        return;
      }
      if(type==="error"){
        toast(msg.message || "Server-Fehler");
        return;
      }
      if(type==="pong") return;
    };

    ws.onerror = () => { setNetStatus("Fehler – Reconnect…", false); showNetBanner("Verbindungsfehler – Reconnect läuft…"); };
    ws.onclose = () => {
      setNetStatus("Getrennt – Reconnect…", false);
      showNetBanner("Verbindung getrennt – Reconnect läuft…");
      if(netMode!=="offline") scheduleReconnect();
    };
  }

  function disconnectWS(){
    stopReconnect();
    if(ws){
      try{ ws.onopen=ws.onmessage=ws.onerror=ws.onclose=null; ws.close(); }catch(_e){}
      ws=null;
    }
    setNetStatus("Offline", false);
    hideNetBanner();
  }

  function saveSession(){
    try{
      localStorage.setItem("barikade_room", roomCode||"");
      localStorage.setItem("barikade_mode", netMode||"offline");
      localStorage.setItem("barikade_clientId", clientId||"");
    }catch(_e){}
  }
  function loadSession(){
    try{
      return {
        r: localStorage.getItem("barikade_room")||"",
        m: localStorage.getItem("barikade_mode")||"offline",
        id: localStorage.getItem("barikade_clientId")||""
      };
    }catch(_e){ return {r:"", m:"offline", id:""}; }
  }

  // Server uses sessionToken to reconnect a "slot" (same color) after refresh.
  function getSessionToken(){
    try{
      let t = localStorage.getItem("barikade_sessionToken") || "";
      if(!t){
        t = "S-" + randId(16);
        localStorage.setItem("barikade_sessionToken", t);
      }
      return t;
    }catch(_e){
      return "S-" + randId(16);
    }
  }

  function chooseColor(_color){
    toast("Farbe wird vom Server automatisch vergeben");
  }

  function getActiveColors(){
    if(netMode==="offline") return [...PLAYERS];
    const order=["red","blue","green","yellow"];
    const colors=[], seen=new Set();
    for(const p of lastNetPlayers){
      if(!p || !p.color) continue;
      if(seen.has(p.color)) continue;
      seen.add(p.color);
      colors.push(p.color);
    }
    colors.sort((a,b)=>order.indexOf(a)-order.indexOf(b));
    return colors.length>=2 ? colors : ["red","blue"];
  }

  // ===== State sync =====
  function applyRemoteState(remote){
    const st = (typeof remote==="string") ? safeJsonParse(remote) : remote;
    if(!st || typeof st!=="object") return;

    // --- Server-state adapter (serverfinal protocol) ---
    // server state: {turnColor, phase, rolled, pieces:[{id,color,posKind,houseId,nodeId}], barricades:[...], goal}
    if(st.turnColor && Array.isArray(st.pieces) && Array.isArray(st.barricades)){
      const server = st;
      const players = ["red","blue"];
      setPlayers(players);
      const piecesByColor = {red:[], blue:[], green:[], yellow:[]};
      // ensure 5 slots per color
      for(const c of players) piecesByColor[c] = Array.from({length:5}, ()=>({pos:"house"}));

      for(const pc of server.pieces){
        if(!pc || (pc.color!=="red" && pc.color!=="blue")) continue;
        // pc.label is 1..5
        const idx = Math.max(0, Math.min(4, Number(pc.label||1)-1));
        let pos = "house";
        if(pc.posKind==="board" && pc.nodeId) pos = String(pc.nodeId);
        else if(pc.posKind==="goal") pos = "goal";
        else pos = "house";
        piecesByColor[pc.color][idx] = {pos, pieceId: pc.id};
      }

      state = {
        players,
        currentPlayer: server.turnColor,
        dice: (server.rolled==null ? null : Number(server.rolled)),
        phase: server.phase,
        placingChoices: [],
        pieces: {red:piecesByColor.red, blue:piecesByColor.blue},
        barricades: new Set(server.barricades.map(String)),
        winner: null,
        goalNodeId: server.goal ? String(server.goal) : goalNodeId
      };

      // map phases
      const ph = server.phase;
      if(ph==="need_roll") phase="need_roll";
      else if(ph==="need_move") phase="need_move";
      else if(ph==="place_barricade") phase="placing_barricade";
      else if(ph==="anim") phase="anim";
      else phase="need_roll";

      // show dice
      setDiceFaceAnimated(state.dice==null ? 0 : Number(state.dice));
      if(barrInfo) barrInfo.textContent = String(state.barricades.size);

      // in online mode we let the server validate moves, so don't compute legalTargets
      legalTargets = [];
      legalMovesAll = [];
      legalMovesByPiece = new Map();
      placingChoices = [];
      updateTurnUI(); draw();
      ensureFittedOnce();
      return;
    }

    if(st.barricades && Array.isArray(st.barricades)) st.barricades = new Set(st.barricades);
    state = st;

    if(st.players && Array.isArray(st.players) && st.players.length>=2) setPlayers(st.players);

    if(typeof st.phase === "string") phase = st.phase;
    else phase = st.winner ? "game_over" : (st.dice==null ? "need_roll" : "need_move");

    placingChoices = Array.isArray(st.placingChoices) ? st.placingChoices : [];

    if(phase==="need_move" && st.dice!=null && !st.winner){
      legalMovesAll = computeLegalMoves(st.currentPlayer, st.dice);
      legalMovesByPiece = new Map();
      for(const m of legalMovesAll){
        const idx = m.piece.index;
        if(!legalMovesByPiece.has(idx)) legalMovesByPiece.set(idx, []);
        legalMovesByPiece.get(idx).push(m);
      }
      legalTargets = legalMovesAll;
    }else{
      legalTargets = [];
      legalMovesAll = [];
      legalMovesByPiece = new Map();
      if(phase!=="placing_barricade") selected=null;
    }

    if(barrInfo) barrInfo.textContent = String(state.barricades?.size ?? 0);
    setDiceFaceAnimated(state.dice==null ? 0 : Number(state.dice));
    updateTurnUI(); draw();
      ensureFittedOnce();
  }

  function serializeState(){
    const st = JSON.parse(JSON.stringify(state));
    if(state.barricades instanceof Set) st.barricades = Array.from(state.barricades);
    st.players = state?.players ? [...state.players] : [...PLAYERS];
    st.phase = phase;
    st.placingChoices = Array.isArray(placingChoices) ? [...placingChoices] : [];
    return st;
  }

  function broadcastState(kind="state"){
    if(netMode!=="host") return;
    wsSend({type:kind, room:roomCode, state:serializeState(), ts:Date.now()});
  }

  function sendIntent(intent){
    const msg = {type:"intent", room:roomCode, clientId, intent, ts:Date.now()};
    if(!wsSend(msg)) pendingIntents.push(msg);
  }

  // ===== Game =====
  function toast(msg){
    if(!toastEl) return;
    toastEl.textContent=msg;
    toastEl.classList.add("show");
    clearTimeout(toastEl._t);
    toastEl._t=setTimeout(()=>toastEl.classList.remove("show"), 1200);
  }


  // ===== Visual helpers (safe) =====
  function showNetBanner(text){
    if(!netBannerEl) return;
    netBannerEl.textContent = text || "";
    netBannerEl.classList.add("show");
  }
  function hideNetBanner(){
    if(!netBannerEl) return;
    netBannerEl.classList.remove("show");
  }

  function spawnDiceParticles(){
    if(!diceEl) return;
    const host = diceEl.parentElement;
    if(!host) return;
    const rect = diceEl.getBoundingClientRect();
    const hostRect = host.getBoundingClientRect();
    const cx = (rect.left - hostRect.left) + rect.width/2;
    const cy = (rect.top - hostRect.top) + rect.height/2;

    const count = 12;
    for(let i=0;i<count;i++){
      const el = document.createElement("div");
      el.className = "diceParticle";
      el.style.left = (cx-3) + "px";
      el.style.top  = (cy-3) + "px";
      const ang = Math.random()*Math.PI*2;
      const dist = 14 + Math.random()*20;
      const dx = Math.cos(ang)*dist;
      const dy = Math.sin(ang)*dist;
      el.style.setProperty("--dx", dx.toFixed(1) + "px");
      el.style.setProperty("--dy", dy.toFixed(1) + "px");
      host.appendChild(el);
      setTimeout(()=>{ try{ el.remove(); }catch(_e){} }, 650);
    }
  }

  function setDiceFaceAnimated(v){
    if(!diceEl) return;
    const face = (v>=1 && v<=6) ? v : 0;
    if(face===0){
      diceEl.dataset.face = "0";
      lastDiceFace = 0;
      return;
    }

    // avoid spamming if same face
    if(face === lastDiceFace) return;
    lastDiceFace = face;

    // (108) jitter before showing result
    diceEl.classList.remove("shake");
    void diceEl.offsetWidth; // restart animation
    diceEl.classList.add("shake");

    // (26) particles
    spawnDiceParticles();

    // show result slightly delayed for suspense
    setTimeout(()=>{
      if(diceEl) diceEl.dataset.face = String(face);
      if(diceEl) diceEl.classList.remove("shake");
    }, 280);
  }

  function parseColorFromPieceId(pieceId){
    const s = String(pieceId||"");
    // expected: p_red_1, p_blue_3 ...
    if(s.includes("red")) return "red";
    if(s.includes("blue")) return "blue";
    if(s.includes("green")) return "green";
    if(s.includes("yellow")) return "yellow";
    return null;
  }


  // ===== Small animation helpers (visual only) =====
  function easeOutQuad(t){ t = Math.max(0, Math.min(1, t)); return 1 - (1-t)*(1-t); }

  function buildGhostWeights(pts){
    // weights based on segment length; last step gets extra drama
    const segN = Math.max(0, (pts?.length||0) - 1);
    const w = [];
    for(let i=0;i<segN;i++){
      const a=pts[i], b=pts[i+1];
      const d = Math.hypot((b.x-a.x),(b.y-a.y));
      w.push(Math.max(0.001, d));
    }
    if(segN>=1) w[segN-1] *= 1.7;      // last step slower
    if(segN>=2) w[segN-2] *= 1.25;     // penultimate a bit slower
    let sum = 0;
    const cum = w.map(v => (sum += v));
    return {w, cum, total: sum || 1};
  }

  function sampleGhostAt(pts, weights, f){
    // f: 0..1 across total weighted length
    const segN = (pts?.length||0) - 1;
    if(segN <= 0) return {x:pts?.[0]?.x||0, y:pts?.[0]?.y||0, idx:0, localT:0};
    const w = weights?.w, cum = weights?.cum, total = weights?.total || 1;
    const tlen = Math.max(0, Math.min(1, f)) * total;
    let i = 0;
    while(i < segN-1 && cum && cum[i] < tlen) i++;
    const prev = i===0 ? 0 : (cum[i-1] || 0);
    const segW = (w && w[i]) ? w[i] : 1;
    const localT = segW ? ((tlen - prev) / segW) : 0;
    const a = pts[i], b = pts[i+1];
    const lt = Math.max(0, Math.min(1, localT));
    return {x: a.x + (b.x-a.x)*lt, y: a.y + (b.y-a.y)*lt, idx:i, localT:lt};
  }

  // Find a client-side piece (color/index/pos) by server pieceId.
  function findClientPieceById(pieceId){
    const pid = String(pieceId||"");
    if(!pid || !state?.pieces) return null;
    for(const c of (state.players || PLAYERS)){
      const arr = state.pieces[c];
      if(!Array.isArray(arr)) continue;
      for(let i=0;i<arr.length;i++){
        if(arr[i]?.pieceId === pid) return {color:c, index:i, pos: arr[i].pos};
      }
    }
    return null;
  }

  // Piece animation overrides: pieceId -> {pts, weights, t0, dur, color}
  let movingPiecesFx = new Map();


  // Step-by-step animation sampler: moves segment by segment with a short land pause on each node.
  // ===== Move animation tuning (Option A: technisch/sauber) =====
  const MOVE_STEP_MS = 230;   // travel time per field (ms)
  const MOVE_HOLD_MS = 130;   // pause on each field (ms)
  const MOVE_HOP_PX  = 26;    // hop height (px)
  const MOVE_LAND_BOUNCE_PX = 8; // landing bounce (px)
  const MOVE_TIMING_JITTER = false; // optional: tiny speed variation (off)

  function sampleStepGhostAt(fx, now){
    const pts = fx.pts || [];
    const segN = Math.max(0, pts.length - 1);
    if(segN <= 0) return {x: pts?.[0]?.x||0, y: pts?.[0]?.y||0, idx:0, local:0, inHold:false, holdT:0};

    const travelBase = Math.max(80, fx.stepMs || MOVE_STEP_MS);
    const hold = Math.max(0, fx.holdMs ?? MOVE_HOLD_MS);

    const travel = (MOVE_TIMING_JITTER && typeof fx._jitterMs==="number")
      ? Math.max(80, travelBase + fx._jitterMs)
      : travelBase;

    const per = travel + hold;
    const elapsed = Math.max(0, now - fx.t0);
    const total = segN * per;
    const clamped = Math.min(elapsed, Math.max(0, total - 1e-6));

    const idx = Math.max(0, Math.min(segN-1, Math.floor(clamped / per)));
    const u = clamped - idx * per;

    const a = pts[idx], b = pts[idx+1];
    const inHold = (u >= travel);
    const local = inHold ? 1 : (u / travel);
    const holdT = (inHold && hold>0) ? Math.max(0, Math.min(1, (u - travel) / hold)) : 0;

    let x = a.x + (b.x - a.x) * local;
    let y = a.y + (b.y - a.y) * local;

    const hopAmp = (fx.hopPx != null) ? fx.hopPx : MOVE_HOP_PX;

    if(!inHold){
      y -= Math.sin(local * Math.PI) * hopAmp;
    }else{
      const k = Math.max(0, 1 - holdT);
      const bounce = Math.sin((1 - holdT) * Math.PI) * k * (fx.landBouncePx ?? MOVE_LAND_BOUNCE_PX);
      y -= bounce;
    }

    return {x,y,idx,local,inHold,holdT,a,b};
  }


  function queueMoveFx(action){
    if(!action || !board) return;
    const pathRaw = Array.isArray(action.path) ? action.path.map(String) : [];
    const pid = String(action.pieceId||"");
    if(!pid || pathRaw.length < 1) return;

    // If the piece comes from house, server path starts at the start-field.
    // We prepend the current house node (client knows it via color/index).
    const before = findClientPieceById(pid);
    const color = parseColorFromPieceId(pid) || before?.color || null;

    const fullPath = [...pathRaw];
    if(before && before.pos === "house" && fullPath.length >= 1){
      // locate house node for that slot
      const slot = (before.index ?? 0) + 1;
      let houseNodeId = null;
      for(const n of (board.nodes||[])){
        if(n.kind!=="house") continue;
        if(String(n.flags?.houseColor||"") !== String(before.color)) continue;
        if(Number(n.flags?.houseSlot||0) !== slot) continue;
        houseNodeId = n.id; break;
      }
      if(houseNodeId) fullPath.unshift(String(houseNodeId));
    }

    // Build screen points
    const pts=[];
    for(const id of fullPath){
      const n = nodeById.get(String(id));
      if(!n) continue;
      const s = worldToScreen(n);
      pts.push({x:s.x, y:s.y, id:String(id)});
    }
    if(pts.length < 2) return;

    const now = performance.now();
    const steps = Math.max(1, pts.length - 1);

    // weights based on distance (and last step drama) for the REAL piece animation
    const weights = buildGhostWeights(pts);

    // Per-field stepping: travel + short land pause so you can SEE each field being entered.
    const stepMs = MOVE_STEP_MS;   // travel time per field
    const holdMs = MOVE_HOLD_MS;   // pause on each field
    const dur = Math.min(5200, steps * (stepMs + holdMs));

    lastMoveFx = { color: color || "white", pts, t0: now, dur, weights, landed:false };
    moveGhostFx = { pieceId: String(action.pieceId||""), color: color || "white", pts, t0: now, dur, stepMs, holdMs, hopPx: MOVE_HOP_PX, landBouncePx: MOVE_LAND_BOUNCE_PX, _jitterMs: (MOVE_TIMING_JITTER ? (Math.floor(Math.random()*21)-10) : 0) };

    // This is what prevents "teleport": we temporarily draw the real piece at interpolated positions
    movingPiecesFx.set(pid, { color: color || "white", pts, t0: now, dur, weights, stepMs, holdMs, hopPx: MOVE_HOP_PX, landBouncePx: MOVE_LAND_BOUNCE_PX, _jitterMs: 0 });

    // landing ring / dust (purely visual)
    const endW = nodeById.get(pts[pts.length-1].id) || null;
    ensureAnimLoop();

    if(endW){
      landFxs.push({
        x: endW.x, y: endW.y,
        t0: now + dur,
        dur: 320,
        color: color || "white",
        seed: Math.random()
      });
      if(landFxs.length > 18) landFxs = landFxs.slice(-18);
    }
  }

  function showOverlay(title, sub, hint){
    overlayTitle.textContent=title;
    overlaySub.textContent=sub||"";
    overlayHint.textContent=hint||"";
    overlay.classList.add("show");
  }
  function hideOverlay(){ overlay.classList.remove("show"); }
  overlayOk.addEventListener("click", hideOverlay);

  async function loadBoard(){
    const res = await fetch("board.json", {cache:"no-store"});
    if(!res.ok) throw new Error("board.json nicht gefunden");
    return await res.json();
  }

  function buildGraph(){
    nodeById.clear(); adj.clear(); runNodes.clear();
    goalNodeId=null;
    startNodeId={red:null,blue:null,green:null,yellow:null};

    for(const n of board.nodes){
      nodeById.set(n.id, n);
      if(n.kind==="board"){
        adj.set(n.id, []);
        if(n.flags?.run) runNodes.add(n.id);
        if(n.flags?.goal) goalNodeId=n.id;
        if(n.flags?.startColor) startNodeId[n.flags.startColor]=n.id;
      }
    }
    for(const e of board.edges||[]){
      const a=String(e[0]), b=String(e[1]);
      if(!adj.has(a)||!adj.has(b)) continue;
      adj.get(a).push(b); adj.get(b).push(a);
    }
    if(board.meta?.goal) goalNodeId=board.meta.goal;
    if(board.meta?.starts){
      for(const c of DEFAULT_PLAYERS) if(board.meta.starts[c]) startNodeId[c]=board.meta.starts[c];
    }
    if(boardInfo) boardInfo.textContent = `${[...adj.keys()].length} Felder`;
  }

  // ===== View / Fit-to-screen (Tablet / Zoom-Fix) =====
  function clamp(v,a,b){ return Math.max(a, Math.min(b, v)); }

  function computeBounds(){
    if(!board || !Array.isArray(board.nodes) || board.nodes.length===0) return null;
    let minX=Infinity, minY=Infinity, maxX=-Infinity, maxY=-Infinity;
    for(const n of board.nodes){
      if(typeof n.x!=="number" || typeof n.y!=="number") continue;
      if(n.x<minX) minX=n.x; if(n.x>maxX) maxX=n.x;
      if(n.y<minY) minY=n.y; if(n.y>maxY) maxY=n.y;
    }
    if(!isFinite(minX)) return null;
    return {minX,maxX,minY,maxY};
  }

  function fitBoardToView(){
    const b = computeBounds();
    if(!b) return;
    const rect = canvas.getBoundingClientRect();
    const vw = rect.width, vh = rect.height;
    if(vw < 20 || vh < 20) return;

    const pad = 70; // world units
    const minX = b.minX - pad, maxX = b.maxX + pad;
    const minY = b.minY - pad, maxY = b.maxY + pad;
    const bw = (maxX - minX);
    const bh = (maxY - minY);

    const s = Math.min(vw / bw, vh / bh);
    view.s = clamp(s, 0.28, 3.2);

    const leftPx = (vw - bw * view.s) / 2;
    const topPx  = (vh - bh * view.s) / 2;
    view.x = (leftPx / view.s) - minX;
    view.y = (topPx  / view.s) - minY;
    saveView();
  }

  function ensureFittedOnce(){
    if(view._fittedOnce) return;
    fitBoardToView();
    view._fittedOnce = true;
    draw();
  }


  function newGame(){
    const active = getActiveColors();
    setPlayers(active);

    state={
      players:[...PLAYERS],
      currentPlayer:PLAYERS[0],
      dice:null,
      phase:"need_roll",
      placingChoices:[],
      pieces:Object.fromEntries(PLAYERS.map(c=>[c, Array.from({length:5},()=>({pos:"house"}))])),
      barricades:new Set(),
      winner:null
    };

    // 🔥 BRUTAL: Barikaden starten auf ALLEN RUN-Feldern (außer Ziel)
    for(const id of runNodes){
      if(id===goalNodeId) continue;
      state.barricades.add(id);
    }

    if(barrInfo) barrInfo.textContent=String(state.barricades.size);
    setPhase("need_roll");
    /* dice handled via data-face */
    legalTargets=[]; setPlacingChoices([]);
    selected=null; legalMovesAll=[]; legalMovesByPiece=new Map();
    updateTurnUI(); draw();
    try{ ensureFittedOnce(); }catch(_e){}
  }

  function updateTurnUI(){
    const c=state.currentPlayer;
    const emoji = TURN_EMOJI[c] || "";
    turnText.textContent = state.winner
      ? `${PLAYER_NAME[state.winner]} gewinnt!`
      : `${emoji} ${PLAYER_NAME[c]} ist am Zug`;
    turnDot.style.background = COLORS[c];

    // (1) visual: glow ring + pulsing dot (no logic impact)
    if(turnPill){
      if(state.winner){
        turnPill.classList.remove("activeTurnGlow");
      }else{
        turnPill.classList.add("activeTurnGlow");
      }
    }
    if(turnDot){
      if(state.winner) turnDot.classList.remove("turnPulse");
      else turnDot.classList.add("turnPulse");
    }

    const isMyTurn = (netMode==="offline") ? true : (myColor && myColor===state.currentPlayer);
    rollBtn.disabled = (phase!=="need_roll") || (phase==="anim") || !isMyTurn;
    endBtn.disabled  = (phase==="need_roll"||phase==="placing_barricade"||phase==="game_over"||phase==="anim") || !isMyTurn;
    if(skipBtn) skipBtn.disabled = (phase==="placing_barricade"||phase==="game_over"||phase==="anim") || !isMyTurn;

    if(colorPickWrap){
      colorPickWrap.style.display = (netMode!=="offline" && !myColor) ? "block" : "none";
    }
  }

  function endTurn(){
    if(!state){ console.warn('endTurn: state is null'); return; }
    if(state && state.dice === 6 && !state.winner){
      state.dice = null;
      setDiceFaceAnimated(0);

      legalTargets=[]; setPlacingChoices([]);
      selected=null; legalMovesAll=[]; legalMovesByPiece=new Map();
      setPhase("need_roll");
      updateTurnUI(); draw();
      toast("6! Nochmal würfeln");
      return;
    }
    nextPlayer();
  }

  function nextPlayer(){
    if(!state){ console.warn('nextPlayer: state is null'); return; }
    const order = state.players?.length ? state.players : PLAYERS;
    const idx = order.indexOf(state.currentPlayer);
    state.currentPlayer = order[(idx+1)%order.length];
    state.dice=null;
    setDiceFaceAnimated(0);
    legalTargets=[]; setPlacingChoices([]);
    selected=null; legalMovesAll=[]; legalMovesByPiece=new Map();
    setPhase("need_roll");
    updateTurnUI(); draw();
  }

  function rollDice(){
    if(phase!=="need_roll") return;
    state.dice = 1 + Math.floor(Math.random()*6);
    setDiceFaceAnimated(state.dice);

    toast(`Wurf: ${state.dice}`);

    legalMovesAll = computeLegalMoves(state.currentPlayer, state.dice);
    legalMovesByPiece = new Map();
    for(const m of legalMovesAll){
      const idx = m.piece.index;
      if(!legalMovesByPiece.has(idx)) legalMovesByPiece.set(idx, []);
      legalMovesByPiece.get(idx).push(m);
    }
    legalTargets = legalMovesAll;

    if(legalMovesAll.length===0){
      toast("Kein Zug möglich – Zug verfällt");
      endTurn();
      return;
    }
    setPhase("need_move");
    updateTurnUI(); draw();
  }

  function pieceAtBoardNode(nodeId, color){
    const arr = state.pieces[color];
    for(let i=0;i<arr.length;i++){
      if(arr[i].pos === nodeId) return {color, index:i};
    }
    return null;
  }
  function selectPiece(sel){
    selected = sel;
    toast(`${PLAYER_NAME[sel.color]} Figur ${sel.index+1} gewählt`);
  }
  function trySelectAtNode(node){
    if(!node) return false;
    const c = state.currentPlayer;
    if(node.kind === "board"){
      const p = pieceAtBoardNode(node.id, c);
      if(p){ selectPiece(p); return true; }
      return false;
    }
    if(node.kind === "house" && node.flags?.houseColor === c && node.flags?.houseSlot){
      const idx = Number(node.flags.houseSlot) - 1;
      if(idx>=0 && idx<5){
        if(state.pieces[c][idx].pos === "house"){
          selectPiece({color:c, index:idx});
          return true;
        }else{
          toast("Diese Figur ist nicht im Haus");
          return true;
        }
      }
    }
    return false;
  }

  function anyPiecesAtNode(nodeId){
    const res=[];
    for(const c of PLAYERS){
      const arr=state.pieces[c];
      for(let i=0;i<arr.length;i++) if(arr[i].pos===nodeId) res.push({color:c,index:i});
    }
    return res;
  }

  function enumeratePaths(startId, steps){
    const results=[];
    const visited=new Set([startId]);
    function dfs(curr, remaining, path){
      if(remaining===0){ results.push([...path]); return; }
      for(const nb of (adj.get(curr)||[])){
        if(visited.has(nb)) continue;
        if(state.barricades.has(nb) && remaining>1) continue; // cannot pass barricade
        visited.add(nb); path.push(nb);
        dfs(nb, remaining-1, path);
        path.pop(); visited.delete(nb);
      }
    }
    dfs(startId, steps, [startId]);
    return results;
  }

  function computeLegalMoves(color, dice){
    const moves=[];
    for(let i=0;i<5;i++){
      const pc=state.pieces[color][i];
      if(typeof pc.pos==="string" && adj.has(pc.pos)){
        for(const p of enumeratePaths(pc.pos, dice)){
          moves.push({piece:{color,index:i}, path:p, toId:p[p.length-1], fromHouse:false});
        }
      }
    }
    const start=startNodeId[color];
    const hasHouse = state.pieces[color].some(p=>p.pos==="house");
    if(hasHouse && start && !state.barricades.has(start)){
      const remaining=dice-1;
      if(remaining===0){
        for(let i=0;i<5;i++) if(state.pieces[color][i].pos==="house"){
          moves.push({piece:{color,index:i}, path:[start], toId:start, fromHouse:true});
        }
      }else{
        const paths=enumeratePaths(start, remaining);
        for(let i=0;i<5;i++) if(state.pieces[color][i].pos==="house"){
          for(const p of paths) moves.push({piece:{color,index:i}, path:p, toId:p[p.length-1], fromHouse:true});
        }
      }
    }
    const seen=new Set(), uniq=[];
    for(const m of moves){
      const k=`${m.piece.color}:${m.piece.index}->${m.toId}:${m.fromHouse?'H':'B'}`;
      if(seen.has(k)) continue;
      seen.add(k); uniq.push(m);
    }
    return uniq;
  }

  function checkWin(){
    for(const c of PLAYERS){
      if(state.pieces[c].filter(p=>p.pos==="goal").length===5){ state.winner=c; return; }
    }
  }

  // 🔥 BRUTAL placements: any node (except goal, no duplicates)
  function computeBarricadePlacements(){
    const choices=[];
    for(const id of adj.keys()){
      if(id===goalNodeId) continue;
      if(state.barricades.has(id)) continue;
      choices.push(id);
    }
    setPlacingChoices(choices);
  }

  function movePiece(move){
    const {color,index}=move.piece;
    const toId=move.toId;

    // hit enemies
    const enemies = anyPiecesAtNode(toId).filter(p=>p.color!==color);
    for(const e of enemies) state.pieces[e.color][e.index].pos="house";

    const landsOnBarr = state.barricades.has(toId);
    state.pieces[color][index].pos=toId;

    if(toId===goalNodeId){
      state.pieces[color][index].pos="goal";
      toast("Ziel erreicht!");
      checkWin();
      if(state.winner){
        setPhase("game_over"); updateTurnUI(); draw();
        showOverlay("🎉 Spiel vorbei", `${PLAYER_NAME[state.winner]} gewinnt!`, "Tippe Reset für ein neues Spiel.");
        return;
      }
      endTurn();
      return;
    }

    if(landsOnBarr){
      state.barricades.delete(toId);
      if(barrInfo) barrInfo.textContent=String(state.barricades.size);
      setPhase("placing_barricade");
      computeBarricadePlacements();
      updateTurnUI(); draw();
      toast("Barikade eingesammelt – jetzt neu platzieren");
      return;
    }

    endTurn();
  }

  function placeBarricade(nodeId){
    if(phase!=="placing_barricade") return;
    if(nodeId===goalNodeId){ toast("Ziel ist gesperrt"); return; }
    if(!placingChoices.includes(nodeId)){ toast("Hier darf keine Barikade hin"); return; }
    state.barricades.add(nodeId);
    if(barrInfo) barrInfo.textContent=String(state.barricades.size);
    setPlacingChoices([]);
    toast("Barikade platziert");
    endTurn();
  }

  // ===== Rendering =====
  function resize(){
    dpr=Math.max(1, Math.min(2.5, window.devicePixelRatio||1));
    const r=canvas.getBoundingClientRect();
    canvas.width=Math.floor(r.width*dpr);
    canvas.height=Math.floor(r.height*dpr);
    ctx.setTransform(dpr,0,0,dpr,0,0);
    draw();
    // Mobile browsers report unstable canvas size during load/orientation.
    setTimeout(()=>{ if(!view._fittedOnce) { try{ ensureFittedOnce(); }catch(_e){} } }, 80);

  }
  window.addEventListener("resize", resize);
  window.addEventListener("orientationchange", ()=>{
    // force re-fit after rotation/addressbar changes
    view._fittedOnce = false;
    setTimeout(()=>{ try{ resize(); ensureFittedOnce(); }catch(_e){} }, 200);
  });

  function worldToScreen(p){ return {x:(p.x+view.x)*view.s, y:(p.y+view.y)*view.s}; }
  function screenToWorld(p){ return {x:p.x/view.s-view.x, y:p.y/view.s-view.y}; }

  function drawBarricadeIcon(x,y,r){
    ctx.save();
    ctx.fillStyle="rgba(0,0,0,0.85)";
    ctx.strokeStyle="rgba(230,237,243,0.9)";
    ctx.lineWidth=3;
    ctx.beginPath();
    ctx.arc(x,y,r*0.95,0,Math.PI*2);
    ctx.fill();
    ctx.stroke();
    ctx.restore();
  }
  function drawSelectionRing(x,y,r){
    ctx.save();
    ctx.strokeStyle = "rgba(255,255,255,0.95)";
    ctx.lineWidth = 5;
    ctx.beginPath();
    ctx.arc(x,y,r*1.05,0,Math.PI*2);
    ctx.stroke();
    ctx.restore();
  }
  function drawHousePieces(node, x, y, r){
    const color = node.flags && node.flags.houseColor;
    const slot = Number(node.flags && node.flags.houseSlot);
    if(!color || !slot) return;
    const idx = slot - 1;
    if(!state?.pieces?.[color]) return;
    if(state.pieces[color][idx].pos !== "house") return;

    ctx.save();
    // (27) subtle gradient for pieces
    const g = ctx.createRadialGradient(x - r*0.18, y - r*0.18, r*0.15, x, y, r*0.75);
    g.addColorStop(0, "rgba(255,255,255,0.45)");
    g.addColorStop(0.35, COLORS[color]);
    g.addColorStop(1, "rgba(0,0,0,0.25)");
    ctx.fillStyle = g;
    ctx.strokeStyle = "rgba(0,0,0,0.7)";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(x, y, r*0.55, 0, Math.PI*2);
    ctx.fill(); ctx.stroke();
    ctx.restore();
  }
  function drawStack(arr, x, y, r){
    const p = arr[0];
    ctx.save();
    // (27) subtle gradient for pieces
    const g = ctx.createRadialGradient(x - r*0.22, y - r*0.22, r*0.2, x, y, r*1.15);
    g.addColorStop(0, "rgba(255,255,255,0.45)");
    g.addColorStop(0.4, COLORS[p.color]);
    g.addColorStop(1, "rgba(0,0,0,0.25)");
    ctx.fillStyle = g;
    ctx.strokeStyle = "rgba(0,0,0,0.7)";
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.arc(x, y, r*0.95, 0, Math.PI*2);
    ctx.fill(); ctx.stroke();

    if(arr.length > 1){
      ctx.fillStyle="rgba(0,0,0,0.65)";
      ctx.beginPath();
      ctx.arc(x, y, r*0.45, 0, Math.PI*2);
      ctx.fill();
      ctx.fillStyle="rgba(230,237,243,0.95)";
      ctx.font="bold 14px system-ui";
      ctx.textAlign="center"; ctx.textBaseline="middle";
      ctx.fillText(String(arr.length), x, y);
    }
    ctx.restore();
  }

  function draw(){
    if(!board||!state) return;
    const rect=canvas.getBoundingClientRect();
    ctx.clearRect(0,0,rect.width,rect.height);

    // grid
    const grid=Math.max(10,(board.ui?.gridSize||20))*view.s;
    ctx.save();
    ctx.strokeStyle="rgba(28,36,51,0.75)";
    ctx.lineWidth=1;
    const ox=(view.x*view.s)%grid, oy=(view.y*view.s)%grid;
    for(let x=-ox;x<rect.width;x+=grid){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,rect.height);ctx.stroke();}
    for(let y=-oy;y<rect.height;y+=grid){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(rect.width,y);ctx.stroke();}
    ctx.restore();

    // edges
    ctx.save();
    ctx.lineWidth=3; ctx.strokeStyle=COLORS.edge;
    for(const e of board.edges||[]){
      const a=nodeById.get(String(e[0])), b=nodeById.get(String(e[1]));
      if(!a||!b||a.kind!=="board"||b.kind!=="board") continue;
      const sa=worldToScreen(a), sb=worldToScreen(b);
      ctx.beginPath();ctx.moveTo(sa.x,sa.y);ctx.lineTo(sb.x,sb.y);ctx.stroke();
    }
    ctx.restore();

    // (109) last move trail + (8) destination glow
    const nowFx = performance.now();
    if(lastMoveFx && lastMoveFx.pts && nowFx - lastMoveFx.t0 < 900){
      const age = (nowFx - lastMoveFx.t0);
      const a = Math.max(0, 1 - age/900);
      const col = COLORS[lastMoveFx.color] || lastMoveFx.color || 'rgba(255,255,255,0.9)';
      ctx.save();
      ctx.globalAlpha = 0.55 * a;
      ctx.strokeStyle = col;
      ctx.lineWidth = 6;
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      ctx.beginPath();
      ctx.moveTo(lastMoveFx.pts[0].x, lastMoveFx.pts[0].y);
      for(let i=1;i<lastMoveFx.pts.length;i++) ctx.lineTo(lastMoveFx.pts[i].x, lastMoveFx.pts[i].y);
      ctx.stroke();
      // destination glow
      const end = lastMoveFx.pts[lastMoveFx.pts.length-1];
      ctx.globalAlpha = 0.35 * a;
      ctx.beginPath();
      ctx.arc(end.x, end.y, 22, 0, Math.PI*2);
      ctx.stroke();
      ctx.restore();
    }

    // (7) ghost piece stepping field-to-field (visual only)
    if(moveGhostFx && moveGhostFx.pts && (nowFx - moveGhostFx.t0) < moveGhostFx.dur){
      const sp = sampleStepGhostAt(moveGhostFx, nowFx);
      let x = sp.x;
      let y = sp.y;

      const segN = Math.max(1, moveGhostFx.pts.length - 1);
      const col = COLORS[moveGhostFx.color] || moveGhostFx.color || 'rgba(255,255,255,0.95)';

      // Highlight the field being entered (ring pulse on the landing node)
      const target = sp.b || moveGhostFx.pts[Math.min(segN, sp.idx+1)];
      if(target){
        const pulse = sp.inHold ? 1 : 0.55;
        ctx.save();
        ctx.globalAlpha = 0.55 * pulse;
        ctx.strokeStyle = col;
        ctx.lineWidth = 4;
        ctx.beginPath();
        ctx.arc(target.x, target.y, 18 + (sp.inHold ? 6*(1-sp.local) : 0), 0, Math.PI*2);
        ctx.stroke();
        ctx.restore();
      }

      // Draw a CLEAR colored piece (so you SEE which color is moving)
      ctx.save();
      ctx.globalAlpha = 0.92;
      const rr = 15;
      ctx.fillStyle = col;
      ctx.strokeStyle = 'rgba(0,0,0,0.65)';
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.arc(x, y, rr, 0, Math.PI*2);
      ctx.fill();
      ctx.stroke();

      // tiny white highlight
      ctx.globalAlpha = 0.35;
      ctx.fillStyle = 'rgba(255,255,255,0.95)';
      ctx.beginPath();
      ctx.arc(x - rr*0.3, y - rr*0.3, rr*0.35, 0, Math.PI*2);
      ctx.fill();

      // step counter (e.g. 3/5) near the moving piece
      ctx.globalAlpha = 0.85;
      ctx.fillStyle = 'rgba(0,0,0,0.65)';
      ctx.beginPath();
      ctx.rect(x+18, y-22, 34, 18);
      ctx.fill();
      ctx.fillStyle = 'rgba(255,255,255,0.95)';
      ctx.font = 'bold 12px system-ui';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(String(sp.idx+1) + "/" + String(segN), x+35, y-13);

      ctx.restore();

      ensureAnimLoop();
    }


    const r=Math.max(16, board.ui?.nodeRadius || 20);

    // nodes
    for(const n of board.nodes){
      const s=worldToScreen(n);
      let fill=COLORS.node;
      if(n.kind==="board"){
        if(n.id===goalNodeId) fill=COLORS.goal;
        else if(n.flags?.startColor) fill=COLORS.node; // ✅ neutral start fields
        else if(n.flags?.run) fill=COLORS.run;
      }else if(n.kind==="house"){
        fill=COLORS[n.flags?.houseColor]||COLORS.node;
      }

      ctx.beginPath(); ctx.fillStyle=fill; ctx.arc(s.x,s.y,r,0,Math.PI*2); ctx.fill();
      ctx.lineWidth=3; ctx.strokeStyle=COLORS.stroke; ctx.stroke();

      if(n.kind==="house" && n.flags?.houseSlot){
        ctx.fillStyle="rgba(0,0,0,0.55)";
        ctx.beginPath(); ctx.arc(s.x,s.y,r*0.55,0,Math.PI*2); ctx.fill();
        ctx.fillStyle="rgba(230,237,243,0.95)";
        ctx.font="bold 13px system-ui";
        ctx.textAlign="center"; ctx.textBaseline="middle";
        ctx.fillText(String(n.flags.houseSlot), s.x, s.y);
        drawHousePieces(n, s.x, s.y, r);

        if(selected && n.flags && n.flags.houseColor===selected.color && Number(n.flags.houseSlot)===selected.index+1){
          drawSelectionRing(s.x, s.y, r*0.85);
        }
      }

      if(n.kind==="board" && state.barricades.has(n.id)){
        drawBarricadeIcon(s.x,s.y,r);
      }
    }

    if(phase==="placing_barricade"){
      ctx.save();
      ctx.lineWidth=6;
      ctx.strokeStyle="rgba(255,209,102,0.9)";
      ctx.setLineDash([10,7]);
      for(const id of placingChoices){
        const n=nodeById.get(id); if(!n) continue;
        const s=worldToScreen(n);
        ctx.beginPath(); ctx.arc(s.x,s.y,r+7,0,Math.PI*2); ctx.stroke();
      }
      ctx.restore();
    }

    // pieces stacked
    // While a piece is moving, we temporarily draw it at its interpolated position
    // so it doesn't "teleport" to the destination immediately.
    const stacks=new Map();
    const movingToDraw=[];
    const nowMove = performance.now();

    // cleanup expired
    if(movingPiecesFx && movingPiecesFx.size){
      for(const [pid, fx] of movingPiecesFx.entries()){
        if(!fx || !fx.t0 || !fx.dur) { movingPiecesFx.delete(pid); continue; }
        if(nowMove - fx.t0 > fx.dur + 60) movingPiecesFx.delete(pid);
      }
    }

    for(const c of PLAYERS){
      const pcs=state.pieces[c];
      for(let i=0;i<pcs.length;i++){
        const pc = pcs[i];
        const pid = pc?.pieceId ? String(pc.pieceId) : "";
        const fx = pid ? movingPiecesFx.get(pid) : null;
        if(fx){
          movingToDraw.push({color:c,index:i,pid,fx});
          continue;
        }
        const pos=pc.pos;
        if(typeof pos==="string" && adj.has(pos)){
          if(!stacks.has(pos)) stacks.set(pos, []);
          stacks.get(pos).push({color:c,index:i});
        }
      }
    }
    for(const [nodeId, arr] of stacks.entries()){
      const n=nodeById.get(nodeId); if(!n) continue;
      const s=worldToScreen(n);
      drawStack(arr, s.x, s.y, r);
    }

    // draw moving pieces (single piece, visible hop)
    if(movingToDraw.length){
      for(const m of movingToDraw){
        const fx = m.fx;
        const t = (nowMove - fx.t0) / fx.dur;
        const fRaw = Math.max(0, Math.min(1, t));
        const f = easeOutQuad(fRaw);
        const sp = (fx && fx.stepMs) ? sampleStepGhostAt(fx, nowMove) : sampleGhostAt(fx.pts, fx.weights, f);
        let x = sp.x;
        let y = sp.y;

        // big, clear hop per segment (field-to-field)
        const hopAmp = MOVE_HOP_PX * 0.6; // px
        const hop = Math.sin(sp.localT * Math.PI) * hopAmp;
        y -= hop;

        // a small landing bounce near the end
        if (fRaw > 0.86){
          const u = Math.max(0, Math.min(1, (fRaw - 0.86) / 0.14));
          const bounce = Math.sin(u * Math.PI) * (1-u) * (MOVE_LAND_BOUNCE_PX*0.8);
          y -= bounce;
        }

        // Draw like a normal stack-piece but single
        drawStack([{color:m.color,index:m.index}], x, y, r);
      }
    }

    if(selected){
      const pc = state.pieces[selected.color]?.[selected.index];
      if(pc && typeof pc.pos==="string" && adj.has(pc.pos)){
        const n = nodeById.get(pc.pos);
        if(n){
          const s = worldToScreen(n);
          drawSelectionRing(s.x, s.y, r);
        }
      }
    }
  }

  // ===== Interaction =====
  function pointerPos(ev){
    const r=canvas.getBoundingClientRect();
    return {x:ev.clientX-r.left, y:ev.clientY-r.top};
  }
  function hitNode(wp){
    const r=Math.max(16, board.ui?.nodeRadius || 20);
    const hitR=(r+10)/view.s;
    let best=null, bd=Infinity;
    for(const n of board.nodes){
      const d=Math.hypot(n.x-wp.x, n.y-wp.y);
      if(d<hitR && d<bd){best=n; bd=d;}
    }
    return best;
  }

  function onPointerDown(ev){
    canvas.setPointerCapture(ev.pointerId);
    const sp=pointerPos(ev);
    // double-tap (or double-click) to auto-fit board (tablet safe)
    const nowTs = Date.now();
    if(pointerMap.size===0){
      if(lastTapPos && (nowTs - lastTapTs) < 350){
        const dx = sp.x - lastTapPos.x, dy = sp.y - lastTapPos.y;
        if((dx*dx + dy*dy) < (28*28)){
          // fit + persist
          clearView();
          try{ ensureFittedOnce(); }catch(_e){}
          saveView();
          lastTapTs = 0; lastTapPos = null;
          return;
        }
      }
      lastTapTs = nowTs;
      lastTapPos = {x:sp.x,y:sp.y};
    }
    pointerMap.set(ev.pointerId, {x:sp.x,y:sp.y});
    if(pointerMap.size===2){ isPanning=false; panStart=null; return; }

    const wp=screenToWorld(sp);
    const hit=hitNode(wp);

    const isMyTurn = (netMode!=="client") || (myColor && myColor===state.currentPlayer);

    if(phase==="anim"){
      toast("Animation läuft…");
      return;
    }
    if(netMode==="client" && (!myColor || !isMyTurn) && (phase==="placing_barricade" || phase==="need_move" || phase==="need_roll")){
      toast(!myColor ? "Bitte Farbe wählen" : "Du bist nicht dran");
      return;
    }

if(phase==="placing_barricade" && hit && hit.kind==="board"){
  // ONLINE: Server entscheidet immer (Host + Client senden)
  if(netMode!=="offline"){
    wsSend({type:"place_barricade", nodeId: hit.id, ts:Date.now()});
    return;
  }

  // OFFLINE: lokal platzieren
  placeBarricade(hit.id);
  return;
}

    if(phase==="need_move"){
      if(trySelectAtNode(hit)) { draw(); return; }
      if(selected && hit && hit.kind==="board"){
        if(netMode!=="offline"){
          const pid = state?.pieces?.[selected.color]?.[selected.index]?.pieceId;
          if(!pid){ toast("PieceId fehlt"); return; }
          wsSend({type:"move_request", pieceId: pid, targetId: hit.id, ts:Date.now()});
          return;
        }
        const list = legalMovesByPiece.get(selected.index) || [];
        const m = list.find(x => x.toId===hit.id);
        if(m){
          if(netMode==="client"){ wsSend({type:"move_request", pieceId: (state.pieces[selected.color][selected.index].pieceId), targetId: hit.id, ts:Date.now()}); return; }
          movePiece(m);
          if(netMode==="host") broadcastState("state");
          draw();
          return;
        }
        toast("Ungültiges Zielfeld (bitte neu zählen)");
        return;
      }
    }

    isPanning=true;
    panStart={sx:sp.x,sy:sp.y,vx:view.x,vy:view.y};
  }

  function onPointerMove(ev){
    if(!pointerMap.has(ev.pointerId)) return;
    const sp=pointerPos(ev);
    pointerMap.set(ev.pointerId, {x:sp.x,y:sp.y});

    if(pointerMap.size===2){
      const pts=[...pointerMap.values()];
      const a=pts[0], b=pts[1];
      if(!onPointerMove._pinch){
        onPointerMove._pinch={d0:Math.hypot(a.x-b.x,a.y-b.y), s0:view.s};
      }
      const pz=onPointerMove._pinch;
      const d1=Math.hypot(a.x-b.x,a.y-b.y);
      const factor=d1/Math.max(10,pz.d0);
      view.s=Math.max(0.25, Math.min(3.2, pz.s0*factor));
      draw(); return;
    } else { onPointerMove._pinch=null; }

    if(isPanning && panStart){
      const dx=(sp.x-panStart.sx)/view.s;
      const dy=(sp.y-panStart.sy)/view.s;
      view.x=panStart.vx+dx;
      view.y=panStart.vy+dy;
      draw();
    }
  }
  function onPointerUp(ev){
    if(pointerMap.has(ev.pointerId)) pointerMap.delete(ev.pointerId);
    if(pointerMap.size===0){ isPanning=false; panStart=null; onPointerMove._pinch=null; saveView(); }
  }

  canvas.addEventListener("pointerdown", onPointerDown);
  canvas.addEventListener("pointermove", onPointerMove);
  canvas.addEventListener("pointerup", onPointerUp);
  canvas.addEventListener("pointercancel", onPointerUp);

  // ===== Buttons =====
  rollBtn.addEventListener("click", () => {
    if(netMode!=="offline"){
      if(!ws || ws.readyState!==1){ toast("Nicht verbunden"); return; }
      // server checks turn
      wsSend({type:"roll_request", ts:Date.now()});
      return;
    }
    rollDice();
    if(netMode==="host") broadcastState("state");
  });

  endBtn.addEventListener("click", () => {
    if(netMode!=="offline"){
      toast("Zug beenden macht der Server automatisch nach dem Zug");
      return;
    }
    if(phase!=="placing_barricade" && phase!=="game_over") nextPlayer();
    if(netMode==="host") broadcastState("state");
  });

  if(skipBtn) skipBtn.addEventListener("click", () => {
    if(netMode==="client"){
      if(!myColor){ toast("Bitte Farbe wählen"); return; }
      if(myColor!==state.currentPlayer){ toast("Du bist nicht dran"); return; }
      sendIntent({type:"skip"}); return;
    }
    if(phase!=="placing_barricade" && phase!=="game_over"){ toast("Runde ausgesetzt"); nextPlayer(); }
    if(netMode==="host") broadcastState("state");
  });

  resetBtn.addEventListener("click", () => {
    if(netMode==="offline"){
      newGame();
      return;
    }
    if(!ws || ws.readyState!==1){ toast("Nicht verbunden"); return; }
    wsSend({type:"reset", ts:Date.now()});
  });

  // Online actions
  hostBtn.addEventListener("click", () => {
    netMode = "host";
    clientId = clientId || ("H-" + randId(8));
    roomCode = normalizeRoomCode(roomCodeInp.value) || randId(6);
    roomCodeInp.value = roomCode;
    saveSession();
    connectWS();
    toast("Host gestartet – teile den Raumcode");
  });

  joinBtn.addEventListener("click", () => {
    netMode = "client";
    clientId = clientId || ("C-" + randId(8));
    roomCode = normalizeRoomCode(roomCodeInp.value);
    if(!roomCode){ toast("Bitte Raumcode eingeben"); return; }
    saveSession();
    connectWS();
    toast("Beitreten…");
  });

  leaveBtn.addEventListener("click", () => {
    netMode = "offline";
    saveSession();
    disconnectWS();
    setNetPlayers([]);
    toast("Offline");
  });

  // Color pick
  if(btnPickRed) btnPickRed.addEventListener("click", ()=>chooseColor("red"));
  if(btnPickBlue) btnPickBlue.addEventListener("click", ()=>chooseColor("blue"));
  if(btnPickGreen) btnPickGreen.addEventListener("click", ()=>chooseColor("green"));
  if(btnPickYellow) btnPickYellow.addEventListener("click", ()=>chooseColor("yellow"));

  // ===== Host: intent processing =====
  function colorOf(id){
    const p = rosterById.get(id) || null;
    return p && p.color ? p.color : null;
  }
  function roleOf(id){
    const p = rosterById.get(id) || null;
    return p && p.role ? p.role : null;
  }
  function handleRemoteIntent(intent, senderId=""){
    const senderColor = colorOf(senderId);
    const mustBeTurnPlayer = () => senderColor && senderColor===state.currentPlayer;

    const t = intent.type;
    if(t==="roll"){
      if(!mustBeTurnPlayer()) return;
      rollDice(); broadcastState("state"); return;
    }
    if(t==="end"){
      if(!mustBeTurnPlayer()) return;
      if(phase!=="placing_barricade" && phase!=="game_over") nextPlayer();
      broadcastState("state"); return;
    }
    if(t==="skip"){
      if(!mustBeTurnPlayer()) return;
      if(phase!=="placing_barricade" && phase!=="game_over"){ toast("Runde ausgesetzt"); nextPlayer(); }
      broadcastState("state"); return;
    }
    if(t==="reset"){
      if(roleOf(senderId)!=="host") return;
      newGame(); broadcastState("snapshot"); return;
    }
    if(t==="move"){
      if(!mustBeTurnPlayer()) return;
      if(phase!=="need_move") return;

      const toId = intent.toId;
      const pieceIndex = Number(intent.pieceIndex);
      if(!toId || !(pieceIndex>=0 && pieceIndex<5)) return;

      const list = legalMovesByPiece.get(pieceIndex) || [];
      const m = list.find(x=>x.toId===toId && x.piece.color===senderColor);
      if(m){ movePiece(m); broadcastState("state"); return; }
      return;
    }
    if(t==="placeBarricade"){
      if(!mustBeTurnPlayer()) return;
      if(phase!=="placing_barricade") return;
      placeBarricade(intent.nodeId);
      broadcastState("state");
      return;
    }
  }

  // ===== Init =====
  (async function init(){
    try{
      board = await loadBoard();
      buildGraph();
      resize();

      // restore previous view if available (optional)
      let hadSavedView = false;
      if(AUTO_CENTER_ALWAYS){
        clearView();
        hadSavedView = false;
      }else{
        hadSavedView = loadView();
      }

      // auto center
      if(AUTO_CENTER_ALWAYS || !hadSavedView){
      const xs = board.nodes.map(n=>n.x), ys=board.nodes.map(n=>n.y);
      const minX=Math.min(...xs), maxX=Math.max(...xs);
      const minY=Math.min(...ys), maxY=Math.max(...ys);
      const cx=(minX+maxX)/2, cy=(minY+maxY)/2;
      const rect = canvas.getBoundingClientRect();
      const bw=(maxX-minX)+200, bh=(maxY-minY)+200;
      const sx=rect.width/Math.max(200,bw), sy=rect.height/Math.max(200,bh);
      view.s = Math.max(0.35, Math.min(1.4, Math.min(sx,sy)));
      view.x = (rect.width/2)/view.s - cx;
      view.y = (rect.height/2)/view.s - cy;

      }

      // ensure board is on-screen immediately
      view._fittedOnce = false;
      try{ ensureFittedOnce(); }catch(_e){}

      const sess = loadSession();
      clientId = sess.id || "";
      if(sess.r){ roomCode = normalizeRoomCode(sess.r); roomCodeInp.value = roomCode; }
      if(sess.m==="host" || sess.m==="client"){
        netMode = sess.m;
        setNetStatus("Reconnect…", false);
        connectWS();
      }
      if(netMode==="offline"){
        newGame();
      }
      window.__DBG = { get state(){ return state; }, get board(){ return board; }, get phase(){ return phase; }, get netMode(){ return netMode; } };
      toast("Bereit. Online: Host/Beitreten.");
    }catch(err){
      showOverlay("Fehler","Board konnte nicht geladen werden", String(err.message||err));
      console.error(err);
    }
  })();
})();
