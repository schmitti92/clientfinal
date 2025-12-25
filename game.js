(() => {
  const $ = (id) => document.getElementById(id);

  // ===== UI refs =====
  const canvas = $("c");
  const ctx = canvas.getContext("2d");
  const toastEl = $("toast");

  const rollBtn = $("rollBtn");
  const endBtn  = $("endBtn");
  const skipBtn = $("skipBtn");
  const resetBtn= $("resetBtn");
  const diceEl  = $("dice");
  const turnText= $("turnText");
  const turnDot = $("turnDot");
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
  let dpr=1, view={x:40,y:40,s:1};
  let pointerMap=new Map(), isPanning=false, panStart=null;

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

  // ===== Online =====
  const SERVER_URL = "wss://barikade-server.onrender.com";
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
    try{ ws = new WebSocket(SERVER_URL); }
    catch(_e){ setNetStatus("WebSocket nicht möglich", false); scheduleReconnect(); return; }

    ws.onopen = () => {
      stopReconnect();
      setNetStatus("Verbunden – join…", true);
      wsSend({type:"hello", room:roomCode, mode:netMode, clientId, ts:Date.now()});
      wsSend({type:"join", room:roomCode, role:netMode, clientId, name:(netMode==="host"?"Host":"Client"), ts:Date.now()});
      wsSend({type:"need_snapshot", room:roomCode, clientId, ts:Date.now()});
      wsSend({type:"need_state", room:roomCode, clientId, ts:Date.now()});

      if(netMode==="host") setTimeout(()=>broadcastState("snapshot"), 120);

      if(netMode==="client" && pendingIntents.length){
        const copy=[...pendingIntents]; pendingIntents=[];
        for(const it of copy) wsSend(it);
      }
    };

    ws.onmessage = (ev) => {
      const msg = (typeof ev.data==="string") ? safeJsonParse(ev.data) : null;
      if(!msg) return;
      const type = msg.type || msg.t || msg.action || msg.kind;

      if(type==="players" || type==="roster" || type==="presence"){
        setNetPlayers(msg.players || msg.list || msg.payload || []);
        return;
      }
      if(type==="room" || type==="joined"){
        if(msg.room) roomCode = normalizeRoomCode(msg.room);
        if(roomCodeInp) roomCodeInp.value = roomCode;
        if(msg.players) setNetPlayers(msg.players);
        setNetStatus("Verbunden", true);
        return;
      }
      if(type==="snapshot" || type==="state" || type==="sync"){
        const st = msg.state || msg.payload || msg.data;
        if(st) applyRemoteState(st);
        if(msg.players) setNetPlayers(msg.players);
        return;
      }
      if(type==="intent"){
        if(netMode!=="host") return;
        const it = msg.intent || msg.payload || msg.data || msg;
        const sender = msg.clientId || msg.id || msg.from || "";
        if(it) handleRemoteIntent(it, sender);
        return;
      }
      if(type==="colorDenied"){ toast(msg.reason || "Farbe belegt"); return; }
      if(type==="colorChosen"){ toast(`Farbe: ${PLAYER_NAME[msg.color]}`); return; }
      if(type==="need_snapshot" || type==="need_state"){
        if(netMode==="host") broadcastState("snapshot");
        return;
      }
      if(type==="ping"){ wsSend({type:"pong", ts:Date.now()}); return; }
    };

    ws.onerror = () => { setNetStatus("Fehler – Reconnect…", false); };
    ws.onclose = () => {
      setNetStatus("Getrennt – Reconnect…", false);
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

  function chooseColor(color){
    if(netMode==="offline"){ toast("Offline: Farbe egal"); return; }
    if(!ws || ws.readyState!==1){ toast("Nicht verbunden"); return; }
    wsSend({type:"chooseColor", room:roomCode, clientId, color, ts:Date.now()});
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
    if(diceEl) diceEl.textContent = state.dice==null ? "–" : String(state.dice);
    updateTurnUI(); draw();
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
    diceEl.textContent="–";
    legalTargets=[]; setPlacingChoices([]);
    selected=null; legalMovesAll=[]; legalMovesByPiece=new Map();
    updateTurnUI(); draw();
  }

  function updateTurnUI(){
    const c=state.currentPlayer;
    turnText.textContent = state.winner ? `${PLAYER_NAME[state.winner]} gewinnt!` : `${PLAYER_NAME[c]} ist dran`;
    turnDot.style.background = COLORS[c];

    const isMyTurn = (netMode==="offline") ? true : (myColor && myColor===state.currentPlayer);
    rollBtn.disabled = (phase!=="need_roll") || !isMyTurn;
    endBtn.disabled  = (phase==="need_roll"||phase==="placing_barricade"||phase==="game_over") || !isMyTurn;
    if(skipBtn) skipBtn.disabled = (phase==="placing_barricade"||phase==="game_over") || !isMyTurn;

    if(colorPickWrap){
      colorPickWrap.style.display = (netMode!=="offline" && !myColor) ? "block" : "none";
    }
  }

  function endTurn(){
    if(state && state.dice === 6 && !state.winner){
      state.dice = null;
      diceEl.textContent="–";
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
    const order = state.players?.length ? state.players : PLAYERS;
    const idx = order.indexOf(state.currentPlayer);
    state.currentPlayer = order[(idx+1)%order.length];
    state.dice=null;
    diceEl.textContent="–";
    legalTargets=[]; setPlacingChoices([]);
    selected=null; legalMovesAll=[]; legalMovesByPiece=new Map();
    setPhase("need_roll");
    updateTurnUI(); draw();
  }

  function rollDice(){
    if(phase!=="need_roll") return;
    state.dice = 1 + Math.floor(Math.random()*6);
    diceEl.textContent=String(state.dice);
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
  }
  window.addEventListener("resize", resize);

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
    ctx.fillStyle = COLORS[color];
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
    ctx.fillStyle = COLORS[p.color];
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
    const stacks=new Map();
    for(const c of PLAYERS){
      const pcs=state.pieces[c];
      for(let i=0;i<pcs.length;i++){
        const pos=pcs[i].pos;
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
    pointerMap.set(ev.pointerId, {x:sp.x,y:sp.y});
    if(pointerMap.size===2){ isPanning=false; panStart=null; return; }

    const wp=screenToWorld(sp);
    const hit=hitNode(wp);

    const isMyTurn = (netMode!=="client") || (myColor && myColor===state.currentPlayer);
    if(netMode==="client" && (!myColor || !isMyTurn) && (phase==="placing_barricade" || phase==="need_move" || phase==="need_roll")){
      toast(!myColor ? "Bitte Farbe wählen" : "Du bist nicht dran");
      return;
    }

    if(phase==="placing_barricade" && hit && hit.kind==="board"){
      if(netMode==="client"){ sendIntent({type:"placeBarricade", nodeId: hit.id}); return; }
      placeBarricade(hit.id);
      if(netMode==="host") broadcastState("state");
      return;
    }

    if(phase==="need_move"){
      if(trySelectAtNode(hit)) { draw(); return; }
      if(selected && hit && hit.kind==="board"){
        const list = legalMovesByPiece.get(selected.index) || [];
        const m = list.find(x => x.toId===hit.id);
        if(m){
          if(netMode==="client"){ sendIntent({type:"move", pieceIndex: selected.index, toId: hit.id}); return; }
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
    if(pointerMap.size===0){ isPanning=false; panStart=null; onPointerMove._pinch=null; }
  }

  canvas.addEventListener("pointerdown", onPointerDown);
  canvas.addEventListener("pointermove", onPointerMove);
  canvas.addEventListener("pointerup", onPointerUp);
  canvas.addEventListener("pointercancel", onPointerUp);

  // ===== Buttons =====
  rollBtn.addEventListener("click", () => {
    if(netMode==="client"){
      if(!myColor){ toast("Bitte Farbe wählen"); return; }
      if(myColor!==state.currentPlayer){ toast("Du bist nicht dran"); return; }
      sendIntent({type:"roll"}); return;
    }
    rollDice();
    if(netMode==="host") broadcastState("state");
  });

  endBtn.addEventListener("click", () => {
    if(netMode==="client"){
      if(!myColor){ toast("Bitte Farbe wählen"); return; }
      if(myColor!==state.currentPlayer){ toast("Du bist nicht dran"); return; }
      sendIntent({type:"end"}); return;
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
    if(netMode==="client"){ toast("Nur Host kann resetten"); return; }
    newGame();
    if(netMode==="host") broadcastState("snapshot");
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

      // auto center
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

      const sess = loadSession();
      clientId = sess.id || "";
      if(sess.r){ roomCode = normalizeRoomCode(sess.r); roomCodeInp.value = roomCode; }
      if(sess.m==="host" || sess.m==="client"){
        netMode = sess.m;
        setNetStatus("Reconnect…", false);
        connectWS();
      }

      newGame();
      toast("Bereit. Online: Host/Beitreten + Farbe wählen.");
    }catch(err){
      showOverlay("Fehler","Board konnte nicht geladen werden", String(err.message||err));
      console.error(err);
    }
  })();
})();