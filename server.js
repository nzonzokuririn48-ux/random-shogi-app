const express = require("express");
const http = require("http");
const { Server } = require("socket.io");
const fs = require("fs");
const path = require("path");

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static("public"));

const DATA_DIR = path.join(__dirname, "data");
const USERS_FILE = path.join(DATA_DIR, "users.json");

if (!fs.existsSync(DATA_DIR)) {
  fs.mkdirSync(DATA_DIR, { recursive: true });
}
if (!fs.existsSync(USERS_FILE)) {
  fs.writeFileSync(USERS_FILE, JSON.stringify({}, null, 2), "utf8");
}

function loadUsers() {
  try {
    return JSON.parse(fs.readFileSync(USERS_FILE, "utf8"));
  } catch {
    return {};
  }
}

function saveUsers(users) {
  fs.writeFileSync(USERS_FILE, JSON.stringify(users, null, 2), "utf8");
}

function ensureUser(name) {
  const users = loadUsers();
  if (!users[name]) {
    users[name] = {
      name,
      rating: 1500,
      games: 0,
      wins: 0,
      losses: 0,
      draws: 0
    };
    saveUsers(users);
  }
  return users[name];
}

function calcElo(rA, rB, scoreA, K = 32) {
  const expectedA = 1 / (1 + Math.pow(10, (rB - rA) / 400));
  return Math.round(rA + K * (scoreA - expectedA));
}

function updateRatings(game, result) {
  const users = loadUsers();

  const blackName = game.players.black.name;
  const whiteName = game.players.white.name;

  if (!users[blackName]) {
    users[blackName] = { name: blackName, rating: 1500, games: 0, wins: 0, losses: 0, draws: 0 };
  }
  if (!users[whiteName]) {
    users[whiteName] = { name: whiteName, rating: 1500, games: 0, wins: 0, losses: 0, draws: 0 };
  }

  const rb = users[blackName].rating;
  const rw = users[whiteName].rating;

  let sb = 0.5;
  if (result === "black") sb = 1;
  if (result === "white") sb = 0;

  users[blackName].rating = calcElo(rb, rw, sb);
  users[whiteName].rating = calcElo(rw, rb, 1 - sb);

  users[blackName].games += 1;
  users[whiteName].games += 1;

  if (result === "black") {
    users[blackName].wins += 1;
    users[whiteName].losses += 1;
  } else if (result === "white") {
    users[whiteName].wins += 1;
    users[blackName].losses += 1;
  } else {
    users[blackName].draws += 1;
    users[whiteName].draws += 1;
  }

  saveUsers(users);

  return {
    black: users[blackName].rating,
    white: users[whiteName].rating
  };
}

const PIECE_LABELS = {
  K: "玉",
  R: "飛",
  B: "角",
  G: "金",
  S: "銀",
  N: "桂",
  L: "香",
  P: "歩",
  PR: "龍",
  PB: "馬",
  PS: "全",
  PN: "圭",
  PL: "杏",
  PP: "と"
};

function createEmptyHands() {
  return {
    black: { R: 0, B: 0, G: 0, S: 0, N: 0, L: 0, P: 0 },
    white: { R: 0, B: 0, G: 0, S: 0, N: 0, L: 0, P: 0 }
  };
}

function clone(obj) {
  return JSON.parse(JSON.stringify(obj));
}

function createPiece(type, owner) {
  return { type, owner };
}

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function randomInitialBoard() {
  const board = Array.from({ length: 9 }, () => Array(9).fill(null));
  const back = shuffle(["L", "N", "S", "G", "K", "G", "S", "N", "L"]);

  for (let c = 0; c < 9; c++) {
    board[8][c] = createPiece(back[c], "black");
    board[0][8 - c] = createPiece(back[c], "white");
  }

  board[7][1] = createPiece("B", "black");
  board[7][7] = createPiece("R", "black");
  board[1][7] = createPiece("B", "white");
  board[1][1] = createPiece("R", "white");

  for (let c = 0; c < 9; c++) {
    board[6][c] = createPiece("P", "black");
    board[2][8 - c] = createPiece("P", "white");
  }

  return board;
}

function inBounds(r, c) {
  return r >= 0 && r < 9 && c >= 0 && c < 9;
}

function opponent(side) {
  return side === "black" ? "white" : "black";
}

function dir(side) {
  return side === "black" ? -1 : 1;
}

function canPromote(type) {
  return ["R", "B", "S", "N", "L", "P"].includes(type);
}

function promotedType(type) {
  return {
    R: "PR",
    B: "PB",
    S: "PS",
    N: "PN",
    L: "PL",
    P: "PP"
  }[type] || type;
}

function baseType(type) {
  return {
    PR: "R",
    PB: "B",
    PS: "S",
    PN: "N",
    PL: "L",
    PP: "P"
  }[type] || type;
}

function promotionZone(side, row) {
  return side === "black" ? row <= 2 : row >= 6;
}

function mustPromote(type, side, toRow) {
  const t = baseType(type);
  if (t === "P" || t === "L") {
    return (side === "black" && toRow === 0) || (side === "white" && toRow === 8);
  }
  if (t === "N") {
    return (side === "black" && toRow <= 1) || (side === "white" && toRow >= 7);
  }
  return false;
}

function pieceDisplay(piece) {
  if (!piece) return "";
  return PIECE_LABELS[piece.type] || piece.type;
}

function getPseudoMoves(board, r, c) {
  const piece = board[r][c];
  if (!piece) return [];
  const side = piece.owner;
  const d = dir(side);
  const moves = [];

  function pushStep(dr, dc) {
    const nr = r + dr;
    const nc = c + dc;
    if (!inBounds(nr, nc)) return;
    const target = board[nr][nc];
    if (!target || target.owner !== side) {
      moves.push({ r: nr, c: nc });
    }
  }

  function pushSlide(dr, dc) {
    let nr = r + dr;
    let nc = c + dc;
    while (inBounds(nr, nc)) {
      const target = board[nr][nc];
      if (!target) {
        moves.push({ r: nr, c: nc });
      } else {
        if (target.owner !== side) moves.push({ r: nr, c: nc });
        break;
      }
      nr += dr;
      nc += dc;
    }
  }

  switch (piece.type) {
    case "K":
      [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
    case "G":
    case "PS":
    case "PN":
    case "PL":
    case "PP":
      [[d,-1],[d,0],[d,1],[0,-1],[0,1],[-d,0]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
    case "S":
      [[d,-1],[d,0],[d,1],[-d,-1],[-d,1]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
    case "N":
      [[2*d,-1],[2*d,1]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
    case "L":
      pushSlide(d,0);
      break;
    case "P":
      pushStep(d,0);
      break;
    case "R":
      [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>pushSlide(dr,dc));
      break;
    case "B":
      [[-1,-1],[-1,1],[1,-1],[1,1]].forEach(([dr,dc])=>pushSlide(dr,dc));
      break;
    case "PR":
      [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>pushSlide(dr,dc));
      [[-1,-1],[-1,1],[1,-1],[1,1]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
    case "PB":
      [[-1,-1],[-1,1],[1,-1],[1,1]].forEach(([dr,dc])=>pushSlide(dr,dc));
      [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>pushStep(dr,dc));
      break;
  }

  return moves;
}

function findKing(board, side) {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const p = board[r][c];
      if (p && p.owner === side && p.type === "K") {
        return { r, c };
      }
    }
  }
  return null;
}

function isCheck(board, side) {
  const king = findKing(board, side);
  if (!king) return true;

  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const p = board[r][c];
      if (!p || p.owner !== opponent(side)) continue;
      const pseudo = getPseudoMoves(board, r, c);
      if (pseudo.some(m => m.r === king.r && m.c === king.c)) {
        return true;
      }
    }
  }
  return false;
}

function applyBoardMove(board, hands, from, to, promoteFlag) {
  const nextBoard = clone(board);
  const nextHands = clone(hands);
  const piece = nextBoard[from.r][from.c];
  if (!piece) return null;

  const target = nextBoard[to.r][to.c];
  if (target) {
    const captured = baseType(target.type);
    if (captured !== "K") {
      nextHands[piece.owner][captured] += 1;
    }
  }

  nextBoard[from.r][from.c] = null;
  nextBoard[to.r][to.c] = {
    type: promoteFlag ? promotedType(piece.type) : piece.type,
    owner: piece.owner
  };

  return { board: nextBoard, hands: nextHands };
}

function legalBoardMoves(board, hands, r, c) {
  const piece = board[r][c];
  if (!piece) return [];

  const pseudo = getPseudoMoves(board, r, c);
  const legal = [];

  for (const move of pseudo) {
    const must = mustPromote(piece.type, piece.owner, move.r);
    const can =
      canPromote(piece.type) &&
      !["PR","PB","PS","PN","PL","PP"].includes(piece.type) &&
      (promotionZone(piece.owner, r) || promotionZone(piece.owner, move.r));

    const choices = must ? [true] : can ? [false, true] : [false];

    for (const promoteFlag of choices) {
      const applied = applyBoardMove(board, hands, { r, c }, move, promoteFlag);
      if (!applied) continue;
      if (!isCheck(applied.board, piece.owner)) {
        legal.push({
          from: { r, c },
          to: move,
          promote: promoteFlag
        });
      }
    }
  }

  return legal;
}

function hasPawnInFile(board, side, col) {
  for (let r = 0; r < 9; r++) {
    const p = board[r][col];
    if (p && p.owner === side && p.type === "P") return true;
  }
  return false;
}

function legalDrops(board, hands, side, type) {
  const moves = [];
  if (hands[side][type] <= 0) return moves;

  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (board[r][c]) continue;

      if (type === "P") {
        if ((side === "black" && r === 0) || (side === "white" && r === 8)) continue;
        if (hasPawnInFile(board, side, c)) continue;
      }
      if (type === "L") {
        if ((side === "black" && r === 0) || (side === "white" && r === 8)) continue;
      }
      if (type === "N") {
        if ((side === "black" && r <= 1) || (side === "white" && r >= 7)) continue;
      }

      const nextBoard = clone(board);
      const nextHands = clone(hands);
      nextBoard[r][c] = createPiece(type, side);
      nextHands[side][type] -= 1;

      if (!isCheck(nextBoard, side)) {
        moves.push({ to: { r, c }, piece: type });
      }
    }
  }

  return moves;
}

function allLegalExists(board, hands, side) {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const p = board[r][c];
      if (!p || p.owner !== side) continue;
      if (legalBoardMoves(board, hands, r, c).length > 0) return true;
    }
  }

  for (const t of ["R","B","G","S","N","L","P"]) {
    if (legalDrops(board, hands, side, t).length > 0) return true;
  }

  return false;
}

function isCheckmate(board, hands, side) {
  return isCheck(board, side) && !allLegalExists(board, hands, side);
}

let waitingPlayer = null;
const games = new Map();

function emitState(roomId) {
  const game = games.get(roomId);
  if (!game) return;

  const users = loadUsers();
  const blackRating = users[game.players.black.name]?.rating ?? 1500;
  const whiteRating = users[game.players.white.name]?.rating ?? 1500;

  io.to(roomId).emit("state", {
    board: game.board,
    hands: game.hands,
    turn: game.turn,
    players: {
      black: { name: game.players.black.name, rating: blackRating },
      white: { name: game.players.white.name, rating: whiteRating }
    }
  });
}

io.on("connection", (socket) => {
  socket.on("join", (name) => {
    name = String(name || "").trim();
    if (!name) return;

    ensureUser(name);
    socket.data.name = name;

    if (!waitingPlayer) {
      waitingPlayer = socket;
      socket.emit("waiting");
      return;
    }

    const p1 = waitingPlayer;
    const p2 = socket;
    waitingPlayer = null;

    const roomId = `room_${p1.id}_${p2.id}`;
    p1.join(roomId);
    p2.join(roomId);

    p1.data.roomId = roomId;
    p2.data.roomId = roomId;
    p1.data.side = "black";
    p2.data.side = "white";

    const game = {
      roomId,
      board: randomInitialBoard(),
      hands: createEmptyHands(),
      turn: "black",
      players: {
        black: { id: p1.id, name: p1.data.name },
        white: { id: p2.id, name: p2.data.name }
      },
      ended: false
    };

    games.set(roomId, game);

    p1.emit("start", { side: "black" });
    p2.emit("start", { side: "white" });

    emitState(roomId);
  });

  socket.on("move", (data) => {
    const roomId = socket.data.roomId;
    const side = socket.data.side;
    if (!roomId || !games.has(roomId)) return;

    const game = games.get(roomId);
    if (game.ended) return;
    if (game.turn !== side) return;

    if (data.kind === "move") {
      const from = data.from;
      const to = data.to;
      const promoteFlag = !!data.promote;

      if (!inBounds(from.r, from.c) || !inBounds(to.r, to.c)) return;

      const piece = game.board[from.r][from.c];
      if (!piece || piece.owner !== side) return;

      const legal = legalBoardMoves(game.board, game.hands, from.r, from.c);
      const found = legal.find(
        m =>
          m.to.r === to.r &&
          m.to.c === to.c &&
          m.promote === promoteFlag
      );
      if (!found) return;

      const applied = applyBoardMove(game.board, game.hands, from, to, promoteFlag);
      if (!applied) return;

      game.board = applied.board;
      game.hands = applied.hands;
    }

    if (data.kind === "drop") {
      const to = data.to;
      const piece = data.piece;

      if (!inBounds(to.r, to.c)) return;
      if (!["R","B","G","S","N","L","P"].includes(piece)) return;

      const legal = legalDrops(game.board, game.hands, side, piece);
      const found = legal.find(m => m.to.r === to.r && m.to.c === to.c && m.piece === piece);
      if (!found) return;

      game.board[to.r][to.c] = createPiece(piece, side);
      game.hands[side][piece] -= 1;
    }

    game.turn = opponent(game.turn);
    emitState(roomId);

    if (isCheckmate(game.board, game.hands, game.turn)) {
      game.ended = true;
      const winner = opponent(game.turn);
      const ratings = updateRatings(game, winner);

      io.to(roomId).emit("gameOver", {
        winner,
        reason: "checkmate",
        ratings
      });
    }
  });

  socket.on("resign", () => {
    const roomId = socket.data.roomId;
    const side = socket.data.side;
    if (!roomId || !games.has(roomId)) return;

    const game = games.get(roomId);
    if (game.ended) return;

    game.ended = true;
    const winner = opponent(side);
    const ratings = updateRatings(game, winner);

    io.to(roomId).emit("gameOver", {
      winner,
      reason: "resign",
      ratings
    });
  });

  socket.on("disconnect", () => {
    if (waitingPlayer && waitingPlayer.id === socket.id) {
      waitingPlayer = null;
    }

    const roomId = socket.data.roomId;
    if (roomId && games.has(roomId)) {
      const game = games.get(roomId);
      if (!game.ended) {
        io.to(roomId).emit("opponentLeft");
      }
    }
  });
});

app.get("/api/ranking", (req, res) => {
  const users = loadUsers();
  const ranking = Object.values(users).sort((a, b) => b.rating - a.rating);
  res.json(ranking);
});

server.listen(3001, () => {
  console.log("server running on http://localhost:3001");
});