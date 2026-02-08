use cozy_chess::{Board, Color, GameStatus, Move, Piece, BitBoard, Rank, File, Square};
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock};
use std::time::Instant; // تمت الإضافة لحساب الوقت

// ============================================================================
//  GLOBAL STATICS (عداد العقد)
// ============================================================================
pub static NODES: AtomicU64 = AtomicU64::new(0);

// ============================================================================
//  CONSTANTS (ثوابتك الأصلية محفوظة 100%)
// ============================================================================

pub const MAX_SEARCH_DEPTH: u8 = 8; 
pub const MAX_QUIESCENCE_DEPTH: u8 = 5;
const MATE_SCORE: i32 = 30000;
const INFINITY: i32 = 50000; 

// --- Contempt Factor ---
const CONTEMPT: i32 = 250;
const CONTEMPT_THRESHOLD: i32 = 0;

const ASPIRATION_WINDOW: i32 = 50;
const PARALLEL_THRESHOLD: u8 = 6;

const MG_VAL: [i32; 6] = [100, 305, 333, 563, 975, 0];
const EG_VAL: [i32; 6] = [100, 305, 333, 563, 975, 0];
const PHASE_W: [i32; 6] = [0, 3, 3, 5, 10, 0];

// PST Tables
const PAWN_MG: [i32; 64] = [0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, -10,-5,0,20,20,0,-5,-10, -5,0,5,25,25,5,0,-5, -10,-5,0,10,10,0,-5,-10, 0,0,5,5,5,5,0,0, 0,0,0,0,0,0,0,0];
const PAWN_EG: [i32; 64] = [0,0,0,0,0,0,0,0, -10,-20,-30,-40,-40,-30,-20,-10, -5,-10,-15,-20,-20,-15,-10,-5, 0,0,0,0,0,0,0,0, 10,20,30,40,40,30,20,10, 0,0,0,0,0,0,0,0, 0,0,5,10,10,5,0,0, 0,0,0,0,0,0,0,0];
const KNIGHT_PST: [i32; 64] = [-50,-40,-30,-30,-30,-30,-40,-50,-40,-20,0,5,5,0,-20,-40,-30,5,10,15,15,10,5,-30,-30,0,15,20,20,15,0,-30,-30,5,15,20,20,15,5,-30,-30,0,10,15,15,10,0,-30,-40,-20,0,0,0,0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50];
const BISHOP_PST: [i32; 64] = [-20,-10,-10,-10,-10,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,0,0,0,0,0,-10,-20,-10,-10,-10,-10,-10,-10,-20];
const ROOK_PST: [i32; 64] = [0,0,0,5,5,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 20,20,20,20,20,20,20,20, 0,0,0,0,0,0,0,0];
const QUEEN_PST: [i32; 64] = [-20,-10,-10,-5,-5,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,5,5,5,5,5,5,-10, 0,5,5,5,5,5,5,0, -5,0,5,5,5,5,0,-5, -10,0,5,5,5,5,0,-10, -10,-5,0,0,0,0,-5,-10, -20,-10,-10,-5,-5,-10,-10,-20];
const KING_MG: [i32; 64] = [20,30,10,0,0,10,30,20, 20,20,0,0,0,0,20,20, -10,-20,-20,-20,-20,-20,-20,-10, -20,-30,-30,-40,-40,-30,-30,-20, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30];
const KING_EG: [i32; 64] = [-50,-40,-30,-20,-20,-30,-40,-50, -50,-40,-30,-20,-20,-30,-40,-50, -30,-20,0,10,10,0,-20,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,10,20,20,10,-10,-30, -30,-20,-10,0,0,-10,-20,-30, -50,-40,-30,-20,-20,-30,-40,-50];

const PST_MG: [[i32; 64]; 6] = [PAWN_MG, KNIGHT_PST, BISHOP_PST, ROOK_PST, QUEEN_PST, KING_MG];
const PST_EG: [[i32; 64]; 6] = [PAWN_EG, KNIGHT_PST, BISHOP_PST, ROOK_PST, QUEEN_PST, KING_EG];

// --- LMR Table (نحتفظ به ولكن سنستخدمه بحذر شديد) ---
static LMR_TABLE: LazyLock<[[u8; 64]; 64]> = LazyLock::new(|| {
    let mut table = [[0; 64]; 64];
    let mut d = 0;
    while d < 64 {
        let mut i = 0;
        while i < 64 {
            if d < 3 || i < 2 {
                table[d][i] = 0;
            } else {
                let reduction = (0.75 + (d as f64).ln() * (i as f64).ln() / 2.25) as u8;
                table[d][i] = reduction;
            }
            i += 1;
        }
        d += 1;
    }
    table
});

// ============================================================================
//  TRANSPOSITION TABLE
// ============================================================================

#[derive(Clone, Copy, PartialEq, Debug)] 
pub enum TTNodeType { None = 0, Exact = 1, Alpha = 2, Beta = 3 }

struct AtomicTTEntry {
    key: AtomicU64,
    data: AtomicU64,
}

pub struct TranspositionTable {
    table: Vec<AtomicTTEntry>,
    size: usize,
}

impl TranspositionTable {
    pub fn new(mb: usize) -> Self {
        let size = (mb * 1024 * 1024) / std::mem::size_of::<AtomicTTEntry>();
        let mut table = Vec::with_capacity(size);
        for _ in 0..size {
            table.push(AtomicTTEntry {
                key: AtomicU64::new(0),
                data: AtomicU64::new(0),
            });
        }
        Self { table, size }
    }

    fn pack(score: i32, depth: u8, node_type: TTNodeType, best_move: Option<Move>) -> u64 {
        let mv_u16 = if let Some(m) = best_move {
            let from = m.from as u16;
            let to = m.to as u16;
            let promo = match m.promotion {
                None => 0,
                Some(Piece::Knight) => 1,
                Some(Piece::Bishop) => 2,
                Some(Piece::Rook) => 3,
                Some(Piece::Queen) => 4,
                _ => 0,
            };
            from | (to << 6) | (promo << 12)
        } else { 0 };

        let score_u16 = (score + 30000) as u16; 
        let type_u8 = node_type as u64;

        (mv_u16 as u64) | ((score_u16 as u64) << 16) | ((depth as u64) << 32) | (type_u8 << 40)
    }

    fn unpack(data: u64) -> (i32, u8, TTNodeType, Option<Move>) {
        let mv_u16 = (data & 0xFFFF) as u16;
        let score = ((data >> 16) & 0xFFFF) as i32 - 30000;
        let depth = ((data >> 32) & 0xFF) as u8;
        let type_raw = ((data >> 40) & 0x3) as u8;
        
        let node_type = match type_raw {
            1 => TTNodeType::Exact,
            2 => TTNodeType::Alpha,
            3 => TTNodeType::Beta,
            _ => TTNodeType::None,
        };

        let best_move = if mv_u16 == 0 {
            None
        } else {
            let from_idx = mv_u16 & 0x3F;
            let to_idx = (mv_u16 >> 6) & 0x3F;
            let promo_idx = (mv_u16 >> 12) & 0x7;
            let promo = match promo_idx {
                1 => Some(Piece::Knight),
                2 => Some(Piece::Bishop),
                3 => Some(Piece::Rook),
                4 => Some(Piece::Queen),
                _ => None,
            };
            Some(Move { from: Square::index(from_idx as usize), to: Square::index(to_idx as usize), promotion: promo })
        };

        (score, depth, node_type, best_move)
    }

    pub fn probe(&self, hash: u64) -> (bool, i32, u8, TTNodeType, Option<Move>) {
        let idx = (hash as usize) % self.size;
        let entry = &self.table[idx];
        let key_start = entry.key.load(Ordering::Acquire);
        if key_start != hash { return (false, 0, 0, TTNodeType::None, None); }
        let data = entry.data.load(Ordering::Acquire);
        let key_end = entry.key.load(Ordering::Acquire);
        if key_start == key_end {
            let (score, depth, node_type, best_move) = Self::unpack(data);
            return (true, score, depth, node_type, best_move);
        }
        (false, 0, 0, TTNodeType::None, None)
    }

    pub fn store(&self, hash: u64, score: i32, depth: u8, node_type: TTNodeType, best_move: Option<Move>) {
        let idx = (hash as usize) % self.size;
        let entry = &self.table[idx];
        let current_data = entry.data.load(Ordering::Relaxed);
        let (_, current_depth, _, _) = Self::unpack(current_data);
        let current_key = entry.key.load(Ordering::Relaxed);

        if current_key != hash || depth >= current_depth {
            let new_data = Self::pack(score, depth, node_type, best_move);
            entry.data.store(new_data, Ordering::Release);
            entry.key.store(hash, Ordering::Release);
        }
    }
}

// ============================================================================
//  HEURISTICS
// ============================================================================

#[derive(Clone)]
pub struct KillerMoves { pub killers: [[Option<Move>; 2]; 64] }
impl Default for KillerMoves { fn default() -> Self { Self { killers: [[None; 2]; 64] } } }

#[derive(Clone)]
pub struct HistoryTable { pub history: [[i32; 64]; 64] }
impl Default for HistoryTable { fn default() -> Self { Self { history: [[0; 64]; 64] } } }

// ============================================================================
//  BITBOARD HELPERS
// ============================================================================

const FILE_A: u64 = 0x0101010101010101;
#[inline(always)] fn file_bb(f: File) -> u64 { FILE_A << (f as usize) }
#[inline(always)] fn adj_files_bb(f: File) -> u64 {
    let f_bb = file_bb(f);
    let left = (f_bb >> 1) & !file_bb(File::H);
    let right = (f_bb << 1) & !file_bb(File::A);
    left | right
}
#[inline(always)] fn forward_bb(color: Color, r: Rank) -> u64 {
    match color {
        Color::White => !0u64 << ((r as usize + 1) * 8),
        Color::Black => !0u64 >> ((8 - r as usize) * 8),
    }
}

// ============================================================================
//  EVALUATION
// ============================================================================

pub fn evaluate(board: &Board) -> i32 {
    let mut score = 0;
    let mut phase = 24;
    for p_type in Piece::ALL {
        if p_type == Piece::Pawn || p_type == Piece::King { continue; }
        let count = board.pieces(p_type).len() as i32;
        phase -= PHASE_W[p_type as usize] * count;
    }
    let phase = phase.max(0).min(24);
    for sq in board.occupied() {
        let p = board.piece_on(sq).unwrap();
        let c = board.color_on(sq).unwrap();
        let p_idx = p as usize;
        let sq_idx = if c == Color::White { sq as usize } else { sq.flip_rank() as usize };
        let val = ((MG_VAL[p_idx] * phase) + (EG_VAL[p_idx] * (24 - phase))) / 24;
        let pst = ((PST_MG[p_idx][sq_idx] * phase) + (PST_EG[p_idx][sq_idx] * (24 - phase))) / 24;
        if c == Color::White { score += val + pst; } else { score -= val + pst; }
    }
    score += pawn_eval_fast(board, Color::White) - pawn_eval_fast(board, Color::Black);
    score += mobility_per_color(board, Color::White) - mobility_per_color(board, Color::Black);
    if board.side_to_move() == Color::White { score } else { -score }
}

fn pawn_eval_fast(board: &Board, color: Color) -> i32 {
    let mut s = 0;
    let us = board.colors(color);
    let them = board.colors(!color); 
    let pawns = board.pieces(Piece::Pawn) & us;
    let enemy_pawns = board.pieces(Piece::Pawn) & them;
    let no_enemy_queen = (board.pieces(Piece::Queen) & them).is_empty();
    for sq in pawns {
        let f = sq.file();
        let r = sq.rank();
        let file_mask = file_bb(f);
        let adj_mask = adj_files_bb(f);
        let forward_mask = forward_bb(color, r);
        if (pawns & BitBoard(file_mask)).len() > 1 { s -= 10; }
        if (pawns & BitBoard(adj_mask)).is_empty() { s -= 15; }
        let passed_mask = (BitBoard(file_mask) | BitBoard(adj_mask)) & BitBoard(forward_mask);
        if (passed_mask & enemy_pawns).is_empty() {
            let mut bonus = if no_enemy_queen { 20 } else { 15 };
            let rel_rank = if color == Color::White { r as i32 } else { 7 - r as i32 };
            bonus += rel_rank * 10;
            s += bonus;
        }
        let my_sq_mask = 1u64 << (sq as usize);
        let behind_mask_u64 = !forward_mask & !my_sq_mask;
        let supports = pawns & BitBoard((adj_mask | file_mask) & behind_mask_u64);
        if supports.is_empty() { s -= 5; }
    }
    s
}

fn mobility_per_color(board: &Board, color: Color) -> i32 {
    let mut m = 0;
    let occ = board.occupied();
    let us = board.colors(color);
    for p_type in [Piece::Knight, Piece::Bishop, Piece::Rook, Piece::Queen] {
        let pieces = board.pieces(p_type) & us;
        for sq in pieces {
            let attacks = match p_type {
                Piece::Knight => cozy_chess::get_knight_moves(sq),
                Piece::Bishop => cozy_chess::get_bishop_moves(sq, occ),
                Piece::Rook => cozy_chess::get_rook_moves(sq, occ),
                Piece::Queen => cozy_chess::get_bishop_moves(sq, occ) | cozy_chess::get_rook_moves(sq, occ),
                _ => BitBoard::EMPTY,
            };
            m += (attacks.len() as i32) * 2;
        }
    }
    m
}

// ============================================================================
//  SEARCH HELPERS
// ============================================================================

fn order_moves(bd: &Board, mvs: &mut Vec<Move>, ttm: Option<Move>, km: &KillerMoves, ht: &HistoryTable, d: u8) {
    mvs.sort_by_cached_key(|&m| {
        if Some(m) == ttm { return -2_000_000_000; }
        if let Some(cap) = bd.piece_on(m.to) {
            let attacker = bd.piece_on(m.from).unwrap();
            return -1_000_000 - (MG_VAL[cap as usize] * 10 - MG_VAL[attacker as usize]);
        }
        if km.killers[d as usize].contains(&Some(m)) { return -900_000; }
        -ht.history[m.from as usize][m.to as usize]
    });
}

fn has_non_pawn_material(bd: &Board) -> bool {
    let us = bd.colors(bd.side_to_move());
    let others = bd.pieces(Piece::Knight) | bd.pieces(Piece::Bishop) | bd.pieces(Piece::Rook) | bd.pieces(Piece::Queen);
    !(others & us).is_empty()
}

fn make_null_move(bd: &Board) -> Option<Board> {
    let fen = format!("{}", bd);
    let mut parts: Vec<&str> = fen.split_whitespace().collect();
    parts[1] = if parts[1] == "w" { "b" } else { "w" };
    parts[3] = "-";
    let new_fen = parts.join(" ");
    Board::from_fen(&new_fen, false).ok()
}

// ============================================================================
//  QUIESCENCE SEARCH
// ============================================================================

pub fn quiescence(bd: &mut Board, mut alpha: i32, beta: i32, qd: u8) -> i32 {
    NODES.fetch_add(1, Ordering::Relaxed); // زيادة عداد العقد

    let stand_pat = evaluate(bd);
    if stand_pat >= beta { return beta; }
    if stand_pat > alpha { alpha = stand_pat; }
    if qd == 0 { return stand_pat; }
    
    let mut mvs = Vec::with_capacity(16);
    let enemy_pieces = bd.colors(!bd.side_to_move());
    bd.generate_moves(|mut moves| {
        let mut capture_mask = enemy_pieces;
        if let Some(ep_sq) = bd.en_passant() { capture_mask |= BitBoard(1u64 << ep_sq as usize); }
        moves.to &= capture_mask; 
        for m in moves { mvs.push(m); }
        false
    });
    
    mvs.sort_by_cached_key(|&m| {
        let attacker = bd.piece_on(m.from).unwrap() as i32;
        let victim = bd.piece_on(m.to).unwrap_or(Piece::Pawn) as i32;
        -(MG_VAL[victim as usize] * 10 - MG_VAL[attacker as usize])
    });

    for m in mvs {
        let mut nb = bd.clone(); 
        nb.play(m);
        let s = -quiescence(&mut nb, -beta, -alpha, qd - 1);
        if s >= beta { return beta; }
        if s > alpha { alpha = s; }
    }
    alpha
}

// ============================================================================
//  NEGAMAX (With HIGH-DEPTH ONLY LMR)
// ============================================================================

pub fn negamax(
    bd: &mut Board, 
    mut d: u8, 
    mut alpha: i32, 
    beta: i32, 
    km: &mut KillerMoves, 
    ht: &mut HistoryTable, 
    hs: &[u64], 
    path: &mut Vec<u64>, 
    tt: &Arc<TranspositionTable>, 
    ply: u8,
    allow_nmp: bool
) -> i32 {
    NODES.fetch_add(1, Ordering::Relaxed); // زيادة عداد العقد

    let hash = bd.hash();
    
    // --- Repetition & Contempt ---
    let in_path = path.iter().any(|&h| h == hash);
    let in_history = hs.iter().rev().take(bd.halfmove_clock() as usize + 1).any(|&h| h == hash);

    if ply > 0 && (in_path || in_history) {
        let ev = evaluate(bd);
        if ev > CONTEMPT_THRESHOLD { return -CONTEMPT; } else { return 0; }
    }
    
    path.push(hash);

    // --- TT Probe ---
    let mut ttm = None;
    let (found, entry_score, entry_depth, entry_type, entry_move) = tt.probe(hash);
    if found {
        ttm = entry_move;
        if entry_depth >= d {
            let mut score = entry_score;
            if score > MATE_SCORE - 1000 { score -= ply as i32; }
            else if score < -MATE_SCORE + 1000 { score += ply as i32; }
            match entry_type {
                TTNodeType::Exact => { path.pop(); return score; },
                TTNodeType::Alpha => if score <= alpha { path.pop(); return score; },
                TTNodeType::Beta => if score >= beta { path.pop(); return score; },
                _ => {}
            }
        }
    }

    if bd.status() != GameStatus::Ongoing {
        path.pop();
        if bd.status() == GameStatus::Won { return -MATE_SCORE + ply as i32; }
        let ev = evaluate(bd);
        if ev > CONTEMPT_THRESHOLD { return -CONTEMPT; } else { return 0; }
    }
    
    if d == 0 { 
        path.pop();
        return quiescence(bd, alpha, beta, MAX_QUIESCENCE_DEPTH); 
    }

    let in_check = !bd.checkers().is_empty();
    if in_check { d += 1; }

    // --- Null Move Pruning ---
    if allow_nmp && d >= 3 && !in_check && has_non_pawn_material(bd) {
        let r = 2;
        if let Some(mut null_bd) = make_null_move(bd) {
            let score = -negamax(&mut null_bd, d - 1 - r, -beta, -beta + 1, km, ht, hs, path, tt, ply + 1, false);
            if score >= beta {
                path.pop();
                return beta;
            }
        }
    }

    let mut mvs = Vec::with_capacity(32);
    bd.generate_moves(|pm| { mvs.extend(pm); false });
    if mvs.is_empty() { 
        path.pop();
        let ev = evaluate(bd);
        if ev > CONTEMPT_THRESHOLD { return -CONTEMPT; } else { return 0; }
    }

    order_moves(bd, &mut mvs, ttm, km, ht, d);

    let mut max_s = -INFINITY;
    let mut best_m = None;
    let mut moves_searched = 0;

    for m in mvs {
        let mut nb = bd.clone(); 
        nb.play(m);
        
        let mut s;
        
        if moves_searched == 0 {
            // PV Move: Full Window Search
            s = -negamax(&mut nb, d - 1, -beta, -alpha, km, ht, hs, path, tt, ply + 1, true);
        } else {
            // --- HIGH-DEPTH ONLY LMR Logic ---
            let is_capture = bd.piece_on(m.to).is_some();
            let is_promotion = m.promotion.is_some();
            let gives_check = !nb.checkers().is_empty();
            let is_killer = km.killers[d as usize].contains(&Some(m));

            let mut reduction = 0;
            
            // التعديل النهائي:
            // 1. العمق يجب أن يكون 4 أو أكثر (لحماية التكتيكات القصيرة)
            // 2. النقلة يجب أن تكون بعد السادسة (لضمان أننا لا نقلص نقلات جيدة)
            if d >= 4 && moves_searched >= 6 && !in_check && !is_capture && !is_promotion && !gives_check && !is_killer {
                let mut r = LMR_TABLE[d.min(63) as usize][moves_searched.min(63)] as i32;
                
                // تخفيف قوي جداً: نقلل الخصم بمقدار 1 دائماً
                if r > 0 { r -= 1; }
                
                // حماية إضافية للتاريخ
                if ht.history[m.from as usize][m.to as usize] > 0 {
                    r = 0;
                }

                reduction = r.max(0) as u8;
            }

            // Reduced Search (Zero Window)
            let reduced_depth = (d - 1).saturating_sub(reduction).max(0);
            s = -negamax(&mut nb, reduced_depth, -alpha - 1, -alpha, km, ht, hs, path, tt, ply + 1, true);

            // Re-search if reduced search failed (too good)
            if s > alpha && reduction > 0 {
                s = -negamax(&mut nb, d - 1, -alpha - 1, -alpha, km, ht, hs, path, tt, ply + 1, true);
            }

            // Full Window Search if Zero Window failed
            if s > alpha && s < beta {
                s = -negamax(&mut nb, d - 1, -beta, -alpha, km, ht, hs, path, tt, ply + 1, true);
            }
        }
        
        moves_searched += 1;
        if s > max_s { max_s = s; best_m = Some(m); }
        if s > alpha {
            alpha = s;
            if alpha >= beta {
                if bd.piece_on(m.to).is_none() {
                    km.killers[d as usize][1] = km.killers[d as usize][0];
                    km.killers[d as usize][0] = Some(m);
                    ht.history[m.from as usize][m.to as usize] += (d * d) as i32;
                    if ht.history[m.from as usize][m.to as usize] > 100_000 {
                        for r in 0..64 { for c in 0..64 { ht.history[r][c] /= 2; } }
                    }
                }
                break;
            }
        }
    }

    let mut store_score = max_s;
    if store_score > MATE_SCORE - 1000 { store_score += ply as i32; }
    else if store_score < -MATE_SCORE + 1000 { store_score -= ply as i32; }

    let node_type = if max_s >= beta { TTNodeType::Beta } 
                    else if max_s > alpha { TTNodeType::Exact } 
                    else { TTNodeType::Alpha };
    
    tt.store(hash, store_score, d, node_type, best_m);
    
    path.pop();
    max_s
}

// ============================================================================
//  ROOT SEARCH
// ============================================================================

pub fn find_best_move(
    bd: &mut Board, 
    md: u8, 
    hs: &Vec<u64>, 
    tt: &Arc<TranspositionTable>
) -> Option<Move> {
    let mut best_global = None;
    
    let mut main_km = KillerMoves::default();
    let mut main_ht = HistoryTable::default();

    let mut last_score = 0;

    // تصفير عداد العقد وبدء التوقيت
    NODES.store(0, Ordering::Relaxed);
    let start_time = Instant::now();

    for d in 1..=md {
        let mut delta = ASPIRATION_WINDOW;
        let mut alpha = -INFINITY;
        let mut beta = INFINITY;
        let mut fail_count = 0;

        if d > 5 {
            alpha = (last_score - delta).max(-INFINITY);
            beta = (last_score + delta).min(INFINITY);
        }

        loop {
            let mut mvs = Vec::new();
            bd.generate_moves(|pm| { mvs.extend(pm); false });
            if mvs.is_empty() { break; }

            let (_, _, _, _, ttm) = tt.probe(bd.hash());
            order_moves(bd, &mut mvs, ttm, &main_km, &main_ht, d);

            let mut best_move_this_iter = mvs[0];
            let mut best_score_this_iter = -INFINITY;
            
            // --- PVS Root Search ---
            let mut nb = bd.clone();
            nb.play(best_move_this_iter);
            
            let mut root_path = Vec::with_capacity(64);
            root_path.push(bd.hash());

            let score = -negamax(&mut nb, d - 1, -beta, -alpha, &mut main_km, &mut main_ht, hs, &mut root_path, tt, 1, true);
            
            if score > best_score_this_iter {
                best_score_this_iter = score;
            }

            let mut search_alpha = alpha.max(score);

            let rest_moves = &mvs[1..];
            if !rest_moves.is_empty() {
                if d < PARALLEL_THRESHOLD {
                    for &m in rest_moves {
                        if search_alpha >= beta { break; } 

                        let mut nb = bd.clone();
                        nb.play(m);
                        let mut path = Vec::with_capacity(64);
                        path.push(bd.hash());
                        
                        let mut s = -negamax(&mut nb, d - 1, -search_alpha - 1, -search_alpha, &mut main_km, &mut main_ht, hs, &mut path, tt, 1, true);
                        
                        if s > search_alpha && s < beta {
                            s = -negamax(&mut nb, d - 1, -beta, -search_alpha, &mut main_km, &mut main_ht, hs, &mut path, tt, 1, true);
                        }

                        if s > best_score_this_iter {
                            best_score_this_iter = s;
                            best_move_this_iter = m;
                            if s > search_alpha { search_alpha = s; }
                        }
                    }
                } else {
                    let results: Vec<(Move, i32)> = rest_moves.par_iter().map(|&m| {
                        let mut nb = bd.clone();
                        nb.play(m);
                        let mut l_km = main_km.clone();
                        let mut l_ht = main_ht.clone();
                        let mut path = Vec::with_capacity(64);
                        path.push(bd.hash());
                        
                        let mut s = -negamax(&mut nb, d - 1, -search_alpha - 1, -search_alpha, &mut l_km, &mut l_ht, hs, &mut path, tt, 1, true);
                        
                        if s > search_alpha && s < beta {
                            s = -negamax(&mut nb, d - 1, -beta, -search_alpha, &mut l_km, &mut l_ht, hs, &mut path, tt, 1, true);
                        }
                        (m, s)
                    }).collect();

                    for (m, s) in results {
                        if s > best_score_this_iter {
                            best_score_this_iter = s;
                            best_move_this_iter = m;
                            if s > search_alpha { search_alpha = s; }
                        }
                    }
                }
            }

            // --- Aspiration Window Logic ---
            if best_score_this_iter > alpha && best_score_this_iter < beta {
                last_score = best_score_this_iter;
                best_global = Some(best_move_this_iter);
                tt.store(bd.hash(), best_score_this_iter, d, TTNodeType::Exact, Some(best_move_this_iter));
                
                // --- طباعة المعلومات مع الوقت و NPS ---
                let nodes = NODES.load(Ordering::Relaxed);
                let elapsed = start_time.elapsed();
                let nps = if elapsed.as_micros() > 0 {
                    (nodes as u128 * 1_000_000) / elapsed.as_micros()
                } else { 0 };
                
                println!("Info: Depth {} Score {} Move {} Time {:.3}s Nodes {} NPS {}", 
                    d, best_score_this_iter, best_move_this_iter, elapsed.as_secs_f64(), nodes, nps);
                
                break; 
            }

            if best_score_this_iter <= alpha {
                if alpha <= -INFINITY {
                    last_score = best_score_this_iter;
                    best_global = Some(best_move_this_iter);
                    tt.store(bd.hash(), best_score_this_iter, d, TTNodeType::Exact, Some(best_move_this_iter));
                    break;
                }
                println!("Info: AspWin Fail Low (Score: {}, Alpha: {}) -> Widening", best_score_this_iter, alpha);
                alpha = (alpha - delta).max(-INFINITY);
                fail_count += 1;
            }
            else if best_score_this_iter >= beta {
                if beta >= INFINITY {
                    last_score = best_score_this_iter;
                    best_global = Some(best_move_this_iter);
                    tt.store(bd.hash(), best_score_this_iter, d, TTNodeType::Exact, Some(best_move_this_iter));
                    break;
                }
                println!("Info: AspWin Fail High (Score: {}, Beta: {}) -> Widening", best_score_this_iter, beta);
                beta = (beta + delta).min(INFINITY);
                fail_count += 1;
            }

            if fail_count >= 3 || delta > 1000 {
                println!("Info: Switching to FULL SEARCH (FailCount={})", fail_count);
                alpha = -INFINITY;
                beta = INFINITY;
            } else {
                delta += delta / 2;
            }
        }

        if last_score.abs() > MATE_SCORE - 1000 { break; }
    }
    best_global
}