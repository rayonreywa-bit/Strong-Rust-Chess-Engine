// src/main.rs
// CrispyCrab — Ultimate Chess GUI
//ستجد في الاسفل وفي ملف ai.rs جميع التعليقات باللغة الانجليزية

use macroquad::prelude::*;
// *** Import load_sound_from_bytes for embedded audio ***
use macroquad::audio::{load_sound_from_bytes, play_sound, play_sound_once, Sound, PlaySoundParams}; 

use cozy_chess::{Board, Move, PieceMoves, Square, Piece, Color}; 
use std::str::FromStr;
use std::collections::{HashSet, HashMap}; 
use rust_embed::RustEmbed;
use async_std::{channel, task};
use std::sync::Arc;
use std::time::{Instant, Duration};

// Import the AI module
mod ai;
use ai::{TranspositionTable, MAX_SEARCH_DEPTH}; 

#[derive(RustEmbed)]
#[folder = "assets/"]
struct Asset;

const BOARD_SIZE: f32 = 512.0;
const SQUARE_SIZE: f32 = BOARD_SIZE / 8.0;
const TEXT_FONT_SIZE: u16 = 20;
const ANIMATION_DURATION: f32 = 0.25; 

#[derive(Clone, Copy, PartialEq)]
enum GameMode {
    PlayerVsPlayer,
    PlayerVsAi,
    AiVsPlayer,
    AiVsAi,
}

#[derive(Clone, Copy, PartialEq)]
enum HintStyle {
    Normal,                 
    Capture,                
    Castle(Square),         
}

struct PieceAnimation {
    piece: Piece,
    color: Color,
    start_pos: Vec2,
    target_pos: Vec2,
    start_time: f64,
    duration: f32,
    target_sq: Square, 
}

#[derive(Clone)]
struct Game {
    board: Board,
    history_hashes: Vec<u64>,
    san_moves: Vec<String>,
    history_boards: Vec<Board>,
    last_move: Option<Move>,
}

impl Game {
    fn new() -> Self {
        let board = Board::default();
        let mut g = Self {
            board: board.clone(),
            history_hashes: Vec::new(),
            san_moves: Vec::new(),
            history_boards: Vec::new(),
            last_move: None,
        };
        g.history_hashes.push(g.board.hash());
        g.history_boards.push(board);
        g
    }
    
    fn reload_from_fen(&mut self, fen: &str) -> Result<(), String> {
        match Board::from_fen(fen, false) {
            Ok(new_board) => {
                self.board = new_board;
                self.history_boards.clear();
                self.history_boards.push(self.board.clone());
                self.history_hashes.clear();
                self.history_hashes.push(self.board.hash());
                self.san_moves.clear();
                self.last_move = None;
                Ok(())
            }
            Err(e) => Err(format!("Invalid FEN: {:?}", e)),
        }
    }

    fn legal_moves_vec(&self) -> Vec<Move> {
        let mut moves = Vec::new();
        self.board.generate_moves(|pm: PieceMoves| {
            for mv in pm {
                moves.push(mv);
            }
            false
        });
        moves
    }

    fn make_move(&mut self, mv: Move) -> Result<(), String> {
        self.board.try_play(mv).map_err(|e| format!("Illegal move: {:?}", e))?;
        self.history_hashes.push(self.board.hash());
        self.san_moves.push(format_move_short(&mv));
        self.history_boards.push(self.board.clone());
        self.last_move = Some(mv);
        Ok(())
    }

    fn undo_move(&mut self) -> bool {
        if self.history_boards.len() > 1 {
            self.history_boards.pop();
            self.san_moves.pop();
            self.history_hashes.pop();
            self.board = self.history_boards.last().unwrap().clone();
            self.last_move = None; 
            true
        } else {
            false
        }
    }

    fn is_threefold_repetition(&self) -> bool {
        let h = self.board.hash();
        let count = self.history_hashes.iter().filter(|&&x| x == h).count();
        count >= 3
    }

    fn is_fifty_move_rule(&self) -> bool {
        self.board.halfmove_clock() >= 100
    }

    // *** New Function: Check for Insufficient Material ***
    fn is_insufficient_material(&self) -> bool {
        // 1. If there are Pawns, Rooks, or Queens, it's NOT a draw by material.
        if !self.board.pieces(Piece::Pawn).is_empty()
            || !self.board.pieces(Piece::Rook).is_empty()
            || !self.board.pieces(Piece::Queen).is_empty()
        {
            return false;
        }

        // Count pieces for each side (Kings are always present if game is valid)
        let white_pieces = self.board.colors(Color::White);
        let black_pieces = self.board.colors(Color::Black);
        let white_count = white_pieces.len();
        let black_count = black_pieces.len();

        // Case 1: King vs King (1 vs 1)
        if white_count == 1 && black_count == 1 {
            return true;
        }

        // Case 2: King + Minor Piece vs King (2 vs 1 OR 1 vs 2)
        // Since we already ruled out P, R, Q, the extra piece MUST be N or B.
        if (white_count == 2 && black_count == 1) || (white_count == 1 && black_count == 2) {
            return true;
        }

        // Case 3: King + Bishop vs King + Bishop (Same Color Bishops)
        // This is a specific draw scenario.
        if white_count == 2 && black_count == 2 {
            let white_bishops = self.board.pieces(Piece::Bishop) & white_pieces;
            let black_bishops = self.board.pieces(Piece::Bishop) & black_pieces;

            // Ensure both extra pieces are bishops
            if white_bishops.len() == 1 && black_bishops.len() == 1 {
                let wb_sq = white_bishops.next_square().unwrap();
                let bb_sq = black_bishops.next_square().unwrap();
                
                // Check square color (Light or Dark)
                // (rank + file) % 2 == 0 is dark (usually), != 0 is light.
                // We just need to check if they are equal.
                let wb_color = (wb_sq.rank() as usize + wb_sq.file() as usize) % 2;
                let bb_color = (bb_sq.rank() as usize + bb_sq.file() as usize) % 2;

                if wb_color == bb_color {
                    return true;
                }
            }
        }

        false
    }

    fn game_over_status(&self) -> Option<String> {
        let mut legal_count = 0usize;
        self.board.generate_moves(|pm: PieceMoves| {
            legal_count += pm.len();
            false
        });

        // Checkmate or Stalemate
        if legal_count == 0 {
            let checkers = self.board.checkers();
            let in_check = !checkers.is_empty();
            if in_check {
                let winner = if self.board.side_to_move() == Color::White { "Black" } else { "White" };
                return Some(format!("Checkmate — {} wins", winner));
            } else {
                return Some("Stalemate — draw".to_string());
            }
        }

        // Draw Rules
        if self.is_fifty_move_rule() {
            return Some("Draw by fifty-move rule".to_string());
        }
        if self.is_threefold_repetition() {
            return Some("Draw by threefold repetition".to_string());
        }
        // *** Added Insufficient Material Check ***
        if self.is_insufficient_material() {
            return Some("Draw by insufficient material".to_string());
        }

        None
    }

    // *** Generate PGN String ***
    fn generate_pgn(&self) -> String {
        let mut pgn = String::new();
        pgn.push_str("[Event \"CrispyCrab Game\"]\n");
        pgn.push_str("[Site \"Local\"]\n");
        pgn.push_str("[Date \"????.??.??\"]\n");
        pgn.push_str("[Round \"?\"]\n");
        pgn.push_str("[White \"?\"]\n");
        pgn.push_str("[Black \"?\"]\n");
        
        let result = if let Some(status) = self.game_over_status() {
            if status.contains("White wins") { "1-0" }
            else if status.contains("Black wins") { "0-1" }
            else { "1/2-1/2" }
        } else {
            "*"
        };
        pgn.push_str(&format!("[Result \"{}\"]\n\n", result));

        for (i, mv_str) in self.san_moves.iter().enumerate() {
            if i % 2 == 0 {
                pgn.push_str(&format!("{}. ", (i / 2) + 1));
            }
            pgn.push_str(mv_str);
            pgn.push(' ');
        }
        pgn.push_str(result);
        pgn
    }
}

fn format_move_short(mv: &Move) -> String {
    let mut s = format!("{}{}", mv.from, mv.to);
    if let Some(promo) = mv.promotion {
        let ch = match promo {
            Piece::Queen => 'q',
            Piece::Rook => 'r',
            Piece::Bishop => 'b',
            Piece::Knight => 'n',
            _ => '?',
        };
        s.push(ch);
    }
    s
}

fn get_piece_filename(piece: Piece, color: Color) -> String {
    let p_char = match piece {
        Piece::Pawn => 'P',
        Piece::Knight => 'N',
        Piece::Bishop => 'B',
        Piece::Rook => 'R',
        Piece::Queen => 'Q',
        Piece::King => 'K',
    };
    let c_char = match color {
        Color::White => 'w',
        Color::Black => 'b',
    };
    format!("{}{}.png", c_char, p_char)
}

fn fen_char_to_piece_color(ch: char) -> Option<(Piece, Color)> {
    match ch {
        'P' => Some((Piece::Pawn, Color::White)),
        'N' => Some((Piece::Knight, Color::White)),
        'B' => Some((Piece::Bishop, Color::White)),
        'R' => Some((Piece::Rook, Color::White)),
        'Q' => Some((Piece::Queen, Color::White)),
        'K' => Some((Piece::King, Color::White)),
        'p' => Some((Piece::Pawn, Color::Black)),
        'n' => Some((Piece::Knight, Color::Black)),
        'b' => Some((Piece::Bishop, Color::Black)),
        'r' => Some((Piece::Rook, Color::Black)),
        'q' => Some((Piece::Queen, Color::Black)),
        'k' => Some((Piece::King, Color::Black)),
        _ => None,
    }
}

// -------------------------------------------------------------------------
// *** FEN Helper Functions ***
// -------------------------------------------------------------------------

fn piece_to_fen_char(piece: Piece, color: Color) -> char {
    let ch = match piece {
        Piece::Pawn => 'p',
        Piece::Knight => 'n',
        Piece::Bishop => 'b',
        Piece::Rook => 'r',
        Piece::Queen => 'q',
        Piece::King => 'k',
    };
    if color == Color::White {
        ch.to_ascii_uppercase()
    } else {
        ch
    }
}

fn fen_to_array(fen_part: &str) -> Vec<char> {
    let mut board_arr = Vec::new();
    for row in fen_part.split('/') {
        for ch in row.chars() {
            if ch.is_ascii_digit() {
                let skip = ch.to_digit(10).unwrap() as usize;
                for _ in 0..skip {
                    board_arr.push('1');
                }
            } else {
                board_arr.push(ch);
            }
        }
    }
    board_arr
}

fn array_to_fen(arr: &[char]) -> String {
    let mut fen_part = String::new(); 
    for rank_idx in 0..8 {
        let mut empty_count = 0;
        for file_idx in 0..8 {
            let index = rank_idx * 8 + file_idx;
            let ch = arr[index];
            if ch == '1' {
                empty_count += 1;
            } else {
                if empty_count > 0 {
                    fen_part.push_str(&empty_count.to_string());
                    empty_count = 0;
                }
                fen_part.push(ch);
            }
        }
        if empty_count > 0 {
            fen_part.push_str(&empty_count.to_string());
        }
        if rank_idx < 7 {
            fen_part.push('/');
        }
    }
    fen_part 
}

fn update_castling_rights(board_arr: &[char], original_castling: &str) -> String {
    let mut new_rights = String::new();
    let white_king_sq = Square::E1;
    let black_king_sq = Square::E8;
    let white_q_rook_sq = Square::A1;
    let white_k_rook_sq = Square::H1;
    let black_q_rook_sq = Square::A8;
    let black_k_rook_sq = Square::H8;

    let check_piece_at = |sq: Square, piece: Piece, color: Color| -> bool {
        let rank_idx = 7 - sq.rank() as usize;
        let file_idx = sq.file() as usize;
        let array_index = rank_idx * 8 + file_idx;
        let expected_char = piece_to_fen_char(piece, color);
        board_arr.get(array_index) == Some(&expected_char)
    };

    if check_piece_at(white_king_sq, Piece::King, Color::White) {
        if original_castling.contains('K') && check_piece_at(white_k_rook_sq, Piece::Rook, Color::White) {
            new_rights.push('K');
        }
        if original_castling.contains('Q') && check_piece_at(white_q_rook_sq, Piece::Rook, Color::White) {
            new_rights.push('Q');
        }
    }

    if check_piece_at(black_king_sq, Piece::King, Color::Black) {
        if original_castling.contains('k') && check_piece_at(black_k_rook_sq, Piece::Rook, Color::Black) {
            new_rights.push('k');
        }
        if original_castling.contains('q') && check_piece_at(black_q_rook_sq, Piece::Rook, Color::Black) {
            new_rights.push('q');
        }
    }
    
    if new_rights.is_empty() {
        "-".to_string()
    } else {
        new_rights
    }
}

fn update_board_from_fen_manually(current_fen: &str, square: Square, piece_info: Option<(Piece, Color)>) -> String {
    let parts: Vec<&str> = current_fen.split_whitespace().collect();
    if parts.len() < 6 { return current_fen.to_string(); }
    
    let board = Board::from_fen(current_fen, false).unwrap_or_else(|_| Board::default());
    let mut board_arr = fen_to_array(parts[0]);
    
    let rank_idx = 7 - square.rank() as usize; 
    let file_idx = square.file() as usize;     
    let array_index = rank_idx * 8 + file_idx;
    
    if let Some((piece, color)) = piece_info {
        if piece == Piece::King {
            let old_king_sq = board.king(color);
            if board.piece_on(old_king_sq) == Some(Piece::King) && board.color_on(old_king_sq) == Some(color) {
                let old_rank_idx = 7 - old_king_sq.rank() as usize;
                let old_file_idx = old_king_sq.file() as usize;
                let old_array_index = old_rank_idx * 8 + old_file_idx;
                if old_array_index != array_index {
                    board_arr[old_array_index] = '1';
                }
            }
            board_arr[array_index] = piece_to_fen_char(piece, color);
        } else {
            board_arr[array_index] = piece_to_fen_char(piece, color);
        }
    } else {
        let piece_on_sq = board.piece_on(square);
        if piece_on_sq == Some(Piece::King) {
            return current_fen.to_string();
        } else {
            board_arr[array_index] = '1'; 
        }
    }
    
    let fen_piece_part = array_to_fen(&board_arr);
    let new_castling_rights = update_castling_rights(&board_arr, parts[2]);

    format!("{} {} {} {} {} {}", fen_piece_part, parts[1], new_castling_rights, parts[3], parts[4], parts[5])
}

fn square_to_screen(sq: Square, origin: Vec2) -> (f32, f32) {
    let s = format!("{}", sq);
    let file = s.chars().nth(0).unwrap();
    let rank = s.chars().nth(1).unwrap();
    let file_idx = (file as u8 - b'a') as usize;
    let rank_idx = (rank as u8 - b'1') as usize;
    let x = origin.x + file_idx as f32 * SQUARE_SIZE;
    let y = origin.y + (7 - rank_idx) as f32 * SQUARE_SIZE;
    (x, y)
}

fn screen_to_square(mx: f32, my: f32, origin: Vec2) -> Option<Square> {
    if mx < origin.x || my < origin.y || mx > origin.x + BOARD_SIZE || my > origin.y + BOARD_SIZE {
        return None;
    }
    let relx = mx - origin.x;
    let rely = my - origin.y;
    let file_idx = (relx / SQUARE_SIZE).floor() as usize;
    let rank_idx = 7 - (rely / SQUARE_SIZE).floor() as usize;
    if file_idx > 7 || rank_idx > 7 { return None; }
    let file_char = (b'a' + file_idx as u8) as char;
    let rank_char = (b'1' + rank_idx as u8) as char;
    let s = format!("{}{}", file_char, rank_char);
    match Square::from_str(&s) {
        Ok(sq) => Some(sq),
        Err(_) => None,
    }
}

fn draw_piece_centered(
    texture: Texture2D,
    x: f32,
    y: f32,
    square_size: f32,
    piece_type: Piece
) {
    let base_scale = 0.75; 
    let width_scale = if piece_type == Piece::Pawn {
        base_scale * 0.80 
    } else {
        base_scale
    };
    let draw_width = square_size * width_scale;
    let draw_height = square_size * base_scale;
    let offset_x = (square_size - draw_width) / 2.0;
    let offset_y = (square_size - draw_height) / 2.0;

    draw_texture_ex(
        texture,
        x + offset_x,
        y + offset_y,
        WHITE,
        DrawTextureParams {
            dest_size: Some(vec2(draw_width, draw_height)),
            ..Default::default()
        }
    );
}

fn get_castling_rook_square(king_from: Square, king_to: Square) -> Option<Square> {
    if king_from == Square::E1 && king_to == Square::G1 { return Some(Square::H1); }
    if king_from == Square::E1 && king_to == Square::C1 { return Some(Square::A1); }
    if king_from == Square::E8 && king_to == Square::G8 { return Some(Square::H8); }
    if king_from == Square::E8 && king_to == Square::C8 { return Some(Square::A8); }
    None
}

fn calculate_hints(game: &Game, from_sq: Square) -> Vec<(Square, HintStyle)> {
    let mut hints = Vec::new();
    let legal_moves = game.legal_moves_vec();
    for m in legal_moves {
        if m.from == from_sq {
            let mut style = HintStyle::Normal;
            let moving_piece = game.board.piece_on(m.from);
            
            let is_capture = game.board.colors(!game.board.side_to_move()).has(m.to)
                || (moving_piece == Some(Piece::Pawn) && m.from.file() != m.to.file() && game.board.piece_on(m.to).is_none());
            
            if is_capture {
                style = HintStyle::Capture;
            } else if moving_piece == Some(Piece::King) {
                if let Some(rook_sq) = get_castling_rook_square(m.from, m.to) {
                    style = HintStyle::Castle(rook_sq);
                }
            }
            hints.push((m.to, style));
        }
    }
    hints
}

fn hex_color(hex: u32) -> macroquad::prelude::Color {
    let r = ((hex >> 16) & 0xFF) as f32 / 255.0;
    let g = ((hex >> 8) & 0xFF) as f32 / 255.0;
    let b = (hex & 0xFF) as f32 / 255.0;
    macroquad::prelude::Color::new(r, g, b, 1.0)
}

fn draw_rounded_rect(x: f32, y: f32, w: f32, h: f32, r: f32, color: macroquad::prelude::Color) {
    draw_rectangle(x + r, y, w - 2.0 * r, h, color);
    draw_rectangle(x, y + r, w, h - 2.0 * r, color);
    draw_circle(x + r, y + r, r, color);
    draw_circle(x + w - r, y + r, r, color);
    draw_circle(x + r, y + h - r, r, color);
    draw_circle(x + w - r, y + h - r, r, color);
}

// *** Modified to accept font_size for custom button text sizes ***
fn draw_interactive_button(rect: Rect, text: &str, font: Font, base_color: macroquad::prelude::Color, is_active: bool, font_size: u16) -> bool {
    let (mx, my) = mouse_position();
    let is_hovered = rect.contains(vec2(mx, my));
    
    let mut draw_rect = rect;
    let mut color = if is_active { GREEN } else { base_color };
    
    if is_hovered {
        let scale = 0.96;
        let w_diff = rect.w * (1.0 - scale);
        let h_diff = rect.h * (1.0 - scale);
        draw_rect = Rect::new(rect.x + w_diff / 2.0, rect.y + h_diff / 2.0, rect.w * scale, rect.h * scale);
        
        color = macroquad::prelude::Color::new(color.r * 0.8, color.g * 0.8, color.b * 0.8, color.a);
    }

    draw_rounded_rect(draw_rect.x, draw_rect.y, draw_rect.w, draw_rect.h, 10.0, color);
    draw_rounded_rect(draw_rect.x + 2.0, draw_rect.y + 2.0, draw_rect.w - 4.0, draw_rect.h - 4.0, 8.0, macroquad::prelude::Color::new(0.0, 0.0, 0.0, 0.1)); 

    let text_dims = measure_text(text, Some(font), font_size, 1.0);
    draw_text_ex(
        text,
        draw_rect.x + (draw_rect.w - text_dims.width) / 2.0,
        draw_rect.y + (draw_rect.h + text_dims.height) / 2.0 - 2.0, // Centering logic
        TextParams { font, font_size, color: WHITE, ..Default::default() },
    );

    is_hovered && is_mouse_button_pressed(MouseButton::Left)
}

fn ease_in_out_cubic(t: f32) -> f32 {
    if t < 0.5 {
        4.0 * t * t * t
    } else {
        1.0 - (-2.0 * t + 2.0).powi(3) / 2.0
    }
}

// *** Helper to play sound safely with volume control ***
fn play_move_sound(board: &Board, mv: Move, move_sfx: &Option<Sound>, capture_sfx: &Option<Sound>) {
    let is_capture = board.colors(!board.side_to_move()).has(mv.to) || 
        (board.piece_on(mv.from) == Some(Piece::Pawn) && mv.from.file() != mv.to.file() && board.piece_on(mv.to).is_none());

    if is_capture {
        if let Some(sound) = capture_sfx {
            play_sound_once(*sound);
        }
    } else {
        if let Some(sound) = move_sfx {
            // *** Increase volume by 20% (1.2) ***
            play_sound(*sound, PlaySoundParams {
                looped: false,
                volume: 1.5,
            });
        }
    }
}

#[macroquad::main("CrispyCrab - Ultimate Chess")]
async fn main() {
    let text_font_data = Asset::get("LibertinusSerifDisplay-Regular.ttf").unwrap();
    let text_font = macroquad::text::load_ttf_font_from_bytes(&text_font_data.data).unwrap();

    // *** Load Sounds from Embedded Assets (WAV) ***
    // This ensures sounds are inside the EXE
    let move_sfx: Option<Sound> = if let Some(file) = Asset::get("one-chess-piece-fell-on-the-board.wav") {
        match load_sound_from_bytes(&file.data).await {
            Ok(s) => Some(s),
            Err(_) => { println!("Warning: Invalid move sound format."); None }
        }
    } else {
        println!("Warning: Move sound not found in assets.");
        None
    };

    let capture_sfx: Option<Sound> = if let Some(file) = Asset::get("there-is-such-an-option-small-figures.wav") {
        match load_sound_from_bytes(&file.data).await {
            Ok(s) => Some(s),
            Err(_) => { println!("Warning: Invalid capture sound format."); None }
        }
    } else {
        println!("Warning: Capture sound not found in assets.");
        None
    };

    let mut piece_textures: HashMap<(Piece, Color), Texture2D> = HashMap::new();
    let all_pieces = [Piece::Pawn, Piece::Knight, Piece::Bishop, Piece::Rook, Piece::Queen, Piece::King];
    let all_colors = [Color::White, Color::Black];

    for &p in &all_pieces {
        for &c in &all_colors {
            let filename = get_piece_filename(p, c);
            match Asset::get(&filename) {
                Some(file_data) => {
                    let tex = Texture2D::from_file_with_format(&file_data.data, None);
                    piece_textures.insert((p, c), tex);
                },
                None => {
                    println!("Warning: Could not find image asset: {}", filename);
                }
            }
        }
    }

    let mut game = Game::new();
    let mut game_mode = GameMode::PlayerVsPlayer;
    let mut ai_depth: u8 = MAX_SEARCH_DEPTH;

    // *** Time Control Variables ***
    let mut use_time_control = false;
    let mut time_per_move: u64 = 5; // Seconds

    let mut selected: Option<Square> = None;
    let mut move_hints: Vec<(Square, HintStyle)> = Vec::new();

    let mut dragged_piece: Option<(Square, Piece, Color)> = None;
    let mut drag_offset: Vec2 = vec2(0.0, 0.0);

    let mut animations: Vec<PieceAnimation> = Vec::new();

    let mut show_promo_choices = false;
    let mut promo_candidates: Vec<Move> = Vec::new();

    let mut setup_mode = false;
    let mut fen_input = format!("{}", game.board);
    let mut fen_error_msg: Option<String> = None;
    
    let mut editor_piece_selection: Option<(Piece, Color)> = Some((Piece::Pawn, Color::White));

    // *** PGN Modal State ***
    let mut show_pgn_modal = false;

    enum AiState {
        Idle,
        Thinking,
    }
    let mut ai_state = AiState::Idle;
    let (tx, rx) = channel::unbounded::<Option<Move>>();
    let tt = Arc::new(TranspositionTable::new(64)); 

    let light_sq_color = hex_color(0xF0D9B5); 
    let dark_sq_color = hex_color(0xB58863);  
    let border_color = hex_color(0x4A3020);   
    let bg_color = hex_color(0x302E2B);       
    let button_color = hex_color(0x5C4033);   
    
    let coord_color_light = dark_sq_color;
    let coord_color_dark = light_sq_color;
    
    let last_move_from_color = macroquad::prelude::Color::new(0.8, 0.8, 0.2, 0.5); 
    let last_move_to_color = macroquad::prelude::Color::new(0.9, 0.9, 0.2, 0.5); 

    loop {
        clear_background(bg_color);

        let win_w = screen_width();
        let win_h = screen_height();
        let board_origin = vec2((win_w - BOARD_SIZE) / 2.0, (win_h - BOARD_SIZE) / 2.0);

        // *** Turn Indicator (Circle above board) ***
        let turn_indicator_pos = vec2(board_origin.x + BOARD_SIZE / 2.0, board_origin.y - 35.0);
        let turn_color = if game.board.side_to_move() == Color::White { WHITE } else { BLACK };
        let turn_border = if game.board.side_to_move() == Color::White { GRAY } else { WHITE };
        
        // Shadow/Glow
        draw_circle(turn_indicator_pos.x + 2.0, turn_indicator_pos.y + 2.0, 12.0, macroquad::prelude::Color::new(0.0, 0.0, 0.0, 0.5));
        // Main Circle
        draw_circle(turn_indicator_pos.x, turn_indicator_pos.y, 12.0, turn_color);
        // Border
        draw_circle_lines(turn_indicator_pos.x, turn_indicator_pos.y, 12.0, 2.0, turn_border);


        // *** 1. Draw Board Border ***
        let border_thickness = 18.0;
        draw_rounded_rect(
            board_origin.x - border_thickness, 
            board_origin.y - border_thickness, 
            BOARD_SIZE + border_thickness * 2.0, 
            BOARD_SIZE + border_thickness * 2.0, 
            5.0,
            border_color
        );

        // *** 2. Draw Board Squares & Coordinates ***
        for rank in 0..8 {
            for file in 0..8 {
                let x = board_origin.x + file as f32 * SQUARE_SIZE;
                let y = board_origin.y + (7 - rank) as f32 * SQUARE_SIZE;
                
                let is_dark_sq = (file + rank) % 2 == 0;
                let color = if is_dark_sq { dark_sq_color } else { light_sq_color };
                
                draw_rectangle(x, y, SQUARE_SIZE, SQUARE_SIZE, color);

                let coord_text_color = if is_dark_sq { coord_color_dark } else { coord_color_light };
                
                if file == 0 {
                    let rank_char = (b'1' + rank as u8) as char;
                    draw_text_ex(
                        &rank_char.to_string(),
                        x + 3.0, 
                        y + 15.0, 
                        TextParams { font: text_font, font_size: 14, color: coord_text_color, ..Default::default() }
                    );
                }

                if rank == 0 {
                    let file_char = (b'a' + file as u8) as char;
                    draw_text_ex(
                        &file_char.to_string(),
                        x + SQUARE_SIZE - 12.0, 
                        y + SQUARE_SIZE - 3.0, 
                        TextParams { font: text_font, font_size: 14, color: coord_text_color, ..Default::default() }
                    );
                }
            }
        }

        // *** 3. Highlight Last Move ***
        if let Some(last_mv) = game.last_move {
            let (fx, fy) = square_to_screen(last_mv.from, board_origin);
            let (tx, ty) = square_to_screen(last_mv.to, board_origin);
            draw_rectangle(fx, fy, SQUARE_SIZE, SQUARE_SIZE, last_move_from_color);
            draw_rectangle(tx, ty, SQUARE_SIZE, SQUARE_SIZE, last_move_to_color);
        }

        // Highlight selected square
        if let Some(sq) = selected {
            let (fx, fy) = square_to_screen(sq, board_origin);
            draw_rectangle_lines(fx, fy, SQUARE_SIZE, SQUARE_SIZE, 4.0, YELLOW);
        }

        // *** 4. Draw Move Hints ***
        for (dest_sq, hint_style) in &move_hints {
            match hint_style {
                HintStyle::Capture => {
                    let (cx, cy) = square_to_screen(*dest_sq, board_origin);
                    draw_rectangle(cx, cy, SQUARE_SIZE, SQUARE_SIZE, macroquad::prelude::Color::new(0.6, 0.0, 0.0, 0.4));
                    draw_rectangle_lines(cx, cy, SQUARE_SIZE, SQUARE_SIZE, 3.0, RED);
                },
                HintStyle::Castle(rook_sq) => {
                    let (rx, ry) = square_to_screen(*rook_sq, board_origin);
                    draw_rectangle(rx, ry, SQUARE_SIZE, SQUARE_SIZE, macroquad::prelude::Color::new(1.0, 0.84, 0.0, 0.5)); 
                    draw_rectangle_lines(rx, ry, SQUARE_SIZE, SQUARE_SIZE, 5.0, GOLD); 
                    
                    let (kx, ky) = square_to_screen(*dest_sq, board_origin);
                    let center_x = kx + SQUARE_SIZE / 2.0;
                    let center_y = ky + SQUARE_SIZE / 2.0;
                    draw_circle(center_x, center_y, SQUARE_SIZE * 0.15, macroquad::prelude::Color::new(0.0, 0.8, 0.0, 0.6));
                },
                HintStyle::Normal => {
                    let (cx, cy) = square_to_screen(*dest_sq, board_origin);
                    let center_x = cx + SQUARE_SIZE / 2.0;
                    let center_y = cy + SQUARE_SIZE / 2.0;
                    let radius = SQUARE_SIZE * 0.18; 
                    draw_circle(center_x, center_y, radius, macroquad::prelude::Color::new(0.0, 0.0, 0.0, 0.2)); 
                }
            }
        }

        // Highlight king in check
        if !setup_mode && !game.board.checkers().is_empty() {
            let king_square = game.board.king(game.board.side_to_move());
            let (x, y) = square_to_screen(king_square, board_origin);
            let time = get_time();
            let radius_pulse = (time * 5.0).sin() as f32 * 3.0 + (SQUARE_SIZE / 2.0);
            let alpha_pulse = (time * 5.0).sin() as f32 * 0.2 + 0.3;
            draw_circle(x + SQUARE_SIZE / 2.0, y + SQUARE_SIZE / 2.0, radius_pulse, macroquad::prelude::Color::new(1.0, 0.0, 0.0, alpha_pulse));
        }

        // *** 5. Draw Pieces ***
        let fen = format!("{}", game.board);
        let parts: Vec<&str> = fen.split_whitespace().collect();
        if parts.len() >= 1 {
            let rows = parts[0].split('/').collect::<Vec<_>>();
            for (r_idx, row) in rows.iter().enumerate() {
                let mut file = 0usize;
                for ch in row.chars() {
                    if ch.is_ascii_digit() {
                        let skip = ch.to_digit(10).unwrap() as usize;
                        file += skip;
                    } else {
                        let rank = 7 - r_idx;
                        let current_sq = Square::new(cozy_chess::File::index(file), cozy_chess::Rank::index(rank));
                        
                        let is_being_dragged = if let Some((d_sq, _, _)) = dragged_piece {
                            d_sq == current_sq
                        } else {
                            false
                        };

                        let is_animating_dest = animations.iter().any(|anim| anim.target_sq == current_sq);

                        if !is_being_dragged && !is_animating_dest {
                            if let Some((piece, color)) = fen_char_to_piece_color(ch) {
                                 if let Some(texture) = piece_textures.get(&(piece, color)) {
                                     let px = board_origin.x + file as f32 * SQUARE_SIZE;
                                     let py = board_origin.y + r_idx as f32 * SQUARE_SIZE;
                                     draw_piece_centered(*texture, px, py, SQUARE_SIZE, piece);
                                 }
                            }
                        }
                        file += 1;
                    }
                }
            }
        }

        // *** 6. Draw Animations ***
        let time_now = get_time();
        animations.retain(|anim| time_now - anim.start_time < anim.duration as f64);

        for anim in &animations {
            let elapsed = (time_now - anim.start_time) as f32;
            let t = (elapsed / anim.duration).clamp(0.0, 1.0);
            let t_smooth = ease_in_out_cubic(t);
            let current_pos = anim.start_pos.lerp(anim.target_pos, t_smooth);
            
            if let Some(texture) = piece_textures.get(&(anim.piece, anim.color)) {
                draw_piece_centered(*texture, current_pos.x, current_pos.y, SQUARE_SIZE, anim.piece);
            }
        }

        // *** 7. Draw Dragged Piece ***
        if let Some((_, piece, color)) = dragged_piece {
            if let Some(texture) = piece_textures.get(&(piece, color)) {
                let (mx, my) = mouse_position();
                draw_piece_centered(*texture, mx - drag_offset.x, my - drag_offset.y, SQUARE_SIZE, piece);
            }
        }

        // Show status
        let game_over = game.game_over_status();
        if let Some(status) = &game_over {
            let (text_to_display, color) = if status.contains("Checkmate") {
                ("Checkmate".to_string(), RED)
            } else if status.contains("Stalemate") {
                ("Stalemate".to_string(), GRAY)
            } else if status.contains("Draw") {
                (status.clone(), ORANGE) // Color for draws
            } else {
                (status.clone(), WHITE)
            };
            draw_text_ex(
                &text_to_display,
                board_origin.x + BOARD_SIZE + 20.0,
                30.0,
                TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color, ..Default::default() },
            );
        }

        // AI Logic
        let is_ai_turn = match game_mode {
            GameMode::PlayerVsAi => game.board.side_to_move() == Color::Black,
            GameMode::AiVsPlayer => game.board.side_to_move() == Color::White,
            GameMode::AiVsAi => true,
            _ => false,
        };

        if is_ai_turn && game_over.is_none() && !show_promo_choices && !setup_mode {
            if let AiState::Idle = ai_state {
                ai_state = AiState::Thinking;
                let tx_clone = tx.clone();
                let mut board_clone = game.board.clone(); 
                let history_hashes_clone = game.history_hashes.clone();
                let tt_clone = Arc::clone(&tt); 
                let depth_clone = ai_depth;
                
                // Time Control Params
                let use_time = use_time_control;
                let time_limit_secs = time_per_move;

                task::spawn(async move {
                    use crate::ai::find_best_move;
                    
                    if use_time {
                        // *** Iterative Deepening with AGGRESSIVE Time Control ***
                        let start_time = Instant::now();
                        let limit = Duration::from_secs(time_limit_secs);
                        let mut best_move_so_far = None;
                        let mut last_iter_duration = Duration::from_millis(0);
                        
                        // Loop deeper and deeper
                        for d in 1..=64 {
                            let elapsed = start_time.elapsed();

                            // 1. Hard Check: Did we ALREADY run out?
                            if elapsed >= limit {
                                break;
                            }

                            // 2. Aggressive Prediction Check:
                            // Only check prediction if we are deeper than depth 4.
                            // AND if we have used a significant portion of time.
                            if d > 4 {
                                let ratio_used = elapsed.as_secs_f32() / time_limit_secs as f32;
                                
                                // FIX: If we haven't used even 25% of our time, FORCE continue.
                                // This solves the "stopping at 0.1s" problem.
                                if ratio_used >= 0.25 {
                                    // Heuristic: Assume next depth takes ~3x longer (Optimistic).
                                    // Previous code used 4x (Pessimistic).
                                    let estimated_next_duration = last_iter_duration * 3; 
                                    
                                    if elapsed + estimated_next_duration > limit {
                                        break; 
                                    }
                                }
                            }

                            let iter_start = Instant::now();
                            
                            let mv = find_best_move(
                                &mut board_clone, 
                                d, 
                                &history_hashes_clone,
                                &tt_clone
                            );
                            
                            last_iter_duration = iter_start.elapsed();

                            if mv.is_some() {
                                best_move_so_far = mv;
                            }
                        }
                        
                        if let Some(mv) = best_move_so_far {
                            tx_clone.send(Some(mv)).await.unwrap();
                        } else {
                            tx_clone.send(None).await.unwrap();
                        }

                    } else {
                        // *** Fixed Depth Search ***
                        let best_move = find_best_move(
                            &mut board_clone, 
                            depth_clone, 
                            &history_hashes_clone,
                            &tt_clone
                        );
                        if let Some(mv) = best_move {
                            tx_clone.send(Some(mv)).await.unwrap();
                        } else {
                            tx_clone.send(None).await.unwrap();
                        }
                    }
                });
            }
        }

        if let AiState::Thinking = ai_state {
            match rx.try_recv() {
                Ok(Some(ai_move)) => {
                    let (sx, sy) = square_to_screen(ai_move.from, board_origin);
                    let (tx, ty) = square_to_screen(ai_move.to, board_origin);
                    
                    // *** Play Sound (AI) ***
                    play_move_sound(&game.board, ai_move, &move_sfx, &capture_sfx);

                    if let Err(e) = game.make_move(ai_move) {
                        println!("AI Move failed: {}", e);
                    } else {
                        if let Some(p) = game.board.piece_on(ai_move.to) {
                            let c = game.board.color_on(ai_move.to).unwrap();
                            animations.push(PieceAnimation {
                                piece: p,
                                color: c,
                                start_pos: vec2(sx, sy),
                                target_pos: vec2(tx, ty),
                                start_time: get_time(),
                                duration: ANIMATION_DURATION,
                                target_sq: ai_move.to,
                            });
                        }
                    }
                    ai_state = AiState::Idle;
                }
                Ok(None) => {
                    ai_state = AiState::Idle;
                }
                Err(channel::TryRecvError::Empty) => {
                    let thinking_text = if use_time_control {
                        format!("AI Thinking (Time: {}s)...", time_per_move)
                    } else {
                        format!("AI Thinking (Depth: {})...", ai_depth)
                    };
                    
                    draw_text_ex(
                        &thinking_text,
                        50.0,
                        30.0,
                        TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: WHITE, ..Default::default() },
                    );
                }
                _ => { ai_state = AiState::Idle; }
            }
        }


        // --- Handle Human Input ---
        let human_turn = match game_mode {
            GameMode::PlayerVsPlayer => true,
            GameMode::PlayerVsAi => game.board.side_to_move() == Color::White,
            GameMode::AiVsPlayer => game.board.side_to_move() == Color::Black,
            _ => false,
        };

        if human_turn && !show_promo_choices && !setup_mode && !show_pgn_modal {
            let (mx, my) = mouse_position();
            
            if is_mouse_button_pressed(MouseButton::Left) {
                if let Some(clicked_sq) = screen_to_square(mx, my, board_origin) {
                    let piece_at = game.board.piece_on(clicked_sq);
                    let color_at = game.board.color_on(clicked_sq);
                    
                    if piece_at.is_some() && color_at == Some(game.board.side_to_move()) {
                        dragged_piece = Some((clicked_sq, piece_at.unwrap(), color_at.unwrap()));
                        let (sq_x, sq_y) = square_to_screen(clicked_sq, board_origin);
                        drag_offset = vec2(mx - sq_x, my - sq_y);
                        
                        selected = Some(clicked_sq);
                        move_hints = calculate_hints(&game, clicked_sq);
                    } else {
                        if let Some(from_sq) = selected {
                            let legal_moves = game.legal_moves_vec();
                            let mut matching: Vec<Move> = Vec::new();
                            for mv in legal_moves {
                                if mv.from == from_sq && mv.to == clicked_sq {
                                    matching.push(mv);
                                }
                            }
                            
                            if !matching.is_empty() {
                                if matching.len() == 1 {
                                    let (sx, sy) = square_to_screen(matching[0].from, board_origin);
                                    let (tx, ty) = square_to_screen(matching[0].to, board_origin);

                                    // *** Play Sound (Click-Click) ***
                                    play_move_sound(&game.board, matching[0], &move_sfx, &capture_sfx);

                                    let _ = game.make_move(matching[0]);
                                    
                                    if let Some(p) = game.board.piece_on(matching[0].to) {
                                        let c = game.board.color_on(matching[0].to).unwrap();
                                        animations.push(PieceAnimation {
                                            piece: p,
                                            color: c,
                                            start_pos: vec2(sx, sy),
                                            target_pos: vec2(tx, ty),
                                            start_time: get_time(),
                                            duration: ANIMATION_DURATION,
                                            target_sq: matching[0].to,
                                        });
                                    }

                                    selected = None;
                                    move_hints.clear();
                                } else {
                                    show_promo_choices = true;
                                    promo_candidates = matching;
                                }
                            } else {
                                selected = None;
                                move_hints.clear();
                            }
                        }
                    }
                } else {
                    selected = None;
                    move_hints.clear();
                }
            }

            if is_mouse_button_released(MouseButton::Left) {
                if let Some((from_sq, _, _)) = dragged_piece {
                    if let Some(to_sq) = screen_to_square(mx, my, board_origin) {
                        if from_sq != to_sq {
                            let legal_moves = game.legal_moves_vec();
                            let mut matching: Vec<Move> = Vec::new();
                            for mv in legal_moves {
                                if mv.from == from_sq && mv.to == to_sq {
                                    matching.push(mv);
                                }
                            }

                            if !matching.is_empty() {
                                if matching.len() == 1 {
                                    // *** Play Sound (Drag & Drop) ***
                                    play_move_sound(&game.board, matching[0], &move_sfx, &capture_sfx);

                                    let _ = game.make_move(matching[0]);
                                    selected = None;
                                    move_hints.clear();
                                } else {
                                    show_promo_choices = true;
                                    promo_candidates = matching;
                                }
                            }
                        }
                    }
                    dragged_piece = None;
                }
            }
        }

        // --- Promotion UI ---
        if show_promo_choices {
            let modal_w = 300.0;
            let modal_h = 120.0;
            let mx_modal = (screen_width() - modal_w) / 2.0;
            let my_modal = (screen_height() - modal_h) / 2.0;
            draw_rounded_rect(mx_modal, my_modal, modal_w, modal_h, 10.0, light_sq_color);
            draw_rectangle_lines(mx_modal, my_modal, modal_w, modal_h, 2.0, border_color);
            draw_text_ex(
                "Choose promotion:",
                mx_modal + 10.0,
                my_modal + 24.0,
                TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: BLACK, ..Default::default() },
            );
            
            let mut buttons: Vec<(Piece, Rect)> = Vec::new();
            let mut seen_piece_types: HashSet<Piece> = HashSet::new();
            for mv in &promo_candidates {
                if let Some(p) = mv.promotion {
                    if seen_piece_types.insert(p) {
                        buttons.push((p, Rect::new(mx_modal + 20.0 + buttons.len() as f32 * 60.0, my_modal + 40.0, 50.0, 50.0)));
                    }
                }
            }
            
            for (piece_type, rect) in &buttons {
                draw_rectangle(rect.x, rect.y, rect.w, rect.h, WHITE);
                draw_rectangle_lines(rect.x, rect.y, rect.w, rect.h, 2.0, BLACK);

                if let Some(tex) = piece_textures.get(&(*piece_type, game.board.side_to_move())) {
                     draw_piece_centered(*tex, rect.x, rect.y, rect.w, *piece_type);
                }

                if is_mouse_button_pressed(MouseButton::Left) {
                    let (mx_pos, my_pos) = mouse_position();
                    if rect.contains(vec2(mx_pos, my_pos)) {
                        let chosen_piece_type = *piece_type;
                        if let Some(mv) = promo_candidates.iter().find(|m| m.promotion == Some(chosen_piece_type)) {
                            // *** Play Sound (Promotion) ***
                            play_move_sound(&game.board, *mv, &move_sfx, &capture_sfx);

                            if let Err(e) = game.make_move(*mv) {
                                println!("Promotion failed: {}", e);
                            }
                        }
                        show_promo_choices = false;
                        promo_candidates.clear();
                        selected = None;
                        move_hints.clear();
                    }
                }
            }
        }

        // Draw move list
        let move_list_start_x = board_origin.x + BOARD_SIZE + 30.0;
        let move_list_y = board_origin.y;
        let mut current_column_x = move_list_start_x;
        let mut current_column_y = move_list_y + 40.0;
        
        // *** Move List Styling Logic ***
        let (list_font_size, list_line_height) = if game.san_moves.len() > 180 {
            (11, 16.0) // Smaller font, tighter spacing
        } else {
            (16, 18.0) // Normal
        };

        let moves_per_column = ((screen_height() - current_column_y) / list_line_height) as usize - 4;

        draw_text_ex(
            "Moves:",
            current_column_x,
            move_list_y + 20.0,
            TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: WHITE, ..Default::default() },
        );

        for (i, m) in game.san_moves.iter().enumerate() {
            if i > 0 && (i % moves_per_column) == 0 {
                current_column_x += 100.0;
                current_column_y = move_list_y + 40.0;
            }

            draw_text_ex(
                &format!("{}.", i + 1),
                current_column_x,
                current_column_y,
                TextParams { font: text_font, font_size: list_font_size as u16, color: LIGHTGRAY, ..Default::default() },
            );
            draw_text_ex(
                m,
                current_column_x + 40.0,
                current_column_y,
                TextParams { font: text_font, font_size: list_font_size as u16, color: WHITE, ..Default::default() },
            );
            current_column_y += list_line_height;
        }

        // --- Setup Mode Logic ---
        if setup_mode {
            let palette_sq_size = 50.0;
            let pieces_to_select = [
                (Some((Piece::Pawn, Color::White))), (Some((Piece::Pawn, Color::Black))),
                (Some((Piece::Knight, Color::White))), (Some((Piece::Knight, Color::Black))),
                (Some((Piece::Bishop, Color::White))), (Some((Piece::Bishop, Color::Black))),
                (Some((Piece::Rook, Color::White))), (Some((Piece::Rook, Color::Black))),
                (Some((Piece::Queen, Color::White))), (Some((Piece::Queen, Color::Black))),
                (Some((Piece::King, Color::White))), (Some((Piece::King, Color::Black))),
                (None), // Empty
            ];

            let palette_width = 110.0; 
            let palette_height = 360.0;
            let palette_x = win_w - palette_width - 20.0; 
            let palette_y = board_origin.y + 10.0; 

            draw_rounded_rect(palette_x - 10.0, palette_y - 10.0, palette_width + 20.0, palette_height, 10.0, button_color);
            draw_text_ex("Place Piece:", palette_x, palette_y, TextParams { font: text_font, font_size: 16, color: WHITE, ..Default::default() });
            
            let current_py = palette_y + 20.0;
            let mut piece_buttons = Vec::new();

            for (i, piece_info) in pieces_to_select.iter().enumerate() {
                let col = i % 2;
                let row = i / 2;
                let rect = Rect::new(palette_x + col as f32 * (palette_sq_size + 5.0), current_py + row as f32 * (palette_sq_size + 5.0), palette_sq_size, palette_sq_size);
                
                let is_selected = match (*piece_info, editor_piece_selection) {
                    (Some(p1), Some(p2)) => p1 == p2,
                    (None, None) => true,
                    _ => false,
                };

                let color = if is_selected { YELLOW } else { light_sq_color };
                draw_rectangle(rect.x, rect.y, rect.w, rect.h, color);
                draw_rectangle_lines(rect.x, rect.y, rect.w, rect.h, 2.0, BLACK);

                if let Some((p, c)) = piece_info {
                    if let Some(tex) = piece_textures.get(&(*p, *c)) {
                         draw_piece_centered(*tex, rect.x, rect.y, rect.w, *p);
                    }
                } else {
                    let text_dimensions = measure_text("X", Some(text_font), 30, 1.0);
                    draw_text_ex(
                        "X",
                        rect.x + (rect.w - text_dimensions.width) / 2.0,
                        rect.y + (rect.h + text_dimensions.height) / 2.0 - 2.0,
                        TextParams { font: text_font, font_size: 30, color: BLACK, ..Default::default() },
                    );
                }
                
                piece_buttons.push((rect, *piece_info));
            }
            
            if is_mouse_button_pressed(MouseButton::Left) {
                let (mx, my) = mouse_position();
                let mouse_point = vec2(mx, my);
                for (rect, piece_info) in &piece_buttons {
                    if rect.contains(mouse_point) {
                        editor_piece_selection = *piece_info;
                        fen_error_msg = None;
                        break;
                    }
                }
            }

            if is_mouse_button_pressed(MouseButton::Left) {
                let (mx, my) = (mouse_position().0, mouse_position().1);
                if let Some(clicked_sq) = screen_to_square(mx, my, board_origin) {
                    let current_fen_str = format!("{}", game.board);
                    let new_fen = update_board_from_fen_manually(&current_fen_str, clicked_sq, editor_piece_selection);
                    if game.reload_from_fen(&new_fen).is_ok() {
                        fen_input = new_fen;
                        fen_error_msg = None;
                    } else {
                         fen_error_msg = Some("Invalid position created!".to_string());
                    }
                }
            }
            
            // FEN Input UI
            let fen_modal_w = board_origin.x + BOARD_SIZE - (board_origin.x + 20.0);
            let fen_modal_h = 100.0;
            let fen_modal_x = board_origin.x;
            let fen_modal_y = screen_height() - fen_modal_h - 20.0;

            draw_rectangle(fen_modal_x, fen_modal_y, fen_modal_w, fen_modal_h, GRAY);
            draw_rectangle_lines(fen_modal_x, fen_modal_y, fen_modal_w, fen_modal_h, 3.0, BLACK);
            draw_text_ex(
                "Full FEN (Edit Side to Move, Castling, etc.):",
                fen_modal_x + 10.0,
                fen_modal_y + 20.0,
                TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: WHITE, ..Default::default() },
            );

            let apply_button_width = 80.0;
            let input_area_padding = 10.0;
            let fen_text_rect = Rect::new(fen_modal_x + input_area_padding, fen_modal_y + 30.0, fen_modal_w - (input_area_padding * 3.0) - apply_button_width, 30.0);
            draw_rectangle(fen_text_rect.x, fen_text_rect.y, fen_text_rect.w, fen_text_rect.h, WHITE);
            draw_rectangle_lines(fen_text_rect.x, fen_text_rect.y, fen_text_rect.w, fen_text_rect.h, 1.0, BLACK);
            draw_text_ex(
                &fen_input,
                fen_text_rect.x + 5.0,
                fen_text_rect.y + 22.0,
                TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: BLACK, ..Default::default() },
            );

            let apply_fen_rect = Rect::new(fen_text_rect.x + fen_text_rect.w + 10.0, fen_text_rect.y, apply_button_width, 30.0);
            if draw_interactive_button(apply_fen_rect, "APPLY", text_font, LIME, false, TEXT_FONT_SIZE) {
                 match game.reload_from_fen(&fen_input) {
                    Ok(_) => { fen_error_msg = None; }
                    Err(e) => { fen_error_msg = Some(e); }
                }
            }
            
            if let Some(msg) = &fen_error_msg {
                draw_text_ex(msg, fen_text_rect.x, fen_text_rect.y + fen_text_rect.h + 15.0, TextParams { font: text_font, font_size: 16, color: RED, ..Default::default() });
            }

            let (mx_pos, my_pos) = mouse_position();
            let is_mouse_over_fen_input = fen_text_rect.contains(vec2(mx_pos, my_pos));

            while let Some(ch) = get_char_pressed() {
                if is_mouse_over_fen_input {
                    if ch.is_ascii_alphanumeric() || ch.is_ascii_whitespace() || ch == '/' || ch == '-' || ch == ':' {
                        fen_input.push(ch);
                    }
                }
            }
            if is_key_pressed(KeyCode::Backspace) && is_mouse_over_fen_input && !fen_input.is_empty() {
                fen_input.pop();
            }
        }


        // --- BUTTONS CODE ---
        let button_w = 160.0;
        let button_h = 40.0;
        let button_x = board_origin.x - button_w - 35.0;
        let mut current_y = board_origin.y;

        let undo_rect = Rect::new(button_x, current_y, button_w, button_h);
        if draw_interactive_button(undo_rect, "Undo", text_font, button_color, false, TEXT_FONT_SIZE) {
            game.undo_move();
            setup_mode = false;
            fen_error_msg = None;
            selected = None;
            move_hints.clear(); 
            animations.clear();
            show_pgn_modal = false; // Hide PGN if undoing
        }
        current_y += button_h + 10.0;

        let restart_rect = Rect::new(button_x, current_y, button_w, button_h);
        if draw_interactive_button(restart_rect, "Restart", text_font, button_color, false, TEXT_FONT_SIZE) {
            game = Game::new();
            selected = None;
            move_hints.clear(); 
            show_promo_choices = false;
            promo_candidates.clear();
            setup_mode = false;
            fen_input = format!("{}", game.board);
            fen_error_msg = None;
            animations.clear();
            show_pgn_modal = false;
        }
        current_y += button_h + 10.0;

        let setup_mode_rect = Rect::new(button_x, current_y, button_w, button_h);
        if draw_interactive_button(setup_mode_rect, "Setup Mode", text_font, button_color, setup_mode, TEXT_FONT_SIZE) {
            setup_mode = !setup_mode; 
            selected = None;
            move_hints.clear(); 
            show_promo_choices = false;
            promo_candidates.clear();
            fen_input = format!("{}", game.board);
            fen_error_msg = None;
            animations.clear();
            show_pgn_modal = false;
        }
        current_y += button_h + 30.0;

        draw_text_ex("Select Mode:", button_x, current_y, TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: WHITE, ..Default::default() });
        current_y += 25.0;

        let modes = [("Player vs Player", GameMode::PlayerVsPlayer), ("Player vs AI", GameMode::PlayerVsAi), ("AI vs Player", GameMode::AiVsPlayer), ("AI vs AI", GameMode::AiVsAi)];
        for (text, mode) in modes.iter() {
            let rect = Rect::new(button_x, current_y, button_w, button_h);
            if draw_interactive_button(rect, text, text_font, button_color, game_mode == *mode, TEXT_FONT_SIZE) {
                game_mode = *mode;
                selected = None;
                move_hints.clear(); 
                show_promo_choices = false;
                promo_candidates.clear();
                let current_board = game.board.clone();
                game.history_boards.clear();
                game.history_boards.push(current_board.clone());
                game.history_hashes.clear();
                game.history_hashes.push(current_board.hash());
                game.san_moves.clear();
                game.last_move = None;
                setup_mode = false;
                fen_input = format!("{}", game.board);
                fen_error_msg = None;
                animations.clear();
                show_pgn_modal = false;
            }
            current_y += button_h + 10.0;
        }

        // *** Depth / Time Control UI ***
        let label_text = if use_time_control {
            format!("Time: {} s", time_per_move)
        } else {
            format!("Depth: {}", ai_depth)
        };
        
        // *** UI TWEAK: Moved label down 5px and right 8px ***
        draw_text_ex(&label_text, button_x + 8.0, current_y + 10.0, TextParams { font: text_font, font_size: TEXT_FONT_SIZE, color: WHITE, ..Default::default() });
        current_y += 25.0 + 5.0;

        let depth_button_w = 75.0;
        let depth_minus_rect = Rect::new(button_x, current_y, depth_button_w, button_h);
        let depth_plus_rect = Rect::new(button_x + depth_button_w + 10.0, current_y, depth_button_w, button_h);

        // *** UI TWEAK: Increased font size for + and - buttons to 30 ***
        if draw_interactive_button(depth_minus_rect, "-", text_font, button_color, false, 30) {
            if use_time_control {
                if time_per_move > 1 { time_per_move -= 1; }
            } else {
                if ai_depth > 1 { ai_depth -= 1; }
            }
        }
        if draw_interactive_button(depth_plus_rect, "+", text_font, button_color, false, 30) {
            if use_time_control {
                if time_per_move < 60 { time_per_move += 1; }
            } else {
                ai_depth += 1;
            }
        }
        current_y += button_h + 10.0;

        // *** Toggle Button (DEPTH / TIME) ***
        let toggle_rect = Rect::new(button_x, current_y, button_w, button_h);
        let toggle_text = if use_time_control { "Mode: TIME" } else { "Mode: DEPTH" };
        if draw_interactive_button(toggle_rect, toggle_text, text_font, button_color, use_time_control, TEXT_FONT_SIZE) {
            use_time_control = !use_time_control;
        }
        current_y += button_h + 10.0;

        // *** PGN Button (Only when Game Over) ***
        if game_over.is_some() {
            let pgn_btn_rect = Rect::new(button_x, current_y, button_w, button_h);
            if draw_interactive_button(pgn_btn_rect, "PGN", text_font, button_color, show_pgn_modal, TEXT_FONT_SIZE) {
                show_pgn_modal = true;
            }
        }

        // *** PGN Modal Overlay ***
        if show_pgn_modal {
            let modal_w = 600.0;
            let modal_h = 400.0;
            let mx_modal = (screen_width() - modal_w) / 2.0;
            let my_modal = (screen_height() - modal_h) / 2.0;

            // Dim background
            draw_rectangle(0.0, 0.0, screen_width(), screen_height(), macroquad::prelude::Color::new(0.0, 0.0, 0.0, 0.7));

            // Modal Box
            draw_rounded_rect(mx_modal, my_modal, modal_w, modal_h, 10.0, bg_color);
            draw_rectangle_lines(mx_modal, my_modal, modal_w, modal_h, 3.0, border_color);

            draw_text_ex(
                "Game PGN",
                mx_modal + 20.0,
                my_modal + 30.0,
                TextParams { font: text_font, font_size: 30, color: WHITE, ..Default::default() },
            );

            let pgn_content = game.generate_pgn();
            
            // Text Area for PGN
            let text_area_rect = Rect::new(mx_modal + 20.0, my_modal + 50.0, modal_w - 40.0, modal_h - 120.0);
            draw_rectangle(text_area_rect.x, text_area_rect.y, text_area_rect.w, text_area_rect.h, macroquad::prelude::Color::new(0.1, 0.1, 0.1, 1.0));
            
            // Simple text wrapping for display
            let words: Vec<&str> = pgn_content.split_whitespace().collect();
            let mut line_y = text_area_rect.y + 20.0;
            let mut current_line = String::new();
            
            for word in words {
                let test_line = format!("{} {}", current_line, word);
                let dims = measure_text(&test_line, Some(text_font), 16, 1.0);
                if dims.width > text_area_rect.w - 20.0 {
                    draw_text_ex(&current_line, text_area_rect.x + 10.0, line_y, TextParams { font: text_font, font_size: 16, color: WHITE, ..Default::default() });
                    current_line = word.to_string();
                    line_y += 20.0;
                } else {
                    current_line = test_line;
                }
                if line_y > text_area_rect.y + text_area_rect.h - 10.0 { break; }
            }
            draw_text_ex(&current_line, text_area_rect.x + 10.0, line_y, TextParams { font: text_font, font_size: 16, color: WHITE, ..Default::default() });

            // Copy Button (Renamed to Print to Console to reflect functionality)
            let copy_btn_rect = Rect::new(mx_modal + 20.0, my_modal + modal_h - 50.0, 100.0, 30.0);
            if draw_interactive_button(copy_btn_rect, "Print PGN", text_font, button_color, false, TEXT_FONT_SIZE) {
                // *** FIXED: Print to console instead of using broken clipboard dependency ***
                println!("--- PGN Output ---\n{}\n------------------", pgn_content);
            }

            // Close Button
            let close_btn_rect = Rect::new(mx_modal + modal_w - 120.0, my_modal + modal_h - 50.0, 100.0, 30.0);
            if draw_interactive_button(close_btn_rect, "Close", text_font, RED, false, TEXT_FONT_SIZE) {
                show_pgn_modal = false;
            }
        }

        next_frame().await;
    }
}