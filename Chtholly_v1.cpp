
#include <bits/stdc++.h>
using namespace std;

using U64 = unsigned long long;

static inline int popcount(U64 b) { return (int)__builtin_popcountll(b); }
static inline int lsb(U64 b) { return __builtin_ctzll(b); }
static inline U64 poplsb(U64 &b) { U64 x = b & -b; b -= x; return x; }
static inline int msb(U64 b) { return 63 - __builtin_clzll(b); }

constexpr int WHITE = 0;
constexpr int BLACK = 1;

constexpr int PAWN = 0;
constexpr int KNIGHT = 1;
constexpr int BISHOP = 2;
constexpr int ROOK = 3;
constexpr int QUEEN = 4;
constexpr int KING = 5;

constexpr int NO_PIECE = -1;

constexpr int MAX_PLY = 128;
constexpr int INF = 32000;
constexpr int MATE_SCORE = 30000;
constexpr int MATE_IN_MAX_PLY = MATE_SCORE - MAX_PLY;

constexpr U64 FileA = 0x0101010101010101ULL;
constexpr U64 FileH = FileA << 7;
constexpr U64 Rank1 = 0xFFULL;
constexpr U64 Rank2 = Rank1 << 8;
constexpr U64 Rank7 = Rank1 << 48;
constexpr U64 Rank8 = Rank1 << 56;

static inline int sq(int file, int rank) { return rank * 8 + file; }
static inline int file_of(int s) { return s & 7; }
static inline int rank_of(int s) { return s >> 3; }
static inline int mirror64(int s) { return s ^ 56; }

enum Dir { N=8, S=-8, E=1, W=-1, NE=9, NW=7, SE=-7, SW=-9 };

// ----------------------------- Zobrist -----------------------------

struct SplitMix64 {
	uint64_t x;
	explicit SplitMix64(uint64_t seed = 0x9e3779b97f4a7c15ULL) : x(seed) {}
	uint64_t next() {
		uint64_t z = (x += 0x9e3779b97f4a7c15ULL);
		z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
		z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
		return z ^ (z >> 31);
	}
};

uint64_t ZPiece[12][64];
uint64_t ZCastle[16];
uint64_t ZEP[8];
uint64_t ZSide;

static void init_zobrist() {
	SplitMix64 rng(0xA1B2C3D4E5F60789ULL);
	for (int p=0;p<12;p++) for (int s=0;s<64;s++) ZPiece[p][s] = rng.next();
	for (int i=0;i<16;i++) ZCastle[i] = rng.next();
	for (int f=0;f<8;f++) ZEP[f] = rng.next();
	ZSide = rng.next();
}

// ----------------------------- 攻击/掩码 -----------------------------

U64 KnightAtt[64], KingAtt[64];
U64 PawnAtt[2][64]; // [color][sq]
U64 FileMask[8], RankMask[8];
U64 PassedMask[2][64];
U64 AdjacentFiles[8];

// 新增：中心掩码/前进掩码
U64 Center4Mask = 0ULL;   // d4,e4,d5,e5
U64 Center16Mask = 0ULL;  // c3..f6
U64 ForwardMask[2][64];   // 从该格“向对面方向”的所有格（用于前哨马检测）

static bool on_board(int f, int r) { return f>=0 && f<8 && r>=0 && r<8; }

static void init_attack_tables() {
	for (int f=0; f<8; ++f) {
		U64 m = 0; for (int r=0;r<8;r++) m |= 1ULL << sq(f, r);
		FileMask[f] = m;
		AdjacentFiles[f] = (f>0?FileMask[f-1]:0ULL) | (f<7?FileMask[f+1]:0ULL);
	}
	for (int r=0;r<8;r++) {
		U64 m = 0; for (int f=0;f<8;f++) m |= 1ULL << sq(f, r);
		RankMask[r] = m;
	}
	for (int s=0;s<64;s++) {
		int f = file_of(s), r = rank_of(s);
		// Knight
		U64 k = 0;
		int nf[] = {f-2,f-1,f+1,f+2,f-2,f-1,f+1,f+2};
		int nr[] = {r-1,r-2,r-2,r-1,r+1,r+2,r+2,r+1};
		for(int i=0;i<8;i++) if(on_board(nf[i], nr[i])) k |= 1ULL<<sq(nf[i], nr[i]);
		KnightAtt[s] = k;
		// King
		U64 g=0;
		for(int df=-1;df<=1;df++) for(int dr=-1;dr<=1;dr++) if(df||dr){
			int nf=f+df, nr=r+dr; if(on_board(nf,nr)) g |= 1ULL<<sq(nf,nr);
		}
		KingAtt[s]=g;
		// Pawns
		U64 pw=0, pb=0;
		if (r<7) {
			if (f>0) pw |= 1ULL<<sq(f-1, r+1);
			if (f<7) pw |= 1ULL<<sq(f+1, r+1);
		}
		if (r>0) {
			if (f>0) pb |= 1ULL<<sq(f-1, r-1);
			if (f<7) pb |= 1ULL<<sq(f+1, r-1);
		}
		PawnAtt[WHITE][s]=pw; PawnAtt[BLACK][s]=pb;
		
		// Passed pawn mask
		U64 pmW = 0, pmB=0;
		U64 sameAdj = FileMask[f] | AdjacentFiles[f];
		for (int rr=r+1; rr<8; rr++) pmW |= sameAdj & RankMask[rr];
		for (int rr=r-1; rr>=0; rr--) pmB |= sameAdj & RankMask[rr];
		PassedMask[WHITE][s]=pmW; PassedMask[BLACK][s]=pmB;
		
		// Forward masks（用于前哨马判定）
		U64 fwdW = 0, fwdB = 0;
		for (int rr=r+1; rr<8; ++rr) fwdW |= RankMask[rr];
		for (int rr=r-1; rr>=0; --rr) fwdB |= RankMask[rr];
		ForwardMask[WHITE][s] = fwdW;
		ForwardMask[BLACK][s] = fwdB;
	}
	
	// 中心掩码
	Center4Mask |= 1ULL<<sq(3,3); Center4Mask |= 1ULL<<sq(4,3);
	Center4Mask |= 1ULL<<sq(3,4); Center4Mask |= 1ULL<<sq(4,4);
	for (int f=2; f<=5; ++f)
		for (int r=2; r<=5; ++r)
			Center16Mask |= 1ULL<<sq(f,r);
}

static inline U64 ray_attacks_dir(int s, int df, int dr, U64 occ) {
	U64 attacks = 0ULL;
	int f = file_of(s), r = rank_of(s);
	int nf = f + df, nr = r + dr;
	while (on_board(nf, nr)) {
		int ns = sq(nf, nr);
		attacks |= 1ULL << ns;
		if ( (occ >> ns) & 1ULL ) break;
		nf += df; nr += dr;
	}
	return attacks;
}

static inline U64 rook_attacks(int s, U64 occ) {
	return ray_attacks_dir(s, +1, 0, occ) |
	ray_attacks_dir(s, -1, 0, occ) |
	ray_attacks_dir(s, 0, +1, occ) |
	ray_attacks_dir(s, 0, -1, occ);
}
static inline U64 bishop_attacks(int s, U64 occ) {
	return ray_attacks_dir(s, +1, +1, occ) |
	ray_attacks_dir(s, -1, +1, occ) |
	ray_attacks_dir(s, +1, -1, occ) |
	ray_attacks_dir(s, -1, -1, occ);
}
static inline U64 queen_attacks(int s, U64 occ) {
	return rook_attacks(s, occ) | bishop_attacks(s, occ);
}

// ----------------------------- 随机抖动控制 -----------------------------

struct RandJit {
	uint64_t x = 0x9e3779b97f4a7c15ULL;
	void seed(uint64_t s) { x = s ? s : 0x9e3779b97f4a7c15ULL; }
	uint64_t next() {
		uint64_t z = (x += 0x9e3779b97f4a7c15ULL);
		z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
		z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
		return z ^ (z >> 31);
	}
} RJ;

struct RandomCtrl {
	int jitter = 0;          // 走法排序扰动幅度 [-jitter, +jitter]
	uint64_t seed = 0;       // 0=按时间播种；非0=固定种子
	bool seeded = false;
} RC;

static inline int rand_jitter() {
	if (RC.jitter <= 0) return 0;
	if (!RC.seeded) {
		uint64_t t = (uint64_t)chrono::steady_clock::now().time_since_epoch().count();
		RC.seed = (RC.seed ? RC.seed : t);
		RJ.seed(RC.seed);
		RC.seeded = true;
	}
	uint64_t r = RJ.next();
	int amp = RC.jitter;
	int v = (int)(r % (uint64_t)(2*amp + 1)) - amp; // [-amp, +amp]
	return v;
}

// ----------------------------- 棋盘与状态 -----------------------------

struct State {
	uint64_t key;
	int castling; // 4 bits: WK=1,WQ=2,BK=4,BQ=8
	int ep; // -1 无；否则 0..63
	int halfmove;
	int captured; // 捕获的棋子代码（0..11）或 -1
	uint32_t move; // 最近一步
	int fullmove; // 保存全回合计数（用于评估）
};

struct Board {
	U64 bb[12];
	U64 occ[2];
	U64 occAll;
	int side; // to move
	int castling; // KQkq bits: 1,2,4,8
	int ep; // en passant sq or -1
	int halfmove; // 50-move
	int fullmove; // FEN 全回合计数（黑走完一步+1）
	int board[64]; // -1 无子；否则 0..11
	int kingSq[2];
	uint64_t key;
	
	State st[MAX_PLY+2048];
	int sp;
	
	Board() { reset(); }
	
	void reset() {
		memset(bb, 0, sizeof(bb));
		occ[0]=occ[1]=occAll=0;
		side=WHITE; castling=0; ep=-1; halfmove=0; fullmove=1;
		for (int i=0;i<64;i++) board[i]=NO_PIECE;
		kingSq[0]=kingSq[1]=-1;
		key=0; sp=0;
	}
	
	static int code(int color, int pt) { return color*6 + pt; }
	
	inline void put_piece(int code, int s) {
		bb[code] |= 1ULL<<s;
		occ[code/6] |= 1ULL<<s;
		occAll |= 1ULL<<s;
		board[s] = code;
		if ((code%6)==KING) kingSq[code/6] = s;
		key ^= ZPiece[code][s];
	}
	inline void remove_piece(int s) {
		int code = board[s];
		if (code == NO_PIECE) return;
		bb[code] &= ~(1ULL<<s);
		occ[code/6] &= ~(1ULL<<s);
		occAll &= ~(1ULL<<s);
		board[s] = NO_PIECE;
		if ((code%6)==KING) kingSq[code/6] = -1;
		key ^= ZPiece[code][s];
	}
	inline void move_piece(int from, int to) {
		int code = board[from];
		bb[code] ^= (1ULL<<from) | (1ULL<<to);
		occ[code/6] ^= (1ULL<<from) | (1ULL<<to);
		occAll ^= (1ULL<<from) | (1ULL<<to);
		board[from] = NO_PIECE; board[to] = code;
		key ^= ZPiece[code][from];
		key ^= ZPiece[code][to];
		if ((code%6)==KING) kingSq[code/6] = to;
	}
	
	void set_startpos() {
		reset();
		string fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
		set_fen(fen);
	}
	
	bool set_fen(const string& fen) {
		reset();
		istringstream ss(fen);
		string boardPart, stm, castle, epstr;
		int hm=0, fm=1;
		if (!(ss >> boardPart >> stm >> castle >> epstr)) return false;
		if (!(ss >> hm)) hm = 0;
		if (!(ss >> fm)) fm = 1;
		
		int sqi = 56;
		for (char c : boardPart) {
			if (c == '/') { sqi -= 16; continue; }
			if (isdigit((unsigned char)c)) { sqi += c - '0'; continue; }
			int color = isupper((unsigned char)c)? WHITE:BLACK;
			char pc = (char)tolower((unsigned char)c);
			int pt = -1;
			if (pc=='p') pt=PAWN;
			else if (pc=='n') pt=KNIGHT;
			else if (pc=='b') pt=BISHOP;
			else if (pc=='r') pt=ROOK;
			else if (pc=='q') pt=QUEEN;
			else if (pc=='k') pt=KING;
			if (pt==-1) return false;
			put_piece(code(color, pt), sqi++);
		}
		
		side = (stm=="w")?WHITE:BLACK;
		key ^= (side==WHITE?0:ZSide);
		
		castling = 0;
		if (castle.find('K')!=string::npos) castling |= 1;
		if (castle.find('Q')!=string::npos) castling |= 2;
		if (castle.find('k')!=string::npos) castling |= 4;
		if (castle.find('q')!=string::npos) castling |= 8;
		key ^= ZCastle[castling];
		
		if (epstr != "-" && epstr.size()==2) {
			int f = epstr[0]-'a';
			int r = epstr[1]-'1';
			int e = sq(f,r);
			ep = e;
			if (r==2 || r==5) { key ^= ZEP[f]; }
		} else ep = -1;
		
		halfmove = hm;
		fullmove = fm;
		return true;
	}
	
	inline bool square_attacked(int s, int bySide) const {
		if ( (PawnAtt[bySide^1][s] & bb[code(bySide, PAWN)]) ) return true;
		if ( KnightAtt[s] & bb[code(bySide, KNIGHT)] ) return true;
		if ( KingAtt[s] & bb[code(bySide, KING)] ) return true;
		U64 occNow = occAll;
		if ( bishop_attacks(s, occNow) & (bb[code(bySide,BISHOP)] | bb[code(bySide,QUEEN)]) ) return true;
		if ( rook_attacks(s, occNow) & (bb[code(bySide,ROOK)] | bb[code(bySide,QUEEN)]) ) return true;
		return false;
	}
	
	uint64_t compute_key() const {
		uint64_t k=0;
		for(int p=0;p<12;p++){
			U64 bbb=bb[p];
			while(bbb){ int s=lsb(bbb); bbb&=bbb-1; k^=ZPiece[p][s]; }
		}
		k ^= ZCastle[castling];
		if (side==BLACK) k ^= ZSide;
		if (ep!=-1) k ^= ZEP[file_of(ep)];
		return k;
	}
};

// ----------------------------- Castling 权利更新表 -----------------------------

int CastleMaskFromTo[64];
int CastleMaskOnCapture[64];

static void init_castle_masks() {
	for(int i=0;i<64;i++){ CastleMaskFromTo[i]=15; CastleMaskOnCapture[i]=15; }
	// 白
	CastleMaskFromTo[sq(4,0)] = 15 & ~1 & ~2;
	CastleMaskFromTo[sq(7,0)] = 15 & ~1;
	CastleMaskFromTo[sq(0,0)] = 15 & ~2;
	CastleMaskOnCapture[sq(7,0)] = 15 & ~1;
	CastleMaskOnCapture[sq(0,0)] = 15 & ~2;
	// 黑
	CastleMaskFromTo[sq(4,7)] = 15 & ~4 & ~8;
	CastleMaskFromTo[sq(7,7)] = 15 & ~4;
	CastleMaskFromTo[sq(0,7)] = 15 & ~8;
	CastleMaskOnCapture[sq(7,7)] = 15 & ~4;
	CastleMaskOnCapture[sq(0,7)] = 15 & ~8;
}

// ----------------------------- 着法编码 -----------------------------

static inline uint32_t enc_move(int from, int to, int piece, int captured, int promoType, bool ep, bool castle, bool dpp) {
	return (from) | (to<<6) | (piece<<12) | ((captured==-1?15:captured)<<16) | ((promoType==-1?15:promoType)<<20)
	| (ep?1u<<24:0) | (castle?1u<<25:0) | (dpp?1u<<26:0);
}
static inline int m_from(uint32_t m){ return m & 63; }
static inline int m_to(uint32_t m){ return (m>>6) & 63; }
static inline int m_piece(uint32_t m){ return (m>>12) & 15; }
static inline int m_captured(uint32_t m){ int x=(m>>16)&15; return x==15?-1:x; }
static inline int m_promo(uint32_t m){ int x=(m>>20)&15; return x==15?-1:x; }
static inline bool m_ep(uint32_t m){ return (m>>24)&1; }
static inline bool m_castle(uint32_t m){ return (m>>25)&1; }
static inline bool m_dpp(uint32_t m){ return (m>>26)&1; }

struct MoveEntry { uint32_t m; int score; };
struct MoveList {
	MoveEntry mv[256];
	int size=0;
	void clear(){ size=0; }
	void add(uint32_t m, int score=0){ mv[size++]={m,score}; }
};

// ----------------------------- TT/历史/Killer -----------------------------

int SEE_Value[12] = {
	100, 320, 330, 500, 900, 20000,
	100, 320, 330, 500, 900, 20000
};

struct TTEntry {
	uint64_t key;
	uint32_t move;
	int16_t score;
	int16_t eval;
	uint8_t depth;
	uint8_t flag; // 0 exact, 1 lower, 2 upper
	uint8_t age;
	uint8_t pad;
};
struct TransTable {
	vector<TTEntry> t;
	uint64_t mask=0;
	uint8_t age=0;
	size_t sizeEntries=0;
	
	void resizeMB(size_t MB) {
		if (MB < 1) MB = 1;
		size_t bytes = MB * 1024ULL * 1024ULL;
		size_t n = bytes / sizeof(TTEntry);
		size_t pow2=1; while(pow2 < n) pow2 <<= 1;
		n = pow2;
		t.assign(n, TTEntry{0,0,0,0,0,0,0,0});
		mask = n-1;
		sizeEntries = n; age=0;
	}
	void clear() { for (auto &e : t) e = TTEntry{0,0,0,0,0,0,0,0}; age=0; }
	inline TTEntry* probe(uint64_t key, bool &found) {
		TTEntry* e = &t[key & mask];
		found = (e->key == key);
		return e;
	}
} TT;

int History[2][64][64];
uint32_t Killers1[MAX_PLY], Killers2[MAX_PLY];

// ----------------------------- 统计/时间 -----------------------------

struct SearchStats {
	uint64_t nodes=0;
	uint64_t qnodes=0;
	chrono::steady_clock::time_point start;
	int seldepth=0;
	void reset(){ nodes=0; qnodes=0; seldepth=0; start=chrono::steady_clock::now(); }
	uint64_t elapsed_ms() const { return (uint64_t)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now()-start).count(); }
	uint64_t nps() const {
		auto ms = elapsed_ms(); if (ms==0) ms=1;
		return (nodes*1000ULL)/ms;
	}
} Stats;

struct Limits {
	int depth = INT_MAX;
	uint64_t nodes = ULLONG_MAX;
	int movetime = -1;
	int wtime = -1, btime = -1, winc = 0, binc = 0, movestogo = 30;
	bool ponder = false;
};

static int game_phase(const Board& b) {
	const int phaseW[6] = {0,1,1,2,4,0};
	int phase = 0;
	for (int color=0;color<2;color++) {
		for (int pt=PAWN; pt<=KING; ++pt) {
			int code = Board::code(color, pt);
			U64 bbp = b.bb[code];
			while (bbp) { poplsb(bbp); phase += phaseW[pt]; }
		}
	}
	if (phase > 24) phase = 24;
	return phase;
}

struct TimeMgr {
	uint64_t softStopTimeMs = ULLONG_MAX; // 建议停止
	uint64_t stopTimeMs = ULLONG_MAX;     // 硬停止
	int timeForMoveMs = 1000;
	
	void setup(const Board& b, const Limits& lim) {
		using namespace chrono;
		auto nowms = (uint64_t)duration_cast<milliseconds>(chrono::steady_clock::now().time_since_epoch()).count();
		
		if (lim.movetime > 0) {
			timeForMoveMs  = lim.movetime;
			softStopTimeMs = nowms + (int)(timeForMoveMs * 0.93);
			stopTimeMs     = nowms + timeForMoveMs;
			return;
		}
		
		int myTime = (b.side == WHITE ? lim.wtime : lim.btime);
		int myInc  = (b.side == WHITE ? lim.winc  : lim.binc);
		if (myTime < 0) myTime = 1000;
		if (myInc  < 0) myInc  = 0;
		
		double mgf = game_phase(b) / 24.0;
		
		double targetOpenMs = 4500.0;
		double targetMidMs  = 12000.0;
		double targetEndMs  = 6000.0;
		
		double targetMs = 0.0;
		if (mgf >= 0.66) {
			targetMs = targetOpenMs;
		} else if (mgf >= 0.33) {
			double t = (mgf - 0.33) / (0.66 - 0.33);
			targetMs = targetMidMs * (1.0 - t) + targetOpenMs * t;
		} else {
			double t = (mgf - 0.00) / (0.33 - 0.00);
			targetMs = targetEndMs * (1.0 - t) + targetMidMs * t;
		}
		
		bool inCheck = b.square_attacked(b.kingSq[b.side], b.side^1);
		if (inCheck) targetMs *= 1.3;
		
		double capFrac = (mgf >= 0.66 ? 0.12 : (mgf >= 0.33 ? 0.16 : 0.12));
		double capByBank = myTime * capFrac;
		targetMs = min(targetMs, capByBank);
		
		if (myInc > 0) {
			targetMs = min(targetMs + myInc * 0.35, capByBank);
		}
		
		if (mgf <= 0.33 && myTime < myInc * 10) {
			targetMs = min<double>(targetMs, max(80.0, myInc * 0.90));
		}
		
		targetMs = max(60.0, targetMs);
		double hardCap = (mgf >= 0.66 ? 8000.0 : (mgf >= 0.33 ? 20000.0 : 12000.0));
		targetMs = min(targetMs, hardCap);
		
		timeForMoveMs  = (int)targetMs;
		softStopTimeMs = nowms + (uint64_t)(timeForMoveMs * 0.93);
		stopTimeMs     = nowms + (uint64_t) timeForMoveMs;
	}
	
	bool time_up() const {
		using namespace chrono;
		auto nowms = (uint64_t)duration_cast<milliseconds>(chrono::steady_clock::now().time_since_epoch()).count();
		return nowms >= stopTimeMs;
	}
	bool soft_time_up() const {
		using namespace chrono;
		auto nowms = (uint64_t)duration_cast<milliseconds>(steady_clock::now().time_since_epoch()).count();
		return nowms >= softStopTimeMs;
	}
} TM;

// ----------------------------- 重复/不足子力 -----------------------------

static bool is_threefold(const Board& b) {
	int limit = min(b.sp, b.halfmove);
	int reps = 1;
	for (int i = 1; i <= limit; ++i) {
		if (b.st[b.sp - i].key == b.key) {
			reps++;
			if (reps >= 3) return true;
		}
	}
	return false;
}
static bool insufficient_material(const Board& b) {
	U64 wp = b.bb[Board::code(WHITE, PAWN)] | b.bb[Board::code(BLACK, PAWN)];
	U64 wrq = b.bb[Board::code(WHITE, ROOK)] | b.bb[Board::code(WHITE, QUEEN)]
	| b.bb[Board::code(BLACK, ROOK)] | b.bb[Board::code(BLACK, QUEEN)];
	if (wp || wrq) return false;
	int wn = popcount(b.bb[Board::code(WHITE, KNIGHT)]);
	int wb = popcount(b.bb[Board::code(WHITE, BISHOP)]);
	int bn = popcount(b.bb[Board::code(BLACK, KNIGHT)]);
	int bbp= popcount(b.bb[Board::code(BLACK, BISHOP)]);
	int minor = wn+wb+bn+bbp;
	if (minor==0) return true;
	if (minor==1) return true;
	if (minor==2 && wn==1 && bn==1 && wb==0 && bbp==0) return true;
	if (minor==2 && wb==1 && bbp==1 && wn==0 && bn==0) return true;
	return false;
}

// ----------------------------- 走子/悔棋 -----------------------------

static bool make_move(Board& b, uint32_t m) {
	int from = m_from(m), to = m_to(m);
	int pc = m_piece(m);
	int side = b.side;
	int pt = pc % 6;
	
	State &st = b.st[b.sp++];
	st.key = b.key;
	st.castling = b.castling;
	st.ep = b.ep;
	st.halfmove = b.halfmove;
	st.captured = -1;
	st.move = m;
	st.fullmove = b.fullmove;
	
	if (b.ep != -1) b.key ^= ZEP[file_of(b.ep)];
	b.ep = -1;
	
	if (pt==PAWN || m_captured(m)!=-1) b.halfmove = 0;
	else b.halfmove++;
	
	if (m_ep(m)) {
		int capSq = to + (side==WHITE ? -8 : 8);
		st.captured = Board::code(side^1, PAWN);
		b.remove_piece(capSq);
	} else if (m_captured(m) != -1) {
		st.captured = m_captured(m);
		b.remove_piece(to);
		b.castling &= CastleMaskOnCapture[to];
	}
	
	b.move_piece(from, to);
	
	if (m_promo(m) != -1) {
		int promoPt = m_promo(m);
		int promoCode = Board::code(side, promoPt);
		b.remove_piece(to);
		b.put_piece(promoCode, to);
	}
	
	if (m_castle(m)) {
		if (side==WHITE) {
			if (to == sq(6,0)) b.move_piece(sq(7,0), sq(5,0));
			else if (to == sq(2,0)) b.move_piece(sq(0,0), sq(3,0));
		} else {
			if (to == sq(6,7)) b.move_piece(sq(7,7), sq(5,7));
			else if (to == sq(2,7)) b.move_piece(sq(0,7), sq(3,7));
		}
	}
	
	if (m_dpp(m)) {
		int epSq = to + (side==WHITE ? -8 : 8);
		b.ep = epSq;
		b.key ^= ZEP[file_of(b.ep)];
	}
	
	b.castling &= CastleMaskFromTo[from];
	b.castling &= CastleMaskFromTo[to];
	b.key ^= ZCastle[st.castling];
	b.key ^= ZCastle[b.castling];
	
	b.side ^= 1;
	b.key ^= ZSide;
	
	if (side == BLACK) b.fullmove++;
	
	int us = side;
	int ksq = b.kingSq[us];
	if (b.square_attacked(ksq, us^1)) {
		b.side ^= 1; b.key ^= ZSide;
		b.key ^= ZCastle[b.castling];
		b.castling = st.castling;
		b.key ^= ZCastle[b.castling];
		if (b.ep!=-1) b.key ^= ZEP[file_of(b.ep)];
		b.ep = st.ep;
		if (b.ep!=-1) b.key ^= ZEP[file_of(b.ep)];
		b.halfmove = st.halfmove;
		b.fullmove = st.fullmove;
		
		if (m_castle(m)) {
			if (us==WHITE) {
				if (to == sq(6,0)) b.move_piece(sq(5,0), sq(7,0));
				else if (to == sq(2,0)) b.move_piece(sq(3,0), sq(0,0));
			} else {
				if (to == sq(6,7)) b.move_piece(sq(5,7), sq(7,7));
				else if (to == sq(2,7)) b.move_piece(sq(3,7), sq(0,7));
			}
		}
		if (m_promo(m) != -1) {
			b.remove_piece(to);
			b.put_piece(Board::code(us, PAWN), to);
		}
		b.move_piece(to, from);
		if (m_ep(m)) {
			int capSq = to + (us==WHITE ? -8 : 8);
			b.put_piece(Board::code(us^1, PAWN), capSq);
		} else if (st.captured != -1) {
			b.put_piece(st.captured, to);
		}
		b.sp--;
		return false;
	}
	return true;
}

static void unmake_move(Board& b) {
	State &st = b.st[--b.sp];
	uint32_t m = st.move;
	int from = m_from(m), to = m_to(m);
	int us = b.side ^ 1;
	
	b.side ^= 1;
	b.key ^= ZSide;
	b.fullmove = st.fullmove;
	
	b.key ^= ZCastle[b.castling];
	b.castling = st.castling;
	b.key ^= ZCastle[b.castling];
	
	if (b.ep != -1) b.key ^= ZEP[file_of(b.ep)];
	b.ep = st.ep;
	if (b.ep != -1) b.key ^= ZEP[file_of(b.ep)];
	
	b.halfmove = st.halfmove;
	
	if (m_castle(m)) {
		if (us==WHITE) {
			if (to == sq(6,0)) b.move_piece(sq(5,0), sq(7,0));
			else if (to == sq(2,0)) b.move_piece(sq(3,0), sq(0,0));
		} else {
			if (to == sq(6,7)) b.move_piece(sq(5,7), sq(7,7));
			else if (to == sq(2,7)) b.move_piece(sq(3,7), sq(0,7));
		}
	}
	
	if (m_promo(m) != -1) {
		b.remove_piece(to);
		b.put_piece(Board::code(us, PAWN), to);
	}
	
	b.move_piece(to, from);
	
	if (m_ep(m)) {
		int capSq = to + (us==WHITE ? -8 : 8);
		b.put_piece(Board::code(us^1, PAWN), capSq);
	} else if (st.captured != -1) {
		b.put_piece(st.captured, to);
	}
}

// ----------------------------- 着法生成 -----------------------------

static void gen_moves(const Board& b, MoveList& list, bool capsOnly=false) {
	list.clear();
	int us = b.side, them = us^1;
	U64 occUs = b.occ[us], occThem = b.occ[them], occAll = b.occAll;
	
	// Pawns（逐个 from）
	U64 pawns = b.bb[Board::code(us, PAWN)];
	if (us == WHITE) {
		U64 p = pawns;
		while (p) {
			int s = lsb(p); p &= p-1;
			int r = rank_of(s), f = file_of(s);
			if (f>0) {
				int to = s + 7;
				if (to<64 && ((occThem >> to)&1ULL)) {
					int captured = b.board[to];
					if (r==6) {
						int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
						for (int i=0;i<4;i++)
							list.add(enc_move(s,to,Board::code(us,PAWN), captured, promoPts[i], false, false, false), 200000 + SEE_Value[captured] + 50*i);
					} else {
						list.add(enc_move(s,to,Board::code(us,PAWN), captured, -1, false, false, false), 100000 + SEE_Value[captured] - 10);
					}
				}
				if (to==b.ep) {
					list.add(enc_move(s,to,Board::code(us,PAWN), Board::code(them,PAWN), -1, true, false, false), 99950);
				}
			}
			if (f<7) {
				int to = s + 9;
				if (to<64 && ((occThem >> to)&1ULL)) {
					int captured = b.board[to];
					if (r==6) {
						int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
						for (int i=0;i<4;i++)
							list.add(enc_move(s,to,Board::code(us,PAWN), captured, promoPts[i], false, false, false), 200000 + SEE_Value[captured] + 50*i);
					} else {
						list.add(enc_move(s,to,Board::code(us,PAWN), captured, -1, false, false, false), 100000 + SEE_Value[captured] - 10);
					}
				}
				if (to==b.ep) {
					list.add(enc_move(s,to,Board::code(us,PAWN), Board::code(them,PAWN), -1, true, false, false), 99950);
				}
			}
			if (capsOnly) continue;
			int to1 = s + 8;
			if (to1<64 && ((occAll >> to1)&1ULL)==0) {
				if (r==6) {
					int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
					for (int i=0;i<4;i++)
						list.add(enc_move(s,to1,Board::code(us,PAWN), -1, promoPts[i], false, false, false), 150000 + 50*i);
				} else {
					list.add(enc_move(s,to1,Board::code(us,PAWN), -1, -1, false, false, false), 10);
					if (r==1) {
						int to2 = s + 16;
						if (((occAll >> to2)&1ULL)==0) {
							list.add(enc_move(s,to2,Board::code(us,PAWN), -1, -1, false, false, true), 9);
						}
					}
				}
			}
		}
	} else {
		U64 p = pawns;
		while (p) {
			int s = lsb(p); p &= p-1;
			int r = rank_of(s), f = file_of(s);
			if (f>0) {
				int to = s - 9;
				if (to>=0 && ((occThem >> to)&1ULL)) {
					int captured = b.board[to];
					if (r==1) {
						int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
						for (int i=0;i<4;i++)
							list.add(enc_move(s,to,Board::code(us,PAWN), captured, promoPts[i], false, false, false), 200000 + SEE_Value[captured] + 50*i);
					} else {
						list.add(enc_move(s,to,Board::code(us,PAWN), captured, -1, false, false, false), 100000 + SEE_Value[captured] - 10);
					}
				}
				if (to==b.ep) {
					list.add(enc_move(s,to,Board::code(us,PAWN), Board::code(them,PAWN), -1, true, false, false), 99950);
				}
			}
			if (f<7) {
				int to = s - 7;
				if (to>=0 && ((occThem >> to)&1ULL)) {
					int captured = b.board[to];
					if (r==1) {
						int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
						for (int i=0;i<4;i++)
							list.add(enc_move(s,to,Board::code(us,PAWN), captured, promoPts[i], false, false, false), 200000 + SEE_Value[captured] + 50*i);
					} else {
						list.add(enc_move(s,to,Board::code(us,PAWN), captured, -1, false, false, false), 100000 + SEE_Value[captured] - 10);
					}
				}
				if (to==b.ep) {
					list.add(enc_move(s,to,Board::code(us,PAWN), Board::code(them,PAWN), -1, true, false, false), 99950);
				}
			}
			if (capsOnly) continue;
			int to1 = s - 8;
			if (to1>=0 && ((occAll >> to1)&1ULL)==0) {
				if (r==1) {
					int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
					for (int i=0;i<4;i++)
						list.add(enc_move(s,to1,Board::code(us,PAWN), -1, promoPts[i], false, false, false), 150000 + 50*i);
				} else {
					list.add(enc_move(s,to1,Board::code(us,PAWN), -1, -1, false, false, false), 10);
					if (r==6) {
						int to2 = s - 16;
						if (((occAll >> to2)&1ULL)==0) {
							list.add(enc_move(s,to2,Board::code(us,PAWN), -1, -1, false, false, true), 9);
						}
					}
				}
			}
		}
	}
	
	// Knights
{
	U64 bbk = b.bb[Board::code(us, KNIGHT)];
	while (bbk) {
		int s = lsb(bbk); bbk &= bbk-1;
		U64 att = KnightAtt[s] & ~occUs;
		U64 x = capsOnly ? (att & occThem) : att;
		while (x) {
			int to = lsb(x); x &= x-1;
			int captured = b.board[to];
			bool cap = captured!=-1;
			list.add(enc_move(s,to,Board::code(us,KNIGHT), captured, -1, false, false, false),
				cap ? 90000 + SEE_Value[captured] - 5 : 20);
		}
	}
}
	// Bishops
{
	U64 bbb = b.bb[Board::code(us, BISHOP)];
	while (bbb) {
		int s = lsb(bbb); bbb &= bbb-1;
		U64 att = bishop_attacks(s, b.occAll) & ~occUs;
		U64 x = capsOnly ? (att & occThem) : att;
		while (x) {
			int to = lsb(x); x &= x-1;
			int captured = b.board[to];
			bool cap = captured!=-1;
			list.add(enc_move(s,to,Board::code(us,BISHOP), captured, -1, false, false, false),
				cap ? 91000 + SEE_Value[captured] : 19);
		}
	}
}
	// Rooks
{
	U64 bbr = b.bb[Board::code(us, ROOK)];
	while (bbr) {
		int s = lsb(bbr); bbr &= bbr-1;
		U64 att = rook_attacks(s, b.occAll) & ~occUs;
		U64 x = capsOnly ? (att & occThem) : att;
		while (x) {
			int to = lsb(x); x &= x-1;
			int captured = b.board[to];
			bool cap = captured!=-1;
			list.add(enc_move(s,to,Board::code(us,ROOK), captured, -1, false, false, false),
				cap ? 92000 + SEE_Value[captured] : 18);
		}
	}
}
	// Queens
{
	U64 bbq = b.bb[Board::code(us, QUEEN)];
	while (bbq) {
		int s = lsb(bbq); bbq &= bbq-1;
		U64 att = queen_attacks(s, b.occAll) & ~occUs;
		U64 x = capsOnly ? (att & occThem) : att;
		while (x) {
			int to = lsb(x); x &= x-1;
			int captured = b.board[to];
			bool cap = captured!=-1;
			list.add(enc_move(s,to,Board::code(us,QUEEN), captured, -1, false, false, false),
				cap ? 93000 + SEE_Value[captured] : 17);
		}
	}
}
	// King
{
	int s = b.kingSq[us];
	U64 att = KingAtt[s] & ~occUs;
	U64 x = capsOnly ? (att & occThem) : att;
	while (x) {
		int to = lsb(x); x &= x-1;
		int captured = b.board[to];
		bool cap = captured!=-1;
		list.add(enc_move(s,to,Board::code(us,KING), captured, -1, false, false, false),
			cap ? 94000 + SEE_Value[captured] : 16);
	}
	if (!capsOnly) {
		int them = us^1;
		if (us==WHITE && s==sq(4,0)) {
			bool inCheck = b.square_attacked(s, them);
			if ((b.castling & 1) && !inCheck
				&& b.board[sq(5,0)]==NO_PIECE && b.board[sq(6,0)]==NO_PIECE
				&& !b.square_attacked(sq(5,0), them) && !b.square_attacked(sq(6,0), them)) {
				list.add(enc_move(s, sq(6,0), Board::code(us,KING), -1, -1, false, true, false), 5);
			}
			if ((b.castling & 2) && !inCheck
				&& b.board[sq(3,0)]==NO_PIECE && b.board[sq(2,0)]==NO_PIECE && b.board[sq(1,0)]==NO_PIECE
				&& !b.square_attacked(sq(3,0), them) && !b.square_attacked(sq(2,0), them)) {
				list.add(enc_move(s, sq(2,0), Board::code(us,KING), -1, -1, false, true, false), 5);
			}
		} else if (us==BLACK && s==sq(4,7)) {
			bool inCheck = b.square_attacked(s, them);
			if ((b.castling & 4) && !inCheck
				&& b.board[sq(5,7)]==NO_PIECE && b.board[sq(6,7)]==NO_PIECE
				&& !b.square_attacked(sq(5,7), them) && !b.square_attacked(sq(6,7), them)) {
				list.add(enc_move(s, sq(6,7), Board::code(us,KING), -1, -1, false, true, false), 5);
			}
			if ((b.castling & 8) && !inCheck
				&& b.board[sq(3,7)]==NO_PIECE && b.board[sq(2,7)]==NO_PIECE && b.board[sq(1,7)]==NO_PIECE
				&& !b.square_attacked(sq(3,7), them) && !b.square_attacked(sq(2,7), them)) {
				list.add(enc_move(s, sq(2,7), Board::code(us,KING), -1, -1, false, true, false), 5);
			}
		}
	}
}
}

// 静态搜索用：吃子 + 非吃子升变
static void gen_qmoves(const Board& b, MoveList& list) {
	gen_moves(b, list, true);
	int us = b.side;
	if (us == WHITE) {
		U64 pawns = b.bb[Board::code(WHITE, PAWN)];
		U64 single = ((pawns << 8) & ~b.occAll) & Rank8;
		U64 pp = single;
		while (pp) {
			int to = lsb(pp); pp &= pp-1;
			int from = to - 8;
			int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
			for (int i=0;i<4;i++) {
				list.add(enc_move(from,to,Board::code(us,PAWN), -1, promoPts[i], false, false, false), 160000 + 50*i);
			}
		}
	} else {
		U64 pawns = b.bb[Board::code(BLACK, PAWN)];
		U64 single = ((pawns >> 8) & ~b.occAll) & Rank1;
		U64 pp = single;
		while (pp) {
			int to = lsb(pp); pp &= pp-1;
			int from = to + 8;
			int promoPts[4]={QUEEN,ROOK,BISHOP,KNIGHT};
			for (int i=0;i<4;i++) {
				list.add(enc_move(from,to,Board::code(us,PAWN), -1, promoPts[i], false, false, false), 160000 + 50*i);
			}
		}
	}
}

// ----------------------------- SEE / 攻击者 -----------------------------

static inline U64 attackers_to_sq(const U64 bb[12], int color, int s, U64 occ) {
	U64 att = 0ULL;
	att |= PawnAtt[color^1][s] & bb[Board::code(color, PAWN)];
	att |= KnightAtt[s] & bb[Board::code(color, KNIGHT)];
	att |= KingAtt[s] & bb[Board::code(color, KING)];
	att |= bishop_attacks(s, occ) & (bb[Board::code(color, BISHOP)] | bb[Board::code(color, QUEEN)]);
	att |= rook_attacks(s, occ) & (bb[Board::code(color, ROOK)] | bb[Board::code(color, QUEEN)]);
	return att;
}

// 修复：正确处理“升变吃子”在交换序列中的子力类型
static int see_move(const Board& b, uint32_t m) {
	int from = m_from(m), to = m_to(m);
	int mover = m_piece(m);
	int us = mover/6, them = us^1;
	int captured = m_captured(m);
	int promo = m_promo(m);
	if (captured == -1 && !m_ep(m)) return 0;
	
	U64 workBB[12]; memcpy(workBB, b.bb, sizeof(workBB));
	U64 occ = b.occAll;
	U64 occSide[2] = { b.occ[WHITE], b.occ[BLACK] };
	
	if (m_ep(m)) {
		int capSq = to + (us==WHITE ? -8 : 8);
		workBB[Board::code(them, PAWN)] &= ~(1ULL<<capSq);
		occ &= ~(1ULL<<capSq);
		occSide[them] &= ~(1ULL<<capSq);
		captured = Board::code(them, PAWN);
	} else if (captured != -1) {
		workBB[captured] &= ~(1ULL<<to);
		occ &= ~(1ULL<<to);
		occSide[captured/6] &= ~(1ULL<<to);
	}
	
	workBB[mover] &= ~(1ULL<<from);
	occ &= ~(1ULL<<from);
	occSide[us] &= ~(1ULL<<from);
	
	int curPieceCode;
	if (promo != -1) {
		int promoCode = Board::code(us, promo);
		workBB[promoCode] |= 1ULL<<to;
		curPieceCode = promoCode;
	} else {
		workBB[mover] |= 1ULL<<to;
		curPieceCode = mover;
	}
	occ |= 1ULL<<to;
	occSide[us] |= 1ULL<<to;
	
	int curPieceType = curPieceCode % 6;
	
	int gain[32]; int d=0;
	gain[0] = SEE_Value[captured==-1?Board::code(them,PAWN):captured];
	int side = them;
	
	while (true) {
		U64 att = attackers_to_sq(workBB, side, to, occ);
		if (!att) break;
		
		int codes[6] = {PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING};
		int atkCode = -1, atkSq=-1, attackerType=-1;
		for (int i=0;i<6;i++) {
			int code = Board::code(side, codes[i]);
			U64 a = att & workBB[code];
			if (a) { attackerType=codes[i]; atkCode=code; atkSq=lsb(a); break; }
		}
		if (atkCode == -1) break;
		
		++d;
		gain[d] = SEE_Value[curPieceType] - gain[d-1];
		
		workBB[curPieceCode] &= ~(1ULL<<to);
		occ &= ~(1ULL<<to);
		occSide[curPieceCode/6] &= ~(1ULL<<to);
		
		workBB[atkCode] &= ~(1ULL<<atkSq);
		occ &= ~(1ULL<<atkSq);
		occSide[side] &= ~(1ULL<<atkSq);
		
		workBB[atkCode] |= 1ULL<<to;
		occ |= 1ULL<<to;
		occSide[side] |= 1ULL<<to;
		
		curPieceCode = atkCode;
		curPieceType = attackerType;
		side ^= 1;
	}
	
	while (d) {
		gain[d-1] = -max(-gain[d-1], gain[d]);
		--d;
	}
	return gain[0];
}

static inline bool see_ge(const Board& b, uint32_t m, int threshold) {
	return see_move(b, m) >= threshold;
}

// ----------------------------- 评估（2/3 缩放 + 机动性扣分 + 新增结构项） -----------------------------

const int mg_value[6] = {82, 337, 365, 477, 1025, 0};
const int eg_value[6] = {94, 281, 297, 512, 936, 0};

const int mg_pawn_table[64] = {
	0, 0, 0, 0, 0, 0, 0, 0,
	98, 134, 61, 95, 68, 126, 34, -11,
	-6, 7, 26, 31, 65, 56, 25, -20,
	-14, 13, 26, 21, 23, 12, 7, -23,
	-27, -2, 5, 12, 17, -4, -10, -25,
	-26, -4, -4, -10, 3, 3, 33, -12,
	-35, -1, -20, -23, -15, 24, 38, -22,
	0, 0, 0, 0, 0, 0, 0, 0
};
const int eg_pawn_table[64] = {
	0, 0, 0, 0, 0, 0, 0, 0,
	178, 173, 158, 134, 147, 132, 165, 187,
	94, 100, 85, 67, 56, 53, 82, 84,
	32, 24, 23, 5, 8, 14, 17, 17,
	13, 9, 3, 3, 3, -8, 3, -1,
	4, 7, -6, 1, 0, -5, -1, -8,
	13, 8, 8, 10, 13, 0, 2, -7,
	0, 0, 0, 0, 0, 0, 0, 0
};
const int mg_knight_table[64] = {
	-167,-89,-34,-49,61,-97,-15,-107, -73,-41,72,36,23,62,7,-17, -47,60,37,65,84,129,73,44, -9,17,19,53,37,69,18,22,
	-13,4,16,13,28,19,21,-8, -23,-9,12,10,19,17,25,-16, -29,-53,-12,-3,-1,18,-14,-19, -105,-11,-58,-33,-17,-28,-9,-23
};
const int eg_knight_table[64] = {
	-58,-38,-13,-28,-31,-27,-63,-99, -25,-8,-25,-2,-9,-25,-24,-52, -24,-20,10,9,-1,-9,-19,-41, -17,3,22,22,22,11,8,-18,
	-18,-6,16,25,16,17,4,-18, -23,-3,-1,15,10,-3,-20,-22, -42,-20,-10,-5,-2,-20,-23,-44, -29,-51,-23,-15,-22,-18,-50,-64
};
const int mg_bishop_table[64] = {
	-29,4,-82,-37,-25,-42,7,-8, -26,16,-18,-13,30,59,18,-47, -16,37,43,40,35,50,37,-2, -4,5,19,50,37,37,7,-2,
	-6,13,13,26,34,12,10,4, 0,15,15,15,14,27,18,10, 4,15,16,0,7,21,33,1, -33,-3,-14,-21,-13,-12,-39,-21
};
const int eg_bishop_table[64] = {
	-14,-21,-11,-8,-7,-9,-17,-24, -8,-4,7,-12,-3,-13,-4,-14, 2,-8,0,-1,-2,6,0,4, -3,9,12,9,14,10,3,2,
	-6,3,13,19,7,10,-3,-9, -12,-3,8,10,13,3,-7,-15, -14,-18,-7,-1,4,-9,-15,-27, -23,-9,-23,-5,-9,-16,-5,-17
};
const int mg_rook_table[64] = {
	32,42,32,51,63,9,31,43, 27,32,58,62,80,67,26,44, -5,19,26,36,17,45,61,16, -24,-11,7,26,24,35,-8,-20,
	-36,-26,-12,-1,9,-7,6,-23, -45,-25,-16,-17,3,0,-5,-33, -44,-16,-20,-9,-1,11,-6,-71, -19,-13,1,17,16,7,-37,-26
};
const int eg_rook_table[64] = {
	13,10,18,15,12,12,8,5, 11,13,13,11,-3,3,8,3, 7,7,7,5,4,-3,-5,-3, 4,3,13,1,2,1,-1,2,
	3,5,8,4,-5,-6,-8,-11, -4,0,-5,-1,-7,-12,-8,-16, -6,-6,0,2,-9,-9,-11,-3, -9,2,3,-1,-5,-13,4,-20
};
const int mg_queen_table[64] = {
	-28,0,29,12,59,44,43,45, -24,-39,-5,1,-16,57,28,54, -13,-17,7,8,29,56,47,57, -27,-27,-16,-16,-1,17,-2,1,
	-9,-26,-9,-10,-2,-4,3,-3, -14,2,-11,-2,-5,2,14,5, -35,-8,11,2,8,15,-3,1, -1,-18,-9,10,-15,-25,-31,-50
};
const int eg_queen_table[64] = {
	-9,22,22,27,27,19,10,20, -17,20,32,41,58,25,30,0, -20,6,9,49,47,35,19,9, 3,22,24,45,57,40,57,36,
	-18,28,19,47,31,34,39,23, -16,-27,15,6,9,17,10,5, -22,-23,-30,-16,-16,-23,-36,-32, -33,-28,-22,-43,-5,-32,-20,-41
};
const int mg_king_table[64] = {
	-65,23,16,-15,-56,-34,2,13, 29,-1,-20,-7,-8,-4,-38,-29, -9,-26,-9,-10,-2,-4,3,-3, -14,-13,-22,-46,-44,-30,-15,-27,
	-27,-27,-16,-16,-1,17,-2,1, -9,-17,19,-3,-9,-6,14,13, -25,-8,-25,-2,-9,-25,-24,-52, -167,-89,-34,-49,61,-97,-15,-107
};
const int eg_king_table[64] = {
	-74,-35,-18,-18,-11,15,4,-17, -12,17,14,17,17,38,23,11, 10,17,23,15,20,45,44,13, -8,22,24,27,26,33,26,3,
	-18,-4,21,24,27,23,9,-11, -19,-3,11,21,23,16,7,-9, -27,-11,4,13,14,4,-5,-17, -53,-34,-21,-11,-28,-14,-24,-43
};
static inline int pst_mg(int pt, int sq) {
	switch(pt){
		case PAWN: return mg_pawn_table[sq];
		case KNIGHT: return mg_knight_table[sq];
		case BISHOP: return mg_bishop_table[sq];
		case ROOK: return mg_rook_table[sq];
		case QUEEN: return mg_queen_table[sq];
		case KING: return mg_king_table[sq];
	}
	return 0;
}
static inline int pst_eg(int pt, int sq) {
	switch(pt){
		case PAWN: return eg_pawn_table[sq];
		case KNIGHT: return eg_knight_table[sq];
		case BISHOP: return eg_bishop_table[sq];
		case ROOK: return eg_rook_table[sq];
		case QUEEN: return eg_queen_table[sq];
		case KING: return eg_king_table[sq];
	}
	return 0;
}

static inline U64 attackers_to_sq(const Board& b, int color, int s) {
	return attackers_to_sq(b.bb, color, s, b.occAll);
}

// 物质平衡（不含王），用于“少兑子”排序偏置（>0 说明当前方领先）
static int material_balance_side(const Board& b, int color) {
	int sum[2] = {0,0};
	for (int c=0;c<2;c++) {
		sum[c] += mg_value[PAWN]   * popcount(b.bb[Board::code(c,PAWN)]);
		sum[c] += mg_value[KNIGHT] * popcount(b.bb[Board::code(c,KNIGHT)]);
		sum[c] += mg_value[BISHOP] * popcount(b.bb[Board::code(c,BISHOP)]);
		sum[c] += mg_value[ROOK]   * popcount(b.bb[Board::code(c,ROOK)]);
		sum[c] += mg_value[QUEEN]  * popcount(b.bb[Board::code(c,QUEEN)]);
	}
	return sum[color] - sum[color^1];
}

// [新增] 机动性/垃圾棋子扣分（马/象/车/后），越不动挨罚越多；被攻不受守时加罚；有吃子时减半
static void mobility_penalty_terms(const Board& b, int mgAdd[2], int egAdd[2]) {
	mgAdd[0]=mgAdd[1]=egAdd[0]=egAdd[1]=0;
	for (int color=0;color<2;color++){
		int them = color^1;
		U64 occUs = b.occ[color];
		U64 occAll = b.occAll;
		
		auto apply_piece = [&](int pt, U64 bbp){
			while (bbp){
				int s = lsb(bbp); bbp &= bbp-1;
				U64 att=0, cap=0;
				int mobility=0;
				switch(pt){
				case KNIGHT:
					att = KnightAtt[s] & ~occUs;
					cap = KnightAtt[s] & b.occ[them];
					break;
				case BISHOP:
					att = bishop_attacks(s, occAll) & ~occUs;
					cap = bishop_attacks(s, occAll) & b.occ[them];
					break;
				case ROOK:
					att = rook_attacks(s, occAll) & ~occUs;
					cap = rook_attacks(s, occAll) & b.occ[them];
					break;
				case QUEEN:
					att = queen_attacks(s, occAll) & ~occUs;
					cap = queen_attacks(s, occAll) & b.occ[them];
					break;
					default: break;
				}
				if (pt==KNIGHT || pt==BISHOP || pt==ROOK || pt==QUEEN) {
					mobility = popcount(att);
					int mgPen=0, egPen=0;
					
					// 基础“低机动”阈值和每格扣分
					if (pt==KNIGHT){
						int thr=4; int k = max(0, thr - mobility);
						mgPen += 6*k; egPen += 4*k;
						// 边线马小扣分
						int f=file_of(s), r=rank_of(s);
						if (f==0||f==7||r==0||r==7){ mgPen += 6; egPen += 2; }
						// 完全被堵
						if (mobility==0){ mgPen += 10; egPen += 6; }
					}else if (pt==BISHOP){
						int thr=5; int k = max(0, thr - mobility);
						mgPen += 5*k; egPen += 3*k;
						if (mobility==0){ mgPen += 10; egPen += 6; }
					}else if (pt==ROOK){
						int thr=7; int k = max(0, thr - mobility);
						mgPen += 3*k; egPen += 2*k;
						if (mobility<=1){ mgPen += 12; egPen += 8; }
					}else if (pt==QUEEN){
						int thr=8; int k = max(0, thr - mobility);
						mgPen += 2*k; egPen += 1*k;
						if (mobility<=1){ mgPen += 16; egPen += 10; }
					}
					
					// 被攻不受守时，加罚（非送子受限）
					bool attacked = attackers_to_sq(b.bb, them, s, occAll)!=0;
					bool defended = attackers_to_sq(b.bb, color, s, occAll)!=0;
					if (attacked && !defended){
						if (pt==KNIGHT||pt==BISHOP){ mgPen += 8; egPen += 4; }
						else if (pt==ROOK){ mgPen += 10; egPen += 5; }
						else if (pt==QUEEN){ mgPen += 12; egPen += 6; }
					}
					
					// 若有直接吃子，对扣分打 0.75 系数
					if (cap){
						mgPen = (mgPen*3)/4;
						egPen = (egPen*3)/4;
					}
					
					mgAdd[color] -= mgPen;
					egAdd[color] -= egPen;
				}
			}
		};
		
		apply_piece(KNIGHT, b.bb[Board::code(color, KNIGHT)]);
		apply_piece(BISHOP, b.bb[Board::code(color, BISHOP)]);
		apply_piece(ROOK,   b.bb[Board::code(color, ROOK)]);
		apply_piece(QUEEN,  b.bb[Board::code(color, QUEEN)]);
	}
}

// 新增：结构/开局常识项（中心兵、连兵、前哨马、堡垒象、开发）
// 辅助：判断是否“前哨”（color 在 s 上的马），基于相邻列前方无敌兵
static bool is_knight_outpost(const Board& b, int color, int s) {
	int them = color^1;
	int f = file_of(s), r = rank_of(s);
	if (color==WHITE) {
		if (r < 2) return false; // 太靠后
	} else {
		if (r > 5) return false;
	}
	U64 enemyPawns = b.bb[Board::code(them, PAWN)];
	U64 lanes = AdjacentFiles[f] & ForwardMask[color][s];
	if (lanes & enemyPawns) return false;
	return true;
}

static int eval_fianchetto_bishop(const Board& b, int color) {
	int mg=0, eg=0;
	int s1 = (color==WHITE? sq(6,1):sq(6,6)); // g2/g7
	int s2 = (color==WHITE? sq(1,1):sq(1,6)); // b2/b7
	int codeB = Board::code(color, BISHOP);
	U64 myPawns = b.bb[Board::code(color, PAWN)];
	bool kingsideCastled = (color==WHITE? (b.kingSq[WHITE]==sq(6,0)): (b.kingSq[BLACK]==sq(6,7)));
	// g2/g7
	if ((b.bb[codeB] >> s1) & 1ULL) {
		bool base = ((myPawns >> (color==WHITE? sq(6,1):sq(6,6))) & 1ULL) || // g2/g7 有兵（开局结构）
		((myPawns >> (color==WHITE? sq(6,2):sq(6,5))) & 1ULL);   // g3/g6
		mg += base? 18:12; eg += base? 12:8;
		if (kingsideCastled) { mg += 6; eg += 4; }
		// 长对角线清空小加成（附近无己方阻挡）
		int mid = (color==WHITE? sq(5,2):sq(5,5)); // f3/f6
		if (b.board[mid]==NO_PIECE) { mg += 3; eg += 2; }
	}
	// b2/b7
	if ((b.bb[codeB] >> s2) & 1ULL) {
		bool base = ((myPawns >> (color==WHITE? sq(1,1):sq(1,6))) & 1ULL) ||
		((myPawns >> (color==WHITE? sq(1,2):sq(1,5))) & 1ULL);
		mg += base? 14:10; eg += base? 10:6;
	}
	return (mg<<16) | (eg & 0xFFFF);
}

struct Eval {
	static int evaluate(const Board& b) {
		if (b.halfmove >= 100) return 0;
		if (is_threefold(b)) return 0;
		if (insufficient_material(b)) return 0;
		
		int mgScore[2]={0,0}, egScore[2]={0,0};
		int phase=0;
		const int phaseW[6]={0,1,1,2,4,0};
		
		// 材料 + PST（2/3 缩放）
		for (int color=0;color<2;color++){
			for (int pt=PAWN; pt<=KING; ++pt){
				int code = Board::code(color, pt);
				U64 bbp = b.bb[code];
				while(bbp){
					int s = lsb(bbp); bbp &= bbp-1;
					int sqw = color==WHITE? s : mirror64(s);
					mgScore[color] += mg_value[pt] + (pst_mg(pt, sqw)*2)/3;
					egScore[color] += eg_value[pt] + (pst_eg(pt, sqw)*2)/3;
					phase += phaseW[pt];
				}
			}
		}
		
		// 象双
		if (popcount(b.bb[Board::code(WHITE,BISHOP)]) >= 2) { mgScore[WHITE]+=20; egScore[WHITE]+=30; }
		if (popcount(b.bb[Board::code(BLACK,BISHOP)]) >= 2) { mgScore[BLACK]+=20; egScore[BLACK]+=30; }
		
		// 通过兵（适度）
{
	U64 wp = b.bb[Board::code(WHITE, PAWN)];
	U64 bp = b.bb[Board::code(BLACK, PAWN)];
	U64 t = wp;
	while (t){
		int s = lsb(t); t &= t-1;
		if ( (bp & PassedMask[WHITE][s]) == 0ULL ) {
			static const int bonusMg[8] = {0,6,10,16,24,36,50,0};
			static const int bonusEg[8] = {0,8,12,20,30,45,70,0};
			int r = rank_of(s);
			mgScore[WHITE] += bonusMg[r]; egScore[WHITE] += bonusEg[r];
		}
	}
	t = bp;
	while (t){
		int s = lsb(t); t &= t-1;
		if ( (wp & PassedMask[BLACK][s]) == 0ULL ) {
			static const int bonusMg[8] = {0,6,10,16,24,36,50,0};
			static const int bonusEg[8] = {0,8,12,20,30,45,70,0};
			int r = 7 - rank_of(s);
			mgScore[BLACK] += bonusMg[r]; egScore[BLACK] += bonusEg[r];
		}
	}
}
		
		// 挂子惩罚（受攻不受守）
		auto hanging = [&](int color){
			int them=color^1;
			int mg=0, eg=0;
			U64 occ = b.occAll;
			for (int pt=PAWN; pt<=QUEEN; ++pt) {
				U64 bbp = b.bb[Board::code(color, pt)];
				while (bbp) {
					int s = lsb(bbp); bbp&=bbp-1;
					bool attacked = attackers_to_sq(b.bb, them, s, occ)!=0;
					bool defended = attackers_to_sq(b.bb, color, s, occ)!=0;
					if (attacked && !defended) {
						int pen = (pt==PAWN?10: pt==KNIGHT||pt==BISHOP?24: pt==ROOK?40:70);
						mg -= pen; eg -= pen/2;
					}
				}
			}
			return pair<int,int>{mg,eg};
		};
		auto hW = hanging(WHITE), hB = hanging(BLACK);
		mgScore[WHITE]+=hW.first; egScore[WHITE]+=hW.second;
		mgScore[BLACK]+=hB.first; egScore[BLACK]+=hB.second;
		
		// [新增] 机动性/垃圾棋子扣分
{
	int mgM[2], egM[2];
	mobility_penalty_terms(b, mgM, egM);
	mgScore[WHITE]+=mgM[WHITE]; egScore[WHITE]+=egM[WHITE];
	mgScore[BLACK]+=mgM[BLACK]; egScore[BLACK]+=egM[BLACK];
}
		
		// [新增] 中心兵权重（中心 4 格、中心 16 格、小幅控制）
		auto center_terms = [&](int color){
			int mg=0, eg=0;
			U64 pawns = b.bb[Board::code(color, PAWN)];
			U64 pCenter4 = pawns & Center4Mask;
			int c4 = popcount(pCenter4);
			mg += 16 * c4; eg += 8 * c4;
			
			U64 pCenter16 = pawns & Center16Mask;
			int c16 = popcount(pCenter16);
			mg += 4 * c16; eg += 2 * c16;
			
			// d/e 兵额外（开局中局）
			U64 dFile = pawns & FileMask[3];
			U64 eFile = pawns & FileMask[4];
			mg += 6 * popcount(dFile);
			mg += 6 * popcount(eFile);
			
			// 控制中心4格的小奖励（由兵控制）
			U64 attAll = 0ULL;
			U64 p = pawns;
			while (p) { int s=lsb(p); p&=p-1; attAll |= PawnAtt[color][s]; }
			int ctrl4 = popcount(attAll & Center4Mask);
			mg += 3 * ctrl4; eg += 2 * ctrl4;
			
			return pair<int,int>{mg,eg};
		};
		auto cW = center_terms(WHITE), cB = center_terms(BLACK);
		mgScore[WHITE]+=cW.first; egScore[WHITE]+=cW.second;
		mgScore[BLACK]+=cB.first; egScore[BLACK]+=cB.second;
		
		// [新增] 中心连兵（d/e 同排，例如 d4+e4 或 d5+e5）
		auto central_connected_pawns = [&](int color){
			int mg=0, eg=0;
			U64 pawns = b.bb[Board::code(color, PAWN)];
			for (int r=2; r<=5; ++r) {
				bool dHere = (pawns & (1ULL<<sq(3,r))) != 0;
				bool eHere = (pawns & (1ULL<<sq(4,r))) != 0;
				if (dHere && eHere) {
					mg += 18; // 中局价值高
					eg += 10;
				}
			}
			return pair<int,int>{mg,eg};
		};
		auto ccW = central_connected_pawns(WHITE), ccB = central_connected_pawns(BLACK);
		mgScore[WHITE]+=ccW.first; egScore[WHITE]+=ccW.second;
		mgScore[BLACK]+=ccB.first; egScore[BLACK]+=ccB.second;
		
		// [新增] 前哨马（有己方兵支持时更高）
		auto outpost_knight_terms = [&](int color){
			int mg=0, eg=0;
			int them = color^1;
			U64 knights = b.bb[Board::code(color, KNIGHT)];
			U64 myPawns = b.bb[Board::code(color, PAWN)];
			while (knights){
				int s = lsb(knights); knights&=knights-1;
				if (!is_knight_outpost(b, color, s)) continue;
				bool supportedByPawn = (PawnAtt[color][s] & myPawns) != 0ULL;
				int baseMg = 18, baseEg = 24;
				if (supportedByPawn) { baseMg += 10; baseEg += 12; }
				// 更靠近中心更值钱
				if ((Center16Mask >> s) & 1ULL) { baseMg += 4; baseEg += 6; }
				// 若此格不易被轻子换掉小加成（粗略：敌方轻子对该格攻击少）
				int attN = popcount((U64)attackers_to_sq(b.bb, them, s, b.occAll) & (b.bb[Board::code(them,KNIGHT)]|b.bb[Board::code(them,BISHOP)]));
				if (attN==0){ baseMg += 4; baseEg += 6; }
				mg += baseMg; eg += baseEg;
			}
			return pair<int,int>{mg,eg};
		};
		auto opW = outpost_knight_terms(WHITE), opB = outpost_knight_terms(BLACK);
		mgScore[WHITE]+=opW.first; egScore[WHITE]+=opW.second;
		mgScore[BLACK]+=opB.first; egScore[BLACK]+=opB.second;
		
		// [新增] 堡垒象（g2/b2/g7/b7）
{
	int vW = eval_fianchetto_bishop(b, WHITE);
	int vB = eval_fianchetto_bishop(b, BLACK);
	mgScore[WHITE] += (vW>>16); egScore[WHITE] += (vW & 0xFFFF);
	mgScore[BLACK] += (vB>>16); egScore[BLACK] += (vB & 0xFFFF);
}
		
		// 易位激励更强 + 未易位轻度惩罚
{
	bool wCastled = (b.kingSq[WHITE]==sq(6,0) || b.kingSq[WHITE]==sq(2,0));
	bool bCastled = (b.kingSq[BLACK]==sq(6,7) || b.kingSq[BLACK]==sq(2,7));
	
	if (wCastled) { mgScore[WHITE] += 50; egScore[WHITE] += 20; }
	if (bCastled) { mgScore[BLACK] += 50; egScore[BLACK] += 20; }
	
	if (!wCastled && b.kingSq[WHITE]==sq(4,0) && (b.castling & 3)) {
		int p = max(0, b.fullmove - 6);
		int pen = min(20, p*2);
		mgScore[WHITE] -= pen;
	}
	if (!bCastled && b.kingSq[BLACK]==sq(4,7) && (b.castling & 12)) {
		int p = max(0, b.fullmove - 6);
		int pen = min(20, p*2);
		mgScore[BLACK] -= pen;
	}
	if (!wCastled && b.kingSq[WHITE]!=sq(4,0) && !b.square_attacked(b.kingSq[WHITE], BLACK)) {
		int p = max(0, 12 - b.fullmove);
		int pen = min(18, 2*p);
		mgScore[WHITE] -= pen;
	}
	if (!bCastled && b.kingSq[BLACK]!=sq(4,7) && !b.square_attacked(b.kingSq[BLACK], WHITE)) {
		int p = max(0, 12 - b.fullmove);
		int pen = min(18, 2*p);
		mgScore[BLACK] -= pen;
	}
}
		
		// 轻微“开发奖励/未开发惩罚”（仅中度开局阶段生效）
{
	int gp = game_phase(b); // 0..24；开局>中局>残局
	if (gp >= 16) {
		// 奖励：白/黑的两马两象离开初始格
		auto dev = [&](int color){
			int mg=0, eg=0;
			int homeRank = (color==WHITE? 0:7);
			// 未开发轻子小惩罚
			if ((b.bb[Board::code(color, KNIGHT)] & (1ULL<<sq(1,homeRank)))==0ULL) mg+=2;
			if ((b.bb[Board::code(color, KNIGHT)] & (1ULL<<sq(6,homeRank)))==0ULL) mg+=2;
			if ((b.bb[Board::code(color, BISHOP)] & (1ULL<<sq(2,homeRank)))==0ULL) mg+=2;
			if ((b.bb[Board::code(color, BISHOP)] & (1ULL<<sq(5,homeRank)))==0ULL) mg+=2;
			return pair<int,int>{mg,eg};
		};
		auto dW = dev(WHITE), dB = dev(BLACK);
		mgScore[WHITE]+=dW.first; egScore[WHITE]+=dW.second;
		mgScore[BLACK]+=dB.first; egScore[BLACK]+=dB.second;
	}
}
		
		// Tapered eval
		int mg = mgScore[WHITE] - mgScore[BLACK];
		int eg = egScore[WHITE] - egScore[BLACK];
		int phaseMax = 24; if (phase > phaseMax) phase = phaseMax;
		int score = (mg * phase + eg * (phaseMax - phase)) / phaseMax;
		
		const int tempo = 8;
		return (b.side == WHITE) ? (score + tempo) : (-(score + tempo));
	}
};

// ----------------------------- 搜索 -----------------------------

static inline int mate_in(int ply) { return MATE_SCORE - ply; }
static inline int mated_in(int ply) { return -MATE_SCORE + ply; }
static int score_to_tt(int score, int ply) {
	if (score >= MATE_IN_MAX_PLY) return score + ply;
	if (score <= -MATE_IN_MAX_PLY) return score - ply;
	return score;
}
static int score_from_tt(int score, int ply) {
	if (score >= MATE_IN_MAX_PLY) return score - ply;
	if (score <= -MATE_IN_MAX_PLY) return score + ply;
	return score;
}
static bool allow_null(const Board& b) {
	if (b.square_attacked(b.kingSq[b.side], b.side^1)) return false;
	if ( (b.bb[Board::code(b.side, QUEEN)] | b.bb[Board::code(b.side, ROOK)] | b.bb[Board::code(b.side, BISHOP)] | b.bb[Board::code(b.side, KNIGHT)]) == 0ULL &&
		popcount(b.bb[Board::code(b.side, PAWN)]) <= 2) return false;
	return true;
}

static inline bool is_hanging_major(const Board& b, int color) {
	U64 occ = b.occAll;
	int them = color ^ 1;
	U64 valuable = b.bb[Board::code(color, QUEEN)] |
	b.bb[Board::code(color, ROOK)] |
	b.bb[Board::code(color, BISHOP)]|
	b.bb[Board::code(color, KNIGHT)];
	while (valuable) {
		int s = lsb(valuable); valuable &= valuable - 1;
		bool attacked = attackers_to_sq(b.bb, them, s, occ) != 0;
		bool defended = attackers_to_sq(b.bb, color, s, occ) != 0;
		if (attacked && !defended) return true;
	}
	return false;
}

static int Quiescence(Board& b, int alpha, int beta, int ply) {
	Stats.qnodes++;
	if (ply > Stats.seldepth) Stats.seldepth = ply;
	
	if (b.halfmove >= 100) return 0;
	if (is_threefold(b)) return 0;
	
	bool inCheck = b.square_attacked(b.kingSq[b.side], b.side^1);
	
	if (!inCheck) {
		int stand = Eval::evaluate(b);
		if (stand >= beta) return stand;
		if (stand > alpha) alpha = stand;
		
		MoveList list;
		gen_qmoves(b, list);
		
		for (int i=0;i<list.size;i++){
			uint32_t m = list.mv[i].m;
			int sc=0;
			if (m_promo(m)!=-1 && m_captured(m)==-1) sc = 300000 + 10*m_promo(m);
			else if (m_captured(m)!=-1) sc = 200000 + SEE_Value[m_captured(m)] - (SEE_Value[m_piece(m)]/10);
			sc += rand_jitter(); // 随机抖动
			list.mv[i].score=sc;
		}
		sort(list.mv, list.mv+list.size, [](const MoveEntry&a,const MoveEntry&b){return a.score>b.score;});
		
		for (int i=0; i<list.size; ++i) {
			uint32_t m = list.mv[i].m;
			bool isCap = m_captured(m)!=-1;
			bool isEp = m_ep(m);
			
			if (isCap && !isEp) {
				int capVal = SEE_Value[m_captured(m)];
				if (stand + capVal + 50 < alpha) continue; // delta 剪枝
				// 更谨慎 SEE 阈值
				if (!see_ge(b, m, -10)) continue;
			}
			
			if (!make_move(b, m)) continue;
			int score = -Quiescence(b, -beta, -alpha, ply+1);
			unmake_move(b);
			
			if (score >= beta) return score;
			if (score > alpha) alpha = score;
		}
		return alpha;
	} else {
		MoveList list; gen_moves(b, list, false);
		for (int i=0;i<list.size;i++){
			uint32_t m = list.mv[i].m;
			int sc=0;
			if (m_captured(m)!=-1) sc = 200000 + SEE_Value[m_captured(m)];
			else if (m_castle(m)) sc = 150000;
			else sc = History[b.side][m_from(m)][m_to(m)];
			sc += rand_jitter(); // 随机抖动
			list.mv[i].score = sc;
		}
		sort(list.mv, list.mv+list.size, [](const MoveEntry&a,const MoveEntry&b){return a.score>b.score;});
		
		for (int i=0;i<list.size;i++){
			uint32_t m = list.mv[i].m;
			if (!make_move(b, m)) continue;
			int score = -Quiescence(b, -beta, -alpha, ply+1);
			unmake_move(b);
			
			if (score >= beta) return score;
			if (score > alpha) alpha = score;
		}
		return alpha;
	}
}

// “少兑子”偏置：基于物质形势与 SEE 对吃子的排序进行小幅调整
static inline int trade_bias_for_sorting(const Board& b, uint32_t m) {
	if (m_captured(m)==-1) return 0;
	int mb = material_balance_side(b, b.side); // >0 领先；<0 落后
	int see = see_move(b, m);
	if (see > 50 || see < -50) return 0;
	if (mb > 150) return +3000;   // 领先：鼓励交换
	if (mb < -150) return -3000;  // 落后：减少交换
	return 0;
}

// 开局走法排序微偏置：中心兵推进/轻子开发
static inline int opening_bias_score(const Board& b, uint32_t m) {
	int gp = game_phase(b); // 0..24（开局越大）
	if (gp < 16) return 0; // 中后期不加
	int us = b.side;
	int piece = m_piece(m)%6;
	int from = m_from(m), to = m_to(m);
	
	int bonus = 0;
	// 中心兵推进（到中心16格，尤其 d/e 兵）
	if (piece == PAWN) {
		if ((Center16Mask >> to) & 1ULL) bonus += 1200;
		int f = file_of(from);
		if (f==3 || f==4) bonus += 800; // d/e 兵
	}
	// 轻子开发：从初始排往外，非王翼无意义来回
	if (piece == KNIGHT || piece == BISHOP) {
		int homeRank = (us==WHITE?0:7);
		if (rank_of(from)==homeRank && rank_of(to)!=homeRank) bonus += 900;
	}
	return bonus;
}

static int Search(Board& b, int depth, int alpha, int beta, int ply,
	bool doNull, uint32_t pvTable[MAX_PLY][MAX_PLY], int pvLen[MAX_PLY]) {
		Stats.nodes++;
		if (ply > Stats.seldepth) Stats.seldepth = ply;
		if (TM.time_up()) return Eval::evaluate(b);
		
		bool inCheck = b.square_attacked(b.kingSq[b.side], b.side^1);
		if (depth <= 0) return Quiescence(b, alpha, beta, ply);
		
		if (b.halfmove >= 100) return 0;
		if (is_threefold(b)) return 0;
		if (insufficient_material(b)) return 0;
		
		bool pvNode = (beta - alpha > 1);
		bool dangerNode = inCheck || is_hanging_major(b, b.side);
		
		bool found=false;
		TTEntry* tte = TT.probe(b.key, found);
		uint32_t ttMove = 0;
		if (found && tte->depth >= depth) {
			int score = score_from_tt(tte->score, ply);
			// 注意：根节点不再允许用 TT 直接返回（避免“凭 TT 就下子”）
			if (ply > 0) {
				if (tte->flag == 0) return score;
				if (tte->flag == 1 && score >= beta) return score;
				if (tte->flag == 2 && score <= alpha) return score;
			}
			ttMove = tte->move;
		}
		
		int staticEval = (found ? tte->eval : Eval::evaluate(b));
		
		// 反向 futility（危险节点不做）
		if (!pvNode && !dangerNode && !inCheck && depth <= 2) {
			int rbeta = alpha - 110*depth;
			if (staticEval <= rbeta) {
				int qs = Quiescence(b, rbeta, rbeta+1, ply);
				if (qs <= rbeta) return qs;
			}
		}
		
		// Null move（谨慎）
		if (doNull && !pvNode && !dangerNode && !inCheck && depth >= 3 && allow_null(b) && staticEval >= beta + 120) {
			State &st = b.st[b.sp++];
			st.key = b.key; st.castling=b.castling; st.ep=b.ep; st.halfmove=b.halfmove; st.captured=-1; st.move=0; st.fullmove=b.fullmove;
			if (b.ep!=-1) b.key ^= ZEP[file_of(b.ep)];
			b.ep = -1;
			b.side ^= 1; b.key ^= ZSide;
			int R = 2 + (depth >= 5 ? 1 : 0);
			int score = -Search(b, depth - 1 - R, -beta, -beta+1, ply+1, false, pvTable, pvLen);
			b.side ^= 1; b.key ^= ZSide;
			if (b.ep!=-1) b.key ^= ZEP[file_of(b.ep)];
			b.ep = st.ep; if (b.ep!=-1) b.key ^= ZEP[file_of(b.ep)];
			b.castling = st.castling; b.halfmove = st.halfmove; b.fullmove = st.fullmove;
			b.sp--;
			if (score >= beta) return score;
		}
		
		MoveList list;
		gen_moves(b, list, false);
		
		// 排序：TT > captures(+少兑子) > Killers > castle > history (+ 开局偏置) + 随机抖动
		for (int i=0;i<list.size;i++){
			uint32_t m = list.mv[i].m;
			int score = 0;
			if ((int)m == (int)ttMove) score = 1<<30;
			else if (m_captured(m)!=-1) {
				score = (1<<29) + SEE_Value[m_captured(m)] - (SEE_Value[m_piece(m)]/10);
				score += trade_bias_for_sorting(b, m);
			}
			else if (m == Killers1[ply]) score = 1<<28;
			else if (m == Killers2[ply]) score = (1<<28)-1;
			else if (m_castle(m)) score = (1<<28)-2; // 易位优先于普通 history
			else score = History[b.side][m_from(m)][m_to(m)];
			
			// 降低“安静的非易位王走子”优先级
			if (!inCheck && (m_piece(m) % 6) == KING && m_captured(m) == -1 && !m_castle(m) && m_promo(m) == -1) {
				score -= (1 << 27);
			}
			
			// 开局微偏置（中心兵推进/轻子开发）
			score += opening_bias_score(b, m);
			
			// 随机抖动
			score += rand_jitter();
			list.mv[i].score = score;
		}
		sort(list.mv, list.mv + list.size, [](const MoveEntry& a, const MoveEntry& b){ return a.score > b.score; });
		
		int origAlpha = alpha;
		int bestScore = -INF;
		uint32_t bestMove = 0;
		pvLen[ply] = 0;
		
		int legalMoves=0;
		
		for (int i=0;i<list.size;i++){
			uint32_t m = list.mv[i].m;
			
			// 仅把“吃子/升变”视为战术步；易位算安静步
			bool isTactical = (m_captured(m)!=-1) || (m_promo(m)!=-1);
			
			// 叶子 futility（危险节点不剪）
			if (!pvNode && !dangerNode && !inCheck && depth == 1 && !isTactical) {
				if (staticEval + 90 <= alpha) continue;
			}
			
			// LMP（危险节点不做）
			if (!pvNode && !dangerNode && !inCheck && depth <= 3 && !isTactical && i > 6 + 2*depth) continue;
			
			// SEE 负收益吃子剪枝（更谨慎）
			if (!pvNode && !dangerNode && !inCheck && m_captured(m)!=-1 && depth <= 5 && !see_ge(b, m, -10))
				continue;
			
			if (!make_move(b, m)) continue;
			legalMoves++;
			
			bool nextInCheck = b.square_attacked(b.kingSq[b.side], b.side^1);
			int ext = nextInCheck ? 1 : 0;
			int newDepth = depth - 1 + ext;
			
			int score;
			// LMR 更保守
			if (!pvNode && !dangerNode && !inCheck && !isTactical && depth >= 3 && !nextInCheck) {
				int r = 1 + (depth>=6) + (i>=8);
				score = -Search(b, newDepth - r, -alpha-1, -alpha, ply+1, true, pvTable, pvLen);
			} else {
				score = -Search(b, newDepth, -alpha-1, -alpha, ply+1, true, pvTable, pvLen);
			}
			
			if (score > alpha && score < beta) {
				score = -Search(b, newDepth, -beta, -alpha, ply+1, true, pvTable, pvLen);
			}
			
			unmake_move(b);
			
			if (score > bestScore) {
				bestScore = score; bestMove = m;
				pvTable[ply][0] = m;
				for (int k=0;k<pvLen[ply+1];k++) pvTable[ply][k+1] = pvTable[ply+1][k];
				pvLen[ply] = pvLen[ply+1] + 1;
			}
			if (score > alpha) {
				alpha = score;
				if (m_captured(m)==-1 && !m_castle(m)) {
					History[b.side][m_from(m)][m_to(m)] += depth * depth;
					if (Killers1[ply] != m) { Killers2[ply] = Killers1[ply]; Killers1[ply] = m; }
				}
				if (alpha >= beta) {
					break;
				}
			}
		}
		
		if (legalMoves==0) {
			if (inCheck) return mated_in(ply);
			return 0;
		}
		
		if (tte) {
			tte->key = b.key;
			tte->move = bestMove;
			tte->depth = depth;
			tte->eval = staticEval;
			tte->age = TT.age;
			if (bestScore <= origAlpha) tte->flag = 2;
			else if (bestScore >= beta) tte->flag = 1;
			else tte->flag = 0;
			tte->score = (int16_t)score_to_tt(bestScore, ply);
		}
		
		return bestScore;
	}

// 复原 PV
static int get_pv_line(Board& b, uint32_t pv[MAX_PLY]) {
	int cnt=0;
	Board copy = b;
	for (int i=0;i<MAX_PLY;i++){
		bool found=false;
		TTEntry* e = TT.probe(copy.key, found);
		if (!found || e->move==0) break;
		uint32_t m = e->move;
		if (!make_move(copy, m)) break;
		pv[cnt++] = m;
	}
	return cnt;
}

static string move_to_uci(uint32_t m) {
	int from = m_from(m), to = m_to(m);
	char s[8];
	s[0] = 'a' + file_of(from);
	s[1] = '1' + rank_of(from);
	s[2] = 'a' + file_of(to);
	s[3] = '1' + rank_of(to);
	int promo = m_promo(m);
	if (promo!=-1) {
		s[4] = "nbrq"[ (promo==KNIGHT)?0 : (promo==BISHOP)?1 : (promo==ROOK)?2 : 3 ];
		s[5] = 0;
	} else {
		s[4] = 0;
	}
	return string(s);
}

static uint32_t parse_move_uci(Board& b, const string& str) {
	if (str.size()<4) return 0;
	int ff = str[0]-'a';
	int fr = str[1]-'1';
	int tf = str[2]-'a';
	int tr = str[3]-'1';
	int from = sq(ff,fr), to = sq(tf,tr);
	int pc = b.board[from];
	if (pc == NO_PIECE) return 0;
	int captured = b.board[to];
	
	bool ep=false, castle=false, dpp=false;
	int promoType = -1;
	
	if ((pc%6)==KING && ((from==sq(4,0) && (to==sq(6,0)||to==sq(2,0))) ||
		(from==sq(4,7) && (to==sq(6,7)||to==sq(2,7))))) {
		castle = true;
	}
	if ((pc%6)==PAWN && to == b.ep && b.ep!=-1 && captured==-1) {
		ep = true;
		captured = Board::code(b.side^1, PAWN);
	}
	if ((pc%6)==PAWN && abs(tr-fr)==2) dpp = true;
	
	if (str.size()>=5) {
		char c = (char)tolower((unsigned char)str[4]);
		if (c=='q') promoType = QUEEN;
		else if (c=='r') promoType = ROOK;
		else if (c=='b') promoType = BISHOP;
		else if (c=='n') promoType = KNIGHT;
	}
	return enc_move(from,to,pc,captured,promoType,ep,castle,dpp);
}

// ----------------------------- 迭代加深与 UCI 输出 -----------------------------

static uint32_t LastBestMoveRoot = 0;

static void print_info_line(int depth, int score, const vector<uint32_t>& pv) {
	cout << "info depth " << depth
	<< " seldepth " << Stats.seldepth
	<< " score ";
	if (score >= MATE_IN_MAX_PLY) {
		int mateIn = (MATE_SCORE - score + 1) / 2;
		cout << "mate " << mateIn;
	} else if (score <= -MATE_IN_MAX_PLY) {
		int mateIn = (MATE_SCORE + score + 1) / 2;
		cout << "mate " << -mateIn;
	} else {
		cout << "cp " << score;
	}
	cout << " time " << Stats.elapsed_ms()
	<< " nodes " << Stats.nodes
	<< " nps " << Stats.nps()
	<< " pv";
	for (auto m : pv) cout << " " << move_to_uci(m);
	cout << endl;
	cout.flush();
}

static uint32_t iterative_deepening(Board& b, const Limits& lim) {
	Stats.reset();
	TM.setup(b, lim);
	TT.age++;
	
	memset(History, 0, sizeof(History));
	memset(Killers1, 0, sizeof(Killers1));
	memset(Killers2, 0, sizeof(Killers2));
	
	uint32_t bestMove = 0;
	int bestScore = -INF;
	
	uint32_t pvTable[MAX_PLY][MAX_PLY] = {};
	int pvLen[MAX_PLY] = {};
	
	int startDepth = 1;
	int maxDepth = min(lim.depth, MAX_PLY-2);
	
	int aspiration = 16;
	int prevScore = Eval::evaluate(b);
	
	for (int depth = startDepth; depth <= maxDepth; ++depth) {
		int alpha = max(-INF, prevScore - aspiration);
		int beta  = min(+INF, prevScore + aspiration);
		
		int score;
		while (true) {
			Stats.seldepth = 0;
			score = Search(b, depth, alpha, beta, 0, true, pvTable, pvLen);
			
			if (TM.time_up()) break;
			
			if (score <= alpha) {
				alpha = max(-INF, score - aspiration - 8);
				aspiration = min(300, aspiration<<1);
				continue;
			}
			if (score >= beta) {
				beta = min(+INF, score + aspiration + 8);
				aspiration = min(300, aspiration<<1);
				continue;
			}
			break;
		}
		
		if (TM.time_up()) break;
		
		prevScore = score;
		bestScore = score;
		
		vector<uint32_t> pv;
		for (int i=0;i<pvLen[0];i++) pv.push_back(pvTable[0][i]);
		if (pv.empty()) {
			uint32_t line[MAX_PLY];
			int l = get_pv_line(b, line);
			for (int i=0;i<l;i++) pv.push_back(line[i]);
		}
		// 选择 bestmove：优先 pv[0]，否则校验 TT/合法走子
		if (!pv.empty()) {
			// 验证 pv 第一手是否可走
			if (make_move(b, pv[0])) { unmake_move(b); bestMove = pv[0]; }
		}
		if (bestMove == 0) {
			MoveList list; gen_moves(b, list, false);
			for (int i=0;i<list.size;i++){
				if (make_move(b, list.mv[i].m)) { bestMove = list.mv[i].m; unmake_move(b); break; }
			}
		}
		
		if (bestMove) LastBestMoveRoot = bestMove;
		
		print_info_line(depth, score, pv);
		
		if (TM.time_up()) break;
		if (lim.movetime > 0) {
			if (Stats.elapsed_ms() >= (uint64_t)lim.movetime) break;
		} else {
			if (TM.soft_time_up()) break;
		}
	}
	
	if (bestMove == 0) {
		// 回退策略：用上次根最佳，或任一合法
		if (LastBestMoveRoot && make_move(b, LastBestMoveRoot)) {
			unmake_move(b);
			bestMove = LastBestMoveRoot;
		} else {
			MoveList list; gen_moves(b, list, false);
			for (int i=0;i<list.size;i++){
				if (make_move(b, list.mv[i].m)) { bestMove = list.mv[i].m; unmake_move(b); break; }
			}
		}
	}
	return bestMove;
}

// ----------------------------- UCI -----------------------------

static void uci_id() {
	cout << "id name Chtholly-Engine 1.0" << endl;
	cout << "id author LLM" << endl;
	cout << "option name Hash type spin default 128 min 1 max 4096" << endl;
	cout << "option name Randomness type spin default 0 min 0 max 100000" << endl;
	cout << "option name RandomSeed type spin default 0 min 0 max 4294967295" << endl;
	cout << "uciok" << endl;
	cout.flush();
}
static void uci_isready() { cout << "readyok" << endl << flush; }
static void uci_ucinewgame() {
	TT.clear();
	// 若随机幅度>0且未固定种子，每盘重播种（时间种子）
	if (RC.jitter > 0 && RC.seed == 0) RC.seeded = false;
}
static void setoption(const string& name, const string& value) {
	if (name == "Hash") {
		int MB = stoi(value);
		TT.resizeMB(MB);
	} else if (name == "Randomness") {
		int A = stoi(value);
		RC.jitter = max(0, min(100000, A));
	} else if (name == "RandomSeed") {
		uint64_t s = 0;
		try { s = stoull(value); } catch(...) { s = 0; }
		RC.seed = s;
		RJ.seed(RC.seed ? RC.seed : (uint64_t)chrono::steady_clock::now().time_since_epoch().count());
		RC.seeded = true;
	}
}
static void uci_position(Board& b, istringstream& iss) {
	string token;
	if (!(iss >> token)) return;
	if (token == "startpos") {
		b.set_startpos();
		if (iss >> token) {
			if (token == "moves") {
				while (iss >> token) {
					uint32_t m = parse_move_uci(b, token);
					if (m==0 || !make_move(b, m)) {
						MoveList list; gen_moves(b, list, false);
						bool done=false;
						for (int i=0;i<list.size;i++) {
							if (move_to_uci(list.mv[i].m) == token) {
								if (make_move(b, list.mv[i].m)) { done=true; break; }
							}
						}
					}
				}
			}
		}
	} else if (token == "fen") {
		string fen, tmp;
		vector<string> parts;
		for (int i=0;i<6 && (iss >> tmp); ++i) parts.push_back(tmp);
		fen = "";
		for (int i=0;i<(int)parts.size();i++){ if (i) fen += " "; fen += parts[i]; }
		if (parts.size()<4) return;
		b.set_fen(fen);
		if (iss >> token) {
			if (token == "moves") {
				while (iss >> token) {
					uint32_t m = parse_move_uci(b, token);
					if (m==0 || !make_move(b, m)) {
						MoveList list; gen_moves(b, list, false);
						for (int i=0;i<list.size;i++) {
							if (move_to_uci(list.mv[i].m) == token) {
								if (make_move(b, list.mv[i].m)) { break; }
							}
						}
					}
				}
			}
		}
	}
}
static void uci_go(Board& b, istringstream& iss) {
	Limits lim;
	string token;
	while (iss >> token) {
		if (token == "wtime") iss >> lim.wtime;
		else if (token == "btime") iss >> lim.btime;
		else if (token == "winc") iss >> lim.winc;
		else if (token == "binc") iss >> lim.binc;
		else if (token == "movestogo") iss >> lim.movestogo;
		else if (token == "movetime") iss >> lim.movetime;
		else if (token == "depth") iss >> lim.depth;
		else if (token == "nodes") { uint64_t nd; iss >> nd; lim.nodes = nd; }
		else if (token == "ponder") lim.ponder = true;
		else if (token == "infinite") { lim.movetime = -1; }
	}
	uint32_t best = iterative_deepening(b, lim);
	cout << "bestmove " << move_to_uci(best) << endl;
	cout.flush();
}

// ----------------------------- 主程序 -----------------------------

int main() {
	ios::sync_with_stdio(false);
	cin.tie(nullptr);
	
	init_zobrist();
	init_attack_tables();
	init_castle_masks();
	TT.resizeMB(128);
	
	Board board;
	board.set_startpos();
	
	string line;
	while (std::getline(cin, line)) {
		if (line.empty()) continue;
		istringstream iss(line);
		string cmd; iss >> cmd;
		if (cmd == "uci") uci_id();
		else if (cmd == "isready") uci_isready();
		else if (cmd == "ucinewgame") uci_ucinewgame();
		else if (cmd == "position") uci_position(board, iss);
		else if (cmd == "go") uci_go(board, iss);
		else if (cmd == "setoption") {
			string name, tmp, value;
			iss >> tmp; // name
			iss >> tmp; // actual name
			name = tmp;
			while (iss >> tmp && tmp!="value") name += " " + tmp;
			getline(iss, value);
			while (!value.empty() && isspace((unsigned char)value.front())) value.erase(value.begin());
			while (!value.empty() && isspace((unsigned char)value.back())) value.pop_back();
			setoption(name, value);
		}
		else if (cmd == "stop") {
			// 优先使用上一次根节点的最佳着作为回退
			uint32_t best = 0;
			if (LastBestMoveRoot && make_move(board, LastBestMoveRoot)) {
				unmake_move(board);
				best = LastBestMoveRoot;
			} else {
				uint32_t pv[MAX_PLY]; int l = get_pv_line(board, pv);
				if (l>0 && make_move(board, pv[0])) {
					unmake_move(board);
					best = pv[0];
				} else {
					MoveList list; gen_moves(board, list, false);
					for (int i=0;i<list.size;i++){
						if (make_move(board, list.mv[i].m)) { best = list.mv[i].m; unmake_move(board); break; }
					}
				}
			}
			cout << "bestmove " << move_to_uci(best) << endl;
			cout.flush();
		}
		else if (cmd == "quit") break;
	}
	return 0;
}
