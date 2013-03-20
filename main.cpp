#include <cstring>
#include <iostream>
#include <cctype>
#include <stack>
#include <map>
#include <boost/variant.hpp>
#include <boost/pool/pool.hpp>

using namespace std;
using boost::variant;
using boost::pool;

struct M;               // [M]achine
struct E;               // [E]xpression
struct C;               // [C]ommand

typedef string       S; // [S]tring
typedef int          N; // [N]umber
typedef void         V; // [V]oid
typedef bool         B; // [B]ool
typedef pool<>       P; // [P]ool
typedef variant<S,N> R; // [R]esult
typedef map<N,C*>    T; // [T]ape
typedef map<S,R >    A; // [A]ssignments

template <typename T> constexpr
T cmax(T a, T b) { return a > b ? a : b; }

template <typename T> constexpr
T cmax(T a, T b, T c, T d) { return cmax(cmax(a, b), cmax(c, d)); }

struct M { M();
	N iptr = 0; T tape; A asgs;
	P e_pool; P c_pool;
	V load(S); V drop(); V run();
};

struct E { virtual R eval(M& m) const = 0; };
struct C { virtual V exec(M& m) const = 0; };

#define Fld1Con(NM, TY, VAR) TY VAR; NM(TY VAR) : VAR(VAR) {}
#define Fld2Con(NM, TY1, VAR1, TY2, VAR2) \
	TY1 VAR1; TY2 VAR2;                   \
	NM(TY1 VAR1, TY2 VAR2) : VAR1(VAR1), VAR2(VAR2) {}
#define CFld1Con(NM, TY, VAR) Fld1Con(NM, const TY, VAR)
#define CFld2Con(NM, TY1, VAR1, TY2, VAR2) \
	Fld2Con(NM, const TY1, VAR1, const TY2, VAR2)

template <typename X, typename Y, typename F>
struct LiftBinOp : E { CFld2Con(LiftBinOp, E&, a, E&, b);
	R eval(M& m) const {
		R ar = a.eval(m);
		R br = b.eval(m);
		X* x = get<X>(&ar);
		Y* y = get<Y>(&br);
		if (x && y)
			return F::apply(*x, *y);
		else
			throw "Dild`o~!";
	}
};

#define MkN2F(NM, EXP) struct NM { static N apply(N a, N b) { return EXP; } }
#define MkBinOp(NM, EXP, TY1, TY2) MkN2F(NM ## F, EXP);  \
	struct NM : LiftBinOp<TY1, TY2, NM ## F> {			 \
		NM (const E& a, const E& b) : LiftBinOp(a, b) {} \
	}

MkBinOp(Sum, a +  b, N, N);
MkBinOp(Sub, a -  b, N, N);
MkBinOp(Mul, a *  b, N, N);
MkBinOp(Div, a /  b, N, N);
MkBinOp(Grt, a >  b, N, N);
MkBinOp(Lsr, a <  b, N, N);
MkBinOp(Geq, a >= b, N, N);
MkBinOp(Leq, a <= b, N, N);

struct Eql : E { Fld2Con(Eql, E&, a, E&, b);
	R eval(M& m) const {
		return a.eval(m) == b.eval(m);
	}
};

struct Var : E { Fld1Con(Var, S, name);
	R eval(M& m) const {
		return m.asgs[name];
	}
};

struct Num : E { Fld1Con(Num, N, numb);
	R eval(M& m) const { return numb; }
};

struct Str : E { Fld1Con(Str, S, text);
	R eval(M& m) const {
		return text;
	}
};

constexpr size_t max_Esub_sz() { return cmax(
    cmax(sizeof(E), sizeof(Var), sizeof(Num), sizeof(LiftBinOp<N, N, SumF>)),
	cmax(sizeof(Sum), sizeof(Eql))
);}

struct Prn : C { Fld1Con(Prn, E&, expr);
	V exec(M& m) const {
		cout << expr.eval(m) << endl;
	}
};

struct Let : C { Fld2Con(Let, S, name, E&, expr);
	V exec(M& m) const {
		m.asgs[name] = expr.eval(m);
	}
};

struct Inp : C { Fld1Con(Inp, S, name);
	V exec(M& m) const {
		N x; cin >> x;
		m.asgs[name] = x;
	}
};

struct Jmp : C { Fld1Con(Jmp, N, iptr);
	V exec(M& m) const { m.iptr = iptr; }
};

struct Cnd : C { Fld2Con(Cnd, E&, cond, N, iptr);
	V exec(M& m) const {
		R cr = cond.eval(m);
		N* x = get<N>(&cr);
		if (x && !*x) return;
		m.iptr = iptr;
	}
};

constexpr size_t max_Csub_sz() { return cmax(
    cmax(sizeof(C), sizeof(Prn), sizeof(Inp), sizeof(Let)),
	cmax(sizeof(Jmp), sizeof(Cnd))
);}

M::M() : e_pool(max_Esub_sz())
	   , c_pool(max_Csub_sz())
{}

struct O { N prior; N assoc; function<E*(M&,E&,E&)> con; };

#define ConF(NM)								\
	[](M& m, E& a, E& b) -> E* {				\
		E* x = (E*)m.e_pool.malloc();			\
		NM y = NM(a, b);						\
		memcpy(x, &y, sizeof(NM));				\
		return x;								\
	}

static auto op = map<S,O> {
	{">", {1,1,ConF(Grt)}}, {"<", {1,1,ConF(Lsr)}}, {"=",{1,1,ConF(Eql)}},
	{">=",{1,1,ConF(Geq)}}, {"<=",{1,1,ConF(Leq)}},
	{"+", {2,1,ConF(Sum)}}, {"-", {2,1,ConF(Sub)}},
	{"*", {3,1,ConF(Mul)}}, {"/" ,{3,1,ConF(Div)}}
};

template <typename I>
B parse_num(I& it, const I& end, N& out) {
	N neg = 1;
	I itb = it;
	if (it != end && *it == '-') {
		neg = -1;
		++it;
	}
	N n   = 0;
	I itf = it;
	while (itf != end && isdigit(*itf))
		n = n * 10 + *itf++ - '0';
	if (itf == it) {
		it = itb;
		return false;
	}
	it  = itf;
    out = n * neg;
	return true;
}

template <typename I>
N parse_spaces(I& it, const I& end) {
	N n = 0;
	while (it != end && isspace(*it)) {
		++n; ++it;
	}
	return n;
}

template <typename I>
B parse_op(I& it, const I& end, S& op) {
	for (int i = 0; it != end; ++i, ++it)
		switch (*it) {
		case '+': case '-': case '*': case '/':
		case '<': case '=': case '>':
			op += *it; break;
		default:
			return i > 0;
		}
	return false;
}

template <typename I>
B parse_paren(I& it, const I& end, S& p) {
	if (it != end && (*it == '(' || *it == ')')) {
		p += *it++;
		return true;
	}
	return false;
}

template <typename I>
E* parse_expr(I& it, const I& end, M& m) {	
	stack<E*> out;
	stack<S > ops;
	auto apply = [&](S o) {
		if (out.size() < 2) throw "OP/APPLY: Not enought args.";
		E* b = out.top(); out.pop();
		E* a = out.top(); out.pop();		
		out.push(op[o].con(m, *a, *b));
	};
	bool prev_op = true;
	while (it != end) {
		N n; S s;
		if (prev_op && isalpha(*it)) {
			S varnm;
			varnm.reserve(4);
			do varnm += *it++;
			while (it != end && isalpha(*it));
			E*  e = (E*)m.e_pool.malloc();
			Var x = Var("");
			memcpy(e, &x, sizeof(Var));
			((Var*)e)->name = varnm;
			out.push(e);
			prev_op = false;
		} else if (*it == '"') {
			++it;
			S str;
			str.reserve(16);
			while (it != end && *it != '"')
				str += *it++;
			++it;
			E*  e = (E*)m.e_pool.malloc();
			Str x = Str("");
			memcpy(e, &x, sizeof(Str));
			((Str*)e)->text = str;
			out.push(e);
		} else if (prev_op && parse_num(it, end, n)) {
			E*  e = (E*)m.e_pool.malloc();
			Num x = Num(n);
			memcpy(e, &x, sizeof(Num));
			out.push(e);
			prev_op = false;
		} else if (!prev_op && parse_op(it, end, s)) {
			while (!ops.empty()) {
				S o = ops.top();
				if (o == "(") break;
				N p1 = op[s].prior;
				N p2 = op[o].prior;
				N a1 = op[s].assoc;
				if ((a1 == 1 && p1 <= p2) || p1 < p2)
					apply(o);
				else break;
			}
			ops.push(s);
			prev_op = true;
		} else if (parse_paren(it, end, s)) {
			if (s == "(") {
				ops.push(s);
				prev_op = true;
			}
			else {
				do {
					S o = ops.top(); ops.pop();
					apply(o);
				} while (ops.top() != "(");
				ops.pop();
				prev_op = false;
			}			
		} else break;
		parse_spaces(it, end);
	}
	while (!ops.empty()) {
		apply(ops.top());
		ops.pop();
	}
	return out.empty() ? nullptr : out.top();
}

template <typename I>
C* parse_cmd(I& it, const I& end, M& m) {	
	parse_spaces(it, end);
	S cmstr;
	cmstr.reserve(8);
	while (it != end && isalpha(*it))
		cmstr += *it++;
	if (cmstr.empty())
		return nullptr;
	C* c = nullptr;
	if (cmstr != "REM") {
		c = (C*)m.c_pool.malloc();
		parse_spaces(it, end);
		if (cmstr == "PRINT") {
			E* e = parse_expr(it, end, m);
			if (!e) throw "PRINT: expression expected as argument.";
			Prn x = Prn(*e);
			memcpy(c, &x, sizeof(Prn));
		} else if (cmstr == "LET") {			
			S varnm;
			varnm.reserve(4);
			while (isalpha(*it))
				varnm += *it++;
			if (varnm.size() == 0)
				throw "LET: variable name expected as LHS.";
			parse_spaces(it, end);
			if (it == end || *it != '=')
				throw "LET: `=' expected after variable name.";
			++it;
			parse_spaces(it, end);
			E* e = parse_expr(it, end, m);
			if (!e) throw "LET: expression expected as RHS.";
			Let x = Let("", *e);
			memcpy(c, &x, sizeof(Let));
			((Let*)c)->name = varnm;
		} else if (cmstr == "INPUT") {
			S varnm;
			varnm.reserve(4);
			while (it != end && isalpha(*it))
				varnm += *it++;
			if (varnm.size() == 0)
				throw "INPUT: variable name expected.";
			Inp x = Inp("");
			memcpy(c, &x, sizeof(Inp));
			((Inp*)c)->name = varnm;
		} else if (cmstr == "GOTO") {
			int iptr;
			if (!parse_num(it, end, iptr))
				throw "GOTO: instruction pointer expected.";
			Jmp x = Jmp(iptr);
			memcpy(c, &x, sizeof(Jmp));
		} else if (cmstr == "IF") {
			E* e = parse_expr(it, end, m);
			if (!e) throw "IF: expression expected as condition.";
			parse_spaces(it, end);
			S then;
			then.reserve(4);
			while (it != end && isalpha(*it))
				then += *it++;
			if (then != "THEN")
				throw "IF: `THEN' expected after condition.";
			parse_spaces(it, end);
			int iptr;
			if (!parse_num(it, end, iptr))
				throw "IF: instruction pointer expected after `THEN'.";
			Cnd x = Cnd(*e, iptr);
			memcpy(c, &x, sizeof(Cnd));
		} else throw "BAD COMMAND.";
	}	
	return c;
}

V M::load(string code) {
  stringstream ss(code);
  string line;
  for (;;) {
	  int n; ss >> n;
	  if (!getline(ss, line, '\n')) break;
	  auto it = line.begin();
	  C* c = parse_cmd(it, line.end(), *this);
	  tape[n] = c;
  }
}

V M::run() {
 START: // todo: bsearch
	for (auto& kv : tape)
		if (kv.first >= iptr) {
			iptr = kv.first + 1;
			kv.second->exec(*this);
			goto START;
		}
	return;	
}

N main() {
	#define NL "\n"
	S code =
		"10 PRINT \"Type N:\"" NL
		"20 INPUT N"           NL
		"30 LET X = 1"         NL
		"40 IF N < 2 THEN 75"  NL
		"50 LET X = X * N"     NL
		"60 LET N = N+ -1"     NL
		"70 GOTO 40"           NL
		"75 PRINT \"N! = \""   NL
		"80 PRINT X"           NL;
	M m;	
	try {
		m.load(code);
		m.run();
	} catch (const char* err) {
		cout << err << endl;
	}
	return 0;
}

