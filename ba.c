
#define _POSIX_C_SOURCE	200809L	/* opt{arg,ind,opt} */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <assert.h>
#include <stddef.h>
#include <unistd.h>	/* getopt */

static unsigned rate, cap, rounds;
static unsigned coll_ensure_unequal = 0;
static unsigned constant_folding = 1;

struct bits {
	unsigned o, n;
};

typedef unsigned long bb_t;
#define bb_t_bits	(sizeof(bb_t) * 8)
#define bb_t_mask	(~(bb_t)0)

struct operation {
	enum op_t {
		AND,        /* n,r,a,b */
		OR,         /* n,r,a,b */
		XOR,        /* n,r,a,b */
		NOT,        /* n,r,a */
		ROL,        /* n,r,a,b */
		CALL,       /* n,tgt */
		EXPECT,     /* n,a,b */
		EXPECT_ANY, /* n,a */
	//	FIX,        /* n,r,a */
		VAR,        /* n,r */

		SET,        /* n,r,a */
		SET0,       /* n,r */
		LOAD,       /* n,r,a,v */
	} op;
	unsigned n, r, a, b;
	const struct operation *tgt;
	const bb_t *v;
};

static const char *op_names[] = {
	"and", "or", "xor", "not", "rol", "call", "expect", "expect_any",
	"var", "set", "set0", "load"
};

static struct op_flags {
	unsigned mem_r : 1;
	unsigned mem_a : 1;
	unsigned mem_b : 1;
} const op_flags[] = {
	[AND]        = { 1, 1, 1 },
	[OR]         = { 1, 1, 1 },
	[XOR]        = { 1, 1, 1 },
	[NOT]        = { 1, 1, 0 },
	[ROL]        = { 1, 1, 0 }, /* b valid but rot amount, no mem ptr */
	[CALL]       = { 0, 0, 0 },
	[EXPECT]     = { 0, 1, 1 },
	[EXPECT_ANY] = { 0, 1, 0 },
	[VAR]        = { 1, 0, 0 },
	[SET]        = { 1, 1, 0 },
	[SET0]       = { 1, 0, 0 },
	[LOAD]       = { 1, 0, 0 }, /* a valid but offset, no mem ptr */
};

#define OP_AND(out,b0,b1) (struct operation){ AND, (out).n, (out).o, (b0).o, (b1).o }
#define OP_OR(out,b0,b1)  (struct operation){ OR , (out).n, (out).o, (b0).o, (b1).o }
#define OP_XOR(out,b0,b1) (struct operation){ XOR, (out).n, (out).o, (b0).o, (b1).o }
#define OP_NOT(out,b0)    (struct operation){ NOT, (out).n, (out).o, (b0).o }
#define OP_ROL(out,b0,m)  (struct operation){ ROL, (out).n, (out).o, (b0).o, (m) }
#define OP_CALL(n,target) (struct operation){ CALL, (n), .tgt = (target) }
#define OP_CALL_ARR(arr)  OP_CALL(ARRAY_SIZE(arr),arr)
#define OP_EXPECT(b,c)    (struct operation){ EXPECT, (b).n, 0, (b).o, (c).o }
#define OP_EXPECT_ANY(a)  (struct operation){ EXPECT_ANY, (a).n, 0, (a).o }
#define OP_VAR(b)         (struct operation){ VAR, (b).n, (b).o }
#define OP_SET(out,src)   (struct operation){ SET, (out).n, (out).o, (src).o }
#define OP_SET0(out)      (struct operation){ SET0, (out).n, (out).o }
#define OP_LOAD(out,off,bb) (struct operation){ LOAD, (out).n, (out).o, (off), .v = (bb) }


#if 0
static void bb_clear(bb_t *mem, unsigned o, unsigned n)
{
	unsigned k = o / bb_t_bits;
	unsigned m = (o + n + bb_t_bits-1) / bb_t_bits;
	for (; k < m; k++) {
		bb_t m = bb_t_mask;
		if (k * bb_t_bits < o)
			m &= bb_t_mask << (o - k * bb_t_bits);
		if (k * bb_t_bits > o+n)
			m &= bb_t_mask >> (k * bb_t_bits - (o+n));
		mem[k] &= ~m;
	}
}

static void bb_op(bb_t *mem, unsigned to, const bb_t *src, unsigned so, unsigned n, enum op_t op)
{
	unsigned si, ti;
	unsigned s0 = so / bb_t_bits;
	unsigned t0 = to / bb_t_bits;
	unsigned s1 = (so + n + bb_t_bits - 1) / bb_t_bits;
	unsigned t1 = (to + n + bb_t_bits - 1) / bb_t_bits;
	int shl = to - so;
	bb_t s, v0, v1;

	for (si = s0, ti = t0; si < s1; si++) {
		s = op == NOT ? bb_t_mask : src[si];
		if (op == AND)
			s = ~s;
		if (si == s0)
			s &= bb_t_mask << (              so    & (bb_t_bits - 1));
		if (si + 1 == s1)
			s &= bb_t_mask >> (bb_t_bits - ((so+n) & (bb_t_bits - 1)));
		v0 = shl < 0 ? s >> -shl : s << shl;
		v1 = shl < 0 ? s << (bb_t_bits + shl) : s >> (bb_t_bits - shl);
		switch (op) {
		case AND:
			mem[ti] &= ~v0;
			if (++ti == t1)
				break;
			mem[ti] &= ~v1;
		case OR:
			mem[ti] |= v0;
			if (++ti == t1)
				break;
			mem[ti] |= v1;
			break;
		case NOT:
		case XOR:
			mem[ti] ^= v0;
			if (++ti == t1)
				break;
			mem[ti] ^= v1;
			break;
		}
	}
}
#endif

static bb_t bb_get(const bb_t *mem, unsigned o, unsigned n)
{
	unsigned shl = o & (bb_t_bits - 1);
	unsigned shr = bb_t_bits - shl;
	unsigned so = o / bb_t_bits;
	bb_t r0 = mem[so];
	bb_t r1 = n + shl > bb_t_bits ? mem[so+1] : 0;
	return (r0 >> shl | r1 << shr) & (bb_t_mask >> (bb_t_bits - n));
}

static void bb_put(bb_t *mem, bb_t v, unsigned o, unsigned n)
{
	unsigned shl = o & (bb_t_bits - 1);
	unsigned shr = bb_t_bits - shl;
	unsigned so = o / bb_t_bits;
	if (n < bb_t_bits)
		v &= bb_t_mask >> (bb_t_bits - n);
	mem[so]   = (mem[so  ] & (bb_t_mask >> shr)) | v << shl;
	if (n + shl > bb_t_bits)
		mem[so+1] = (mem[so+1] & (bb_t_mask << shl)) | v >> shr;
}

#if 0
static void bb_cpy(bb_t *mem, unsigned to, const bb_t *src, unsigned so, unsigned n)
{
	while (n) {
		unsigned n0 = n > bb_t_bits ? bb_t_bits : n;
		bb_put(mem, bb_get(src, so, n0), to, n0);
		so += n0;
		to += n0;
		n -= n0;
	}
}

static void bits_set(bb_t *mem, bb_t v, const struct bits *b)
{
	unsigned i;
	for (i=0; i<b->n; i+=bb_t_bits)
		bb_put(mem, v, b->o + i,
			b->n - i < bb_t_bits ? b->n - i : bb_t_bits);
}

static int exec(bb_t *mem, const struct operation *op)
{
	bb_t tmp[(op->n + 2*bb_t_bits - 1) / bb_t_bits];
	unsigned i;
	unsigned in = (op->n + bb_t_bits - 1) / bb_t_bits;
	unsigned r = op->r, a = op->a, b = op->b, n = op->n;
	int ret = 0;

	memset(tmp, 0, sizeof(tmp));

	switch (op->op) {
	case AND:
		for (i=0; i<in; i++, a += bb_t_bits, b += bb_t_bits, n -= bb_t_bits)
			tmp[i] = bb_get(mem, a, n) & bb_get(mem, b, n);
		break;
	case OR:
		for (i=0; i<in; i++, a += bb_t_bits, b += bb_t_bits, n -= bb_t_bits)
			tmp[i] = bb_get(mem, a, n) | bb_get(mem, b, n);
		break;
	case XOR:
		for (i=0; i<in; i++, a += bb_t_bits, b += bb_t_bits, n -= bb_t_bits)
			tmp[i] = bb_get(mem, a, n) ^ bb_get(mem, b, n);
		break;
	case NOT:
		for (i=0; i<in; i++, a += bb_t_bits, b += bb_t_bits, n -= bb_t_bits)
			tmp[i] = ~bb_get(mem, a, n);
		break;
	case ROL:
		b %= n;
		bb_cpy(tmp, 0, mem, a + n - b, b);
		bb_cpy(tmp, b, mem, a        , n - b);
		break;
	case CALL:
		for (i=0; i<n; i++)
			if ((ret = exec(mem, op->tgt + i)) != 0)
				break;
		goto done;
	case EXPECT:
		for (i=0; i<in; i++, a += bb_t_bits, b += bb_t_bits, n -= bb_t_bits)
			if (bb_get(mem, a, n) != bb_get(mem, b, n)) {
				ret = i << 1 | 1;
				break;
			}
		printf("expect fail: %d\n", ret & 1);
		ret = 0;
		goto done;
	}

#if 1
	n = op->n;
	for (i=0; i<in; i++, r += bb_t_bits, n -= bb_t_bits)
		bb_put(mem, tmp[i], r, n);
#else
	bb_clear(mem, op->r, op->n);
	bb_op(mem, r, tmp, 0, op->n, OR);
#endif
done:
	return ret;
}
#endif

#define PRI_BUFSZ	256

static const char * opstr(const struct operation *op)
{
	static char buf[PRI_BUFSZ];

	snprintf(buf, sizeof(buf), "%s[n:%u,r:%u,a:%u,b:%u]",
		op_names[op->op], op->n, op->r, op->a, op->b);

	return buf;
}

#include "common.h"

enum lop_t {
	L_AND, /* binary */
	L_OR, /* n-ary */
	L_XOR, /* binary */
	L_NOT, /* unary */
	L_EQ, /* n-ary (if none fixed, otherwise collapsed) */
	L_VAR, /* leaf */
};

struct bitxform {
	enum op_t op; /* subset: AND, OR, XOR, NOT, SET, VAR */
	unsigned a, b; /* for op=VAR, variable=1: a = memory bit address (op->r+i) */ 
	unsigned resolved : 1;
	unsigned variable : 1;
	unsigned referees_n;
	unsigned referees_sz;
	unsigned *referees;
	signed folded_value;
};

static void bit_referee_add(struct bitxform *bx, unsigned referee)
{
#if 1
	// darray_ensure(&bx->referees, &bx->referees_sz, sizeof(*bx->referees), bx->referees_n + 1);
	darr_ensure(bx->referees, bx->referees_sz, bx->referees_n + 1);
#else
	if (bx->referees_n + 1 >= bx->referees_sz) {
		unsigned nsz = 2 * (bx->referees_n + 1);
		bx->referees = realloc(bx->referees, sizeof(signed) * nsz);
		if (!bx->referees) {
			perror("realloc");
			exit(EXIT_FAILURE);
		}
		memset(bx->referees + bx->referees_sz, 0,
			sizeof(signed) * (nsz - bx->referees_sz));
		bx->referees_sz = nsz;
	}
#endif
	bx->referees[bx->referees_n++] = referee;
}

#define OPX_NIL		0
#define OPX_FALSE	1
#define OPX_TRUE	2
#define OPX_RESERVED	3
/* kind of SSA */
struct opxform {
	struct bitxform *xf; /* idx 0,1,2 are reserved for nil,false,true */
	unsigned xf_n;
	unsigned xf_sz;
	unsigned mem2xf[]; /* size: total_bits */
};

struct opxform * opx_init(unsigned total_bits)
{
	struct opxform *r = calloc(offsetof(struct opxform, mem2xf)
		+ sizeof(unsigned) * total_bits,
		1);
	r->xf_n = OPX_RESERVED;
	return r;
}

static unsigned opx_alloc(struct opxform *x, unsigned n)
{
	unsigned r = x->xf_n;
#if 1
	darr_ensure(x->xf, x->xf_sz, r + n);
#else
	if (x->xf_sz < x->xf_n + n) {
		unsigned nsz = 2 * (x->xf_n + n);
		if (!(x->xf = realloc(x->xf, nsz * sizeof(struct bitxform)))) {
			perror("realloc");
			exit(EXIT_FAILURE);
		}
		memset(x->xf + x->xf_sz, 0,
			(nsz - x->xf_sz) * sizeof(struct bitxform));
		x->xf_sz = nsz;
	}
#endif
	x->xf_n += n;
	return r;
}

static struct {
	unsigned and;
	unsigned or;
	unsigned xor;
	unsigned anti;
	unsigned equi;
	unsigned free;
} stat = { 0, 0, 0, 0, 0, 0 };

/* TODO: equivalence class transformations (0,1: bitxform.constant = 1, OPX_*)
 * (NOT NOT) = id                     [done]
 * (SET a) = a                        [done]
 * (NOT a) = -a                       [done]
 * (XOR a a) = 0                      [done]
 * (XOR a -a) = 1                     [done]
 * (XOR 0 a) = a                      [done]
 * (XOR 1 a) = -a                     [done]
 * // (NOT XOR a b) = (EXPECT a b)
 * (AND a  a) = a                     [done]
 * (AND a -a) = 0                     [done]
 * (AND 0  a) = 0                     [done]
 * (AND 1  a) = a                     [done]
 * (OR a  a) = a                      [done]
 * (OR a -a) = 1                      [done]
 * (OR 0  a) = a                      [done]
 * (OR 1  a) = 1                      [done]
 *
 * (OR AND a NOT b AND NOT a b) = (XOR a b)
 * (AND OR NOT a b OR a NOT b) = (NOT XOR a b)
 * // (OR NOT a NOT b) = (NOT AND a b)
 * // (AND NOT a NOT b) = (NOT OR a b)
 * (EXPECT_ANY OR a b) = (EXPECT_ANY (ab))
 * (EXPECT SET a b c) = (AND OR -a c OR b -c OR a -b)
 * 
 * (SET SET a b c) = (AND OR -a c OR b -c OR a -b)
 * 
 * 1. SSA form
 * 2. do
 *    - run above reductions / constant/variable propagations
 *    - common subexpression elimination
 *    while (changes)
 * 3. transform EXPECT*'s
 */

static signed bit_fold(const struct opxform *x, unsigned a);

static signed _bit_fold(const struct opxform *x, unsigned a)
{
	const struct bitxform *ax = x->xf + a;
	signed s, t;
	unsigned as, at;

	if (a < OPX_RESERVED)
		return a;

	switch (ax->op) {
	case AND:
	case OR:
	case XOR:
		break;
	case NOT:
#if 0
		return -bit_fold(x, ax->a);
#else
		s = bit_fold(x, ax->a);
		as = s < 0 ? -s : s;
		switch (as) {
		case OPX_FALSE:
		case OPX_TRUE:
			return -s;
		}
		return a;
#endif
	case SET:
		return bit_fold(x, ax->a);
	case VAR:
		return a;
	default:
		goto fail;
	}

	s = bit_fold(x, ax->a);
	t = bit_fold(x, ax->b);

	if (s == t) {
		switch (ax->op) {
		case AND: /* a AND a */
		case OR:  /* a OR  a */
			return s;
		case XOR: /* a XOR a */
			return OPX_FALSE;
		default:
			goto fail;
		}
	} else if (s == -t) {
		switch (ax->op) {
		case AND: /* a AND -a */
			return OPX_FALSE;
		case OR:  /* a OR  -a */
		case XOR: /* a XOR -a */
			return OPX_TRUE;
		default:
			goto fail;
		}
	}

	as = s < 0 ? -s : s;
	at = t < 0 ? -t : t;

	if (at < OPX_RESERVED) {
		/* AND, OR, XOR are commutative */
		signed tmp = t;
		unsigned atmp = at;
		t = s;
		at = as;
		s = tmp;
		as = atmp;
	}

	switch (as) {
	case OPX_NIL:
		fprintf(stderr, "invalid bit-folded value: OPX_NIL for bit a = %u\n", a);
		abort();
	/* further folding possible for (at least) one constant */
	/* -OPX_FALSE = OPX_TRUE, -OPX_TRUE = OPX_FALSE */
	case OPX_FALSE:
		if (s < 0)
			as = OPX_TRUE;
		break;
	case OPX_TRUE:
		if (s < 0)
			as = OPX_FALSE;
		break;
	default:
		/* both unequal and non-const, can't fold here */
		return a;
	}

	switch (ax->op) {
	case AND:
		return as == OPX_FALSE ? OPX_FALSE : t;
	case OR:
		return as == OPX_FALSE ? t : OPX_TRUE;
	case XOR:
		return as == OPX_FALSE ? t : -t;
	default:
		goto fail;
	}
fail:
	abort();
}

static signed bit_fold(const struct opxform *x, unsigned a)
{
	struct bitxform *ax = x->xf + a;

	if (!constant_folding)
		return a;

	if (!ax->folded_value)
		ax->folded_value = _bit_fold(x, a);
	return ax->folded_value;
}

static struct op_stat {
	unsigned a[12], b[12];
} par_stat[12];

// /* returns a dimacs_cnf literal corresponding to x->xf[a] */
static int bit_resolve(const struct opxform *x, unsigned a, const struct out *o)
{
	struct bitxform *ax = x->xf + a;
	enum op_t op = ax->op;
	signed ta, tb;
	unsigned ata, atb;
	int r = 0;

	/* if ax is 'already resolved', return */
	if (ax->resolved)
		return r;

	if (a == OPX_FALSE) {
		// dimacs_cnf_addn(cnf, -a);
		o->constr_out(o->p, 1, (signed[]){ -a });
		goto done;
	}
	if (a == OPX_TRUE) {
		// dimacs_cnf_addn(cnf,  a);
		o->constr_out(o->p, 1, (signed[]){  a });
		goto done;
	}

	assert(a >= OPX_RESERVED);

	ta = ax->a;
	tb = ax->b;
#if 1
	/* TODO: bit_fold shall only proceed further down while refcnt == 1 */
	if (op_flags[op].mem_a)
		ta = bit_fold(x, ta);
	if (op_flags[op].mem_b)
		tb = bit_fold(x, tb);
#endif
	ata = ta < 0 ? -ta : ta;
	atb = tb < 0 ? -tb : tb;

	switch (op) {
	case AND:
	case OR:
	case XOR:
		bit_resolve(x, atb, o);
		par_stat[op].b[x->xf[atb].op]++;
	case NOT:
	case SET:
		bit_resolve(x, ata, o);
		par_stat[op].a[x->xf[ata].op]++;
	case VAR:
		break;
	default:
		fprintf(stderr, "invalid bit_resolve: %s\n", op_names[op]);
		exit(EXIT_FAILURE);
	}

	switch (op) {
	case AND:
		stat.and++;
		break;
	case OR:
		stat.or++;
		break;
	case XOR:
		stat.xor++;
		break;
	case NOT:
		stat.anti++;
		break;
	case SET:
		stat.equi++;
		break;
	case VAR:
		stat.free++;
		break;
	default:;
	}

	r = o->bit_out(o->p, op, a, ta, tb);

done:
	/* mark ax as 'already resolved' */
	ax->resolved = 1;

	return r;
}

#if 0
/* SET, EXPECT -> EQ */
/* EXPECT_ANY  -> EQ OR TRUE */

struct lnode {
	enum lop_t op;
	/* indices into lgraph's nodes array */
	/* successors */
	union {
		struct { unsigned a, b; };         /* L_AND, L_XOR, L_NOT */
		struct { unsigned n, sz, *ops; };  /* L_OR, L_EQ */
	};
	unsigned *referees; /* ordered predecessor list (not a set) */
	unsigned referees_n, referees_sz;
	unsigned var_id;
};

struct lnode root = { L_AND, { { 3, 4 } }, NULL, 0, 0, 0 };

/* top -> down */
static void simplify_fact(struct lnode *n, signed v) /* v: +/- OPX_TRUE */
{
	switch (n->op) {
	case L_AND:
	case L_OR:
	case L_XOR:
	case L_NOT:
	case L_EQ:
	case L_VAR:
		forall p : referees
			simplify_fact(reference[p,this], v);
		this->value = v;
		break;
	}
}

static void merge(struct lnode *tgt, struct lnode *src)
{
	forall p : src->referees {
		delete reference[p,src]
		add    reference[p,tgt]
	}
	forall c : src->operands {
		delete reference[src,c]
		add    reference[tgt,c]
	}
}

static void simplify_merge(struct lnode *n)
{
	switch (n->op) {
	case L_AND:
	case L_OR:
	case L_XOR:
	case L_EQ:
		/* associativity */
		forall c : operands
			if (c->op == n->op && c->refcnt == 1)
				merge(n, c)
		break;
	case L_NOT:
	case L_VAR:
	}
}

struct exec_plan {
	unsigned (*exp)[2];
	unsigned exp_n, exp_sz;
	struct exp_any {
		unsigned n;
		unsigned *v;
	} *exp_any;
	unsigned exp_any_n, exp_any_sz;
};
#endif

static int opx_exec(struct opxform *x, const struct operation *op, const struct out *o)
{
	unsigned i, k, n, b;
	int r = 0;
	struct clause *c;
	struct op_flags of = op_flags[op->op];

	n = op->n;

	/* check validity of memory references */
	for (i=0; i<n; i++) {
		unsigned a = of.mem_a ? x->mem2xf[op->a + i] : 0;
		unsigned b = of.mem_b ? x->mem2xf[op->b + i] : 0;
		if ((of.mem_a ? !a : 0) || (of.mem_b ? !b : 0)) {
			fprintf(stderr, "op %p: %s: %c @ %u undef\n",
				(void *)op, opstr(op),
				of.mem_a && !a ? 'a' : 'b',
				i);
			return 1;
		}
	}

	if (of.mem_r) {
		/* allocate new variables for the output ... */
		k = opx_alloc(x, n);
	}

	/* ... and assign the results (where applicable) */
	switch (op->op) {
	case AND:
	case OR:
	case XOR:
	case NOT:
	case SET:
		for (i=0; i<n; i++) {
			x->xf[k+i].op = op->op;
			if (of.mem_a)
				x->xf[k+i].a = x->mem2xf[op->a + i];
			if (of.mem_b)
				x->xf[k+i].b = x->mem2xf[op->b + i];
		}
		break;
	case ROL:
		b = op->b % n;
		for (i=0; i<n; i++) {
			x->xf[k+i].op = SET;
			x->xf[k+i].a  = x->mem2xf[op->a + (n - b + i) % n];
		}
		break;
	case LOAD:
		for (i=0; i<n; i++) {
			x->xf[k+i].op = SET;
			x->xf[k+i].a  = bb_get(op->v, op->a + i, 1) ? OPX_TRUE : OPX_FALSE;
		}
		break;
	case SET0:
		for (i=0; i<n; i++) {
			x->xf[k+i].op = SET;
			x->xf[k+i].a  = OPX_FALSE;
		}
		break;
	case VAR:
		for (i=0; i<n; i++) {
			x->xf[k+i].op = VAR;
			x->xf[k+i].variable = 1;
			x->xf[k+i].a = op->r + i;
		}
		break;
	case CALL:
		for (i=0; i<n; i++)
			if ((r = opx_exec(x, op->tgt + i, o)) != 0) {
				fprintf(stderr, "call stack %u: op %p: %s\n",
					i, (void *)op, opstr(op));
				break;
			}
		break;
	case EXPECT:
		fprintf(stderr, "expect, current ssa vars: %u, op: %s\n",
			x->xf_n, opstr(op));
#if 0
		struct exec_plan *ep;
		darr_ensure(ep->exp, ep->exp_sz, ep->exp_n + n);
		for (i=0; i<n; i++) {
			unsigned v = x->mem2xf[op->a + i];
			unsigned e = x->mem2xf[op->b + i];
			bit_traverse(x, v);
			bit_traverse(x, e);
			ep->exp[ep->exp_n + i][0] = v;
			ep->exp[ep->exp_n + i][1] = e;
		}
#else
		for (i=0; i<n; i++) {
			unsigned v = x->mem2xf[op->a + i];
			unsigned e = x->mem2xf[op->b + i];
			if ((r = bit_resolve(x, v, o)) != 0) {
				fprintf(stderr, "ERROR: offending operation: %s\n", opstr(op));
				break;
			}
			if ((r = bit_resolve(x, e, o)) != 0) {
				fprintf(stderr, "ERROR: offending operation: %s\n", opstr(op));
				break;
			}
			// dimacs_cnf_eq(cnf, v, e);
			o->constr_out(o->p, 2, (signed[]){  v, -e });
			o->constr_out(o->p, 2, (signed[]){ -v,  e });
		}
#endif
		break;
	case EXPECT_ANY:
		fprintf(stderr, "expect_any, current ssa vars: %u, op: %s\n",
			x->xf_n, opstr(op));
		/* TODO! */
		c = malloc(offsetof(struct clause,l) + sizeof(signed)*n);
		c->n = n;
		for (i=0; i<n; i++) {
			unsigned v = x->mem2xf[op->a + i];
			bit_resolve(x, v, o);
			c->l[i] = v;
		}
		// dimacs_cnf_add(o->p, c);
		o->constr_out(o->p, n, c->l);
		free(c);
		break;
	}

	if (of.mem_r) {
#if 0
		for (i=0; i<n; i++) {
			if (op_flags[x->xf[k+i].op].mem_a)
				bit_referee_add(&x->xf[x->xf[k+i].a], k+i);
			if (op_flags[x->xf[k+i].op].mem_b)
				bit_referee_add(&x->xf[x->xf[k+i].b], k+i);
		}
#endif
		/* finally assign the output slots, s.t. an operation using
		 * these op->r later references the correct values */
		for (i=0; i<n; i++)
			x->mem2xf[op->r + i] = k + i;
	}

	return r;
}

static void print_bits(const char *name, const struct bits *b)
{
	fprintf(stderr, "%s[n:%u,o:%u] -- [%u,%u)\n", name,
		b->n, b->o, b->o, b->o + b->n);
}

struct instance {
	unsigned total_bits;
	struct opxform *x;
};

static int dot_bit_out(void *p, enum op_t op, unsigned a, signed ta, signed tb)
{
	switch (op) {
	case AND:
	case OR:
	case XOR:
		fprintf(p, "\t%u -> %d\n", a, tb);
	case NOT:
	case SET:
		fprintf(p, "\t%u -> %d\n", a, ta);
		fprintf(p, "\t%u [label=\"%u %s\"]\n", a, a, op_names[op]);
		break;
	case VAR:
		fprintf(p, "\t%u [style=filled,color=green]\n", a);
		break;
	default:
		return 1;
	}
	return 0;
}

static int dot_constr_out(void *p, unsigned n, const signed *l)
{
	static int or_n = 0;
	if (n == 2) {
		fprintf(p, "\t%d [style=filled,color=red]\n", l[0]);
		fprintf(p, "\t%d [style=filled,color=red]\n", l[1]);
		fprintf(p, "\t%d -> %d [dir=both,label=\"=\",color=purple]\n", l[0], l[1]);
	} else {
		fprintf(p, "\tor%u [label=\"or\",color=purple,shape=box]\n", ++or_n);
		while (n--) {
			signed v = *l++;
			fprintf(p, "%d [style=filled,color=red]\n", v);
			fprintf(p, "\tor%u -> %d [color=purple]\n", or_n, v);
		}
	}
	return 0;
}

#define INSTANCE_INIT	(struct instance){ 0, NULL }

static int instance_run(
	struct instance *in, const struct operation *op, const struct out *o
) {
	in->x      = opx_init(in->total_bits);

	int r = opx_exec(in->x, op, o); /* TODO: param: _const_ struct out *o */
	return r;
}

struct bits bits(struct instance *in, unsigned n)
{
	struct bits r = { in->total_bits, n };
	in->total_bits += n;
	return r;
}

struct keccak {
	unsigned w, r, c, rounds;
	struct bits RC;
	struct bits S, B, C, D, t, b;
	struct operation *absorb, *f, *round/*, *squeeze*/;
};

static void keccak_init(
	struct keccak *kc,
	struct instance *in,
	unsigned r, unsigned c, unsigned rounds
) {
	unsigned w = (r + c) / 25;

	assert((r + c) % 25 == 0);
	assert(w <= bb_t_bits);
	assert(rounds <= 24);

	kc->w = w;
	kc->r = r;
	kc->c = c;
	kc->rounds = rounds;

	kc->RC = bits(in, w);
	kc->S  = bits(in, w * 5 * 5);
	kc->B  = bits(in, w * 5 * 5);
	kc->C  = bits(in, w * 5);
	kc->D  = bits(in, w * 5);
	kc->t  = bits(in, w);

	print_bits("S", &kc->S);
	print_bits("B", &kc->B);
	print_bits("C", &kc->C);
	print_bits("D", &kc->D);
	print_bits("t", &kc->t);
}

static struct operation * keccak_f(
	const struct keccak *kc,
	const struct operation *call_round
) {
	static const bb_t keccak_RC[24] = {
		[ 0] = 0x0000000000000001,
		[ 1] = 0x0000000000008082,
		[ 2] = 0x800000000000808A,
		[ 3] = 0x8000000080008000,
		[ 4] = 0x000000000000808B,
		[ 5] = 0x0000000080000001,
		[ 6] = 0x8000000080008081,
		[ 7] = 0x8000000000008009,
		[ 8] = 0x000000000000008A,
		[ 9] = 0x0000000000000088,
		[10] = 0x0000000080008009,
		[11] = 0x000000008000000A,
		[12] = 0x000000008000808B,
		[13] = 0x800000000000008B,
		[14] = 0x8000000000008089,
		[15] = 0x8000000000008003,
		[16] = 0x8000000000008002,
		[17] = 0x8000000000000080,
		[18] = 0x000000000000800A,
		[19] = 0x800000008000000A,
		[20] = 0x8000000080008081,
		[21] = 0x8000000000008080,
		[22] = 0x0000000080000001,
		[23] = 0x8000000080008008,
	};

	struct operation *f = malloc(sizeof(struct operation) * (1 + 2 * kc->rounds));
	unsigned i;

	f[0] = OP_CALL(2 * kc->rounds, f + 1);
	for (i=0; i<kc->rounds; i++) {
		f[2*i+1] = OP_LOAD(kc->RC, i * bb_t_bits, keccak_RC);
		f[2*i+2] = *call_round;
	}

	return f;
}

struct operation * keccak_round(const struct keccak *kc, struct instance *in)
{
	static const unsigned rotation_offsets[5][5] = {
		{  0,  1, 62, 28, 27 },
		{ 36, 44,  6, 55, 20 },
		{  3, 10, 43, 25, 39 },
		{ 41, 45, 15, 21,  8 },
		{ 18,  2, 61, 56, 14 }
	};

#define A(x,y)	(A.o + ((x) + (y)*5)*z)
#define B(x,y)	(B.o + ((x) + (y)*5)*z)
#define C(x)	(C.o + (x)*z)
#define D(x)	(D.o + (x)*z)

	unsigned z = kc->w;

	struct bits A = kc->S;
	struct bits B = kc->B;
	struct bits C = kc->C;
	struct bits D = kc->D;
	struct bits t = kc->t;

	const struct operation keccak_round[] = {
		/* θ step */
#define t0(x)	{ XOR, z, t.o, A(x,0), A(x,1) }, \
		{ XOR, z, t.o, t.o, A(x,2) }, \
		{ XOR, z, t.o, t.o, A(x,3) }, \
		{ XOR, z, C(x), t.o, A(x,4) }
		t0(0),
		t0(1),
		t0(2),
		t0(3),
		t0(4),

#define t1(x)	{ ROL, z, t.o, C(((x)+1)%5), 1 }, \
		{ XOR, z, D(x), C(((x)+5-1)%5), t.o }
		t1(0),
		t1(1),
		t1(2),
		t1(3),
		t1(4),

#define t2(x,y) { XOR, z, A(x,y), A(x,y), D(x) }
		t2(0,0), t2(1,0), t2(2,0), t2(3,0), t2(4,0),
		t2(0,1), t2(1,1), t2(2,1), t2(3,1), t2(4,1),
		t2(0,2), t2(1,2), t2(2,2), t2(3,2), t2(4,2),
		t2(0,3), t2(1,3), t2(2,3), t2(3,3), t2(4,3),
		t2(0,4), t2(1,4), t2(2,4), t2(3,4), t2(4,4),

		/* ρ and π steps */
#define rp(x,y) { ROL, z, B(y,(2*x+3*y)%5), A(x,y), rotation_offsets[y][x] }
		rp(0,0), rp(1,0), rp(2,0), rp(3,0), rp(4,0),
		rp(0,1), rp(1,1), rp(2,1), rp(3,1), rp(4,1),
		rp(0,2), rp(1,2), rp(2,2), rp(3,2), rp(4,2),
		rp(0,3), rp(1,3), rp(2,3), rp(3,3), rp(4,3),
		rp(0,4), rp(1,4), rp(2,4), rp(3,4), rp(4,4),

		/* χ step */
#define xi(x,y) { NOT, z, t.o, B(((x)+1)%5,y) }, \
		{ AND, z, t.o, t.o, B(((x)+2)%5,y) }, \
		{ XOR, z, A(x,y), B(x,y), t.o }
		xi(0,0), xi(1,0), xi(2,0), xi(3,0), xi(4,0),
		xi(0,1), xi(1,1), xi(2,1), xi(3,1), xi(4,1),
		xi(0,2), xi(1,2), xi(2,2), xi(3,2), xi(4,2),
		xi(0,3), xi(1,3), xi(2,3), xi(3,3), xi(4,3),
		xi(0,4), xi(1,4), xi(2,4), xi(3,4), xi(4,4),

		/* ι step */
		{ XOR, z, A(0,0), A(0,0), kc->RC.o },
	};

	struct operation *f = malloc(sizeof(struct operation) + sizeof(keccak_round));
	f[0] = OP_CALL(ARRAY_SIZE(keccak_round), f + 1);
	memcpy(f + 1, keccak_round, sizeof(keccak_round));
	return f;
}

/* absorbing phase */
static struct operation * keccak_input(
	const struct keccak *kc,
	struct instance *in,
	struct bits M,
	const struct operation *call_keccak_f
) {
	unsigned loops = (M.n + 2 + kc->r - 1) / kc->r;
	struct bits P = bits(in, kc->r * loops);
	unsigned i, k;

	/* P = I10*1 : w divides |P| */
	struct operation p_prep[] = {
		OP_SET0(P),
		{ SET, M.n, P.o          , M.o },
		{ NOT,   1, P.o + M.n    , P.o + M.n     },
		{ NOT,   1, P.o + P.n - 1, P.o + P.n - 1 },
	};

	struct operation *f = malloc(
		sizeof(struct operation) * (1 + 2 * loops) + sizeof(p_prep));

	f[0] = OP_CALL(ARRAY_SIZE(p_prep) + 2 * loops, f + 1);
	memcpy(f + 1, p_prep, sizeof(p_prep));

	k = 1 + ARRAY_SIZE(p_prep);
	for (i=0; i<loops; i++) {
		f[k++] = (struct operation){ XOR, kc->r, kc->S.o, kc->S.o, P.o + i*kc->r };
		f[k++] = *call_keccak_f;
	}

	return f;
}

static struct operation * keccak_output(
	const struct keccak *kc,
	const struct instance *in,
	struct bits O,
	const struct operation *call_keccak_f
) {
	unsigned loops = (O.n + kc->r - 1) / kc->r;
	unsigned i, k, n = O.n;

	assert(loops >= 1);

	struct operation *f = malloc(
		sizeof(struct operation) * (1 + (loops - 1) * 2 + 1));

	f[0] = OP_CALL((loops - 1) * 2 + 1, f + 1);
	for (i=0; i<loops-1; i++, n-=kc->r) {
		f[1+2*i  ] = (struct operation){ SET, kc->r, O.o + kc->r * i, kc->S.o };
		f[1+2*i+1] = *call_keccak_f;
	}
	f[1+2*i] = (struct operation){ SET, n, O.o + kc->r * i, kc->S.o };

	return f;
}

static void keccak_init_full(
	struct keccak *kc,
	struct instance *in,
	unsigned r, unsigned c, unsigned rounds,
	struct bits M/*, struct bits O*/
) {
	keccak_init(kc, in, r, c, rounds);
	kc->round   = keccak_round(kc, in);
	kc->f       = keccak_f(kc, kc->round);
	kc->absorb  = keccak_input(kc, in, M, kc->f);
	// kc->squeeze = keccak_output(kc, in, O, kc->f);
}

union bc {
	unsigned char c[10];
	bb_t b[2];
};

static const union bc out_r40[] = {
	[ 1] = { { 0xe9, 0xf5, 0x7f, 0x02, 0xa9, 0xb0, 0xeb, 0xd8, 0x44, 0x98 } },
	[ 2] = { { 0x02, 0x4a, 0x55, 0x18, 0xe1, 0xe9, 0x5d, 0xb5, 0x32, 0x19 } },
	[ 3] = { { 0xd8, 0xed, 0x85, 0x69, 0x2a, 0xfb, 0xee, 0x4c, 0x99, 0xce } },
	[ 4] = { { 0x74, 0x2c, 0x7e, 0x3c, 0xd9, 0x46, 0x1d, 0x0d, 0x03, 0x4e } },
	[ 5] = { { 0xe0, 0x53, 0xf9, 0x64, 0x4f, 0xaa, 0xb1, 0xda, 0x31, 0x1b } },
	[ 6] = { { 0xe5, 0x1c, 0x00, 0xc4, 0x8e, 0xd5, 0xdb, 0x07, 0x02, 0xb3 } },
	[ 7] = { { 0x95, 0x93, 0x25, 0xc5, 0x67, 0x73, 0xa7, 0x4a, 0x43, 0xc6 } },
	[ 8] = { { 0x05, 0x4d, 0xda, 0xf1, 0xb9, 0xb5, 0x9b, 0x9a, 0x60, 0xbf } },
	[ 9] = { { 0x5e, 0xd1, 0xa9, 0xc1, 0x84, 0xeb, 0x72, 0xb9, 0x45, 0x46 } },
	[10] = { { 0xc3, 0x8f, 0x61, 0x8f, 0x53, 0xa9, 0x6e, 0x4f, 0xfd, 0x53 } },
	[11] = { { 0x19, 0xf8, 0xe6, 0xbc, 0x5d, 0x71, 0x41, 0x77, 0x65, 0x95 } },
	[12] = { { 0x20, 0x68, 0x65, 0xeb, 0x08, 0xb4, 0x2a, 0x66, 0x63, 0xe1 } },
};
static const union bc out_r240[] = {
	[ 1] = { { 0xd9, 0xd6, 0xd3, 0xc8, 0x4d, 0x1a, 0xc1, 0xd7, 0x5f, 0x96 } },
	[ 2] = { { 0x7a, 0xb8, 0x98, 0x1a, 0xda, 0x8f, 0xdb, 0x60, 0xae, 0xfd } },
	[ 3] = { { 0x5c, 0x9d, 0x5e, 0x4b, 0x38, 0x5e, 0x9c, 0x4f, 0x8e, 0x2e } },
	[ 4] = { { 0x0d, 0xd2, 0x5e, 0x6d, 0xe2, 0x9a, 0x42, 0xad, 0xb3, 0x58 } },
	[ 5] = { { 0x8d, 0xf4, 0x44, 0x09, 0xb4, 0x6f, 0xb8, 0xc6, 0x1b, 0xc4 } },
	[ 6] = { { 0x57, 0x16, 0xe7, 0x01, 0xef, 0x67, 0xcc, 0x04, 0x48, 0xb0 } },
	[ 7] = { { 0x9c, 0xec, 0xce, 0x92, 0x93, 0x8a, 0xea, 0xba, 0x26, 0xaf } },
	[ 8] = { { 0x19, 0xc2, 0xd8, 0xff, 0x69, 0xe5, 0x66, 0xa5, 0x07, 0xc9 } },
	[ 9] = { { 0x78, 0xd6, 0x58, 0xde, 0xc5, 0x01, 0xee, 0xd6, 0x3b, 0x1e } },
	[10] = { { 0x46, 0x68, 0x1a, 0x4a, 0x3a, 0x97, 0x5b, 0x16, 0x2a, 0xc4 } },
	[11] = { { 0x12, 0x9e, 0x94, 0x0f, 0x63, 0x43, 0x00, 0xf6, 0xb4, 0x14 } },
	[12] = { { 0x85, 0x5a, 0x86, 0x45, 0x96, 0xc5, 0x1c, 0xaf, 0x7d, 0x3d } },
};
static const union bc out_r640[] = {
	[ 1] = { { 0x3f, 0x41, 0x9f, 0x88, 0x1c, 0x42, 0xcf, 0xfc, 0x5f, 0xd7 } },
	[ 2] = { { 0x82, 0x8d, 0x4d, 0x09, 0x05, 0x0e, 0x06, 0x35, 0x07, 0x5e } },
	[ 3] = { { 0x00, 0x7b, 0xb5, 0xc5, 0x99, 0x80, 0x66, 0x0e, 0x02, 0x93 } },
	[ 4] = { { 0x75, 0x1a, 0x16, 0xe5, 0xe4, 0x95, 0xe1, 0xe2, 0xff, 0x22 } },
	[ 5] = { { 0x6e, 0xf2, 0x61, 0x6f, 0xeb, 0xb9, 0x9b, 0x1f, 0x70, 0xed } },
	[ 6] = { { 0x5f, 0x9e, 0x63, 0x88, 0x4f, 0x2e, 0x94, 0xf1, 0xa1, 0x0e } },
	[ 7] = { { 0xa4, 0xc1, 0x35, 0x21, 0x90, 0x12, 0xaa, 0xc8, 0x08, 0xed } },
	[ 8] = { { 0xf4, 0x83, 0x5d, 0x80, 0x2a, 0xab, 0xc5, 0xbe, 0x75, 0x8e } },
	[ 9] = { { 0x2e, 0xdd, 0x24, 0x58, 0x7f, 0x22, 0x5c, 0x69, 0x6e, 0x61 } },
	[10] = { { 0xb8, 0x6d, 0xb6, 0x0f, 0xf7, 0x23, 0x18, 0x76, 0x6e, 0xef } },
	[11] = { { 0xa2, 0x49, 0x0a, 0x3e, 0x68, 0xd5, 0xd0, 0x2d, 0xd4, 0xaa } },
	[12] = { { 0x68, 0xed, 0xde, 0x13, 0xa4, 0x79, 0xe1, 0x47, 0x71, 0xbd } },
};
static const union bc out_r1440[] = {
	[ 1] = { { 0x0f, 0x0a, 0xf7, 0x07, 0x4b, 0x6a, 0xbd, 0x48, 0x6f, 0x80 } },
	[ 2] = { { 0x63, 0x90, 0x22, 0x0e, 0x7b, 0x5d, 0x32, 0x84, 0xd2, 0x3e } },
	[ 3] = { { 0x06, 0x25, 0xa3, 0x46, 0x28, 0xc0, 0xcf, 0xe7, 0x6c, 0x75 } },
	[ 4] = { { 0x7d, 0xaa, 0xd8, 0x07, 0xf8, 0x50, 0x6c, 0x9c, 0x02, 0x76 } },
	[ 5] = { { 0x65, 0x3b, 0xc0, 0xf8, 0x7d, 0x26, 0x4f, 0x08, 0x57, 0xd0 } },
	[ 6] = { { 0xd6, 0x05, 0x33, 0x5e, 0xdc, 0xe7, 0xd2, 0xca, 0xf4, 0x10 } },
	[ 7] = { { 0x5e, 0x0d, 0x17, 0x9c, 0x50, 0xc2, 0x93, 0x0c, 0x0d, 0x76 } },
	[ 8] = { { 0x34, 0xe1, 0x81, 0x23, 0x29, 0xd5, 0xe8, 0x9d, 0x67, 0x1a } },
	[ 9] = { { 0xca, 0x18, 0x6a, 0x0f, 0xe1, 0x26, 0xed, 0xbe, 0x2c, 0xa6 } },
	[10] = { { 0xdf, 0x7b, 0xf3, 0x01, 0x7c, 0xd3, 0x22, 0xa4, 0x6c, 0x31 } },
	[11] = { { 0x69, 0xc9, 0x4f, 0x0a, 0xe8, 0x30, 0x40, 0x26, 0xb3, 0xda } },
	[12] = { { 0xbf, 0x8c, 0x82, 0x63, 0xa9, 0x87, 0x59, 0x5b, 0x21, 0xc0 } },
};

/* TODO:
 * - optimize/collapse paths of bitxform's that are referenced only once:
 *   - SET, NOT, VAR, EXPECT?
 * - modify keccak_output to apply EXPECT directly instead of SET'ing O */

static int keccak_preimage(struct instance *in, struct bits I, struct bits O, const struct out *o)
{
	struct keccak kc;
	const union bc *out_r;

	assert(0 < rounds);
	switch (rate) {
	case   40: out_r = out_r40; assert(rounds < ARRAY_SIZE(out_r40)); break;
	case  240: out_r = out_r240; assert(rounds < ARRAY_SIZE(out_r240)); break;
	case  640: out_r = out_r640; assert(rounds < ARRAY_SIZE(out_r640)); break;
	case 1440: out_r = out_r1440; assert(rounds < ARRAY_SIZE(out_r1440)); break;
	default:
		fprintf(stderr, "invalid rate: %u\n", rate);
		exit(EXIT_FAILURE);
	}

	// struct bits P = bits(in, O.n);

	keccak_init_full(&kc, in, rate, cap, rounds, I/*, P*/);

	struct bits S = kc.S;

	struct operation op_expect_40[] = {
		{ EXPECT, 40, 0, S.o, O.o },
		*kc.f,
		{ EXPECT, 40, 0, S.o, O.o + 40 },
	};
	struct operation op_expect_n[] = {
		{ EXPECT, 80, 0, S.o, O.o },
	};

	struct operation ops[] = {
		OP_VAR(I),
		OP_LOAD(O,0,out_r[kc.rounds].b),
#if 0
		OP_VAR(S),
#else
		OP_SET0(S),
		*kc.absorb,
#endif
		kc.r == 40 ? OP_CALL_ARR(op_expect_40) : OP_CALL_ARR(op_expect_n),
	};

	return instance_run(in, &OP_CALL_ARR(ops), o);

	// keccak_free(&kc)
}

static int keccak_collision(
	struct instance *in,
	struct bits I, struct bits J,
	const struct out *o
) {
	struct keccak kc0, kc1;

	keccak_init_full(&kc0, in, rate, cap, rounds, I);
	keccak_init_full(&kc1, in, rate, cap, rounds, J);

	struct operation op_expect_40[] = {
		{ EXPECT, 40, 0, kc0.S.o, kc1.S.o },
		*kc0.f,
		*kc1.f,
		{ EXPECT, 40, 0, kc0.S.o, kc1.S.o },
		*kc0.f,
		*kc1.f,
		{ EXPECT, 40, 0, kc0.S.o, kc1.S.o },
		*kc0.f,
		*kc1.f,
		{ EXPECT, 40, 0, kc0.S.o, kc1.S.o },
	};
	struct operation op_expect_n[] = {
		{ EXPECT, 160, 0, kc0.S.o, kc1.S.o },
	};

	struct operation coll[] = {
		OP_VAR(I),
		OP_VAR(J),

		OP_SET0(kc0.S),
		OP_SET0(kc1.S),

		*kc0.absorb,
		*kc1.absorb,

		// *kc0.squeeze,
		// *kc1.squeeze,
		// OP_EXPECT(O,P), /* time worse for c 640 160 2 than w/o squeeze */

		// { EXPECT, kc0.S.n/*160*/, 0, kc0.S.o, kc1.S.o },
		rate == 40 ? OP_CALL_ARR(op_expect_40) : OP_CALL_ARR(op_expect_n),
	};

	if (coll_ensure_unequal && I.n == J.n) {
		struct bits IN = bits(in, I.n);
		struct bits JN = bits(in, J.n);

		struct operation I_neq_J[] = {
			OP_NOT(IN, I),
			OP_NOT(JN, J),
			OP_AND(JN, I, JN),
			OP_AND(IN, IN, J),
			OP_OR(IN, IN, JN),
			OP_EXPECT_ANY(IN),
		};

		struct operation coll0[] = {
			OP_CALL_ARR(coll),
			OP_CALL_ARR(I_neq_J),
		};

		return instance_run(in, &OP_CALL_ARR(coll0), o);
	} else {
		return instance_run(in, &OP_CALL_ARR(coll), o);
	}
}

static void usage(const char *progname)
{
	fprintf(stderr, "usage: %s [-OPTS] {p|c} RATE CAP ROUNDS [SOLUTION]\n",
		progname);
	fprintf(stderr, "\n"
			"  -c    DIMACS CNF output format [default]\n"
			"  -d    dot(1) output format instead of DIMACS CNF\n"
			"  -F    disable constant folding\n"
			"  -h    show this help message\n"
			"  -i N  set size in bits of (first, for 'c') input\n"
			"  -j N  set size in bits of second ('c') input\n"
			"  -u    ensure unequality of two collision inputs\n"
	);
	exit(EXIT_FAILURE);
}

int main(int argc, char **argv)
{
	struct instance in = INSTANCE_INIT;
	struct dimacs_cnf cnf = DIMACS_CNF_INIT;
	struct out o;
	unsigned i, j;
	int ret = EXIT_SUCCESS;
	FILE *sol = NULL;
	int opt;
	enum {
		OUT_CNF = 'c',
		OUT_DOT = 'd',
	} output_fmt = OUT_CNF;
	enum {
		ATTACK_PREIMAGE = 'p',
		ATTACK_COLLISION = 'c',
	} attack_mode;

	unsigned i_n, j_n; /* TODO */

	struct bits I, J, O;

	while ((opt = getopt(argc, argv, ":cdFhi:j:u")) != -1) {
		switch (opt) {
		case 'c':
		case 'd':
			output_fmt = opt;
			break;
		case 'F':
			constant_folding = 0;
			break;
		case 'h':
			usage(argv[0]);
		case 'i':
			if ((i_n = atoi(optarg)) < 0) {
				fprintf(stderr, "-i needs an argument > 0\n");
				exit(EXIT_FAILURE);
			}
			break;
		case 'j':
			if ((i_n = atoi(optarg)) < 0) {
				fprintf(stderr, "-j needs an argument > 0\n");
				exit(EXIT_FAILURE);
			}
			break;
		case 'u':
			coll_ensure_unequal = 1;
			break;
		case ':':
			fprintf(stderr, "option -%c requires an argument\n",
				optopt);
			exit(EXIT_FAILURE);
		case '?':
			fprintf(stderr, "unrecognized option -%c\n", optopt);
			exit(EXIT_FAILURE);
		}
	}

	if (argc - optind < 4 || argc - optind > 5)
		usage(argv[0]);

	switch (argv[optind][0]) {
	case 'p':
	case 'c':
		attack_mode = argv[optind][0];
		break;
	default:
		fprintf(stderr, "unrecognized attack mode: '%s'\n",
			argv[optind]);
		exit(EXIT_FAILURE);
	}

	rate = atoi(argv[optind+1]);   /* {,2,6,14}40 */
	cap = atoi(argv[optind+2]);    /* 160 */
	rounds = atoi(argv[optind+3]); /* 1+ */

	if (optind + 4 < argc) {
		sol = fopen(argv[optind+4], "r");
		if (!sol) {
			perror(argv[optind+4]);
			exit(EXIT_FAILURE);
		}
	}

	switch (output_fmt) {
	case OUT_CNF:
		o.bit_out    = dimacs_cnf_bit_out;
		o.constr_out = dimacs_cnf_constr_out;
		o.p          = &cnf;
		break;
	case OUT_DOT:
		o.bit_out    = dot_bit_out;
		o.constr_out = dot_constr_out;
		o.p          = stdout;
		fprintf(o.p, "digraph G {\n");
		break;
	}

	switch (attack_mode) {
	case ATTACK_PREIMAGE:
		I = bits(&in, rate == 40 ? 3 * rate - 2 : rate - 16);
		O = bits(&in, 80);
		ret = keccak_preimage(&in, I, O, &o);
		break;
	case ATTACK_COLLISION:
		i_n = rate == 40 ? 4 * rate - 2 : rate - 8;
		j_n = rate == 40 ? 4 * rate - 3 : rate - 9;
		I = bits(&in, i_n);
		J = bits(&in, j_n);
		ret = keccak_collision(&in, I, J, &o);
		break;
	}
	if (output_fmt == OUT_DOT) {
		fprintf(o.p, "}\n");
		fclose(o.p);
	}
	if (ret)
		goto done;

	fprintf(stderr,
		"var summary: %u and, %u or, %u xor, %u anti, %u equi, %u free\n",
		stat.and, stat.or, stat.xor, stat.anti, stat.equi, stat.free);

	for (i=0; i<12; i++)
		switch (i) {
		case AND:
		case OR:
		case XOR:
			fprintf(stderr, "%s b: ", op_names[i]);
			for (j=0; j<12; j++)
				switch (j) {
				case AND:
				case OR:
				case XOR:
				case NOT:
				case SET:
				case VAR:
					fprintf(stderr, "%s: %u, ", op_names[j], par_stat[i].b[j]);
				}
			fprintf(stderr, "\n");
		case NOT:
		case SET:
			fprintf(stderr, "%s a: ", op_names[i]);
			for (j=0; j<12; j++)
				switch (j) {
				case AND:
				case OR:
				case XOR:
				case NOT:
				case SET:
				case VAR:
					fprintf(stderr, "%s: %u, ", op_names[j], par_stat[i].a[j]);
				}
			fprintf(stderr, "\n");
		}

	/* mode of operation: CNF generation vs. solution compilation */
	if (!sol) {
		FILE *o = stdout;
		fprintf(o, "c rate: %u, cap: %u, rounds: %u, I.n: %u, J.n: %u\n",
			rate, cap, rounds, I.n, J.n);
		dimacs_cnf_print(o, &cnf);
	} else {
		/* assuming minisat, which unfortunately got an output format
		 * that differs from DIMACS */
		char buf[16];
		signed var;
		bb_t mem[(in.total_bits + bb_t_bits - 1) / bb_t_bits];

		if (fscanf(sol, "%s\n", buf) < 1 || strncmp("SAT", buf, 3)) {
			fprintf(stderr, "supplied file does not contain a solution: %s\n", buf);
			ret = EXIT_FAILURE;
			goto done;
		}

		memset(&mem, 0, sizeof(mem));

		while (fscanf(sol, "%d", &var) == 1) {
			unsigned idx = var < 0 ? -var : var;
			struct bitxform *vx = in.x->xf + idx;
			if (vx->variable)
				bb_put(mem, var < 0 ? 0 : 1, vx->a, 1);
		}

		switch (attack_mode) {
		case ATTACK_COLLISION:
			printf("J %d bits, %d bytes: ", J.n, (J.n + 7) / 8);
			for (i=J.o; i<J.o+J.n; i+=8)
				printf("\\x%02lx", bb_get(mem, i, 8));
			printf("\n");
		case ATTACK_PREIMAGE:
			printf("I %d bits, %d bytes: ", I.n, (I.n + 7) / 8);
			for (i=I.o; i<I.o+I.n; i+=8)
				printf("\\x%02lx", bb_get(mem, i, 8));
			printf("\n");
			break;
		}
	}
done:
	if (sol)
		fclose(sol);

	return ret;
}
