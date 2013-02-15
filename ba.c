
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>

#define ARRAY_SIZE(arr)		(sizeof(arr)/sizeof(*(arr)))

// typedef unsigned long bit_t;

struct bits {
	unsigned o, n;
};

typedef unsigned long bb_t;
#define bb_t_bits	(sizeof(bb_t) * 8)
#define bb_t_mask	(~(bb_t)0)

struct operation {
	enum op_t {
		AND,    /* n,r,a,b */
		OR,     /* n,r,a,b */
		XOR,    /* n,r,a,b */
		NOT,    /* n,r,a */
		ROL,    /* n,r,a,b */
		CALL,   /* n,tgt */
		EXPECT, /* n,r,a */
	//	FIX,    /* n,r,a */
		VAR,    /* n,r */

		SET,    /* n,r,a */
		SET0,   /* n,r */
		LOAD,   /* n,r,a,v */
	} op;
	unsigned n, r, a, b;
	const struct operation *tgt;
	const bb_t *v;
};


#define OP_AND(out,b0,b1) (struct operation){ AND, (out).n, (out).o, (b0).o, (b1).o }
#define OP_OR(out,b0,b1)  (struct operation){ OR , (out).n, (out).o, (b0).o, (b1).o }
#define OP_XOR(out,b0,b1) (struct operation){ XOR, (out).n, (out).o, (b0).o, (b1).o }
#define OP_NOT(out,b0)    (struct operation){ NOT, (out).n, (out).o, (b0).o }
#define OP_ROL(out,b0,m)  (struct operation){ ROL, (out).n, (out).o, (b0).o, (m) }
#define OP_CALL(n,target) (struct operation){ CALL, (n), .tgt = (target) }
#define OP_CALL_ARR(arr)  OP_CALL(ARRAY_SIZE(arr),arr)
#define OP_EXPECT(b,c)    (struct operation){ EXPECT, (b).n, (b).o, (c).o }
#define OP_VAR(b)         (struct operation){ VAR, (b).n, (b).o }
#define OP_SET(out,src)   (struct operation){ SET, (out).n, (out).o, (src).o }
#define OP_SET0(out)      (struct operation){ SET0, (out).n, (out).o }
#define OP_LOAD(out,off,bb) (struct operation){ LOAD, (out).n, (out).o, (off), .v = (bb) }

static const char *op_names[] = {
	"and", "or", "xor", "not", "rol", "call", "expect",
	"var", "set"
};


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

struct bitxform {
	enum op_t op; /* subset: AND, OR, XOR, NOT, SET, VAR */
	unsigned a, b;
	unsigned resolved : 1;
	unsigned variable : 1;
};

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

#include <stddef.h>

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
	x->xf_n += n;
	return r;
}

#define PRI_BUFSZ	256

static const char * opstr(const struct operation *op)
{
	static char buf[PRI_BUFSZ];

	snprintf(buf, sizeof(buf), "%s[n:%u,r:%u,a:%u,b:%u]",
		op_names[op->op], op->n, op->r, op->a, op->b);

	return buf;
}

struct clause {
	unsigned n;
	signed l[];
};

#define DIMACS_CNF_INIT	(struct dimacs_cnf){ 0, 0, NULL, 0 }
struct dimacs_cnf {
	unsigned v, c;
	struct clause **cl;
	unsigned cl_sz;
};

static void dimacs_cnf_print(FILE *f, const struct dimacs_cnf *cnf)
{
	unsigned i, j;
	struct clause *c;

	fprintf(f, "p cnf %u %u\n", cnf->v, cnf->c);
	for (i=0; i<cnf->c; i++) {
		c = cnf->cl[i];
		for (j=0; j<c->n; j++)
			fprintf(f, "%d ", c->l[j]);
		fprintf(f, "0\n");
	}
}

static void dimacs_cnf_add(struct dimacs_cnf *cnf, struct clause *c)
{
	unsigned n = cnf->c;
	unsigned i;

	if (cnf->cl_sz < n + 1) {
		unsigned nsz = 2 * (n + 1);
		if (!(cnf->cl = realloc(cnf->cl, sizeof(struct clause *) * nsz))) {
			perror("realloc");
			exit(EXIT_FAILURE);
		}
		memset(cnf->cl + cnf->cl_sz, 0,
			(nsz - n) * sizeof(struct clause *));
		cnf->cl_sz = nsz;
	}
	cnf->cl[cnf->c++] = c;

	for (i=0; i<c->n; i++) {
		int l = c->l[i];
		if (l < 0)
			l = -l;
		if (cnf->v < l)
			cnf->v = l;
	}
}

static struct clause * clause_create(unsigned n, ...)
{
	struct clause *c = malloc(offsetof(struct clause,l) + sizeof(signed)*n);
	va_list ap;
	unsigned i;

	c->n = n;

	va_start(ap, n);
	for (i=0; i<n; i++)
		c->l[i] = va_arg(ap, signed);
	va_end(ap);

	return c;
}

static void dimacs_cnf_eq(struct dimacs_cnf *cnf, int a, int b)
{
	dimacs_cnf_add(cnf, clause_create(2, a, -b));
	dimacs_cnf_add(cnf, clause_create(2, -a, b));
}

// /* returns a dimacs_cnf literal corresponding to x->xf[a] */
static int bit_resolve(struct opxform *x, unsigned a, struct dimacs_cnf *cnf)
{
	struct bitxform *ax = x->xf + a;
	enum op_t op = ax->op;

	/* if ax is 'already resolved', return */
	if (ax->resolved)
		return 0;

	if (a == OPX_FALSE) {
		dimacs_cnf_add(cnf, clause_create(1, -a));
		goto done;
	}
	if (a == OPX_TRUE) {
		dimacs_cnf_add(cnf, clause_create(1,  a));
		goto done;
	}

	switch (op) {
	case AND:
	case OR:
	case XOR:
		bit_resolve(x, ax->b, cnf);
	case NOT:
	case SET:
		bit_resolve(x, ax->a, cnf);
	case VAR:
		break;
	default:
		fprintf(stderr, "invalid bit_resolve: %s\n", op_names[op]);
		exit(EXIT_FAILURE);
	}

	switch (op) {
	case AND:
		/* express a = ax->a*ax->b */
		dimacs_cnf_add(cnf, clause_create(2,  ax->a,         -a));
		dimacs_cnf_add(cnf, clause_create(2,          ax->b, -a));
		dimacs_cnf_add(cnf, clause_create(3, -ax->a, -ax->b,  a));
		break;
	case OR:
		/* express a = ax->a+ax->b */
		dimacs_cnf_add(cnf, clause_create(2, -ax->a,          a));
		dimacs_cnf_add(cnf, clause_create(2,         -ax->b,  a));
		dimacs_cnf_add(cnf, clause_create(3,  ax->a,  ax->b, -a));
		break;
	case XOR:
		/* express a = ax->a^ax->b */
		dimacs_cnf_add(cnf, clause_create(3, -ax->a,  ax->b,  a));
		dimacs_cnf_add(cnf, clause_create(3, -ax->a, -ax->b, -a));
		dimacs_cnf_add(cnf, clause_create(3,  ax->a,  ax->b, -a));
		dimacs_cnf_add(cnf, clause_create(3,  ax->a, -ax->b,  a));
		break;
	case NOT:
		/* express a = -ax->a */
		dimacs_cnf_add(cnf, clause_create(2,  ax->a,  a));
		dimacs_cnf_add(cnf, clause_create(2, -ax->a, -a));
		// dimacs_cnf_eq(&cnf, a, -bit_resolve(x, ax->a));
		break;
	case SET:
		/* express a = ax->a */
		dimacs_cnf_add(cnf, clause_create(2, -ax->a,  a));
		dimacs_cnf_add(cnf, clause_create(2,  ax->a, -a));
		// dimacs_cnf_eq(&cnf, a, bit_resolve(x, ax->a));
		break;
	case VAR:
		break;
	default:;
	}

done:
	/* mark ax as 'already resolved' */
	ax->resolved = 1;

	return 0;
}

#if 0
/* a,b: indices into xf */
static int bit_expect(const struct opxform *x, unsigned a, unsigned b)
{
	struct bitxform *ax = x->xf + a;
	enum op_t op = ax->op;

	if (a < OPX_RESERVED) {
		fprintf(stderr, "bit_expect: a (%u) is reserved\n", a);
		return 1;
	}
	if (b >= OPX_RESERVED) {
		fprintf(stderr, "bit_expect: b (%u) is not reserved\n", b);
		return 1;
	}

	switch (op) {
	case AND:
	case OR:
		if (b) {
			dimacs_cnf_add(&cnf, clause_create(2, ax->a, ax->b));
		} else {
			dimacs_cnf_add(&cnf, clause_create(1, -ax->a));
			dimacs_cnf_add(&cnf, clause_create(1, -ax->b));
		}
		return 0;
	case XOR:
		dimacs_cnf_eq(&cnf, b ? -ax->a : ax->a, ax->b);
		return 0;
	case NOT:
		dimacs_cnf_eq(&cnf, a, -ax->a);
		return bit_expect(x, ax->a, !b);
	case SET:
		dimacs_cnf_eq(&cnf, a, ax->a);
		return bit_expect(x, ax->a, b);
	case VAR:
		dimacs_cnf_add(&cnf, clause_create(1, b ? a : -a));
		return 0;
	case ROL:
	case CALL:
	case EXPECT:
	case SET0:
	case LOAD:
		fprintf(stderr, "invalid bit_expect: %s\n", op_names[op]);
		break;
	}
	return 1;
}
#endif

#include <assert.h>

/* n,r,a */
static int opx_expect(struct opxform *x, const struct operation *op, struct dimacs_cnf *cnf)
{
	int r = 0;
	unsigned i, n, var, expected;

	fprintf(stderr, "expect, current ssa vars: %u, op: %s\n", x->xf_n, opstr(op));

	n = op->n;
	for (i=0; i<n; i++) {
#if 1
		var = x->mem2xf[op->r + i];
		bit_resolve(x, var, cnf);
		expected = x->mem2xf[op->a + i];/*
		printf("var: %u -> %u, expected: %u -> %u\n",
			op->r + i, var, op->a + i, expected);*/

		assert(x->xf[expected].op == SET);
#if 0
		dimacs_cnf_eq(cnf, var, expected);
#else
		switch (x->xf[expected].a) {
		case OPX_FALSE:
			dimacs_cnf_add(cnf, clause_create(1, -var));
			break;
		case OPX_TRUE:
			dimacs_cnf_add(cnf, clause_create(1,  var));
			break;
		default:
			fprintf(stderr, "invalid opx_expect @ i: %u, xf[expected]: %u\n",
				i, x->xf[expected].a);
			r = 1;
			goto done;
		}
#endif
#else
		if ((r = bit_expect(x, x->mem2xf[op->r + i], x->mem2xf[op->a + i])) != 0) {
			fprintf(stderr, "invalid opx_expect @ i: %u\n", i);
			goto done;
		}
#endif
	}

done:
	return r;
}

static int opx_exec(struct opxform *x, const struct operation *op, struct dimacs_cnf *cnf)
{
	int r = 0;
	unsigned i, k, n;
	unsigned have_a = 0, have_b = 0;

	n = op->n;

	switch (op->op) {
	case AND:
	case OR:
	case XOR:
		have_b = 1;
	case NOT:
	case ROL: /* b valid but rot amount, no mem ptr */
	case SET:
		have_a = 1;
	case VAR:
	case LOAD: /* a valid but offset, no mem ptr */
	case SET0:
		/* check validity */
		for (i=0; i<n; i++) {
			unsigned a = have_a ? x->mem2xf[op->a + i] : 0;
			unsigned b = have_b ? x->mem2xf[op->b + i] : 0;
			if ((have_a ? !a : 0) || (have_b ? !b : 0)) {
				fprintf(stderr, "op %p: %s: %c @ %u undef\n",
					(void *)op, opstr(op),
					have_a && !a ? 'a' : 'b',
					i);
				r = 1;
				goto done;
			}
		}
		/* allocate new variables for the output and assign the results */
		k = opx_alloc(x, n);
		if (op->op == ROL) {
			unsigned b = op->b % n;
			for (i=0; i<n; i++) {
				x->xf[k+i].op = SET;
				x->xf[k+i].a  = x->mem2xf[op->a + (n - b + i) % n];
			}
		} else if (op->op == LOAD) {
			for (i=0; i<n; i++) {
				x->xf[k+i].op = SET;
				x->xf[k+i].a  = bb_get(op->v, op->a + i, 1) ? OPX_TRUE : OPX_FALSE;
			}
		} else if (op->op == SET0) {
			for (i=0; i<n; i++) {
				x->xf[k+i].op = SET;
				x->xf[k+i].a  = OPX_FALSE;
			}
		} else {
			for (i=0; i<n; i++) {
				x->xf[k+i].op = op->op;
				if (have_a)
					x->xf[k+i].a = x->mem2xf[op->a + i];
				if (have_b)
					x->xf[k+i].b = x->mem2xf[op->b + i];
			}
		}
		if (op->op == VAR)
			for (i=0; i<n; i++)
				x->xf[k+i].variable = 1;
		/* finally assign the output slots, s.t. an operation using
		 * these op->r later references the correct values */
		for (i=0; i<n; i++)
			x->mem2xf[op->r + i] = k + i;
		break;
	case CALL:
		for (i=0; i<n; i++)
			if ((r = opx_exec(x, op->tgt + i, cnf)) != 0) {
				fprintf(stderr, "call stack %u: op %p: %s\n",
					i, (void *)op, opstr(op));
				goto done;
			}
		break;
	case EXPECT:
		/* check validity */
		for (i=0; i<n; i++) {
			unsigned a = x->mem2xf[op->r + i];
			unsigned b = x->mem2xf[op->a + i];
			if (!a || !b) {
				fprintf(stderr, "op %p: %s: %c @ %u undef\n",
					(void *)op, opstr(op),
					!a ? 'r' : 'a', i);
				r = 1;
				goto done;
			}
		}
		r = opx_expect(x, op, cnf);
		if (r)
			fprintf(stderr, "ERROR: offending operation: %s\n", opstr(op));
		break;
	}

done:
	return r;
}

static void print_bits(const char *name, const struct bits *b)
{
	fprintf(stderr, "%s[n:%u,o:%u] -- [%u,%u)\n", name,
		b->n, b->o, b->o, b->o + b->n);
}

struct instance {
	unsigned total_bits;
	const struct operation *op;
	struct opxform *x;
	struct dimacs_cnf cnf;
};

#define INSTANCE_INIT	(struct instance){ 0, NULL, NULL, DIMACS_CNF_INIT }

static int instance_run(
	struct instance *in, const struct operation *op
) {
	in->op     = op;
	in->x      = opx_init(in->total_bits);
	memset(&in->cnf, 0, sizeof(in->cnf));

	return opx_exec(in->x, in->op, &in->cnf);
}

struct bits bits(struct instance *in, unsigned n)
{
	struct bits r = { in->total_bits, n };
	in->total_bits += n;
	return r;
}

#if 0
int main()
{
	struct instance in = INSTANCE_INIT;

	unsigned z = 2;
	struct bits I = bits(&in, z);
	struct bits t = bits(&in, z);
	struct bits O = bits(&in, z);

	struct operation ops[] = {
		OP_VAR(I),
		OP_SET0(O),
		OP_ROL(t,I,1),
		OP_XOR(I,I,t),
		OP_NOT(I,I),
		OP_EXPECT(I,O),
	};

	int ret = instance_run(&in, &OP_CALL_ARR(ops));
	if (!ret)
		dimacs_cnf_print(stdout, &in.cnf);

	return ret;
}
#elif 1
static void * memdup(const void *src, size_t n)
{
	void *r = malloc(n);
	if (!r) {
		perror("malloc");
		abort();
	}
	return memcpy(r, src, n);
}

#define memdup_arr(arr)	memdup((arr), sizeof(arr))

struct keccak {
	unsigned w, r, c, rounds;
	struct bits RC;
	struct bits S, B, C, D, t, b;
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

int main(int argc, char **argv)
{
	struct instance in = INSTANCE_INIT;
	struct keccak kc;
	int ret;

	if (argc < 4) {
		fprintf(stderr, "usage: %s RATE CAP ROUNDS\n", argv[0]);
		return 1;
	}

	unsigned rate = atoi(argv[1]);   /* 40 */
	unsigned cap = atoi(argv[2]);    /* 160 */
	unsigned rounds = atoi(argv[3]); /* 1 */

	struct operation *r;
	struct operation *f;
	struct operation *i;

	union bc {
		unsigned char c[16];
		bb_t b[2];
	};

	static const union bc out_r40[] = {
		[1] = { { 0xe9, 0xf5, 0x7f, 0x02, 0xa9, 0xb0, 0xeb, 0xd8, 0x44, 0x98 } },
		[2] = { { 0x02, 0x4a, 0x55, 0x18, 0xe1, 0xe9, 0x5d, 0xb5, 0x32, 0x19 } },
		[3] = { { 0xd8, 0xed, 0x85, 0x69, 0x2a, 0xfb, 0xee, 0x4c, 0x99, 0xce } },
	};
	static const union bc out_r240[] = {
		[1] = { { 0xd9, 0xd6, 0xd3, 0xc8, 0x4d, 0x1a, 0xc1, 0xd7, 0x5f, 0x96 } },
		[2] = { { 0x7a, 0xb8, 0x98, 0x1a, 0xda, 0x8f, 0xdb, 0x60, 0xae, 0xfd } },
		[3] = { { 0x5c, 0x9d, 0x5e, 0x4b, 0x38, 0x5e, 0x9c, 0x4f, 0x8e, 0x2e } },
	};
	static const union bc out_r640[] = {
		[1] = { { 0x3f, 0x41, 0x9f, 0x88, 0x1c, 0x42, 0xcf, 0xfc, 0x5f, 0xd7 } },
		[2] = { { 0x82, 0x8d, 0x4d, 0x09, 0x05, 0x0e, 0x06, 0x35, 0x07, 0x5e } },
		[3] = { { 0x00, 0x7b, 0xb5, 0xc5, 0x99, 0x80, 0x66, 0x0e, 0x02, 0x93 } },
		[4] = { { 0x75, 0x1a, 0x16, 0xe5, 0xe4, 0x95, 0xe1, 0xe2, 0xff, 0x22 } },
		[5] = { { 0x6e, 0xf2, 0x61, 0x6f, 0xeb, 0xb9, 0x9b, 0x1f, 0x70, 0xed } },
	};
	static const union bc out_r1440[] = {
		[1] = { { 0x0f, 0x0a, 0xf7, 0x07, 0x4b, 0x6a, 0xbd, 0x48, 0x6f, 0x80 } },
		[2] = { { 0x63, 0x90, 0x22, 0x0e, 0x7b, 0x5d, 0x32, 0x84, 0xd2, 0x3e } },
		[3] = { { 0x06, 0x25, 0xa3, 0x46, 0x28, 0xc0, 0xcf, 0xe7, 0x6c, 0x75 } },
	};
	static const union bc *out_r;

	switch (rate) {
	case   40: out_r = out_r40; assert(0 < rounds && rounds < ARRAY_SIZE(out_r40)); break;
	case  240: out_r = out_r240; assert(0 < rounds && rounds < ARRAY_SIZE(out_r240)); break;
	case  640: out_r = out_r640; assert(0 < rounds && rounds < ARRAY_SIZE(out_r640)); break;
	case 1440: out_r = out_r1440; assert(0 < rounds && rounds < ARRAY_SIZE(out_r1440)); break;
	default: fprintf(stderr, "invalid rate: %u\n", rate); return EXIT_FAILURE;
	}

	keccak_init(&kc, &in, rate, cap, rounds);

	r = keccak_round(&kc, &in);
	f = keccak_f(&kc, r);

	struct bits S = kc.S;
	struct bits I = bits(&in, 1 * kc.r - 16);
	struct bits O = bits(&in, 80);

	i = keccak_input(&kc, &in, I, f);

	struct operation ops[] = {
		OP_VAR(I),
		OP_LOAD(O,0,out_r[kc.rounds].b),
		OP_SET0(S),

#if 0
		{ XOR, kc.r, S.o, S.o, I.o },
		*f,/*
		{ XOR, kc.r, S.o, S.o, I.o + kc.r },
		*f,*/
#else
		*i,
#endif

#if 240
		{ EXPECT, 80, S.o, O.o },
#else
		{ EXPECT,     kc.r, S.o, O.o },
		*f,
		{ EXPECT,     kc.r, S.o, O.o + kc.r },
#endif
	};

	ret = instance_run(&in, &OP_CALL_ARR(ops));
	if (ret)
		goto done;

	dimacs_cnf_print(stdout, &in.cnf);

done:
	free(f);
	free(r);
	return ret;
}
#else
int main(int argc, char **argv)
{
	unsigned k_r = 40;
	unsigned z = 8; /* lane size, w */
	unsigned rounds = 1;

	const struct bits A  = {           0, 5 * 5 * z }; /* I/O */
	const struct bits B  = {  A.o +  A.n, 5 * 5 * z };
	const struct bits C  = {  B.o +  B.n, 5 * z };
	const struct bits D  = {  C.o +  C.n, 5 * z };
	const struct bits r  = {  D.o +  D.n, z }; /* RC[round] */
	const struct bits t  = {  r.o +  r.n, z };
	const struct bits RC = {  t.o +  t.n, rounds * z }; /* constants */
	const struct bits P  = { RC.o + RC.n, 2 * k_r }; /* I, mostly */
	const struct bits O  = {  P.o +  P.n, 8 * 10 }; /* O */
	unsigned total_bits = O.o + O.n;
	const struct bits S  = A; /* state, in main loop */

	print_bits("A", &A);
	print_bits("B", &B);
	print_bits("C", &C);
	print_bits("D", &D);
	print_bits("r", &r);
	print_bits("t", &t);
	print_bits("RC", &RC);
	print_bits("P", &P);
	print_bits("O", &O);

	static const unsigned char out_r40[][10] = {
		[1] = { 0xe9, 0xf5, 0x7f, 0x02, 0xa9, 0xb0, 0xeb, 0xd8, 0x44, 0x98 },
		[2] = { 0x02, 0x4a, 0x55, 0x18, 0xe1, 0xe9, 0x5d, 0xb5, 0x32, 0x19 },
	};

	static const unsigned rotation_offsets[5][5] = {
		{  0,  1, 62, 28, 27 },
		{ 36, 44,  6, 55, 20 },
		{  3, 10, 43, 25, 39 },
		{ 41, 45, 15, 21,  8 },
		{ 18,  2, 61, 56, 14 }
	};

	static const uint64_t keccak_rc[24] = {
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


#define A(x,y)	(A.o + ((x) + (y)*5)*z)
#define B(x,y)	(B.o + ((x) + (y)*5)*z)
#define C(x)	(C.o + (x)*z)
#define D(x)	(D.o + (x)*z)

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
		{ XOR, z, A(0,0), A(0,0), r.o },
	};
	struct operation keccak_f[3*rounds];
	unsigned i;
	for (i=0; i<rounds; i++) {
		struct operation loop[] = {
			{ SET0, z, r.o, r.o },
			{ XOR, z, r.o, r.o, RC.o + i * z },
			{ CALL, ARRAY_SIZE(keccak_round), .tgt = keccak_round },
		};
		memcpy(keccak_f + 3*i, loop, sizeof(loop));
	}

	unsigned nops = sizeof(keccak_round)/sizeof(*keccak_round);
	fprintf(stderr, "%u, %u\n", nops, total_bits);

	bb_t *bb = calloc((total_bits + bb_t_bits - 1) / bb_t_bits, sizeof(bb_t));

	bits_set(bb, 0, &A);
	bits_set(bb, 0, &B);
	bits_set(bb, 0, &C);
	bits_set(bb, 0, &D);
	bits_set(bb, 0, &t);

	for (i=0; i<rounds; i++)
		bb_put(bb, keccak_rc[i], RC.o + z * i, z);

	const unsigned char (*out)[10] = out_r40 + rounds;
	for (i=0; i<ARRAY_SIZE(*out); i++)
		bb_put(bb, (*out)[i], O.o + i * 8, 8);

	const struct operation keccak_test[] = {
		{ VAR, P.n, P.o },
		{ SET0, S.n, S.o },
		{ LOAD, RC.n, RC.o, RC.o, .v = bb },
		{ LOAD,  O.n,  O.o,  O.o, .v = bb },

		{ XOR, k_r, S.o, P.o + 0 * k_r },
		{ CALL, ARRAY_SIZE(keccak_f), .tgt = keccak_f },
		{ XOR, k_r, S.o, P.o + 1 * k_r },
		{ CALL, ARRAY_SIZE(keccak_f), .tgt = keccak_f },

		{ EXPECT, k_r, S.o, O.o + 0 * k_r },
		{ CALL, ARRAY_SIZE(keccak_f), .tgt = keccak_f },
		{ EXPECT, k_r, S.o, O.o + 1 * k_r },
	};

	struct operation run = {
		CALL,
		ARRAY_SIZE(keccak_test),
		.tgt = keccak_test
	};

	int ret;
#if 1
	struct opxform *x = opx_init(total_bits);
	struct dimacs_cnf cnf = { 0, 0, NULL, 0 };
	ret = opx_exec(x, &run, &cnf);
#else
	ret = exec(bb, &run);
#endif

	cnf.v = x->xf_n;

	dimacs_cnf_print(stdout, &cnf);

	return ret;
}
#endif