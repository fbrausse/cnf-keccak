
#ifndef COMMON_H
#define COMMON_H

#include <stdlib.h>
#include <stdarg.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>

#define ARRAY_SIZE(arr)		(sizeof(arr)/sizeof(*(arr)))
#define STR(x)			#x
#define XSTR(x)			STR(x)

static void darray_ensure(
	void **darr, unsigned *sz, unsigned elem_sz, unsigned new_n
) {
	unsigned nsz;
	if (new_n < *sz)
		return;
	nsz = 2 * new_n;
	if (!(*darr = realloc(*darr, elem_sz * nsz))) {
		perror("realloc");
		exit(EXIT_FAILURE);
	}
	memset((char *)*darr + elem_sz * *sz, 0, elem_sz * (nsz - *sz));
	*sz = nsz;
}

#define darr_ensure(darr,sz,new_n) \
	darray_ensure((void **)&(darr), &(sz), sizeof(*(darr)), (new_n))

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
#if 1
	darr_ensure(cnf->cl, cnf->cl_sz, n + 1);
#else
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
#endif
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

#define dimacs_cnf_addn(cnf, ...)                         \
	dimacs_cnf_add(cnf, clause_create(                \
		ARRAY_SIZE(((signed []){ __VA_ARGS__ })), \
		__VA_ARGS__))

static void dimacs_cnf_eq(struct dimacs_cnf *cnf, signed a, signed b)
{
	dimacs_cnf_addn(cnf,  a, -b);
	dimacs_cnf_addn(cnf, -a,  b);
}

typedef int bit_out_f(void *p, enum op_t op, unsigned a, signed ta, signed tb);
typedef int constr_out_f(void *p, unsigned n, const signed *l);

struct out {
	bit_out_f *bit_out;
	constr_out_f *constr_out;
	void *p;
};

static int dimacs_cnf_constr_out(void *p, unsigned n, const signed *l)
{
	struct dimacs_cnf *cnf = p;
	struct clause *c = malloc(offsetof(struct clause,l) + sizeof(signed)*n);
	c->n = n;
	memcpy(c->l, l, sizeof(signed)*n);
	dimacs_cnf_add(cnf, c);
	return 0;
}

static int dimacs_cnf_bit_out(void *p, enum op_t op, unsigned a, signed ta, signed tb)
{
	struct dimacs_cnf *cnf = p;

	switch (op) {
	case AND:
		/* express a = ax->a*ax->b */
		dimacs_cnf_addn(cnf,  ta,      -a);
		dimacs_cnf_addn(cnf,       tb, -a);
		dimacs_cnf_addn(cnf, -ta, -tb,  a);
		break;
	case OR:
		/* express a = ax->a+ax->b */
		dimacs_cnf_addn(cnf, -ta,       a);
		dimacs_cnf_addn(cnf,      -tb,  a);
		dimacs_cnf_addn(cnf,  ta,  tb, -a);
		break;
	case XOR:
		/* express a = ax->a^ax->b */
		dimacs_cnf_addn(cnf, -ta,  tb,  a);
		dimacs_cnf_addn(cnf, -ta, -tb, -a);
		dimacs_cnf_addn(cnf,  ta,  tb, -a);
		dimacs_cnf_addn(cnf,  ta, -tb,  a);
		break;
	case NOT:
		/* express a = -ax->a */
		dimacs_cnf_addn(cnf,  ta,  a);
		dimacs_cnf_addn(cnf, -ta, -a);
		// dimacs_cnf_eq(&cnf, a, -ax->a);
		break;
	case SET:
		/* express a = ax->a */
		dimacs_cnf_addn(cnf, -ta,  a);
		dimacs_cnf_addn(cnf,  ta, -a);
		// dimacs_cnf_eq(&cnf, a, ax->a);
		break;
	case VAR:
		break;
	default:
		abort();
		return 1;
	}

	return 0;
}

#endif
