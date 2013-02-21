
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

#define CNF_INIT	(struct cnf){ 0, 0, NULL, 0 }
struct cnf {
	unsigned v, c;
	struct clause **cl;
	unsigned cl_sz;
};

static void dimacs_cnf_print(FILE *f, const struct cnf *cnf)
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

static void cnf_add(struct cnf *cnf, struct clause *c)
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

#define cnf_addn(cnf, ...)                                \
	cnf_add(cnf, clause_create(                       \
		ARRAY_SIZE(((signed []){ __VA_ARGS__ })), \
		__VA_ARGS__))

static void cnf_eq(struct cnf *cnf, signed a, signed b)
{
	cnf_addn(cnf,  a, -b);
	cnf_addn(cnf, -a,  b);
}

static void cnf_clause_add(struct cnf *cnf, const signed *v, unsigned n)
{
	struct clause *c = malloc(offsetof(struct clause,l) + sizeof(signed)*n);
	if (!c) {
		perror("malloc");
		exit(EXIT_FAILURE);
	}
	c->n = n;
	memcpy(c->l, v, sizeof(signed)*n);
	cnf_add(cnf, c);
}

static void cnf_read_dimacs(struct cnf *cnf, FILE *f)
{
	char *line = NULL;
	size_t size = 0;
	ssize_t len;
	unsigned have_p = 0;
	char *vline = NULL;
	signed v;
	signed *va = NULL;
	unsigned va_n = 0;
	unsigned va_sz = 0;
	unsigned c_n, v_n;
	int k;

	while ((len = getline(&line, &size, f)) > 0) {
		switch (line[0]) {
		case 'c':
			continue;
		case 'p':
			if (have_p) {
				fprintf(stderr, "double 'p' line, aborting\n");
				exit(EXIT_FAILURE);
			}
			if (sscanf(line + 1, "%s %u %u", line, &v_n, &c_n) < 3) {
				fprintf(stderr, "invalid 'p' line, aborting\n");
				exit(EXIT_FAILURE);
			}
			have_p = 1;
			continue;
		default:
			break;
		}
		for (vline = line; sscanf(vline, "%d%n", &v, &k) >= 1; vline += k) {
			if (v) {
				darr_ensure(va, va_sz, va_n + 1);
				va[va_n++] = v;
			} else if (va_n) {
				cnf_clause_add(cnf, va, va_n);
				va_n = 0;
			} else {
				fprintf(stderr, "error: clause %u empty\n", cnf->c);
				exit(EXIT_FAILURE);
			}
		}
	}
	free(line);

	if (va_n > 0) {
		fprintf(stderr, "warning: last dimacs clause not finished by '0'\n");
		cnf_clause_add(cnf, va, va_n);
	}

	if (v_n != cnf->v || c_n != cnf->c)
		fprintf(stderr,
			"warning: #clauses/#variables (%u/%u) doesn't match "
			"dimacs header (%u/%u)\n",
			cnf->c, cnf->v, c_n, v_n);
}

#endif
