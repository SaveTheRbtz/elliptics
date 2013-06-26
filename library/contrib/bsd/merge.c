/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Peter McIlroy.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *	notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *	notice, this list of conditions and the following disclaimer in the
 *	documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *	may be used to endorse or promote products derived from this software
 *	without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Hybrid exponential search/linear search merge sort with hybrid
 * natural/pairwise first pass.  Requires about .3% more comparisons
 * for random data than LSMS with pairwise first pass alone.
 * It works for objects as small as two bytes.
 */

#define DNET_THRESHOLD 16	/* Best choice for natural merge cut-off. */

#include <sys/types.h>

#include <errno.h>
#include <stdlib.h>
#include <string.h>

static void setup(u_char *, u_char *, size_t, size_t,
	int (*)(const void *, const void *));
static inline void insertionsort(u_char *, size_t, size_t,
	int (*)(const void *, const void *));

#define DNET_ISIZE sizeof(int)
#define DNET_PSIZE sizeof(u_char *)
#define DNET_ICOPY_LIST(src, dst, last)						\
	do									\
	*(int*)dst = *(int*)src, src += DNET_ISIZE, dst += DNET_ISIZE;		\
	while(src < last)
#define DNET_ICOPY_ELT(src, dst, i)						\
	do									\
	*(int*) dst = *(int*) src, src += DNET_ISIZE, dst += DNET_ISIZE;	\
	while (i -= DNET_ISIZE)

/*
 * Find the next possible pointer head.  (Trickery for forcing an array
 * to do double duty as a linked list when objects do not align with word
 * boundaries.
 */
/* Assumption: DNET_PSIZE is a power of 2. */
#define DNET_EVAL(p) (u_char **)						\
	((u_char *)0 + (((u_char *)p + DNET_PSIZE - 1 - (u_char *) 0) & ~(DNET_PSIZE - 1)))

/*
 * Arguments are as for qsort plus + BYOB for temporaral storage
 */
int
dnet_mergesort(void *base, size_t nmemb, size_t size,
		int (*cmp)(const void *, const void *),
		u_char *list2, size_t list2_sz)
{
	size_t i;
	int big, sense;
	u_char *f1, *f2, *t, *b, *tp2, *q, *l1, *l2;
	u_char *list1, *p2, *p, *last, **p1;

	if (size < DNET_PSIZE / 2) /* Pointers must fit into 2 * size. */
		return -EINVAL;

	if (nmemb == 0)
		return 0;

	if (list2_sz < nmemb * size + DNET_PSIZE)
		return -EINVAL;

	list1 = base;
	setup(list1, list2, nmemb, size, cmp);
	last = list2 + nmemb * size;
	i = big = 0;
	while (*DNET_EVAL(list2) != last) {
		l2 = list1;
		p1 = DNET_EVAL(list1);
		for (tp2 = p2 = list2; p2 != last; p1 = DNET_EVAL(l2)) {
			p2 = *DNET_EVAL(p2);
			f1 = l2;
			f2 = l1 = list1 + (p2 - list2);
			if (p2 != last)
				p2 = *DNET_EVAL(p2);
			l2 = list1 + (p2 - list2);
			while (f1 < l1 && f2 < l2) {
				if ((*cmp)(f1, f2) <= 0) {
					q = f2;
					b = f1, t = l1;
					sense = -1;
				} else {
					q = f1;
					b = f2, t = l2;
					sense = 0;
				}
				if (!big) {	/* here i = 0 */
				while ((b += size) < t && cmp(q, b) >sense)
						if (++i == 6) {
							big = 1;
							goto EXPONENTIAL;
						}
				} else {
EXPONENTIAL:				for (i = size; ; i <<= 1)
						if ((p = (b + i)) >= t) {
							if ((p = t - size) > b && (*cmp)(q, p) <= sense)
								t = p;
							else
								b = p;
							break;
						} else if ((*cmp)(q, p) <= sense) {
							t = p;
							if (i == size)
								big = 0;
							goto FASTCASE;
						} else
							b = p;
				while (t > b+size) {
						i = (((t - b) / size) >> 1) * size;
						if ((*cmp)(q, p = b + i) <= sense)
							t = p;
						else
							b = p;
					}
					goto COPY;
FASTCASE:				while (i > size)
						if ((*cmp)(q, p = b + (i >>= 1)) <= sense)
							t = p;
						else
							b = p;
COPY:					b = t;
				}
				i = size;
				if (q == f1) {
					DNET_ICOPY_LIST(f2, tp2, b);
					DNET_ICOPY_ELT(f1, tp2, i);
				} else {
					DNET_ICOPY_LIST(f1, tp2, b);
					DNET_ICOPY_ELT(f2, tp2, i);
				}
			}
			if (f2 < l2) {
				DNET_ICOPY_LIST(f2, tp2, l2);
			} else if (f1 < l1) {
				DNET_ICOPY_LIST(f1, tp2, l1);
			}
			*p1 = l2;
		}
		tp2 = list1;	/* swap list1, list2 */
		list1 = list2;
		list2 = tp2;
		last = list2 + nmemb*size;
	}
	if (base == list2) {
		memmove(list2, list1, nmemb*size);
		list2 = list1;
	}
	return 0;
}

#define	swap(a, b) {					\
		s = b;					\
		i = size;				\
		do {					\
			tmp = *a; *a++ = *s; *s++ = tmp; \
		} while (--i);				\
		a -= size;				\
	}
#define reverse(bot, top) {				\
	s = top;					\
	do {						\
		i = size;				\
		do {					\
			tmp = *bot; *bot++ = *s; *s++ = tmp; \
		} while (--i);				\
		s -= size2;				\
	} while(bot < s);				\
}

/*
 * Optional hybrid natural first pass. Eats up list1 in runs of increasing
 * order, list2 in a corresponding linked list. Checks for runs when
 * DNET_THRESHOLD/2 pairs compare with same sense.
 */
void
setup(list1, list2, n, size, cmp)
	size_t n, size;
	int (*cmp)(const void *, const void *);
	u_char *list1, *list2;
{
	int i, length, size2, tmp, sense;
	u_char *f1, *f2, *s, *l2, *last, *p2;

	size2 = size*2;
	if (n <= 5) {
		insertionsort(list1, n, size, cmp);
		*DNET_EVAL(list2) = (u_char*) list2 + n*size;
		return;
	}
	/*
	 * Avoid running pointers out of bounds; limit n to evens
	 * for simplicity.
	 */
	i = 4 + (n & 1);
	insertionsort(list1 + (n - i) * size, i, size, cmp);
	last = list1 + size * (n - i);
	*DNET_EVAL(list2 + (last - list1)) = list2 + n * size;

	p2 = list2;
	f1 = list1;
	sense = (cmp(f1, f1 + size) > 0);
	for (; f1 < last; sense = !sense) {
		length = 2;
					/* Find pairs with same sense. */
		for (f2 = f1 + size2; f2 < last; f2 += size2) {
			if ((cmp(f2, f2+ size) > 0) != sense)
				break;
			length += 2;
		}
		if (length < DNET_THRESHOLD) {		/* Pairwise merge */
			do {
				p2 = *DNET_EVAL(p2) = f1 + size2 - list1 + list2;
				if (sense > 0)
					swap (f1, f1 + size);
			} while ((f1 += size2) < f2);
		} else {				/* Natural merge */
			l2 = f2;
			for (f2 = f1 + size2; f2 < l2; f2 += size2) {
				if ((cmp(f2-size, f2) > 0) != sense) {
					p2 = *DNET_EVAL(p2) = f2 - list1 + list2;
					if (sense > 0)
						reverse(f1, f2-size);
					f1 = f2;
				}
			}
			if (sense > 0)
				reverse (f1, f2-size);
			f1 = f2;
			if (f2 < last || cmp(f2 - size, f2) > 0)
				p2 = *DNET_EVAL(p2) = f2 - list1 + list2;
			else
				p2 = *DNET_EVAL(p2) = list2 + n*size;
		}
	}
}

/*
 * This is to avoid out-of-bounds addresses in sorting the
 * last 4 elements.
 */
static inline void
insertionsort(u_char *a, size_t n, size_t size,
		int (*cmp)(const void *, const void *))
{
	u_char *ai, *s, *t, *u, tmp;
	int i;

	for (ai = a+size; --n >= 1; ai += size)
		for (t = ai; t > a; t -= size) {
			u = t - size;
			if (cmp(u, t) <= 0)
				break;
			swap(u, t);
		}
}
