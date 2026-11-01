/* Rigorous checks for T2 (MinorArcs/T2Bound.lean), in MPFR interval arithmetic (directed rounding).

   g2(n) = sum_{r1, r2 <= n, (r1, r2) = 1, r1 r2 odd} mu(r1)mu(r2)/(sigma(r1)sigma(r2))  (g2(x) = g2(floor x)),
   computed for n <= Z by the incremental identity g2(n) = sum_{d odd} mu(d) (sum_{r<=n, d|r} f(r))^2,
   f(r) = mu(r)/sigma(r) (r odd): when f(n) != 0, for each d | n: g2 += mu(d)(2 S_d f(n) + f(n)^2),
   S_d += f(n).

   Checks (the axioms `T2_small`, `T2_mid` in T2Bound.lean):
   (1) T2(S) <= 0.37273 for 16 <= S < 10^5.  On [n, n+1), T2(S) = alpha_n + beta_n/S with
         alpha_n = sum_{s odd <= n} (g2(n div s)/s - g2(n div 2s)/(2s)),
         beta_n  = sum_{s odd <= n} (Cg(n div s) - Cg(n div 2s)),  Cg(k) = sum_{j<k} g2(j) - k g2(k)
       ([B, (5.29)]; for n <= 15 this is Lean's `T2_eq`); alpha + beta/S is monotone in S, so both
       ends of each piece are checked.
   (2) (1/4) int_1^S g2(y)/y dy <= 0.3607 for 10^5 <= S <= Z.  On [m, m+1] the integral is
       A(m) + g2(m) log(S/m)/4, monotone in S, with A(m) = (1/4) sum_{j<m} g2(j) log(1 + 1/j); so it
       suffices that A(m) <= 0.3607 for 10^5 <= m <= Z.
   (3) int_1^Z |g2| = sum_{j<Z} |g2(j)| <= 10.5.
   (4) For information: max |g2(n)| n on [33, Z], and [B, Lemma 5.1.2]'s bound on [10^6, Z].

   Usage: t2_rig [Z]   (Z = 10^8 by default; about 10 minutes, ~6 GB)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <gmp.h>
#include <mpfr.h>

#define PREC 64
#define D MPFR_RNDD
#define U MPFR_RNDU
typedef struct { mpfr_t lo, hi; } I;
static mpfr_t T0, P4[4], Q4[4];
static void Iinit(I *x) { mpfr_init2(x->lo, PREC); mpfr_init2(x->hi, PREC); mpfr_set_ui(x->lo, 0, D); mpfr_set_ui(x->hi, 0, U); }
static void Iset(I *r, I *a) { mpfr_set(r->lo, a->lo, D); mpfr_set(r->hi, a->hi, U); }
static void Iadd(I *r, I *a, I *b) { mpfr_add(r->lo, a->lo, b->lo, D); mpfr_add(r->hi, a->hi, b->hi, U); }
static void Isub(I *r, I *a, I *b) { mpfr_sub(T0, a->lo, b->hi, D); mpfr_sub(r->hi, a->hi, b->lo, U); mpfr_set(r->lo, T0, D); }
static void Imul(I *r, I *a, I *b) {
  mpfr_mul(P4[0], a->lo, b->lo, D); mpfr_mul(P4[1], a->lo, b->hi, D); mpfr_mul(P4[2], a->hi, b->lo, D); mpfr_mul(P4[3], a->hi, b->hi, D);
  mpfr_mul(Q4[0], a->lo, b->lo, U); mpfr_mul(Q4[1], a->lo, b->hi, U); mpfr_mul(Q4[2], a->hi, b->lo, U); mpfr_mul(Q4[3], a->hi, b->hi, U);
  mpfr_min(P4[0], P4[0], P4[1], D); mpfr_min(P4[2], P4[2], P4[3], D); mpfr_min(r->lo, P4[0], P4[2], D);
  mpfr_max(Q4[0], Q4[0], Q4[1], U); mpfr_max(Q4[2], Q4[2], Q4[3], U); mpfr_max(r->hi, Q4[0], Q4[2], U);
}
static void Idiv_ui(I *r, I *a, unsigned long d) { mpfr_div_ui(r->lo, a->lo, d, D); mpfr_div_ui(r->hi, a->hi, d, U); }
static void Imul_ui(I *r, I *a, unsigned long d) { mpfr_mul_ui(r->lo, a->lo, d, D); mpfr_mul_ui(r->hi, a->hi, d, U); }
static void Iset_q(I *x, long num, unsigned long den) {
  mpfr_set_si(x->lo, num, D); mpfr_div_ui(x->lo, x->lo, den, D); mpfr_set_si(x->hi, num, U); mpfr_div_ui(x->hi, x->hi, den, U);
}

int main(int argc, char **argv) {
  long Z = argc > 1 ? atol(argv[1]) : 100000000L;
  const long NT = 100000;               /* range of check (1) */
  mpfr_init2(T0, PREC); for (int i = 0; i < 4; i++) { mpfr_init2(P4[i], PREC); mpfr_init2(Q4[i], PREC); }
  uint32_t *spf = calloc(Z + 1, sizeof(uint32_t));
  for (long i = 2; i <= Z; i++) if (!spf[i]) for (long j = i; j <= Z; j += i) if (!spf[j]) spf[j] = (uint32_t)i;
  /* S_d for odd d, index d/2 */
  long nS = Z / 2 + 1;
  I *S = malloc(sizeof(I) * nS);
  for (long i = 0; i < nS; i++) Iinit(&S[i]);
  /* g2(n) for n <= NT kept exactly (intervals) for check (1); doubles (outward) for n <= Z */
  I *gs = malloc(sizeof(I) * (NT + 2));
  for (long i = 0; i <= NT + 1; i++) Iinit(&gs[i]);
  I g, f, t, u, A, w; Iinit(&g); Iinit(&f); Iinit(&t); Iinit(&u); Iinit(&A); Iinit(&w);
  mpfr_t ab, m, worst, sumabs, maxA, l512; mpfr_inits2(PREC, ab, m, worst, sumabs, maxA, l512, (mpfr_ptr)0);
  mpfr_set_ui(worst, 0, U); mpfr_set_ui(sumabs, 0, U); mpfr_set_si(maxA, -10, U);
  long wat = 0, maxAat = 0; int lemma_ok = 1;
  long ps[32];
  for (long n = 1; n <= Z; n++) {
    /* A(n) = (1/4) sum_{j<n} g2(j) log(1+1/j): add the j = n-1 term (g2(0) = 0) */
    if (n >= 2) {
      long j = n - 1;
      /* log(1 + 1/j) in [1/j - 1/(2j^2), 1/j] for j >= 2^10; MPFR log1p below */
      if (j < 1024) {
        mpfr_set_ui(w.lo, 1, D); mpfr_div_ui(w.lo, w.lo, j, D); mpfr_log1p(w.lo, w.lo, D);
        mpfr_set_ui(w.hi, 1, U); mpfr_div_ui(w.hi, w.hi, j, U); mpfr_log1p(w.hi, w.hi, U);
      } else {
        mpfr_set_ui(w.lo, 2 * j - 1, D); mpfr_div_ui(w.lo, w.lo, 2 * j, D); mpfr_div_ui(w.lo, w.lo, j, D);
        mpfr_set_ui(w.hi, 1, U); mpfr_div_ui(w.hi, w.hi, j, U);
      }
      Imul(&t, &g, &w); Idiv_ui(&t, &t, 4); Iadd(&A, &A, &t);
      if (n >= NT && mpfr_greater_p(A.hi, maxA)) { mpfr_set(maxA, A.hi, U); maxAat = n; }
    }
    if (n & 1) {
      long x = n, k = 0, sig = 1, sq = 0;
      while (x > 1) { long p = spf[x]; ps[k++] = p; sig *= (p + 1); x /= p; if (x % p == 0) { sq = 1; break; } }
      if (!sq) {
        Iset_q(&f, (k & 1) ? -1 : 1, sig);
        long nd = 1L << k;
        for (long msk = 0; msk < nd; msk++) {
          long d = 1; int c = 0;
          for (int i = 0; i < k; i++) if (msk >> i & 1) { d *= ps[i]; c++; }
          I *Sd = &S[d / 2];
          Imul(&t, Sd, &f); Iadd(&t, &t, &t); Imul(&u, &f, &f); Iadd(&t, &t, &u);
          if (c & 1) Isub(&g, &g, &t); else Iadd(&g, &g, &t);
          Iadd(Sd, Sd, &f);
        }
      }
    }
    if (n <= NT + 1) Iset(&gs[n], &g);
    mpfr_abs(T0, g.lo, U); mpfr_abs(ab, g.hi, U); mpfr_max(ab, ab, T0, U);
    if (n < Z) mpfr_add(sumabs, sumabs, ab, U);
    if (n >= 33) { mpfr_mul_ui(m, ab, n + 1, U); if (mpfr_greater_p(m, worst)) { mpfr_set(worst, m, U); wat = n; } }
    if (n >= 1000000) {   /* [B, Lemma 5.1.2]: |g2(x)| <= (1634.34 + 817.168 log x)/x on [10^6, 10^10) */
      double lb = (1634.34 + 817.168 * log((double)n)) / (double)(n + 1);
      if (mpfr_cmp_d(ab, lb * 0.999) > 0) lemma_ok = 0;
    }
  }
  mpfr_printf("g2(%ld) in [%.12Re, %.12Re]\n", Z, g.lo, g.hi);
  mpfr_printf("(3) sum_{j<Z} |g2(j)| <= %.6Rf   (need <= 10.5)\n", sumabs);
  mpfr_printf("(2) max_{10^5 <= m <= Z} A(m) <= %.9Rf at m = %ld   (need <= 0.3607)\n", maxA, maxAat);
  mpfr_printf("(4) max_{33<=n<=Z} |g2(n)|(n+1) <= %.7Rf at n = %ld;  [B, Lemma 5.1.2] bound on [10^6, Z]: %s\n",
              worst, wat, lemma_ok ? "holds" : "VIOLATED");
  int ok2 = mpfr_cmp_d(maxA, 0.3607) <= 0, ok3 = mpfr_cmp_d(sumabs, 10.5) <= 0;

  /* (1): T2 on [16, NT) */
  I *Cg = malloc(sizeof(I) * (NT + 2));   /* Cg(k) = sum_{j<k} g2(j) - k g2(k) */
  I run; Iinit(&run);
  for (long k = 0; k <= NT; k++) {
    Iinit(&Cg[k]); Imul_ui(&t, &gs[k], k); Isub(&Cg[k], &run, &t); Iadd(&run, &run, &gs[k]);
  }
  I al, be, v; Iinit(&al); Iinit(&be); Iinit(&v);
  mpfr_t wT; mpfr_init2(wT, PREC); mpfr_set_si(wT, -10, U); long wTat = 0; int ok1 = 1;
  for (long n = 16; n < NT; n++) {
    mpfr_set_ui(al.lo, 0, D); mpfr_set_ui(al.hi, 0, U); mpfr_set_ui(be.lo, 0, D); mpfr_set_ui(be.hi, 0, U);
    for (long s = 1; s <= n; s += 2) {
      long k1 = n / s, k2 = n / (2 * s);
      Idiv_ui(&t, &gs[k1], s); Iadd(&al, &al, &t);
      Idiv_ui(&t, &gs[k2], 2 * s); Isub(&al, &al, &t);
      Iadd(&be, &be, &Cg[k1]); Isub(&be, &be, &Cg[k2]);
    }
    for (int e = 0; e < 2; e++) {
      Idiv_ui(&t, &be, n + e); Iadd(&v, &al, &t);
      if (mpfr_greater_p(v.hi, wT)) { mpfr_set(wT, v.hi, U); wTat = n + e; }
      if (mpfr_cmp_d(v.hi, 0.37273) > 0) { ok1 = 0; printf("T2 bound fails near S = %ld\n", n + e); }
    }
  }
  mpfr_printf("(1) max_{16 <= S <= 10^5} T2(S) <= %.7Rf at S = %ld   (need <= 0.37273)\n", wT, wTat);
  printf("T2_small: %s\nT2_mid: %s\n", ok1 ? "OK (rigorous)" : "FAILED", (ok2 && ok3) ? "OK (rigorous)" : "FAILED");
  return !(ok1 && ok2 && ok3);
}
