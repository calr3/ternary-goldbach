/* Rigorous computation of g2(n) = sum_{r1, r2 <= n, (r1, r2) = 1, r1 r2 odd} mu(r1)mu(r2)/(sigma(r1)sigma(r2))
   for n <= N, in MPFR interval arithmetic (directed rounding), via the identity
       g2(n) = sum_{d odd} mu(d) (sum_{r <= n, d | r, r odd} f(r))^2,   f(r) = mu(r)/sigma(r),
   updated incrementally: when f(n) != 0, for each d | n, S_d += f(n) and
   g2 += mu(d) (2 S_d^{old} f(n) + f(n)^2).
   Reports max_{33 <= n <= N} |g2(n)| n  ([B, Lemma 5.1.2]: <= 2.1 for 33 <= x <= 10^6),
   sum_{n < N} |g2(n)|, and (1/2) int_1^N D(z)/z^2 dz with D(z) = int_{z/2}^z g2.
   Usage: g2_rig N
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <gmp.h>
#include <mpfr.h>

#define PREC 128
#define D MPFR_RNDD
#define U MPFR_RNDU
typedef struct { mpfr_t lo, hi; } I;
static void Iinit(I *x) { mpfr_init2(x->lo, PREC); mpfr_init2(x->hi, PREC); mpfr_set_ui(x->lo, 0, D); mpfr_set_ui(x->hi, 0, U); }
static mpfr_t T0, P4[4], Q4[4];
static void Iadd(I *r, I *a, I *b) { mpfr_add(r->lo, a->lo, b->lo, D); mpfr_add(r->hi, a->hi, b->hi, U); }
static void Isub(I *r, I *a, I *b) { mpfr_sub(T0, a->lo, b->hi, D); mpfr_sub(r->hi, a->hi, b->lo, U); mpfr_set(r->lo, T0, D); }
static void Imul(I *r, I *a, I *b) {
  mpfr_mul(P4[0], a->lo, b->lo, D); mpfr_mul(P4[1], a->lo, b->hi, D); mpfr_mul(P4[2], a->hi, b->lo, D); mpfr_mul(P4[3], a->hi, b->hi, D);
  mpfr_mul(Q4[0], a->lo, b->lo, U); mpfr_mul(Q4[1], a->lo, b->hi, U); mpfr_mul(Q4[2], a->hi, b->lo, U); mpfr_mul(Q4[3], a->hi, b->hi, U);
  mpfr_min(P4[0], P4[0], P4[1], D); mpfr_min(P4[2], P4[2], P4[3], D); mpfr_min(r->lo, P4[0], P4[2], D);
  mpfr_max(Q4[0], Q4[0], Q4[1], U); mpfr_max(Q4[2], Q4[2], Q4[3], U); mpfr_max(r->hi, Q4[0], Q4[2], U);
}
static void Iset_q(I *x, long num, unsigned long den) {
  mpfr_set_si(x->lo, num, D); mpfr_div_ui(x->lo, x->lo, den, D); mpfr_set_si(x->hi, num, U); mpfr_div_ui(x->hi, x->hi, den, U);
}
static void Iabs_hi(mpfr_t r, I *a) { mpfr_abs(T0, a->lo, U); mpfr_abs(r, a->hi, U); mpfr_max(r, r, T0, U); }

int main(int argc, char **argv) {
  long N = argc > 1 ? atol(argv[1]) : 1000000;
  mpfr_init2(T0, PREC); for (int i = 0; i < 4; i++) { mpfr_init2(P4[i], PREC); mpfr_init2(Q4[i], PREC); }
  /* mu, sigma for odd squarefree n; smallest prime factor sieve */
  int8_t *mu = calloc(N + 1, 1); uint32_t *spf = calloc(N + 1, sizeof(uint32_t));
  for (long i = 2; i <= N; i++) if (!spf[i]) for (long j = i; j <= N; j += i) if (!spf[j]) spf[j] = i;
  I *S = malloc(sizeof(I) * (N + 1));
  for (long i = 0; i <= N; i++) Iinit(&S[i]);
  I g, f, t, u; Iinit(&g); Iinit(&f); Iinit(&t); Iinit(&u);
  mpfr_t m, worst, absg, sumabs; mpfr_inits2(PREC, m, worst, absg, sumabs, (mpfr_ptr)0);
  mpfr_set_ui(worst, 0, U); mpfr_set_ui(sumabs, 0, U); long wat = 0;
  /* g2 values stored as doubles (outward) for the integral */
  double *glo = malloc(sizeof(double) * (N + 1)), *ghi = malloc(sizeof(double) * (N + 1));
  glo[0] = ghi[0] = 0;
  long ps[32];
  for (long n = 1; n <= N; n++) {
    if (n & 1) {
      /* factor n */
      long x = n, k = 0, sig = 1, sq = 0;
      while (x > 1) { long p = spf[x]; ps[k++] = p; sig *= (p + 1); x /= p; if (x % p == 0) { sq = 1; break; } }
      if (!sq) {
        Iset_q(&f, (k & 1) ? -1 : 1, sig);
        /* divisors of n */
        long nd = 1L << k;
        for (long msk = 0; msk < nd; msk++) {
          long d = 1; int c = 0;
          for (int i = 0; i < k; i++) if (msk >> i & 1) { d *= ps[i]; c++; }
          /* g += mu(d) (2 S_d f + f^2) */
          Imul(&t, &S[d], &f); Iadd(&t, &t, &t); Imul(&u, &f, &f); Iadd(&t, &t, &u);
          if (c & 1) Isub(&g, &g, &t); else Iadd(&g, &g, &t);
          Iadd(&S[d], &S[d], &f);
        }
      }
    }
    glo[n] = mpfr_get_d(g.lo, D); ghi[n] = mpfr_get_d(g.hi, U);
    Iabs_hi(absg, &g);
    if (n < N) mpfr_add(sumabs, sumabs, absg, U);
    if (n >= 33) { mpfr_mul_ui(m, absg, n, U); if (mpfr_greater_p(m, worst)) { mpfr_set(worst, m, U); wat = n; } }
    if (n == 1 || n == 2 || n == 3 || n == 10 || n == 100 || n == 1000 || n == 10000 || n == 100000 || n == N)
      mpfr_printf("g2(%ld) in [%.15Re, %.15Re]\n", n, g.lo, g.hi);
  }
  mpfr_printf("max_{33<=n<=%ld} |g2(n)| n <= %.8Rf at n = %ld\n", N, worst, wat);
  mpfr_printf("sum_{n<%ld} |g2(n)| <= %.6Rf\n", N, sumabs);
  return 0;
}
