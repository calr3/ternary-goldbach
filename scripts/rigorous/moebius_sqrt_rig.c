/* Rigorous check of the Moebius bound behind [H, (2.24)] (Lean uses it for k < 11815, Prelim/SmallMoebius.lean):

       |m(k)| <= sqrt(2/(k+1))  for 1 <= k < 10^10,   m(k) = sum_{n <= k} mu(n)/n,

   i.e. [H, (2.24)] |m(x)| <= sqrt(2/x) for real x < 10^10 (Helfgott checked x <= 10^12 in interval
   arithmetic; Ramare earlier x <= 10^10).

   mu(n) comes from a segmented sieve (exact integers).  The sum is enclosed in [lo, hi] using IEEE
   double arithmetic in round-down mode only: lo accumulates mu(n)/n rounded down, and nhi accumulates
   -mu(n)/n rounded down, so hi = -nhi >= m(k).  Each operation is a correctly rounded IEEE operation,
   so lo <= m(k) <= hi exactly.  The test M^2 (k+1) <= 2 with M = max(|lo|, |hi|) is done with upward
   rounding (as -((-a) b) in round-down mode).

   Cross-check with [H, p. 38]: the stronger bound |m(x)| <= 1/(2 sqrt x) holds for 3 <= x <= 7727068587
   but not for x = 7727068588 - eps; i.e. 4 m(k)^2 (k+1) <= 1 for 3 <= k <= 7727068586 and > 1 at
   k = 7727068587.

   Build: sh scripts/rigorous/build.sh   Run: scripts/rigorous/moebius_sqrt_rig   (a few minutes)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <fenv.h>

static double up_mul(double a, double b) { return -((-a) * b); }   /* a*b rounded up (round-down mode) */

int main(void) {
  const uint64_t N = 10000000000ULL;          /* k < N */
  const uint32_t P = 100000;                  /* sqrt(N) */
  char *c = calloc(P + 1, 1); uint32_t *pr = malloc(sizeof(uint32_t) * P); size_t np = 0;
  for (uint32_t i = 2; i <= P; i++) { if (c[i]) continue; pr[np++] = i; for (uint64_t j = (uint64_t)i * i; j <= P; j += i) c[j] = 1; }
  const uint64_t S = 1 << 24;
  int8_t *mu = malloc(S); uint64_t *prod = malloc(S * sizeof(uint64_t));
  if (fesetround(FE_DOWNWARD) != 0) { fprintf(stderr, "fesetround failed\n"); return 2; }
  double lo = 0.0, nhi = 0.0;
  int ok = 1; double worst = 0.0; uint64_t wat = 0;
  uint64_t first_strong = 0; int strong_fails_there = 0; double e_lo = 0, e_hi = 0;
  for (uint64_t base = 1; base < N; base += S) {
    uint64_t len = S; if (base + len > N) len = N - base;
    uint64_t end = base + len;                 /* segment [base, end) */
    for (uint64_t i = 0; i < len; i++) { mu[i] = 1; prod[i] = 1; }
    for (size_t t = 0; t < np; t++) {
      uint64_t p = pr[t];
      for (uint64_t m = (base + p - 1) / p * p; m < end; m += p) { mu[m - base] = -mu[m - base]; prod[m - base] *= p; }
      uint64_t q = p * p;
      for (uint64_t m = (base + q - 1) / q * q; m < end; m += q) mu[m - base] = 0;
    }
    for (uint64_t i = 0; i < len; i++) {
      uint64_t n = base + i;
      if (mu[i] != 0 && prod[i] != n) mu[i] = -mu[i];     /* one prime factor > 10^5 */
      double dn = (double)n;                               /* exact: n < 2^53 */
      if (mu[i] == 1) { lo += 1.0 / dn; nhi += -1.0 / dn; }
      else if (mu[i] == -1) { lo += -1.0 / dn; nhi += 1.0 / dn; }
      /* m(n) in [lo, -nhi] */
      double M = fmax(fabs(lo), fabs(nhi));
      double k1 = (double)(n + 1);
      double v = up_mul(up_mul(M, M), k1);                  /* >= m^2 (k+1) */
      if (!(v <= 2.0)) { if (ok) printf("fails at k = %llu\n", (unsigned long long)n); ok = 0; }
      if (n >= 2) { double r = v / 2.0; if (r > worst) { worst = r; wat = n; } }
      if (n >= 3 && first_strong == 0 && !(4.0 * v <= 1.0)) {
        first_strong = n;
        /* lower bound for |m|: 0 if the interval contains 0 */
        double mlo = (lo > 0) ? lo : ((-nhi) < 0 ? nhi : 0.0);   /* nhi = -hi; hi < 0 => |m| >= -hi = nhi */
        double w = mlo * mlo * k1 * 4.0;                     /* rounded down: lower bound of 4 m^2 (k+1) */
        strong_fails_there = (w > 1.0);
        e_hi = up_mul(up_mul(M, M), (double)n) * 4.0;        /* >= 4 m^2 k  (*4 is exact) */
        e_lo = mlo * mlo * (double)n * 4.0;                   /* <= 4 m^2 k */
      }
    }
  }
  fesetround(FE_TONEAREST);
  printf("m(10^10 - 1) in [%.12e, %.12e]\n", lo, -nhi);
  printf("max over 2 <= k < 10^10 of |m(k)|/sqrt(2/(k+1)) <= %.6f at k = %llu (k = 1: equality)\n",
         sqrt(worst) * (1 + 1e-15), (unsigned long long)wat);
  printf("moebius_sqrt_small: %s\n", ok ? "OK (rigorous)" : "FAILED");
  printf("cross-check [H, p. 38]: first k >= 3 with 4 m(k)^2 (k+1) > 1 (not certified <= 1): %llu; "
         "certainly > 1 there: %s; 4 m(k)^2 k in [%.12f, %.12f] there\n",
         (unsigned long long)first_strong, strong_fails_there ? "yes" : "no", e_lo, e_hi);
  return ok ? 0 : 1;
}
