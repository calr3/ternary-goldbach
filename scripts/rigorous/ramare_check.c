/* Independent checks of [Ram95, Lemma 3.4] = [H, (12.12)] (proved in Lean, Prelim/Ramare.lean):

   (a) c_E = gamma + sum_p log p/(p(p-1)) lies in [1.3325822, 1.3325823] ([Ram95, (3.6)] gives
       1.332582275332...).  Rigorous: MPFR sums over the primes p <= P = 1e9 (rounded down / up),
       MPFR's Euler constant, and the tail
         sum_{p > P} log p/(p(p-1)) <= P/(P-1) sum_{p > P} log p/p^2 <= P/(P-1) * 2 * 1.04 / P,
       by partial summation with theta(t) <= psi(t) <= 1.03883 t (proved in Lean: `psiN_le`).

   (b) For every d in a test set (all d <= 2000 and the primorials 30030, 510510, 9699690) and every
       real X in [1, N], N = 2e6:
         |G_d(X) - (phi(d)/d)(log X + c + S_d)| <= 7.284 X^(-1/3) f1(d)  for all c in [1.3325822, 1.3325823].
       For X in [n, n+1), G_d(X) = G_d(n); it suffices that G_d(n) - M(n) and M(n+1) - G_d(n) are at
       most 7.284 (n+1)^(-1/3) f1(d), where M(X) is the main term.  Interval arithmetic: IEEE double
       with upward rounding (lower bounds via negation), MPFR for logarithms and cube roots.
       This is a numerical test of the published lemma on a finite range, not a proof.

   Usage: ramare_check [threads]
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <fenv.h>
#include <omp.h>
#include <gmp.h>
#include <mpfr.h>

static inline double dn_add(double a, double b) { return -((-a) - b); }
static inline double dn_sub(double a, double b) { return -((-a) + b); }
static inline double dn_mul(double a, double b) { return -((-a) * b); }
static inline double dn_div(double a, double b) { return -((-a) / b); }

static double dlo(const char *s) { mpfr_t x; mpfr_init2(x, 128); mpfr_set_str(x, s, 10, MPFR_RNDD); double r = mpfr_get_d(x, MPFR_RNDD); mpfr_clear(x); return r; }
static double dhi(const char *s) { mpfr_t x; mpfr_init2(x, 128); mpfr_set_str(x, s, 10, MPFR_RNDU); double r = mpfr_get_d(x, MPFR_RNDU); mpfr_clear(x); return r; }

int main(int argc, char **argv) {
  int nth = argc > 1 ? atoi(argv[1]) : 22;
  omp_set_num_threads(nth);
  /* ---------- (a) c_E ---------- */
  const long P = 1000000000L;
  char *comp = calloc(P + 1, 1);
  for (long i = 2; i * i <= P; i++) if (!comp[i]) for (long j = i * i; j <= P; j += i) comp[j] = 1;
  mpfr_t Slo, Shi; mpfr_init2(Slo, 128); mpfr_init2(Shi, 128); mpfr_set_ui(Slo, 0, MPFR_RNDN); mpfr_set_ui(Shi, 0, MPFR_RNDN);
  #pragma omp parallel
  {
    mpfr_t a, b, lo, hi; mpfr_inits2(128, a, b, lo, hi, (mpfr_ptr)0);
    mpfr_set_ui(lo, 0, MPFR_RNDN); mpfr_set_ui(hi, 0, MPFR_RNDN);
    #pragma omp for schedule(dynamic, 1000000)
    for (long p = 2; p <= P; p++) if (!comp[p]) {
      mpfr_set_ui(a, p, MPFR_RNDN);
      mpfr_log(b, a, MPFR_RNDD); mpfr_div_ui(b, b, p, MPFR_RNDD); mpfr_div_ui(b, b, p - 1, MPFR_RNDD); mpfr_add(lo, lo, b, MPFR_RNDD);
      mpfr_log(b, a, MPFR_RNDU); mpfr_div_ui(b, b, p, MPFR_RNDU); mpfr_div_ui(b, b, p - 1, MPFR_RNDU); mpfr_add(hi, hi, b, MPFR_RNDU);
    }
    #pragma omp critical
    { mpfr_add(Slo, Slo, lo, MPFR_RNDD); mpfr_add(Shi, Shi, hi, MPFR_RNDU); }
    mpfr_clears(a, b, lo, hi, (mpfr_ptr)0);
  }
  free(comp);
  mpfr_t g, t, cLo, cHi; mpfr_inits2(128, g, t, cLo, cHi, (mpfr_ptr)0);
  mpfr_const_euler(g, MPFR_RNDD); mpfr_add(cLo, Slo, g, MPFR_RNDD);
  mpfr_const_euler(g, MPFR_RNDU); mpfr_add(cHi, Shi, g, MPFR_RNDU);
  /* tail <= P/(P-1) * 2.08 / P = 2.08/(P-1) */
  mpfr_set_d(t, 2.08, MPFR_RNDU); mpfr_div_ui(t, t, P - 1, MPFR_RNDU); mpfr_add(cHi, cHi, t, MPFR_RNDU);
  mpfr_printf("(a) c_E in [%.12Rf, %.12Rf]  (Ramare (3.6): 1.332582275332...)\n", cLo, cHi);
  int okA = mpfr_cmp_d(cLo, 1.3325822) >= 0 && mpfr_cmp_d(cHi, 1.3325823) <= 0;
  /* the doubles 1.3325822, 1.3325823 are not exact; compare against decimal strings via MPFR */
  { mpfr_t b1, b2; mpfr_init2(b1, 128); mpfr_init2(b2, 128);
    mpfr_set_str(b1, "1.3325822", 10, MPFR_RNDU); mpfr_set_str(b2, "1.3325823", 10, MPFR_RNDD);
    okA = mpfr_cmp(cLo, b1) >= 0 && mpfr_cmp(cHi, b2) <= 0; mpfr_clear(b1); mpfr_clear(b2); }
  printf("(a) %s\n", okA ? "OK" : "FAILED");

  /* ---------- (b) (12.12) on a finite range ---------- */
  const long N = 2000000;
  double *LNlo = malloc(8 * (N + 2)), *LNhi = malloc(8 * (N + 2)), *ICl = malloc(8 * (N + 2));
  double *Flo = malloc(8 * (N + 1)), *Fhi = malloc(8 * (N + 1));
  #pragma omp parallel
  {
    mpfr_t x, y; mpfr_init2(x, 128); mpfr_init2(y, 128);
    #pragma omp for
    for (long n = 1; n <= N + 1; n++) {
      mpfr_set_ui(x, n, MPFR_RNDN);
      mpfr_log(y, x, MPFR_RNDD); LNlo[n] = mpfr_get_d(y, MPFR_RNDD);
      mpfr_log(y, x, MPFR_RNDU); LNhi[n] = mpfr_get_d(y, MPFR_RNDU);
      mpfr_cbrt(y, x, MPFR_RNDU); mpfr_ui_div(y, 1, y, MPFR_RNDD); ICl[n] = mpfr_get_d(y, MPFR_RNDD);  /* n^(-1/3) low */
    }
    mpfr_clear(x); mpfr_clear(y);
  }
  {
    uint32_t *phi = malloc(4 * (N + 1)); char *sqf = malloc(N + 1);
    for (long i = 0; i <= N; i++) { phi[i] = i; sqf[i] = 1; }
    for (long i = 2; i <= N; i++) if (phi[i] == (uint32_t)i) {
      for (long j = i; j <= N; j += i) phi[j] -= phi[j] / i;
      if (i * i <= N) for (long j = i * i; j <= N; j += i * i) sqf[j] = 0;
    }
    fesetround(FE_UPWARD);
    for (long i = 1; i <= N; i++) { Fhi[i] = sqf[i] ? 1.0 / (double)phi[i] : 0; Flo[i] = sqf[i] ? dn_div(1.0, (double)phi[i]) : 0; }
    free(phi); free(sqf);
  }
  double cL_lo = dlo("1.3325822"), cU_hi = dhi("1.3325823"), K_lo = dlo("7.284");
  long ds[2100]; int nd = 0;
  for (long d = 1; d <= 2000; d++) ds[nd++] = d;
  ds[nd++] = 30030; ds[nd++] = 510510; ds[nd++] = 9699690;
  long long nfail = 0; double worst = 0; long wd = 0, wn = 0;
  #pragma omp parallel
  {
    fesetround(FE_UPWARD);
    mpfr_t x, y, z; mpfr_inits2(128, x, y, z, (mpfr_ptr)0);
    double lworst = 0; long lwd = 0, lwn = 0; long long lfail = 0;
    #pragma omp for schedule(dynamic, 1)
    for (int k = 0; k < nd; k++) {
      long d = ds[k];
      long pr[16]; int np = 0; long x0 = d;
      for (long p = 2; p * p <= x0; p++) if (x0 % p == 0) { pr[np++] = p; while (x0 % p == 0) x0 /= p; }
      if (x0 > 1) pr[np++] = x0;
      /* phi(d)/d, S_d, f1(d) (lower bound) */
      double rlo = 1, rhi = 1, Slo2 = 0, Shi2 = 0, f1lo = 1;
      for (int i = 0; i < np; i++) {
        long p = pr[i];
        rlo = dn_mul(rlo, dn_div((double)(p - 1), (double)p)); rhi = rhi * ((double)(p - 1) / (double)p);
        mpfr_set_ui(x, p, MPFR_RNDN);
        mpfr_log(y, x, MPFR_RNDD); mpfr_div_ui(y, y, p, MPFR_RNDD); Slo2 = dn_add(Slo2, mpfr_get_d(y, MPFR_RNDD));
        mpfr_log(y, x, MPFR_RNDU); mpfr_div_ui(y, y, p, MPFR_RNDU); Shi2 = Shi2 + mpfr_get_d(y, MPFR_RNDU);
        /* f1p lower: increasing numerator/decreasing in c, so use c rounded up */
        mpfr_cbrt(z, x, MPFR_RNDU);
        mpfr_sqr(y, z, MPFR_RNDU); mpfr_ui_div(y, 1, y, MPFR_RNDD); mpfr_add_ui(y, y, 1, MPFR_RNDD);   /* num low */
        mpfr_sqr(x, z, MPFR_RNDU); mpfr_add(x, x, z, MPFR_RNDU); mpfr_div_ui(x, x, p, MPFR_RNDU);
        mpfr_div_ui(x, x, p - 1, MPFR_RNDU); mpfr_add_ui(x, x, 1, MPFR_RNDU);                       /* den high */
        mpfr_div(y, y, x, MPFR_RNDD); f1lo = dn_mul(f1lo, mpfr_get_d(y, MPFR_RNDD));
      }
      double Glo = 0, Ghi = 0;
      for (long n = 1; n <= N; n++) {
        if (Fhi[n] != 0) {
          int cop = 1; for (int i = 0; i < np; i++) if (n % pr[i] == 0) { cop = 0; break; }
          if (cop) { Glo = dn_add(Glo, Flo[n]); Ghi = Ghi + Fhi[n]; }
        }
        double R = dn_mul(dn_mul(K_lo, ICl[n + 1]), f1lo);             /* 7.284 (n+1)^(-1/3) f1(d), low */
        double Mlo = dn_mul(rlo, dn_add(dn_add(LNlo[n], cL_lo), Slo2));  /* M(n) low, smallest c */
        double Mhi = rhi * (LNhi[n + 1] + cU_hi + Shi2);                 /* M(n+1) high, largest c */
        double e1 = Ghi - Mlo, e2 = Mhi - Glo;
        double e = e1 > e2 ? e1 : e2;
        double ratio = e / R;
        if (ratio > lworst) { lworst = ratio; lwd = d; lwn = n; }
        if (!(e <= R)) { lfail++; if (lfail < 3) printf("FAIL d=%ld n=%ld\n", d, n); }
      }
    }
    #pragma omp critical
    { if (lworst > worst) { worst = lworst; wd = lwd; wn = lwn; } nfail += lfail; }
    mpfr_clears(x, y, z, (mpfr_ptr)0);
  }
  printf("(b) %d values of d, X <= %ld: failures %lld; max |error| / (7.284 X^(-1/3) f1(d)) <= %.4f at d = %ld, n = %ld\n",
         nd, N, nfail, worst, wd, wn);
  printf("(b) %s\n", nfail == 0 ? "OK" : "FAILED");
  return 0;
}
