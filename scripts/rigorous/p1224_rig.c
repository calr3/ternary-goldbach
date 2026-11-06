/* Interval-arithmetic version of p1224_check.c: the finite check behind [H, Prop 12.2.4] with [H]'s
   constant c+ = 1.36 (the Lean proof, MinorArcs/LSQuot*.lean, has c+ = 2 and needs no such check).

   Claim, for every 1 <= q < Q1 = 2.2e10 and every integer n >= 1 with n < lam(q): (S) or (C), where
     (S)  8.53 <= log q  and  log q + 1.039 (n + 1) <= 0.826 (q n)^(2/9);
     (C)  qphi G_q(n) - log n - 1.3325822 - S_q + 0.1687 qphi f1(q) / n^(1/3)
            <= 0.3726 (max(log q, log(1e5/(n+1))) - S_q) + 0.0274177;
   qphi = q/phi(q), S_q = sum_{p|q} log p/p, f1(q) = prod_{p|q} f1p(p),
   f1p(p) = (1 + p^(-2/3)) / (1 + (p^(1/3) + p^(2/3))/(p(p-1))),
   G_q(n) = sum_{r <= n, (r,q) = 1} mu(r)^2/phi(r), kappa(q) = 0.3726 (log q - S_q) + 0.0274177,
   lam(q) = (qphi 7.4527 f1(q) / kappa(q))^3.

   Rigour.  Every real quantity is enclosed in [lo, hi] (or bounded on the side that matters).
   * Arithmetic: IEEE double with the rounding mode set to upward in every thread; lower bounds are
     computed as -((-a) op b).  Compiled with -frounding-math -ffp-contract=off.
   * Decimal constants, log p, log p/p, p/(p-1), f1p(p) for p <= sqrt(Q1), and the tables log n,
     n^(-1/3) for n <= 3e7: MPFR (correctly rounded, 128 bits), rounded outward to double.
   * log p for the (at most one) prime factor p > sqrt(Q1) of q: log p = e log 2 + 2 artanh(z),
     z = (m-1)/(m+1), m = p/2^e in [1, 2), with the series' partial sum and a geometric tail bound.
   * p^(1/3) for such p: a double c with c^3 <= p verified by upward-rounded multiplication.
   * exp in (S): lower bound by the Taylor partial sum (all terms positive).
   * G_q(n): upward sum of upward-rounded 1/phi(r) (phi exact).
   (S) is evaluated at the ends nlo, nhi of an interval of n only: the left side minus the right side
   of (S) is concave in n, so (S) at nlo and nhi gives (S) on [nlo, nhi].  Every other n < lam(q)
   is checked with (C).  lam(q) is replaced by an upper bound, so possibly more n are checked.

   Usage: p1224_rig [Q1] [threads]   (build: see build.sh)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <fenv.h>
#include <omp.h>
#include <gmp.h>
#include <mpfr.h>


typedef struct { double lo, hi; } I;

static inline double dn_add(double a, double b) { return -((-a) - b); }
static inline double dn_sub(double a, double b) { return -((-a) + b); }
static inline double dn_mul(double a, double b) { return -((-a) * b); }
static inline double dn_div(double a, double b) { return -((-a) / b); }

/* constants as enclosures */
static I K_W, K_OM, K_CL, K_CD, K_CLAM, K_CK, K_TAU, K_CS, K_LQS, K_1039, K_LOG1E5, K_LN2;
static I cst(const char *s) {
  mpfr_t x; mpfr_init2(x, 128);
  I r;
  mpfr_set_str(x, s, 10, MPFR_RNDD); r.lo = mpfr_get_d(x, MPFR_RNDD);
  mpfr_set_str(x, s, 10, MPFR_RNDU); r.hi = mpfr_get_d(x, MPFR_RNDU);
  mpfr_clear(x); return r;
}

/* per small prime: p/(p-1) (hi), log p (lo, hi), log p / p (lo, hi), f1p (hi) */
static double *PA_hi, *PL_lo, *PL_hi, *PS_lo, *PS_hi, *PF_hi;
static uint32_t *primes; static long nprimes;
/* tables for n <= RMAX */
static long RMAX;
static double *LN_lo, *LN_hi, *IC_hi, *F_hi;   /* log n, n^(-1/3), 1/phi(n) (0 if not squarefree) */

static void small_prime_vals(long p, long k) {
  mpfr_t a, b, c, t; mpfr_inits2(128, a, b, c, t, (mpfr_ptr)0);
  /* p/(p-1) */
  mpfr_set_ui(a, p, MPFR_RNDN); mpfr_div_ui(a, a, p - 1, MPFR_RNDU); PA_hi[k] = mpfr_get_d(a, MPFR_RNDU);
  mpfr_set_ui(a, p, MPFR_RNDN); mpfr_log(b, a, MPFR_RNDD); PL_lo[k] = mpfr_get_d(b, MPFR_RNDD);
  mpfr_div_ui(b, b, p, MPFR_RNDD); PS_lo[k] = mpfr_get_d(b, MPFR_RNDD);
  mpfr_log(b, a, MPFR_RNDU); PL_hi[k] = mpfr_get_d(b, MPFR_RNDU);
  mpfr_div_ui(b, b, p, MPFR_RNDU); PS_hi[k] = mpfr_get_d(b, MPFR_RNDU);
  /* f1p upper: decreasing in c = p^(1/3), so use c rounded down and round each step outward */
  mpfr_cbrt(c, a, MPFR_RNDD);
  mpfr_sqr(t, c, MPFR_RNDD);                      /* c^2 low */
  mpfr_ui_div(b, 1, t, MPFR_RNDU); mpfr_add_ui(b, b, 1, MPFR_RNDU);   /* numerator high */
  mpfr_add(t, t, c, MPFR_RNDD);                   /* c + c^2 low */
  mpfr_div_ui(t, t, p, MPFR_RNDD); mpfr_div_ui(t, t, p - 1, MPFR_RNDD); mpfr_add_ui(t, t, 1, MPFR_RNDD);
  mpfr_div(b, b, t, MPFR_RNDU); PF_hi[k] = mpfr_get_d(b, MPFR_RNDU);
  mpfr_clears(a, b, c, t, (mpfr_ptr)0);
}

/* log p for a prime p > sqrt(Q1) (p < 2^53): enclosure via artanh series */
static I log_large(uint64_t p) {
  int e = 0; uint64_t t = p; while (t >= 2) { t >>= 1; e++; }
  double m = (double)p / (double)((uint64_t)1 << e);       /* exact, in [1, 2) */
  double z_hi = (m - 1) / dn_add(m, 1), z_lo = dn_div(dn_sub(m, 1), m + 1);
  double s_lo = 0, s_hi = 0, zl = z_lo, zh = z_hi, zl2 = dn_mul(z_lo, z_lo), zh2 = z_hi * z_hi;
  for (int k = 0; k < 22; k++) {
    s_lo = dn_add(s_lo, dn_div(zl, 2 * k + 1)); s_hi = s_hi + zh / (2 * k + 1);
    zl = dn_mul(zl, zl2); zh = zh * zh2;
  }
  /* tail: sum_{k >= 22} z^(2k+1)/(2k+1) <= z^45 / (45 (1 - z^2)) */
  s_hi = s_hi + zh / (45 * dn_sub(1, zh2));
  I r;
  r.lo = dn_add(dn_mul(e, K_LN2.lo), dn_mul(2, s_lo));
  r.hi = e * K_LN2.hi + 2 * s_hi;
  return r;
}

/* exp lower bound for t >= 0 */
static double exp_lo(double t) {
  double s = 1, term = 1;
  for (int i = 1; i <= 60; i++) { term = dn_div(dn_mul(term, t), i); s = dn_add(s, term); }
  return s;
}

static uint64_t gcdu(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

/* (S) at n, rigorous; returns 1 if it holds; *mg = right low - left high */
static int hS(double lq_lo, double lq_hi, long n, double *mg) {
  double lhs = lq_hi + K_1039.hi * (double)(n + 1);
  double arg = dn_mul(K_TAU.lo, dn_add(lq_lo, LN_lo[n]));
  double rhs = dn_mul(K_CS.lo, exp_lo(arg));
  *mg = dn_sub(rhs, lhs);
  return lhs <= rhs;
}

int main(int argc, char **argv) {
  double Q1d = argc > 1 ? atof(argv[1]) : 2.2e10;
  uint64_t Q1 = (uint64_t)Q1d;
  int nth = argc > 2 ? atoi(argv[2]) : 22;
  omp_set_num_threads(nth);
  K_W = cst("0.6274"); K_OM = cst("0.3726"); K_CL = cst("1.3325822"); K_CD = cst("0.0274177");
  K_CLAM = cst("7.4527"); K_CK = cst("0.1687"); K_CS = cst("0.826"); K_LQS = cst("8.53");
  K_1039 = cst("1.039");
  { mpfr_t x; mpfr_init2(x, 128);
    mpfr_set_ui(x, 2, MPFR_RNDN); mpfr_div_ui(x, x, 9, MPFR_RNDD); K_TAU.lo = mpfr_get_d(x, MPFR_RNDD);
    mpfr_set_ui(x, 2, MPFR_RNDN); mpfr_div_ui(x, x, 9, MPFR_RNDU); K_TAU.hi = mpfr_get_d(x, MPFR_RNDU);
    mpfr_set_ui(x, 100000, MPFR_RNDN); mpfr_log(x, x, MPFR_RNDD); K_LOG1E5.lo = mpfr_get_d(x, MPFR_RNDD);
    mpfr_set_ui(x, 100000, MPFR_RNDN); mpfr_log(x, x, MPFR_RNDU); K_LOG1E5.hi = mpfr_get_d(x, MPFR_RNDU);
    mpfr_const_log2(x, MPFR_RNDD); K_LN2.lo = mpfr_get_d(x, MPFR_RNDD);
    mpfr_const_log2(x, MPFR_RNDU); K_LN2.hi = mpfr_get_d(x, MPFR_RNDU);
    mpfr_clear(x); }
  /* small primes */
  long P = (long)sqrt((double)Q1) + 2;
  char *comp = calloc(P + 1, 1);
  primes = malloc(sizeof(uint32_t) * (P / 2 + 10)); nprimes = 0;
  for (long i = 2; i <= P; i++) if (!comp[i]) { primes[nprimes++] = i; for (long j = i * i; j <= P; j += i) comp[j] = 1; }
  PA_hi = malloc(8 * nprimes); PL_lo = malloc(8 * nprimes); PL_hi = malloc(8 * nprimes);
  PS_lo = malloc(8 * nprimes); PS_hi = malloc(8 * nprimes); PF_hi = malloc(8 * nprimes);
  #pragma omp parallel for schedule(dynamic, 256)
  for (long k = 0; k < nprimes; k++) small_prime_vals(primes[k], k);
  /* tables */
  RMAX = 30000000;
  LN_lo = malloc(8 * (RMAX + 2)); LN_hi = malloc(8 * (RMAX + 2)); IC_hi = malloc(8 * (RMAX + 2));
  F_hi = malloc(8 * (RMAX + 2));
  #pragma omp parallel
  {
    mpfr_t x, y; mpfr_init2(x, 128); mpfr_init2(y, 128);
    #pragma omp for schedule(static)
    for (long n = 1; n <= RMAX + 1; n++) {
      mpfr_set_ui(x, n, MPFR_RNDN);
      mpfr_log(y, x, MPFR_RNDD); LN_lo[n] = mpfr_get_d(y, MPFR_RNDD);
      mpfr_log(y, x, MPFR_RNDU); LN_hi[n] = mpfr_get_d(y, MPFR_RNDU);
      mpfr_cbrt(y, x, MPFR_RNDD); mpfr_ui_div(y, 1, y, MPFR_RNDU); IC_hi[n] = mpfr_get_d(y, MPFR_RNDU);
    }
    mpfr_clear(x); mpfr_clear(y);
  }
  {
    uint32_t *phi = malloc(sizeof(uint32_t) * (RMAX + 1)); char *sqf = malloc(RMAX + 1);
    for (long i = 0; i <= RMAX; i++) { phi[i] = i; sqf[i] = 1; }
    for (long i = 2; i <= RMAX; i++) if (phi[i] == (uint32_t)i) {
      for (long j = i; j <= RMAX; j += i) phi[j] -= phi[j] / i;
      if ((long)i * i <= RMAX) for (long j = (long)i * i; j <= RMAX; j += (long)i * i) sqf[j] = 0;
    }
    fesetround(FE_UPWARD);
    F_hi[0] = 0;
    for (long i = 1; i <= RMAX; i++) F_hi[i] = sqf[i] ? 1.0 / (double)phi[i] : 0.0;
    free(phi); free(sqf);
  }
  const long SEG = 1L << 20;
  long nseg = (long)((Q1 + SEG - 1) / SEG);
  double minS = 1e300, minC = 1e300, maxlam = 0; uint64_t argCq = 0, argCn = 0, argLam = 0;
  long long nq = 0, nchk = 0, nfail = 0, nbig = 0, nSq = 0;
  #pragma omp parallel
  {
    fesetround(FE_UPWARD);
    { volatile double one = 1, three = 3;      /* self-test: the rounding mode is in effect */
      if (!(one / three > dn_div(one, three)) || fegetround() != FE_UPWARD) {
        printf("rounding mode self-test FAILED\n"); exit(1); } }
    double *qp = malloc(8 * SEG), *Slo = malloc(8 * SEG), *Shi = malloc(8 * SEG), *f1 = malloc(8 * SEG),
           *Llo = malloc(8 * SEG), *Lhi = malloc(8 * SEG);
    uint64_t *rem = malloc(sizeof(uint64_t) * SEG);
    double lminS = 1e300, lminC = 1e300, lmaxlam = 0; uint64_t lCq = 0, lCn = 0, lLam = 0;
    long long lnq = 0, lnchk = 0, lnfail = 0, lnbig = 0, lnSq = 0;
    #pragma omp for schedule(dynamic, 1)
    for (long sgi = 0; sgi < nseg; sgi++) {
      uint64_t lo = (uint64_t)sgi * SEG, hi = lo + SEG; if (hi > Q1) hi = Q1;
      long len = hi - lo;
      for (long i = 0; i < len; i++) { qp[i] = 1; Slo[i] = 0; Shi[i] = 0; f1[i] = 1; Llo[i] = 0; Lhi[i] = 0; rem[i] = lo + i; }
      for (long k = 0; k < nprimes; k++) {
        uint64_t p = primes[k]; if (p * p >= hi) break;
        uint64_t st = (lo + p - 1) / p * p; if (st == 0) st = p;
        for (uint64_t m = st; m < hi; m += p) {
          long i = m - lo; int e = 0;
          do { rem[i] /= p; e++; } while (rem[i] % p == 0);
          qp[i] = qp[i] * PA_hi[k]; Slo[i] = dn_add(Slo[i], PS_lo[k]); Shi[i] = Shi[i] + PS_hi[k];
          f1[i] = f1[i] * PF_hi[k];
          Llo[i] = dn_add(Llo[i], dn_mul((double)e, PL_lo[k])); Lhi[i] = Lhi[i] + (double)e * PL_hi[k];
        }
      }
      for (long i = 0; i < len; i++) {
        uint64_t q = lo + i; if (q == 0) continue;
        if (rem[i] > 1) {
          uint64_t p = rem[i];                    /* prime > sqrt(Q1), exponent 1 */
          double pd = (double)p, pm = (double)(p - 1);
          I L = log_large(p);
          qp[i] = qp[i] * (pd / pm);
          Slo[i] = dn_add(Slo[i], dn_div(L.lo, pd)); Shi[i] = Shi[i] + L.hi / pd;
          Llo[i] = dn_add(Llo[i], L.lo); Lhi[i] = Lhi[i] + L.hi;
          double c = cbrt(pd);
          while (c * c * c > pd) c = nextafter(c, 0);         /* c^3 <= p, c <= p^(1/3) */
          double c2 = dn_mul(c, c);
          double num = 1 + 1 / c2;
          double den = dn_add(1, dn_div(dn_add(c, c2), pd * pm));
          f1[i] = f1[i] * (num / den);
        }
        double lq_lo = Llo[i], lq_hi = Lhi[i];
        double kin = dn_sub(lq_lo, Shi[i]);
        double kap = dn_add(kin >= 0 ? dn_mul(K_OM.lo, kin) : dn_mul(K_OM.hi, kin), K_CD.lo);
        if (!(kap > 0)) { lnfail++; printf("kappa FAIL q=%lu\n", (unsigned long)q); continue; }
        double x = qp[i] * K_CLAM.hi * f1[i] / kap;
        double lam = x * x * x;                             /* upper bound for lam(q) */
        if (lam > lmaxlam) { lmaxlam = lam; lLam = q; }
        long nmax = (long)ceil(lam) - 1;                    /* every integer n < lam(q) is <= nmax */
        if (nmax < 1) continue;
        if (nmax > RMAX) { lnbig++; continue; }
        long nlo = 1, nhi = 0;
        if (lq_lo >= K_LQS.hi) {
          double mg;
          int s1 = hS(lq_lo, lq_hi, 1, &mg);
          if (s1 && hS(lq_lo, lq_hi, nmax, &mg)) {
            double mg1; hS(lq_lo, lq_hi, 1, &mg1);
            if (mg < lminS) lminS = mg; if (mg1 < lminS) lminS = mg1;
            lnSq++; continue;                                /* (S) on [1, nmax] by concavity */
          }
          /* locate an n where (S) holds, near the maximiser of the (concave) difference */
          double npk = pow(0.826 * (2.0 / 9) * exp((2.0 / 9) * lq_hi) / 1.039, 9.0 / 7);
          long c1 = (long)floor(npk), c2 = c1 + 1;
          if (c1 < 1) c1 = 1;
          if (c2 < 1) c2 = 1;
          long m0 = -1;
          if (s1) m0 = 1;
          else if (c1 <= nmax && hS(lq_lo, lq_hi, c1, &mg)) m0 = c1;
          else if (c2 <= nmax && hS(lq_lo, lq_hi, c2, &mg)) m0 = c2;
          else if (hS(lq_lo, lq_hi, nmax, &mg)) m0 = nmax;
          if (m0 >= 1) {
            long a = 1, b = m0;
            if (s1) b = 1;
            else { while (b - a > 1) { long mid = (a + b) / 2; if (hS(lq_lo, lq_hi, mid, &mg)) b = mid; else a = mid; } }
            nlo = b;
            a = m0; b = nmax + 1;
            while (b - a > 1) { long mid = (a + b) / 2; if (hS(lq_lo, lq_hi, mid, &mg)) a = mid; else b = mid; }
            nhi = a;
            /* the ends must satisfy (S) */
            if (!hS(lq_lo, lq_hi, nlo, &mg) || !hS(lq_lo, lq_hi, nhi, &mg)) { nlo = 1; nhi = 0; }
            else { hS(lq_lo, lq_hi, nlo, &mg); if (mg < lminS) lminS = mg;
                   hS(lq_lo, lq_hi, nhi, &mg); if (mg < lminS) lminS = mg; }
          }
        }
        lnq++;
        double G = 0; long r = 1;
        for (long n = 1; n <= nmax; n++) {
          if (n >= nlo && n <= nhi) continue;
          for (; r <= n; r++) if (F_hi[r] != 0 && gcdu(q, r) == 1) G = G + F_hi[r];
          /* left side, upper bound */
          double lhs = qp[i] * G;
          lhs = lhs - LN_lo[n]; lhs = lhs - K_CL.lo; lhs = lhs - Slo[i];
          lhs = lhs + K_CK.hi * qp[i] * f1[i] * IC_hi[n];
          /* right side, lower bound */
          double mx = dn_sub(K_LOG1E5.lo, LN_hi[n + 1]); if (lq_lo > mx) mx = lq_lo;
          double inner = dn_sub(mx, Shi[i]);
          double rhs = inner >= 0 ? dn_mul(K_OM.lo, inner) : dn_mul(K_OM.hi, inner);
          rhs = dn_add(rhs, K_CD.lo);
          double mg = dn_sub(rhs, lhs);
          lnchk++;
          if (mg < lminC) { lminC = mg; lCq = q; lCn = n; }
          if (!(lhs <= rhs)) { lnfail++; if (lnfail < 5) printf("FAIL q=%lu n=%ld margin=%.3e\n", (unsigned long)q, n, mg); }
        }
      }
    }
    #pragma omp critical
    {
      if (lminS < minS) minS = lminS;
      if (lminC < minC) { minC = lminC; argCq = lCq; argCn = lCn; }
      if (lmaxlam > maxlam) { maxlam = lmaxlam; argLam = lLam; }
      nq += lnq; nchk += lnchk; nfail += lnfail; nbig += lnbig; nSq += lnSq;
    }
  }
  printf("Q1 = %.4e: q covered by (S) alone: %lld; q with explicit checks: %lld, checks (C): %lld, failures: %lld, nmax > RMAX: %lld\n",
         (double)Q1, nSq, nq, nchk, nfail, nbig);
  printf("max lam (upper bound) = %.6f at q = %lu; min margin (S) = %.4e; min margin (C) = %.6e at q = %lu, n = %lu\n",
         maxlam, (unsigned long)argLam, minS, minC, (unsigned long)argCq, (unsigned long)argCn);
  printf("prop1224_check: %s (interval arithmetic)\n", (nfail == 0 && nbig == 0) ? "OK" : "FAILED");
  return 0;
}
