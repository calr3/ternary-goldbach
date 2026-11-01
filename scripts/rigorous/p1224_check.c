/* The finite check behind [B, Prop 12.2.4] (axiom `prop1224_check`, TernaryGoldbach/MinorArcs/LSQuot2.lean).

   For every 1 <= q < Q1 = 2.2e10 and every integer n >= 1 with n < lam(q), at least one of
     (S)  8.53 <= log q  and  log q + 1.039 (n + 1) <= 0.826 (q n)^(2/9);
     (C)  qphi G_q(n) - log n - 1.3325822 - S_q + 0.1687 qphi f1(q) / n^(1/3)
            <= 0.3726 (max(log q, log(1e5/(n+1))) - S_q) + 0.0274177
   holds.  Here qphi = q/phi(q), S_q = sum_{p | q} log p / p,
   f1(q) = prod_{p | q} (1 + p^(-2/3)) / (1 + (p^(1/3) + p^(2/3)) / (p (p - 1)))  [B, (12.13)],
   G_q(n) = sum_{r <= n, (r, q) = 1} mu(r)^2 / phi(r),
   kappa(q) = 0.3726 (log q - S_q) + 0.0274177,   lam(q) = (qphi 7.4527 f1(q) / kappa(q))^3.

   (S) is not evaluated at every n: n -> 0.826 (q n)^(2/9) - log q - 1.039 (n + 1) is concave, so the
   n where (S) holds form an interval [nlo, nhi]; the program locates it from the maximiser, checks
   (S) at nlo and nhi (with margin), and checks (C) at every other n in [1, lam(q)).

   Arithmetic: long double (64-bit mantissa) throughout; G_q(n) is summed in long double from a
   double table (relative error <= 2^-53 per term).  Every inequality is required to hold with an
   absolute margin of at least 1e-9 (resp. relative 1e-12 for (S) and for n < lam), which exceeds the
   accumulated rounding error by several orders of magnitude (at most ~1e-11 for sums of <= 3e7
   positive terms of size <= 1 and the elementary functions, which glibc evaluates to < 1 ulp).
   The minimal margins found are printed.

   Usage: p1224_check [Q1] [threads]      (OpenMP; build: gcc -O2 -fopenmp p1224_check.c -lm)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>

#define W0 0.6274L
#define OM 0.3726L
#define CL 1.3325822L
#define CD 0.0274177L
#define CLAM 7.4527L
#define CK 0.1687L
#define TAU (2.0L / 9.0L)
#define CS 0.826L
#define LQS 8.53L

static double *Ftab;      /* mu(r)^2/phi(r), r <= RMAX */
static long RMAX;
static uint32_t *primes; static long nprimes;

static long double f1p(long double p) {
  long double c = cbrtl(p);
  return (1 + 1 / (c * c)) / (1 + (c + c * c) / (p * (p - 1)));
}

/* (S) at n: 0.826 (q n)^(2/9) - log q - 1.039 (n + 1) >= 0 (with relative margin); concave in n */
static int hS(long double lq, long double q, long double n, long double *marg) {
  long double lhs = lq + 1.039L * (n + 1), rhs = CS * expl(TAU * logl(q * n));
  *marg = rhs - lhs;
  return rhs - lhs >= 1e-12L * rhs;
}

static uint64_t gcdu(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
  double Q1d = argc > 1 ? atof(argv[1]) : 2.2e10;
  uint64_t Q1 = (uint64_t)Q1d;
  int nth = argc > 2 ? atoi(argv[2]) : 24;
  omp_set_num_threads(nth);
  /* small primes up to sqrt(Q1) */
  long P = (long)sqrt((double)Q1) + 2;
  char *comp = calloc(P + 1, 1);
  primes = malloc(sizeof(uint32_t) * (P / 2 + 10)); nprimes = 0;
  for (long i = 2; i <= P; i++) if (!comp[i]) { primes[nprimes++] = i; for (long j = i * i; j <= P; j += i) comp[j] = 1; }
  /* table mu^2/phi up to RMAX */
  RMAX = 30000000;
  {
    uint32_t *phi = malloc(sizeof(uint32_t) * (RMAX + 1)); char *sqf = malloc(RMAX + 1);
    for (long i = 0; i <= RMAX; i++) { phi[i] = i; sqf[i] = 1; }
    for (long i = 2; i <= RMAX; i++) if (phi[i] == (uint32_t)i) {
      for (long j = i; j <= RMAX; j += i) phi[j] -= phi[j] / i;
      if ((long)i * i <= RMAX) for (long j = (long)i * i; j <= RMAX; j += (long)i * i) sqf[j] = 0;
    }
    Ftab = malloc(sizeof(double) * (RMAX + 1)); Ftab[0] = 0;
    for (long i = 1; i <= RMAX; i++) Ftab[i] = sqf[i] ? 1.0 / phi[i] : 0.0;
    free(phi); free(sqf);
  }
  const long SEG = 1L << 22;
  long nseg = (long)((Q1 + SEG - 1) / SEG);
  long double minS = 1e30L, minC = 1e30L, maxlam = 0; uint64_t argC = 0, argLam = 0;
  long long nq = 0, nchk = 0, nfail = 0, nbig = 0;
  #pragma omp parallel
  {
    double *qphi = malloc(sizeof(double) * SEG), *Ssum = malloc(sizeof(double) * SEG), *f1 = malloc(sizeof(double) * SEG);
    uint64_t *rem = malloc(sizeof(uint64_t) * SEG);
    long double lminS = 1e30L, lminC = 1e30L, lmaxlam = 0; uint64_t largC = 0, largLam = 0;
    long long lnq = 0, lnchk = 0, lnfail = 0, lnbig = 0;
    #pragma omp for schedule(dynamic, 1)
    for (long sgi = 0; sgi < nseg; sgi++) {
      uint64_t lo = (uint64_t)sgi * SEG, hi = lo + SEG; if (hi > Q1) hi = Q1;
      long len = hi - lo;
      for (long i = 0; i < len; i++) { qphi[i] = 1; Ssum[i] = 0; f1[i] = 1; rem[i] = lo + i; }
      for (long k = 0; k < nprimes; k++) {
        uint64_t p = primes[k]; if (p * p >= hi) break;
        double a = (double)p / (p - 1), b = log((double)p) / p, c = (double)f1p(p);
        uint64_t st = (lo + p - 1) / p * p; if (st == 0) st = p;
        for (uint64_t m = st; m < hi; m += p) {
          long i = m - lo; qphi[i] *= a; Ssum[i] += b; f1[i] *= c;
          do rem[i] /= p; while (rem[i] % p == 0);
        }
      }
      for (long i = 0; i < len; i++) {
        uint64_t q = lo + i; if (q == 0) continue;
        if (rem[i] > 1) { long double p = rem[i]; qphi[i] *= (double)(p / (p - 1)); Ssum[i] += (double)(logl(p) / p); f1[i] *= (double)f1p(p); }
        long double lq = logl((long double)q), kap = OM * (lq - Ssum[i]) + CD;
        long double lam = powl(qphi[i] * CLAM * f1[i] / kap, 3);
        if (lam > lmaxlam) { lmaxlam = lam; largLam = q; }
        long nmax = (long)floorl(lam * (1 + 1e-12L) + 1e-9L);
        if ((long double)nmax >= lam * (1 + 1e-12L) + 1e-9L) nmax--;
        if (nmax < 1) continue;
        /* the n in [nlo, nhi] satisfy (S): its left side minus right side is concave in n, so the
           set where (S) holds is an interval; we locate it around the maximiser and check its ends */
        long nlo = 1, nhi = 0;
        if (lq >= LQS + 1e-12L) {
          long double mg;
          long double npk = powl(CS * TAU * expl(TAU * lq) / 1.039L, 1 / (1 - TAU));
          long m0 = -1, c1 = (long)floorl(npk), c2 = c1 + 1;
          if (c1 < 1) c1 = 1;
          if (c2 < 1) c2 = 1;
          if (c1 <= nmax && hS(lq, q, c1, &mg)) m0 = c1; else if (c2 <= nmax && hS(lq, q, c2, &mg)) m0 = c2;
          else if (c1 > nmax && hS(lq, q, nmax, &mg)) m0 = nmax;
          if (m0 >= 1) {
            long a = 1, b = m0;            /* smallest n in [1, m0] with (S) */
            if (hS(lq, q, 1, &mg)) b = 1;
            else { while (b - a > 1) { long mid = (a + b) / 2; if (hS(lq, q, mid, &mg)) b = mid; else a = mid; } }
            nlo = b;
            a = m0; b = nmax + 1;           /* largest n in [m0, nmax] with (S) */
            while (b - a > 1) { long mid = (a + b) / 2; if (hS(lq, q, mid, &mg)) a = mid; else b = mid; }
            nhi = a;
            hS(lq, q, nlo, &mg); if (mg < lminS) lminS = mg;
            hS(lq, q, nhi, &mg); if (mg < lminS) lminS = mg;
            if (nlo == 1 && nhi >= nmax) continue;
          }
        }
        if (nmax > RMAX) { lnbig++; continue; }
        lnq++;
        /* the primes of q, for coprimality */
        long double G = 0; long r = 1;
        for (long n = 1; n <= nmax; n++) {
          if (n >= nlo && n <= nhi) continue;
          for (; r <= n; r++) if (Ftab[r] != 0 && gcdu(q, r) == 1) G += Ftab[r];
          long double lhs = qphi[i] * G - logl((long double)n) - CL - Ssum[i] + CK * qphi[i] * f1[i] / cbrtl((long double)n);
          long double mx = logl(1e5L / (n + 1)); if (lq > mx) mx = lq;
          long double rhs = OM * (mx - Ssum[i]) + CD;
          long double mg = rhs - lhs;
          lnchk++;
          if (mg < lminC) { lminC = mg; largC = q * 100000000ULL + n; }
          if (mg < 1e-9L) { lnfail++; if (lnfail < 5) printf("FAIL q=%lu n=%ld margin=%.3Le\n", (unsigned long)q, n, mg); }
        }
      }
    }
    #pragma omp critical
    {
      if (lminS < minS) minS = lminS;
      if (lminC < minC) { minC = lminC; argC = largC; }
      if (lmaxlam > maxlam) { maxlam = lmaxlam; argLam = largLam; }
      nq += lnq; nchk += lnchk; nfail += lnfail; nbig += lnbig;
    }
    free(qphi); free(Ssum); free(f1); free(rem);
  }
  printf("Q1 = %.4e: q with explicit checks: %lld, checks: %lld, failures: %lld, nmax > RMAX: %lld\n",
         (double)Q1, nq, nchk, nfail, nbig);
  printf("max lam = %.6Lf at q = %lu; min margin (S) = %.4Le; min margin (C) = %.6Le at q = %lu, n = %lu\n",
         maxlam, (unsigned long)argLam, minS, minC, (unsigned long)(argC / 100000000ULL), (unsigned long)(argC % 100000000ULL));
  printf("prop1224_check: %s\n", (nfail == 0 && nbig == 0) ? "OK" : "FAILED");
  return 0;
}
