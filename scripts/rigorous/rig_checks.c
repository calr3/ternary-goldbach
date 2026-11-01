/* Rigorous re-checks of the finite numerical axioms (our own computations).

   Every real quantity is enclosed in an interval [lo, hi] of MPFR numbers; each operation rounds
   lo down and hi up (MPFR is correctly rounded, so the enclosures are rigorous, including log, exp,
   sqrt and the constant gamma).  Integers (sieves, phi, mu, lambda) are exact.  A check passes only
   if it holds for the whole interval.  This is an independent re-implementation of the float64
   scripts in scripts/ (different code, sieves and summation order).

   Build:  sh scripts/rigorous/build.sh      Run:  scripts/rigorous/rig_checks [name ...]
   Names:  nonprime mertens_lower mertens_point logsq mertens_product K liouville C_grid
           lemma7 lemma8      (default: all)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <gmp.h>
#include <mpfr.h>

static mpfr_prec_t PREC = 64;
#define D MPFR_RNDD
#define U MPFR_RNDU

typedef struct { mpfr_t lo, hi; } I;
static mpfr_t T0, P4[4], Q4[4];   /* scratch (single-threaded) */
static void scratch_init(void) {
  mpfr_init2(T0, PREC);
  for (int i = 0; i < 4; i++) { mpfr_init2(P4[i], PREC); mpfr_init2(Q4[i], PREC); }
}
static void Iinit(I *x) { mpfr_init2(x->lo, PREC); mpfr_init2(x->hi, PREC); }
static void Iclear(I *x) { mpfr_clear(x->lo); mpfr_clear(x->hi); }
static void Iset_ui(I *x, unsigned long v) { mpfr_set_ui(x->lo, v, D); mpfr_set_ui(x->hi, v, U); }
static void Iset_si(I *x, long v) { mpfr_set_si(x->lo, v, D); mpfr_set_si(x->hi, v, U); }
static void Iset_str(I *x, const char *s) { mpfr_set_str(x->lo, s, 10, D); mpfr_set_str(x->hi, s, 10, U); }
static void Iset(I *x, I *a) { mpfr_set(x->lo, a->lo, D); mpfr_set(x->hi, a->hi, U); }
/* q = num/den (den > 0) */
static void Iset_q(I *x, long num, unsigned long den) {
  mpfr_set_si(x->lo, num, D); mpfr_div_ui(x->lo, x->lo, den, D);
  mpfr_set_si(x->hi, num, U); mpfr_div_ui(x->hi, x->hi, den, U);
}
static void Iadd(I *r, I *a, I *b) { mpfr_add(r->lo, a->lo, b->lo, D); mpfr_add(r->hi, a->hi, b->hi, U); }
static void Isub(I *r, I *a, I *b) {  /* r may alias a or b */
  mpfr_sub(T0, a->lo, b->hi, D); mpfr_sub(r->hi, a->hi, b->lo, U); mpfr_set(r->lo, T0, D);
}
static void Ineg(I *r, I *a) { mpfr_neg(T0, a->hi, D); mpfr_neg(r->hi, a->lo, U); mpfr_set(r->lo, T0, D); }
/* product of nonnegative intervals */
static void Imul_pos(I *r, I *a, I *b) {
  if (mpfr_sgn(a->lo) < 0 || mpfr_sgn(b->lo) < 0) { fprintf(stderr, "Imul_pos: negative\n"); exit(2); }
  mpfr_mul(r->lo, a->lo, b->lo, D); mpfr_mul(r->hi, a->hi, b->hi, U);
}
/* general product */
static void Imul(I *r, I *a, I *b) {
  mpfr_ptr p[4] = {P4[0], P4[1], P4[2], P4[3]}, q[4] = {Q4[0], Q4[1], Q4[2], Q4[3]};
  mpfr_mul(p[0], a->lo, b->lo, D); mpfr_mul(p[1], a->lo, b->hi, D);
  mpfr_mul(p[2], a->hi, b->lo, D); mpfr_mul(p[3], a->hi, b->hi, D);
  mpfr_mul(q[0], a->lo, b->lo, U); mpfr_mul(q[1], a->lo, b->hi, U);
  mpfr_mul(q[2], a->hi, b->lo, U); mpfr_mul(q[3], a->hi, b->hi, U);
  mpfr_min(p[0], p[0], p[1], D); mpfr_min(p[2], p[2], p[3], D); mpfr_min(r->lo, p[0], p[2], D);
  mpfr_max(q[0], q[0], q[1], U); mpfr_max(q[2], q[2], q[3], U); mpfr_max(r->hi, q[0], q[2], U);
}
/* a / b with b > 0 */
static void Idiv(I *r, I *a, I *b) {
  if (mpfr_sgn(b->lo) <= 0) { fprintf(stderr, "Idiv: denominator not positive\n"); exit(2); }
  mpfr_ptr p[4] = {P4[0], P4[1], P4[2], P4[3]}, q[4] = {Q4[0], Q4[1], Q4[2], Q4[3]};
  mpfr_div(p[0], a->lo, b->lo, D); mpfr_div(p[1], a->lo, b->hi, D);
  mpfr_div(p[2], a->hi, b->lo, D); mpfr_div(p[3], a->hi, b->hi, D);
  mpfr_div(q[0], a->lo, b->lo, U); mpfr_div(q[1], a->lo, b->hi, U);
  mpfr_div(q[2], a->hi, b->lo, U); mpfr_div(q[3], a->hi, b->hi, U);
  mpfr_min(p[0], p[0], p[1], D); mpfr_min(p[2], p[2], p[3], D); mpfr_min(r->lo, p[0], p[2], D);
  mpfr_max(q[0], q[0], q[1], U); mpfr_max(q[2], q[2], q[3], U); mpfr_max(r->hi, q[0], q[2], U);
}
static void Idiv_ui(I *r, I *a, unsigned long d) {  /* d > 0 */
  mpfr_div_ui(r->lo, a->lo, d, D); mpfr_div_ui(r->hi, a->hi, d, U);
}
static void Ilog(I *r, I *a) {
  if (mpfr_sgn(a->lo) <= 0) { fprintf(stderr, "Ilog: argument not positive\n"); exit(2); }
  mpfr_log(r->lo, a->lo, D); mpfr_log(r->hi, a->hi, U);
}
static void Ilog_ui(I *r, unsigned long n) { mpfr_set_ui(r->lo, n, D); mpfr_log(r->lo, r->lo, D); mpfr_set_ui(r->hi, n, U); mpfr_log(r->hi, r->hi, U); }
static void Iexp(I *r, I *a) { mpfr_exp(r->lo, a->lo, D); mpfr_exp(r->hi, a->hi, U); }
static void Isqrt(I *r, I *a) { mpfr_sqrt(r->lo, a->lo, D); mpfr_sqrt(r->hi, a->hi, U); }
static void Iabs(I *r, I *a) {
  if (mpfr_sgn(a->lo) >= 0) { Iset(r, a); return; }
  if (mpfr_sgn(a->hi) <= 0) { Ineg(r, a); return; }
  mpfr_neg(T0, a->lo, U); mpfr_max(r->hi, T0, a->hi, U); mpfr_set_ui(r->lo, 0, D);
}
static void Imax(I *r, I *a, I *b) { mpfr_max(r->lo, a->lo, b->lo, D); mpfr_max(r->hi, a->hi, b->hi, U); }
/* certainly a <= b, a < b */
static int Ile(I *a, I *b) { return mpfr_lessequal_p(a->hi, b->lo); }
static int Ilt(I *a, I *b) { return mpfr_less_p(a->hi, b->lo); }
static double lo_d(I *a) { return mpfr_get_d(a->lo, D); }
static double hi_d(I *a) { return mpfr_get_d(a->hi, U); }

static int failures = 0;
static void verdict(const char *name, int ok) {
  printf("%s: %s\n\n", name, ok ? "OK (rigorous)" : "FAILED");
  if (!ok) failures++;
  fflush(stdout);
}

/* ---------- sieves ---------- */

static uint32_t *small_primes; static size_t n_small;
static void make_small_primes(uint64_t lim) {  /* primes <= lim (lim <= 2^32) */
  char *c = calloc(lim + 1, 1); size_t k = 0;
  small_primes = malloc(sizeof(uint32_t) * (lim / 2 + 10));
  for (uint64_t i = 2; i <= lim; i++) {
    if (c[i]) continue;
    small_primes[k++] = (uint32_t)i;
    for (uint64_t j = i * i; j <= lim; j += i) c[j] = 1;
  }
  n_small = k; free(c);
}

/* calls cb(p, ctx) for each prime p <= N in increasing order (segmented sieve) */
typedef void (*prime_cb)(uint64_t p, void *ctx);
static void for_primes(uint64_t N, prime_cb cb, void *ctx) {
  uint64_t r = (uint64_t)sqrtl((long double)N) + 2;
  make_small_primes(r);
  const uint64_t SEG = 1 << 22;
  char *seg = malloc(SEG);
  for (uint64_t lo = 2; lo <= N; lo += SEG) {
    uint64_t hi = lo + SEG - 1; if (hi > N) hi = N;
    memset(seg, 1, hi - lo + 1);
    for (size_t i = 0; i < n_small; i++) {
      uint64_t p = small_primes[i];
      if (p * p > hi) break;
      uint64_t s = (lo + p - 1) / p * p; if (s < p * p) s = p * p;
      for (uint64_t m = s; m <= hi; m += p) seg[m - lo] = 0;
    }
    for (uint64_t n = lo; n <= hi; n++) if (seg[n - lo]) cb(n, ctx);
  }
  free(seg); free(small_primes);
}

/* prime powers p^k (k >= 2) <= N, sorted */
typedef struct { uint64_t v, p; } PP;
static int ppcmp(const void *a, const void *b) {
  uint64_t x = ((const PP *)a)->v, y = ((const PP *)b)->v; return x < y ? -1 : x > y;
}
static PP *higher_powers(uint64_t N, size_t *cnt) {
  uint64_t r = (uint64_t)sqrtl((long double)N) + 2;
  char *c = calloc(r + 1, 1); size_t k = 0, cap = 1024; PP *a = malloc(cap * sizeof(PP));
  for (uint64_t i = 2; i <= r; i++) {
    if (c[i]) continue;
    for (uint64_t j = i * i; j <= r; j += i) c[j] = 1;
    for (unsigned __int128 v = (unsigned __int128)i * i; v <= N; v *= i) {
      if (k == cap) { cap *= 2; a = realloc(a, cap * sizeof(PP)); }
      a[k].v = (uint64_t)v; a[k].p = i; k++;
    }
  }
  free(c); qsort(a, k, sizeof(PP), ppcmp); *cnt = k; return a;
}

/* stream of all prime powers v = p^k <= N in increasing order: cb2(v, p, ctx) */
typedef void (*pp_cb)(uint64_t v, uint64_t p, void *ctx);
typedef struct { PP *hp; size_t nhp, ihp; pp_cb cb; void *ctx; } PPS;
static void pps_prime(uint64_t p, void *c) {
  PPS *s = c;
  while (s->ihp < s->nhp && s->hp[s->ihp].v < p) { s->cb(s->hp[s->ihp].v, s->hp[s->ihp].p, s->ctx); s->ihp++; }
  s->cb(p, p, s->ctx);
}
static void for_prime_powers(uint64_t N, pp_cb cb, void *ctx) {
  PPS s; s.hp = higher_powers(N, &s.nhp); s.ihp = 0; s.cb = cb; s.ctx = ctx;
  for_primes(N, pps_prime, &s);
  while (s.ihp < s.nhp) { cb(s.hp[s.ihp].v, s.hp[s.ihp].p, ctx); s.ihp++; }
  free(s.hp);
}

/* ---------- nonprime_small: psi(n) - theta(n) < 1.4262 sqrt(n), 1 <= n <= 10^12 ---------- */
static void check_nonprime(void) {
  printf("== nonprime_small: psi(n) - theta(n) < 1.4262 sqrt(n) for 1 <= n <= 10^12\n");
  size_t cnt; PP *hp = higher_powers(1000000000000ULL, &cnt);
  I S, L, R, c, worst; Iinit(&S); Iinit(&L); Iinit(&R); Iinit(&c); Iinit(&worst);
  Iset_ui(&S, 0); Iset_str(&c, "1.4262"); Iset_ui(&worst, 0);
  int ok = 1; uint64_t at = 0;
  /* psi - theta is constant on [v_i, v_{i+1}) and sqrt increasing: check at each v_i */
  for (size_t i = 0; i < cnt; i++) {
    Ilog_ui(&L, hp[i].p); Iadd(&S, &S, &L);
    Iset_ui(&R, hp[i].v); Isqrt(&R, &R);
    I q; Iinit(&q); Idiv(&q, &S, &R);
    if (mpfr_greater_p(q.hi, worst.hi)) { Iset(&worst, &q); at = hp[i].v; }
    Iclear(&q);
    Imul(&R, &R, &c);
    if (!Ilt(&S, &R)) { ok = 0; printf("  fails at n = %llu\n", (unsigned long long)hp[i].v); }
  }
  printf("  %zu prime powers p^k (k >= 2); max (psi - theta)/sqrt(n) in [%.9f, %.9f] at n = %llu\n",
         cnt, lo_d(&worst), hi_d(&worst), (unsigned long long)at);
  verdict("nonprime_small", ok);
  free(hp);
}

/* ---------- Lambda(m)/m family up to 10^6 ---------- */
typedef struct {
  I P, PSI, t, L, lhs, c32; uint64_t prev; int ok; I worst; uint64_t wat; uint64_t N;
} MLctx;
/* run [prev, v-1]: P constant (sum up to prev); worst n = v - 1 */
static void ml_run_end(MLctx *s, uint64_t nend) {
  if (s->prev == 0) return;
  uint64_t lo = s->prev < 3 ? 3 : s->prev;
  if (nend < lo) return;
  Ilog_ui(&s->lhs, nend + 1); Isub(&s->lhs, &s->lhs, &s->c32);   /* log(n+1) - log(3/sqrt 2) */
  I m; Iinit(&m); Isub(&m, &s->P, &s->lhs);
  if (mpfr_less_p(m.lo, s->worst.lo)) { Iset(&s->worst, &m); s->wat = nend; }
  if (mpfr_sgn(m.lo) < 0) { s->ok = 0; printf("  fails at n = %llu\n", (unsigned long long)nend); }
  Iclear(&m);
}
static void ml_pp(uint64_t v, uint64_t p, void *c) {
  MLctx *s = c;
  if (v > s->N) return;
  ml_run_end(s, v - 1);
  Ilog_ui(&s->L, p); Idiv_ui(&s->t, &s->L, v); Iadd(&s->P, &s->P, &s->t); Iadd(&s->PSI, &s->PSI, &s->L);
  s->prev = v;
}
static void check_mertens_family(void) {
  printf("== mertens_lower_small: log(n+1) - log(3/sqrt 2) <= sum_{m<=n} Lambda(m)/m, 3 <= n <= 10^6\n");
  MLctx s; Iinit(&s.P); Iinit(&s.PSI); Iinit(&s.t); Iinit(&s.L); Iinit(&s.lhs); Iinit(&s.c32); Iinit(&s.worst);
  Iset_ui(&s.P, 0); Iset_ui(&s.PSI, 0); s.prev = 0; s.ok = 1; s.N = 1000000;
  mpfr_set_ui(s.worst.lo, 100, D); mpfr_set_ui(s.worst.hi, 100, U);
  { I a, b; Iinit(&a); Iinit(&b); Ilog_ui(&a, 3); Ilog_ui(&b, 2); Idiv_ui(&b, &b, 2); Isub(&s.c32, &a, &b); Iclear(&a); Iclear(&b); }
  for_prime_powers(s.N, ml_pp, &s);
  ml_run_end(&s, s.N);
  printf("  min margin in [%.9f, %.9f] at n = %llu\n", lo_d(&s.worst), hi_d(&s.worst), (unsigned long long)s.wat);
  verdict("mertens_lower_small", s.ok);

  printf("== mertens_point: sum Lambda(m)/m - psi(X)/(X+1) - log(X+2) >= -1.5776, X = 10^6\n");
  I v, t, e; Iinit(&v); Iinit(&t); Iinit(&e);
  Idiv_ui(&t, &s.PSI, 1000001); Isub(&v, &s.P, &t); Ilog_ui(&t, 1000002); Isub(&v, &v, &t);
  Iset_str(&e, "-1.5776");
  printf("  value in [%.9f, %.9f]\n", lo_d(&v), hi_d(&v));
  verdict("mertens_point", Ile(&e, &v));
}

/* ---------- logsq_small ---------- */
typedef struct { I *L2; uint64_t N; I L; } LSctx;   /* L2[x] = sum_{p<=x} (log p)^2, filled at primes */
static void ls_prime(uint64_t p, void *c) {
  LSctx *s = c; Ilog_ui(&s->L, p); Imul(&s->L, &s->L, &s->L); Iadd(&s->L2[p], &s->L2[p], &s->L);
}
static void check_logsq(void) {
  printf("== logsq_small: sum_{n/2<p<=n} (log p)^2 <= n log(n)/2, 117 <= n <= 10^6\n");
  uint64_t N = 1000000; LSctx s; s.N = N; Iinit(&s.L);
  s.L2 = malloc(sizeof(I) * (N + 1));
  for (uint64_t i = 0; i <= N; i++) { Iinit(&s.L2[i]); Iset_ui(&s.L2[i], 0); }
  for_primes(N, ls_prime, &s);
  for (uint64_t i = 1; i <= N; i++) Iadd(&s.L2[i], &s.L2[i], &s.L2[i - 1]);   /* prefix sums */
  I lhs, rhs, m, worst, nn; Iinit(&lhs); Iinit(&rhs); Iinit(&m); Iinit(&worst); Iinit(&nn);
  mpfr_set_ui(worst.lo, 1000000, D); mpfr_set_ui(worst.hi, 1000000, U);
  int ok = 1; uint64_t wat = 0;
  for (uint64_t n = 117; n <= N; n++) {
    Isub(&lhs, &s.L2[n], &s.L2[n / 2]);
    Ilog_ui(&rhs, n); Iset_q(&nn, (long)n, 2); Imul_pos(&rhs, &rhs, &nn);
    Isub(&m, &rhs, &lhs);
    if (mpfr_less_p(m.lo, worst.lo)) { Iset(&worst, &m); wat = n; }
    if (mpfr_sgn(m.lo) < 0) { ok = 0; printf("  fails at n = %llu\n", (unsigned long long)n); }
  }
  printf("  min margin in [%.6f, %.6f] at n = %llu\n", lo_d(&worst), hi_d(&worst), (unsigned long long)wat);
  verdict("logsq_small", ok);
  for (uint64_t i = 0; i <= N; i++) Iclear(&s.L2[i]);
  free(s.L2);
}

/* ---------- mertens_product_small ---------- */
typedef struct { I SL, TH, L, L1, F, lt, rhs, t, eg, c, worst, worst4; uint64_t wat, wat4; int ok; long count; } MPctx;
static void mp_prime(uint64_t p, void *c) {
  MPctx *s = c;
  Ilog_ui(&s->L, p); Iadd(&s->TH, &s->TH, &s->L);                 /* theta */
  Ilog_ui(&s->L1, p - 1 > 0 ? p - 1 : 1);
  if (p > 2) { Isub(&s->t, &s->L, &s->L1); Iadd(&s->SL, &s->SL, &s->t); }
  else Iadd(&s->SL, &s->SL, &s->L);                                /* log(2/1) */
  if (p < 5) return;
  /* F = exp(SL); RHS = e^gamma log TH + 2.50637/log TH (increasing in log TH > 1.19) */
  Iexp(&s->F, &s->SL); Ilog(&s->lt, &s->TH);
  if (mpfr_cmp_d(s->lt.lo, 1.2) < 0) { printf("  log theta too small at %llu\n", (unsigned long long)p); s->ok = 0; return; }
  mpfr_mul(s->rhs.lo, s->eg.lo, s->lt.lo, D); mpfr_div(s->t.lo, s->c.lo, s->lt.lo, D); mpfr_add(s->rhs.lo, s->rhs.lo, s->t.lo, D);
  /* margin lower bound: rhs.lo - F.hi */
  mpfr_sub(s->t.lo, s->rhs.lo, s->F.hi, D);
  if (mpfr_less_p(s->t.lo, s->worst.lo)) { mpfr_set(s->worst.lo, s->t.lo, D); s->wat = p; }
  if (p > 10000 && mpfr_less_p(s->t.lo, s->worst4.lo)) { mpfr_set(s->worst4.lo, s->t.lo, D); s->wat4 = p; }
  if (mpfr_sgn(s->t.lo) <= 0) { s->ok = 0; printf("  fails at x = %llu\n", (unsigned long long)p); }
  s->count++;
}
static void check_mertens_product(void) {
  printf("== mertens_product_small: prod_{p<=x} p/(p-1) < e^gamma log theta(x) + 2.50637/log theta(x), primes 5 <= x <= 2*10^8\n");
  MPctx s;
  Iinit(&s.SL); Iinit(&s.TH); Iinit(&s.L); Iinit(&s.L1); Iinit(&s.F); Iinit(&s.lt); Iinit(&s.rhs); Iinit(&s.t);
  Iinit(&s.eg); Iinit(&s.c); Iinit(&s.worst); Iinit(&s.worst4);
  Iset_ui(&s.SL, 0); Iset_ui(&s.TH, 0); Iset_str(&s.c, "2.50637");
  mpfr_const_euler(s.eg.lo, D); mpfr_exp(s.eg.lo, s.eg.lo, D);
  mpfr_const_euler(s.eg.hi, U); mpfr_exp(s.eg.hi, s.eg.hi, U);
  mpfr_set_ui(s.worst.lo, 100, D); mpfr_set_ui(s.worst4.lo, 100, D); s.ok = 1; s.count = 0;
  for_primes(200000000ULL, mp_prime, &s);
  printf("  %ld primes checked; min margin >= %.4e at x = %llu; for x > 10^4: >= %.6f at x = %llu\n",
         s.count, mpfr_get_d(s.worst.lo, D), (unsigned long long)s.wat, mpfr_get_d(s.worst4.lo, D), (unsigned long long)s.wat4);
  verdict("mertens_product_small", s.ok);
}

/* ---------- K_pieces, K_blocks:  Psi(k) = sum_{n<=k} Lambda(n)/n up to 10^9 ---------- */
static const char *HBLK[20] = {"0.02012", "0.01191", "0.007334", "0.006359", "0.005002", "0.003464",
  "0.002257", "0.001477", "0.001299", "0.0007304", "0.0006189", "0.0003705", "0.0002869", "0.0001922",
  "0.0001315", "0.000125", "0.00007399", "0.00005302", "0.00003196", "0.00002567"};
typedef struct {
  I P, L, Lv, t, X; I small[1001];   /* small[k] = Psi(k), k <= 1000 */
  mpfr_t bmax[20], bmin[20];          /* over block j: max of X.hi, min of X.lo, X = Psi(k) - log t */
  uint64_t prev; I Lprev;             /* current run starts at prev (Psi = P), log(prev) = Lprev */
  uint64_t filled;                    /* small[] filled up to */
} Kctx;
static int blockof(uint64_t k) { uint64_t q = k / 1000; int j = 0; while (q >= 2) { q >>= 1; j++; } return j; }
static void K_upd(Kctx *s, int j, I *X) {
  if (mpfr_greater_p(X->hi, s->bmax[j])) mpfr_set(s->bmax[j], X->hi, U);
  if (mpfr_less_p(X->lo, s->bmin[j])) mpfr_set(s->bmin[j], X->lo, D);
}
/* the run [a, b) of k with Psi(k) = P; t ranges over [a, b] (t = k, k+1) */
static void K_run(Kctx *s, uint64_t a, I *La, uint64_t b, I *Lb) {
  if (b <= 1000 || a >= 1000000000ULL) return;
  if (a < 1000) { a = 1000; Ilog_ui(La, 1000); }
  if (b > 1000000000ULL) { b = 1000000000ULL; Ilog_ui(Lb, b); }
  /* split at block boundaries 1000*2^j */
  uint64_t x = a; I Lx; Iinit(&Lx); Iset(&Lx, La);
  while (x < b) {
    int j = blockof(x); uint64_t e = 1000ULL << (j + 1); if (e > b) e = b;
    I Le; Iinit(&Le); if (e == b) Iset(&Le, Lb); else Ilog_ui(&Le, e);
    Isub(&s->X, &s->P, &Lx); K_upd(s, j, &s->X);
    Isub(&s->X, &s->P, &Le); K_upd(s, j, &s->X);
    Iset(&Lx, &Le); Iclear(&Le); x = e;
  }
  Iclear(&Lx);
}
static void K_pp(uint64_t v, uint64_t p, void *c) {
  Kctx *s = c;
  /* the run [prev, v) ends here */
  Ilog_ui(&s->Lv, v);
  if (s->prev) K_run(s, s->prev, &s->Lprev, v, &s->Lv);
  while (s->filled + 1 < v && s->filled < 1000) { s->filled++; Iset(&s->small[s->filled], &s->P); }
  if (v == p) Iset(&s->L, &s->Lv); else Ilog_ui(&s->L, p);
  Idiv_ui(&s->t, &s->L, v); Iadd(&s->P, &s->P, &s->t);
  if (v <= 1000) { s->filled = v; Iset(&s->small[v], &s->P); }
  s->prev = v; Iset(&s->Lprev, &s->Lv);
}
static void check_K(void) {
  printf("== K_blocks / K_pieces: Psi(k) = sum_{n<=k} Lambda(n)/n to 10^9, EZ = Psi(10^9) - log 10^9\n");
  Kctx *s = malloc(sizeof(Kctx));
  Iinit(&s->P); Iinit(&s->L); Iinit(&s->Lv); Iinit(&s->t); Iinit(&s->X); Iinit(&s->Lprev);
  for (int k = 0; k <= 1000; k++) { Iinit(&s->small[k]); Iset_ui(&s->small[k], 0); }
  for (int j = 0; j < 20; j++) { mpfr_init2(s->bmax[j], PREC); mpfr_init2(s->bmin[j], PREC); mpfr_set_si(s->bmax[j], -1000, U); mpfr_set_si(s->bmin[j], 1000, D); }
  Iset_ui(&s->P, 0); s->prev = 0; s->filled = 1;   /* Psi(1) = 0 */
  uint64_t Z = 1000000000ULL;
  for_prime_powers(Z, K_pp, s);
  /* last run [prev, Z]: k = Z is not in the K_blocks range, but Psi(Z) = P */
  { I LZ; Iinit(&LZ); Ilog_ui(&LZ, Z); K_run(s, s->prev, &s->Lprev, Z, &LZ); Iclear(&LZ); }
  I EZ, LZ; Iinit(&EZ); Iinit(&LZ); Ilog_ui(&LZ, Z); Isub(&EZ, &s->P, &LZ);
  printf("  Psi(10^9) in [%.12f, %.12f];  EZ in [%.12f, %.12f]\n", lo_d(&s->P), hi_d(&s->P), lo_d(&EZ), hi_d(&EZ));
  int ok = 1; mpfr_t a, b; mpfr_init2(a, PREC); mpfr_init2(b, PREC);
  for (int j = 0; j < 20; j++) {
    /* max over block of |X - EZ| <= max(bmax - EZ.lo, EZ.hi - bmin) */
    mpfr_sub(a, s->bmax[j], EZ.lo, U); mpfr_sub(b, EZ.hi, s->bmin[j], U); mpfr_max(a, a, b, U);
    I h; Iinit(&h); Iset_str(&h, HBLK[j]);
    int okj = mpfr_lessequal_p(a, h.lo);
    printf("  block %2d: max |E - EZ| <= %.7g   hblk = %s   %s\n", j, mpfr_get_d(a, U), HBLK[j], okj ? "ok" : "FAIL");
    ok &= okj; Iclear(&h);
  }
  verdict("K_blocks", ok);
  /* K_pieces: sum_{k=1}^{999} sum_{i<m_k} g log(b/a), a = k + i/m, b = k + (i+1)/m */
  I sum, A, B, LA, LB, g1, g2, t; Iinit(&sum); Iinit(&A); Iinit(&B); Iinit(&LA); Iinit(&LB); Iinit(&g1); Iinit(&g2); Iinit(&t);
  Iset_ui(&sum, 0);
  for (unsigned long k = 1; k < 1000; k++) {
    unsigned long m = (400 + k - 1) / k;
    for (unsigned long i = 0; i < m; i++) {
      Iset_q(&A, (long)(k * m + i), m); Iset_q(&B, (long)(k * m + i + 1), m);
      Ilog(&LA, &A); Ilog(&LB, &B);
      Isub(&g1, &s->small[k], &LA); Isub(&g1, &g1, &EZ); Iabs(&g1, &g1);
      Isub(&g2, &s->small[k], &LB); Isub(&g2, &g2, &EZ); Iabs(&g2, &g2);
      Imax(&g1, &g1, &g2); Isub(&t, &LB, &LA); Imul(&t, &t, &g1); Iadd(&sum, &sum, &t);
    }
  }
  I bound; Iinit(&bound); Iset_str(&bound, "0.4035");
  printf("  K_pieces sum in [%.9f, %.9f] (need <= 0.4035)\n", lo_d(&sum), hi_d(&sum));
  verdict("K_pieces", Ile(&sum, &bound));
}

/* ---------- liouville_small ---------- */
static void check_liouville(void) {
  printf("== liouville_small: |sum_{n<=k} lambda(n)/n| log(k+1) <= 0.99, 1 <= k <= 10^5\n");
  int N = 100000; int *om = calloc(N + 1, sizeof(int)); int *rest = malloc((N + 1) * sizeof(int));
  for (int i = 0; i <= N; i++) rest[i] = i;
  for (int p = 2; p <= N; p++) if (rest[p] == p) {   /* p prime (untouched so far) */
    for (int m = p; m <= N; m += p) while (rest[m] % p == 0) { rest[m] /= p; om[m]++; }
  }
  I S, t, L, v, worst, c; Iinit(&S); Iinit(&t); Iinit(&L); Iinit(&v); Iinit(&worst); Iinit(&c);
  Iset_ui(&S, 0); Iset_ui(&worst, 0); Iset_str(&c, "0.99"); int ok = 1, wat = 0;
  for (int k = 1; k <= N; k++) {
    Iset_q(&t, (om[k] & 1) ? -1 : 1, k); Iadd(&S, &S, &t);
    Iabs(&v, &S); Ilog_ui(&L, k + 1); Imul(&v, &v, &L);
    if (mpfr_greater_p(v.hi, worst.hi)) { Iset(&worst, &v); wat = k; }
    if (!Ile(&v, &c)) { ok = 0; printf("  fails at k = %d\n", k); }
  }
  printf("  max in [%.6f, %.6f] at k = %d\n", lo_d(&worst), hi_d(&worst), wat);
  verdict("liouville_small", ok);
  free(om); free(rest);
}

/* ---------- C_grid ---------- */
static void check_C_grid(void) {
  printf("== C_grid: (2.8 + (i+1)/100) G(2.8 + i/100) <= 2.8, i < 7720\n");
  int U0 = 3000; char *sf = malloc(U0 + 1); memset(sf, 1, U0 + 1); sf[0] = 0;
  for (int p = 2; p * p <= U0; p++) for (int m = p * p; m <= U0; m += p * p) sf[m] = 0;
  I *w = malloc(sizeof(I) * (U0 + 1)), *tl = malloc(sizeof(I) * (U0 + 1));
  for (int u = 1; u <= U0; u++) {
    Iinit(&w[u]); Iinit(&tl[u]);
    Iset_q(&w[u], sf[u] ? 1 : 0, (unsigned long)u * u);
    Ilog_ui(&tl[u], u); mpfr_mul_ui(tl[u].lo, tl[u].lo, 2, D); mpfr_mul_ui(tl[u].hi, tl[u].hi, 2, U);
  }
  I f53, c99, tail, a, G, beta, t, v, worst, lim; Iinit(&f53); Iinit(&c99); Iinit(&tail); Iinit(&a); Iinit(&G);
  Iinit(&beta); Iinit(&t); Iinit(&v); Iinit(&worst); Iinit(&lim);
  Iset_q(&f53, 5, 3); Iset_str(&c99, "0.99"); Iset_q(&tail, 10, 18003);  /* (5/3)/(3000 + 1/2) = 10/18003 */
  Iset_str(&lim, "2.8"); Iset_ui(&worst, 0); int ok = 1, wat = 0;
  for (int i = 0; i < 7720; i++) {
    Iset_q(&a, 280 + i, 100); Iset(&G, &tail);
    for (int u = 1; u <= U0; u++) {
      if (!sf[u]) continue;
      /* upper bound for beta(a, u) */
      if (mpfr_less_p(tl[u].hi, a.lo)) {
        mpfr_sub(t.lo, a.lo, tl[u].hi, D);          /* lower bound for a - 2 log u > 0 */
        mpfr_div(t.hi, c99.hi, t.lo, U);           /* upper bound for 0.99/(a - 2 log u) */
        mpfr_min(beta.hi, t.hi, f53.hi, U);
        mpfr_sub(t.hi, a.hi, tl[u].lo, U); mpfr_div(t.lo, c99.lo, t.hi, D);
        mpfr_min(beta.lo, t.lo, f53.lo, D);
      } else if (mpfr_lessequal_p(a.hi, tl[u].lo)) { Iset(&beta, &f53); }
      else { mpfr_set_ui(beta.lo, 0, D); mpfr_set(beta.hi, f53.hi, U); }   /* undecided: beta in [0, 5/3] */
      Imul_pos(&t, &w[u], &beta); Iadd(&G, &G, &t);
    }
    Iset_q(&t, 281 + i, 100); Imul(&v, &t, &G);
    if (mpfr_greater_p(v.hi, worst.hi)) { Iset(&worst, &v); wat = i; }
    if (!Ile(&v, &lim)) { ok = 0; printf("  fails at i = %d\n", i); }
  }
  printf("  max in [%.6f, %.6f] at i = %d\n", lo_d(&worst), hi_d(&worst), wat);
  verdict("C_grid", ok);
}

/* ---------- MV Lemma 7 / Lemma 8 ---------- */
static uint32_t *phi_arr; static char *sqf_arr;
static void sieve_phi_mu2(uint32_t N) {
  phi_arr = malloc(sizeof(uint32_t) * (N + 1)); sqf_arr = malloc(N + 1);
  for (uint32_t i = 0; i <= N; i++) { phi_arr[i] = i; sqf_arr[i] = 1; }
  sqf_arr[0] = 0;
  for (uint32_t p = 2; p <= N; p++) if (phi_arr[p] == p) {        /* p prime */
    for (uint32_t m = p; m <= N; m += p) phi_arr[m] -= phi_arr[m] / p;
    if ((uint64_t)p * p <= N) for (uint64_t m = (uint64_t)p * p; m <= N; m += (uint64_t)p * p) sqf_arr[m] = 0;
  }
}
static void check_lemma7(void) {
  printf("== lemma7_numeric: log(r+1) + 1.07 <= G(r), 6 <= r <= 29999999;  GS_N0: G(3*10^7) >= log(3*10^7) + 1.3325\n");
  uint32_t N = 30000000; sieve_phi_mu2(N);
  I G, t, L, c, m, worst; Iinit(&G); Iinit(&t); Iinit(&L); Iinit(&c); Iinit(&m); Iinit(&worst);
  Iset_ui(&G, 0); Iset_str(&c, "1.07"); mpfr_set_ui(worst.lo, 100, D); mpfr_set_ui(worst.hi, 100, U);
  int ok = 1; uint32_t wat = 0, last = 0;
  /* G constant on [s_i, s_{i+1} - 1]; worst r = s_{i+1} - 1, i.e. log(s_{i+1}) */
  for (uint32_t s = 1; s <= N; s++) {
    if (!sqf_arr[s]) continue;
    if (last >= 6 || (last && s - 1 >= 6)) {
      /* run [max(last, 6), s - 1] with value G */
      Ilog_ui(&L, s); Iadd(&L, &L, &c); Isub(&m, &G, &L);
      if (mpfr_less_p(m.lo, worst.lo)) { Iset(&worst, &m); wat = s - 1; }
      if (mpfr_sgn(m.lo) < 0) { ok = 0; printf("  fails at r = %u\n", s - 1); }
    }
    Iset_q(&t, 1, phi_arr[s]); Iadd(&G, &G, &t); last = s;
  }
  /* final run [last, 29999999] (3*10^7 itself is not squarefree) */
  Ilog_ui(&L, N); Iadd(&L, &L, &c); Isub(&m, &G, &L);
  if (mpfr_less_p(m.lo, worst.lo)) { Iset(&worst, &m); wat = N - 1; }
  if (mpfr_sgn(m.lo) < 0) { ok = 0; printf("  fails at the end\n"); }
  printf("  min margin in [%.6f, %.6f] at r = %u\n", lo_d(&worst), hi_d(&worst), wat);
  verdict("lemma7_numeric", ok);
  Ilog_ui(&L, N); Isub(&m, &G, &L); Iset_str(&c, "1.3325");
  printf("  G(3*10^7) - log(3*10^7) in [%.9f, %.9f] (G(3e7) = G(29999999): %s)\n", lo_d(&m), hi_d(&m), sqf_arr[N] ? "no" : "yes");
  verdict("GS_N0", Ile(&c, &m));
}
static void check_lemma8(void) {
  printf("== lemma8_numeric: for 2 <= n <= 10^4, log(n+1) + 0.25068 < sum g(r)(n+1)/(n+1+r) and sum g(r) r(n+1)/((n+1+r)(n+r)) <= 1\n");
  if (!phi_arr) sieve_phi_mu2(30000000);
  I A, B, t, u, L, c, one, w1, w2; Iinit(&A); Iinit(&B); Iinit(&t); Iinit(&u); Iinit(&L); Iinit(&c); Iinit(&one); Iinit(&w1); Iinit(&w2);
  Iset_str(&c, "0.25068"); Iset_ui(&one, 1); mpfr_set_ui(w1.lo, 100, D); Iset_ui(&w2, 0);
  int ok = 1, a1 = 0, a2 = 0;
  for (unsigned long n = 2; n <= 10000; n++) {
    Iset_ui(&A, 0); Iset_ui(&B, 0);
    for (unsigned long r = 1; r <= n; r++) {
      if (!sqf_arr[r]) continue;
      /* g(r) (n+1)/(n+1+r) = (n+1) / (phi(r) (n+1+r)) : exact rational num/den */
      Iset_q(&t, (long)(n + 1), (unsigned long)phi_arr[r] * (n + 1 + r)); Iadd(&A, &A, &t);
      /* g(r) r (n+1)/((n+1+r)(n+r)) */
      mpfr_set_ui(u.lo, r * (n + 1), D); mpfr_div_ui(u.lo, u.lo, phi_arr[r], D); mpfr_div_ui(u.lo, u.lo, n + 1 + r, D); mpfr_div_ui(u.lo, u.lo, n + r, D);
      mpfr_set_ui(u.hi, r * (n + 1), U); mpfr_div_ui(u.hi, u.hi, phi_arr[r], U); mpfr_div_ui(u.hi, u.hi, n + 1 + r, U); mpfr_div_ui(u.hi, u.hi, n + r, U);
      Iadd(&B, &B, &u);
    }
    Ilog_ui(&L, n + 1); Iadd(&L, &L, &c); Isub(&t, &A, &L);
    if (mpfr_less_p(t.lo, w1.lo)) { Iset(&w1, &t); a1 = (int)n; }
    if (mpfr_sgn(t.lo) <= 0) { ok = 0; printf("  first inequality fails at n = %lu\n", n); }
    if (mpfr_greater_p(B.hi, w2.hi)) { Iset(&w2, &B); a2 = (int)n; }
    if (!Ile(&B, &one)) { ok = 0; printf("  second inequality fails at n = %lu\n", n); }
  }
  printf("  first: min margin in [%.4e, %.4e] at n = %d;  second: max in [%.6f, %.6f] at n = %d\n",
         lo_d(&w1), hi_d(&w1), a1, lo_d(&w2), hi_d(&w2), a2);
  verdict("lemma8_numeric", ok);
}

int main(int argc, char **argv) {
  const char *all[] = {"nonprime", "mertens_lower", "logsq", "mertens_product", "K", "liouville", "C_grid", "lemma7", "lemma8"};
  int na = argc > 1 ? argc - 1 : 9;
  scratch_init();
  printf("MPFR %s, precision %ld bits\n\n", mpfr_get_version(), (long)PREC);
  for (int i = 0; i < na; i++) {
    const char *n = argc > 1 ? argv[i + 1] : all[i];
    if (!strcmp(n, "nonprime")) check_nonprime();
    else if (!strcmp(n, "mertens_lower") || !strcmp(n, "mertens_point")) check_mertens_family();
    else if (!strcmp(n, "logsq")) check_logsq();
    else if (!strcmp(n, "mertens_product")) check_mertens_product();
    else if (!strcmp(n, "K")) check_K();
    else if (!strcmp(n, "liouville")) check_liouville();
    else if (!strcmp(n, "C_grid")) check_C_grid();
    else if (!strcmp(n, "lemma7")) check_lemma7();
    else if (!strcmp(n, "lemma8")) check_lemma8();
    else { fprintf(stderr, "unknown check %s\n", n); return 2; }
  }
  printf(failures ? "SOME CHECKS FAILED (%d)\n" : "ALL CHECKS PASSED\n", failures);
  return failures != 0;
}
