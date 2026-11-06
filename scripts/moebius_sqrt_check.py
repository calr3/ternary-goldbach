"""Finite check behind the former hypothesis `moebius_sqrt_small` (Prelim/LiouvilleBound.lean):

    |m(k)| <= sqrt(2/(k+1))   for 1 <= k < 10^10,   m(k) = sum_{n <= k} mu(n)/n,

i.e. |m(y)| <= sqrt(2/y) for real 1 <= y < 10^10 (cf. [H, (2.24)], checked there to 10^12 by Helfgott).
Equality holds at k = 1 (m(1) = 1); the script reports the maximum of |m(k)| sqrt((k+1)/2) over k >= 2.

Segmented sieve of mu over [0, 10^10) in blocks of 2*10^7: sign flips and log p accumulations for p <= 10^5,
zeroing at multiples of p^2, and one more sign flip where a prime factor > 10^5 remains.  The running sum is
float64 within a block, carried across blocks with math.fsum.  About an hour, < 1 GB.
Usage: python3 scripts/moebius_sqrt_check.py
"""
import numpy as np, math, sys, time
N = 10**10; SEG = 2 * 10**7
P = 10**5
isp = np.ones(P + 1, bool); isp[:2] = False
for p in range(2, int(P ** 0.5) + 1):
    if isp[p]: isp[p*p::p] = False
primes = [int(p) for p in np.nonzero(isp)[0]]
logs = {p: np.float32(math.log(p)) for p in primes}
carry = 0.0
worst = 0.0; at = None
t0 = time.time()
for start in range(0, N, SEG):
    end = min(start + SEG, N)
    L = end - start
    mu = np.ones(L, np.int8)
    lp = np.zeros(L, np.float32)
    for p in primes:
        if p * p >= end and p > end:   # never: all p <= 1e5 < end for start > 0
            break
        f = ((start + p - 1) // p) * p
        if f < end:
            sl = slice(f - start, L, p)
            mu[sl] = -mu[sl]
            lp[sl] += logs[p]
        pp = p * p
        if pp < end:
            f2 = ((start + pp - 1) // pp) * pp
            mu[f2 - start::pp] = 0
    n = np.arange(start, end, dtype=np.float64)
    if start == 0:
        n[0] = 1.0; mu[0] = 0          # n = 0 is not in the sum
        mu[1] = 1                       # n = 1
    big = lp < (np.log(n) - 0.5).astype(np.float32)
    mu[big] = -mu[big]
    if start == 0:
        mu[0] = 0; mu[1] = 1
    terms = mu / n
    c = carry + np.cumsum(terms)
    carry = math.fsum([carry, math.fsum(terms)])
    k = n
    r = np.abs(c) * np.sqrt((k + 1.0) / 2.0)
    if start == 0:
        r[0] = 0.0; r[1] = 0.0          # k = 0 excluded; k = 1 is the equality case
    i = int(np.argmax(r))
    if r[i] > worst:
        worst, at = float(r[i]), start + i
    if (start // SEG) % 50 == 0:
        print(f"{end:.3e}  m={c[-1]:.3e}  worst ratio so far {worst:.6f} at k={at}  ({time.time()-t0:.0f}s)",
              flush=True)
print("m(10^10 - 1) =", carry)
print("max over 2 <= k < 1e10 of |m(k)| sqrt((k+1)/2) =", worst, "at k =", at)
