"""What the g2 tail behind [H, (5.31)] needs from a Moebius bound (float model of G2Tail.lean): int_{1e4}^S |g2|/y <= sum_d f(d)^2 Lam_d Xi_d + V(1)*4*1.2338^2/X,
with V(k) = sum_{k <= j < K} m(j)^2 log(1+1/j) + tau  (tau = the bound for j >= K = 11815).
With Ramare tau ~ 1e-4 and the tail is 0.0046 (Lean: 0.0045); T2 <= 0.37273 needs tau <= 5.7e-4,
i.e. |m(x)| <= 0.073/log x for x >= 11815.

Usage: python3 scripts/g2_tail_moebius_model.py"""
import math, sys
X, K = 10000, 11815
mu = [1] * (K + 1); mu[0] = 0
isp = [True] * (K + 1)
for p in range(2, K + 1):
    if isp[p]:
        for q in range(2 * p, K + 1, p): isp[q] = False
        for q in range(p, K + 1, p): mu[q] = -mu[q]
        for q in range(p * p, K + 1, p * p): mu[q] = 0
m = [0.0] * (K + 1); s = 0.0
for j in range(1, K + 1):
    s += mu[j] / j; m[j] = s
term = [0.0] * (K + 1)
for j in range(1, K): term[j] = m[j] ** 2 * math.log1p(1 / j)
suf = [0.0] * (K + 2)
for j in range(K - 1, 0, -1): suf[j] = suf[j + 1] + term[j]
print("sum_{j<K} m(j)^2 log(1+1/j) =", suf[1], "(Lean cP = 0.81494)")
def primes_of(n):
    ps = []; d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: ps.append(n)
    return ps
PF = [None] + [primes_of(a) for a in range(1, X + 1)]
den1 = [0] + [a * math.prod(p + 1 for p in PF[a] if p % 2) for a in range(1, X + 1)]
def tail_bound(tau):
    V = lambda k: suf[k] + tau if k < K else tau
    sq = [0.0] + [math.sqrt(V(k)) for k in range(1, X + 1)]
    total = 0.0
    for d in range(1, X + 1, 2):
        if mu[d] == 0: continue
        pd = PF[d]
        sig = math.prod(p + 1 for p in pd)
        s1 = sl = 0.0
        for a in range(1, X // d + 1):
            g = math.prod(p + 1 for p in pd if a % p == 0)
            h = g / den1[a]
            s1 += h; sl += h * sq[X // (d * a)]
        Bd = 2.47 * sig / d
        Lam = sl + sq[1] * (Bd - s1)
        total += Lam * Lam / sig ** 2
    return total + V(1) * 4 * 1.2338 ** 2 / X
for name, tau in [("Ramare 0.03/log x", 0.0009 * 1.00001 / math.log(K)),
                  ("own 0.55/(log x - 0.7521)", 0.55 ** 2 / (math.log(K) - 0.7521))]:
    t = tail_bound(tau)
    T2 = 0.3605763 + 0.000922 + 1.25 * t
    print(f"{name}: tau = {tau:.3e}, tail <= {t:.5f}, T2 <= {T2:.5f}  (needed: T2 <= 0.37273)")

def tau_max(T2cap):
    lo, hi = 0.0, 0.05
    for _ in range(60):
        mid = (lo + hi) / 2
        if 0.3605763 + 0.000922 + 1.25 * tail_bound(mid) <= T2cap: lo = mid
        else: hi = mid
    return lo
L = math.log(K)
print()
for cap in [0.37273, 0.38, 0.40]:
    tm = tau_max(cap)
    # tau = C^2/(log K - 0.7521) for a bound C/(log x - 0.7521); tau = c^2/log K for c/log x
    print(f"T2 <= {cap}: tau <= {tm:.3e}  <=> |m(x)| <= {math.sqrt(tm*(L-0.7521)):.4f}/(log x - 0.7521)"
          f"  or {math.sqrt(tm*L):.4f}/log x  for x >= 11815")
# tail if exact m(j) were known further, with C/(log x - 0.7521) beyond J
print()
for J in [10**5, 10**6, 10**7, 10**9]:
    print(f"exact m to {J:.0e}, then 0.55/(log x - 0.7521): tau = {0.55**2/(math.log(J)-0.7521):.4f}")
