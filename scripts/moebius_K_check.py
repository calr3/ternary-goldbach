"""Finite checks behind the former hypotheses `K_pieces` and `K_blocks` (Prelim/MoebiusBound.lean).

Psi(k) = sum_{n<=k} Lambda(n)/n,  E(y) = Psi(floor y) - log y,  EZ = E(10^9).
* K_pieces: sum_{k=1}^{999} sum_{i < m_k} g_{k,i} log(b/a) <= 0.4035, where m_k = ceil(400/k),
  [a, b) = [k + i/m_k, k + (i+1)/m_k), g_{k,i} = max(|Psi(k) - log a - EZ|, |Psi(k) - log b - EZ|).
* K_blocks: for 1000 <= k < 10^9, with j = Nat.log 2 (k / 1000) (integer division; here the exact binary
  exponent of the float k // 1000), max(|Psi(k) - log k - EZ|, |Psi(k) - log(k+1) - EZ|) <= hblk j, where hblk j
  is the printed block maximum plus 1e-7 (allowance for float64 rounding in the running sum), rounded up to
  4 significant digits; the script prints the Lean list.
Float64; the running sum is carried with math.fsum per segment.  ~25 min, < 1 GB.
Usage: python3 scripts/moebius_K_check.py
"""
import numpy as np, math, bisect
Z = 10**9; SEG = 10**7; Y = 1000
r = math.isqrt(Z) + 1
small = np.ones(r + 1, bool); small[:2] = False
for p in range(2, math.isqrt(r) + 1):
    if small[p]: small[p*p::p] = False
sp = [int(p) for p in np.nonzero(small)[0]]
pp = []
for p in sp:
    v = p * p
    while v <= Z: pp.append((v, math.log(p))); v *= p
pp.sort(); ppv = [v for v, _ in pp]
psit = 0.0; Psmall = None
nb = 20
bmax = [0.0] * nb
store = []   # (jj, hi, lo) block extremes, EZ applied later
blo = [1e9] * nb; bhi = [-1e9] * nb
for start in range(0, Z + 1, SEG):
    end = min(start + SEG, Z + 1)
    seg = np.ones(end - start, bool)
    if start == 0: seg[:2] = False
    for p in sp:
        if p * p >= end: break
        f = max(p * p, ((start + p - 1) // p) * p); seg[f - start::p] = False
    idx = np.nonzero(seg)[0]; lam = np.zeros(end - start)
    nn = (idx + start).astype(float); lam[idx] = np.log(nn) / nn
    a = bisect.bisect_left(ppv, start); b = bisect.bisect_left(ppv, end)
    for v, l in pp[a:b]: lam[v - start] += l / v
    c = psit + np.cumsum(lam); psit = math.fsum([psit, math.fsum(lam)])
    if start == 0: Psmall = c[:Y + 1].copy()
    ks = np.arange(start, end, dtype=float)
    m = (ks >= Y) & (ks < Z)
    if m.any():
        kk = ks[m]; cc = c[m]
        hi = cc - np.log(kk); lo = cc - np.log(kk + 1)
        j = np.frexp(np.floor(kk / Y))[1] - 1     # exact floor(log2(k // 1000))
        for jj in np.unique(j):
            sel = j == jj
            bhi[jj] = max(bhi[jj], hi[sel].max()); blo[jj] = min(blo[jj], lo[sel].min())
EZ = psit - math.log(Z)
print("EZ = E(1e9) =", EZ)
A1 = 0.0
for k in range(1, Y):
    mk = -(-400 // k)
    for i in range(mk):
        a = k + i / mk; b = k + (i + 1) / mk
        g = max(abs(Psmall[k] - math.log(a) - EZ), abs(Psmall[k] - math.log(b) - EZ))
        A1 += g * math.log(b / a)
print("K_pieces sum =", A1)
def up(h):
    h += 1e-7; e = math.floor(math.log10(h)); s = 10.0 ** (3 - e)
    return math.ceil(h * s) / s
H = []
for jj in range(nb):
    h = max(abs(bhi[jj] - EZ), abs(blo[jj] - EZ)); H.append(up(h))
    print("block", jj, "h_j =", h, " hblk =", H[-1])
print("Lean hblk values:", ", ".join(repr(v) for v in H))
