"""Generate the data of TernaryGoldbach/Prelim/SmallProdAp.lean (`prod_ap_le'`).

* PK: the primes p < 10^4 with the least k_p such that p k_p^3 >= 10^18 (so p^{-1/3} <= k_p/10^6),
  in chunks PK0..PK12 of 100 entries;
* Q0..Q9: the primes in [1000 i, 1000 (i+1)), for the chunked completeness scan.
Also checks, in exact rational arithmetic, prod (1 + (r^2 + r)/(p-1)) <= 7.99 with r = k_p/10^6
(value 7.985536...).  The Lean file re-checks everything with `decide +kernel`.

Usage: python3 scripts/gen_prod_ap.py   (prints the Lean definitions)
"""
from fractions import Fraction as F
from sympy import primerange

PK = []
for p in primerange(2, 10000):
    k = int(round(10**6 * p ** (-1 / 3))) - 2
    while p * k**3 < 10**18:
        k += 1
    PK.append((p, k))
prod = F(1)
for p, k in PK:
    r = F(k, 10**6)
    prod *= 1 + (r * r + r) / (p - 1)
assert len(PK) == 1229 and prod <= F(799, 100)
print(f"-- product = {float(prod):.9f}")
for i in range(0, len(PK), 100):
    chunk = ", ".join(f"({p}, {k})" for p, k in PK[i:i + 100])
    print(f"def PK{i // 100} : List (ℕ × ℕ) := [{chunk}]")
for i in range(10):
    print(f"def Q{i} : List ℕ := [{', '.join(map(str, primerange(1000 * i, 1000 * (i + 1))))}]")
