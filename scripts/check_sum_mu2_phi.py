"""Rigorous check of the numerical axiom `sum_odd_mu_sq_div_totient` ([B, §14.1]):

    6.798779 <= sum_{q <= 150000, q odd} mu(q)^2 / phi(q) <= 6.79878.

Each term 1/phi(q) is rounded down (lower sum) resp. up (upper sum) with `decimal` at 40 digits,
and the partial sums are accumulated with the same directed rounding, so [lo, hi] encloses the
exact rational value.
"""
from decimal import Decimal, getcontext, ROUND_FLOOR, ROUND_CEILING

N = 150000
phi = list(range(N + 1))
sqfree = [True] * (N + 1)
for p in range(2, N + 1):
    if phi[p] == p:  # p prime
        for m in range(p, N + 1, p):
            phi[m] -= phi[m] // p
        for m in range(p * p, N + 1, p * p):
            sqfree[m] = False

def directed_sum(rounding):
    ctx = getcontext().copy()
    ctx.prec = 40
    ctx.rounding = rounding
    s = Decimal(0)
    for q in range(1, N + 1, 2):
        if sqfree[q]:
            s = ctx.add(s, ctx.divide(Decimal(1), Decimal(phi[q])))
    return s

lo = directed_sum(ROUND_FLOOR)
hi = directed_sum(ROUND_CEILING)
print("lower", lo)
print("upper", hi)
assert Decimal("6.798779") <= lo and hi <= Decimal("6.79878")
print("OK: 6.798779 <= S <= 6.79878")
