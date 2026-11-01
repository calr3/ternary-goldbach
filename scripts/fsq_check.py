"""Rigorous check of the numerical axiom `fsq_le` (Prelim/SqfreeCount.lean, [B, p. 83]):

    f(X) <= 1.27 X  for all X >= 0,   f(X) = #{m <= X sq-free} + (X^2/2) sum_{m > X sq-free} 1/m^2.

Reduction (as in [B]):
* 0 <= X < 1: f(X)/X = (X/2) * 15/pi^2 < 0.76.
* Between consecutive square-free integers m_k <= X < m_{k+1}, f(X)/X = k/X + (X/2) S_k is convex,
  and f jumps up by 1/2 at each square-free integer, so sup f(X)/X = max over square-free m of f(m)/m.
* For m >= 51: #{n <= m sq-free} <= m - floor(m/4) <= 3m/4 + 1 and sum_{n > m} 1/n^2 < 1/m, so
  f(m)/m < 3/4 + 1/m + 1/2 <= 1.2697 < 1.27.
So it suffices to check square-free m <= 50, which is done here in interval arithmetic
(sum_{sq-free} 1/n^2 = zeta(2)/zeta(4) = 15/pi^2).  The maximum is f(2)/2 = 15/pi^2 - 1/4 = 1.269817...

Usage: python3 scripts/fsq_check.py   (instant; needs mpmath)

NOTE: `fsq_le` is now proved in Lean (Prelim/SmallFsq.lean); this script is kept for reference.
"""
from mpmath import iv

iv.dps = 40
def sqfree(n):
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True

total = iv.mpf(15) / iv.pi ** 2           # sum over all square-free n of 1/n^2
worst = None
head = iv.mpf(0); count = 0
for m in range(1, 51):
    if not sqfree(m):
        continue
    count += 1
    head += iv.mpf(1) / (m * m)
    tail = total - head                   # sum over square-free n > m of 1/n^2
    r = (count + iv.mpf(m * m) / 2 * tail) / m
    if worst is None or r.b > worst[0].b:
        worst = (r, m)
    assert r.b < 1.27, (m, r)
assert 3 / 4 + 1 / 51 + 1 / 2 < 1.27
assert (iv.mpf(1) / 2 * total).b < 0.76
print("max_{m <= 50 sq-free} f(m)/m in", worst[0], "at m =", worst[1], "(need < 1.27): OK")
