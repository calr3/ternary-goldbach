"""Rigorous check of the axiom `eta2DD_small` (MinorArcs/InnerSums.lean), i.e. [B, (B.6)] on
0 <= t <= 655 in explicit form:

    |DD(t)| <= 31.521  for 0 <= t <= 655,
    DD(t) = 16 e(-t/2) - 16 e(-t/4) - 4 e(-t) + 4 J(1/4, 1/2) - 4 J(1/2, 1),
    J(a, b) = int_a^b e(-ut)/u^2 du,   e(x) = exp(2 pi i x).

Lean proves DD(t) = (2 pi t)^2 eta2^(t) (two integrations by parts, `eta2DD_eq`) and the bound for
|t| >= 655 (`norm_eta2DD_large`); negative t follow by conjugation.

Method (python-flint / Arb ball arithmetic, which is rigorous):
* For t > 0, with w = 2 pi t, F(u) = -e(-ut)/u - i w (Ci(wu) - i Si(wu)) satisfies
  F'(u) = e(-ut)/u^2, so J(a, b) = F(b) - F(a).  DD(0) = -4 + 4(4 - 2) - 4(2 - 1) = 0.
* Lipschitz bound: d/dt e(-xt) has modulus 2 pi x and |d/dt J(a, b)| <= 2 pi log(b/a), so
  |DD'(t)| <= L = 2 pi (16/2 + 16/4 + 4 + 4 log 2 + 4 log 2) = 2 pi (16 + 8 log 2) < 135.4.
* Stepping: at t0 (a double, exact in Arb), U = upper bound of |DD(t0)|; the step to t1 is accepted
  if U + L (t1 - t0) <= 31.521 (checked in Arb), so |DD| <= 31.521 on [t0, t1].
  Steps continue until t1 >= 655.
A few values are compared with direct rigorous integration (acb.integral).

Usage: pip install python-flint; python3 scripts/rigorous/eta2_fourier_rig.py   (about a minute)
"""
from flint import arb, acb, ctx

ctx.prec = 80
PI = arb.pi()
I = acb(0, 1)
BOUND = arb("31.521")
L = 2 * PI * (16 + 8 * arb(2).log())
assert L.upper() < 135.4


def ex(x):
    return (2 * PI * I * x).exp()


def F(u, t):
    w = 2 * PI * t
    return -ex(-u * t) / u - I * w * (acb((w * u).ci()) - I * acb((w * u).si()))


def DD(t):
    t = arb(t)
    if t == 0:
        return acb(0)
    f14, f12, f1 = F(arb(1) / 4, t), F(arb(1) / 2, t), F(arb(1), t)
    return 16 * ex(-t / 2) - 16 * ex(-t / 4) - 4 * ex(-t) + 4 * (f12 - f14) - 4 * (f1 - f12)


def DD_direct(t):
    t = arb(t)
    J = lambda a, b: acb.integral(lambda u, _: ex(-u * t) / u ** 2, a, b)
    return 16 * ex(-t / 2) - 16 * ex(-t / 4) - 4 * ex(-t) + 4 * J(0.25, 0.5) - 4 * J(0.5, 1)


for tv in [0.5, 3.0, 17.415, 200.0, 654.0]:
    a, b = DD(tv), DD_direct(tv)
    assert (a - b).abs_upper() < 1e-15, (tv, a, b)
print("closed form agrees with direct integration at 5 points")

T0 = 655.0
t0 = 0.0
steps = 0
worst = (0.0, 0.0)          # (largest upper bound of |DD(t0)|, t0)
while t0 < T0:
    U = abs(DD(t0)).upper()
    if U > worst[0]:
        worst = (float(U), t0)
    m = BOUND - U
    assert m > 0, ("bound fails at", t0, U)
    h = 0.999 * float(m.lower()) / float(L.upper())
    t1 = t0 + h
    if t1 == t0:
        raise SystemExit(f"step underflow at t = {t0}")
    ok = (arb(U) + L * (arb(t1) - arb(t0))) <= BOUND
    assert ok, ("step not certified", t0, t1)
    t0 = t1
    steps += 1
print(f"{steps} steps cover [0, {t0:.3f}] ⊇ [0, 655]; max of |DD(t0)| <= {worst[0]:.8f} at t0 = {worst[1]:.6f}")
print("eta2DD_small: OK (rigorous): |DD(t)| <= 31.521 for 0 <= t <= 655")
