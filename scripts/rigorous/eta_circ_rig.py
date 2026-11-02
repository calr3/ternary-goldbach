"""Rigorous check of the axiom `etaO_numerics` (MajorArcs/EtaPlusSqLog.lean), the numerical input
of [H, (9.94)]:

    0.640205997 <= int_0^2 P0(t)^2 dt <= 0.640205998,
    -0.0210947787 <= int_0^2 P0(t)^2 log t dt <= -0.0210947786,
    int_R W0''(u)^2 du <= 36,      int_R W1''(u)^2 du <= 8.4,

with P0(t) = (t(2-t))^3 exp(-(t-1)^2/2) = eta_circ(t) on [0, 2], and, in u = log t, W0 = g E, W1 = u W0,
g(u) = h(e^u), E(u) = e^{3u} e^{-e^{2u}}, h(t) = t^2 (2-t)^3 e^{t-1/2} on [0, 2].  Lean proves
(`IF_W0''`, `IF_W1''`) that W''(u) = e^u 1_{[0,2]}(e^u) k''(e^u), so int W''(u)^2 du = int_0^2 t k''(t)^2 dt,
with the explicit
    k0''(t) = (t (t h''(t) + h'(t)) + 2 t h'(t) (3 - 2t^2) + h(t) ((3 - 2t^2)^2 - 4t^2)) t^2 e^{-t^2},
    k0'(t)  = (t h'(t) + h(t) (3 - 2t^2)) t^2 e^{-t^2},
    k1''(t) = 2 k0'(t) + log t * k0''(t),
    h'(t) = e^{t-1/2} p(t), h''(t) = e^{t-1/2} (p(t) + p'(t)), p(t) = t (2-t)^2 (1-t)(4+t).
The first two values agree with [H, p. 197] (VNODE-LP): 0.64020599736635 and -0.021094778698867.

Method: python-flint (Arb) rigorous integration (acb.integral).  The log t integrands are integrated
from eps = 2^-20; on [0, eps], sup |P0|^2, sup |k0'|, sup |k0''| are enclosed by evaluating on the ball
[0, eps], and int_0^eps |log t| dt = eps (1 - log eps), int_0^eps t log(t)^2 dt =
eps^2 (2 log(eps)^2 - 2 log eps + 1)/4 give the tail bounds (printed).

Usage: pip install python-flint; python3 scripts/rigorous/eta_circ_rig.py   (seconds)
"""
from flint import arb, acb, ctx

ctx.prec = 120
half = arb(1) / 2


def E(t): return t.exp()
def P0(t): return (t * (2 - t)) ** 3 * E(-(t - 1) ** 2 / 2)
def h(t): return t ** 2 * (2 - t) ** 3 * E(t - half)
def p(t): return t * (2 - t) ** 2 * (1 - t) * (4 + t)
def dp(t): return -5 * t ** 4 + 4 * t ** 3 + 36 * t ** 2 - 56 * t + 16
def h1(t): return E(t - half) * p(t)
def h2(t): return E(t - half) * (p(t) + dp(t))
def k0d(t): return (t * h1(t) + h(t) * (3 - 2 * t ** 2)) * t ** 2 * E(-t ** 2)
def k0dd(t):
    return (t * (t * h2(t) + h1(t)) + 2 * (t * h1(t) * (3 - 2 * t ** 2))
            + h(t) * ((3 - 2 * t ** 2) ** 2 - 4 * t ** 2)) * t ** 2 * E(-t ** 2)
def k1dd(t): return 2 * k0d(t) + t.log(analytic=True) * k0dd(t)


def I(f, a, b):
    return acb.integral(lambda t, _: f(t), a, b).real


eps = arb(1) / 2 ** 20
ball = arb(eps / 2, eps / 2)                 # contains [0, eps]
A = I(lambda t: P0(t) ** 2, 0, 2)
S0 = arb(abs(P0(ball) ** 2).upper())          # sup P0^2 on [0, eps]
tailB = S0 * eps * (1 - eps.log())             # >= |int_0^eps P0^2 log t|
B = I(lambda t: P0(t) ** 2 * t.log(analytic=True), eps, 2)
M0 = I(lambda t: t * k0dd(t) ** 2, 0, 2)
K1 = arb(abs(k0d(ball)).upper()); K2 = arb(abs(k0dd(ball)).upper())
# t k1''^2 <= t (2 K1 + |log t| K2)^2 <= 8 K1^2 t + 2 K2^2 t log(t)^2 on [0, eps]
tailM1 = 4 * K1 ** 2 * eps ** 2 + 2 * K2 ** 2 * eps ** 2 * (2 * eps.log() ** 2 - 2 * eps.log() + 1) / 4
M1 = I(lambda t: t * k1dd(t) ** 2, eps, 2)
print("int P0^2          =", A)
print("int P0^2 log t    =", B, " (+/-", tailB.upper(), "from [0, eps])")
print("int W0''^2        =", M0)
print("int W1''^2        =", M1, " (+", tailM1.upper(), "from [0, eps])")
ok = (A >= arb("0.640205997")) and (A <= arb("0.640205998"))
ok &= (B - tailB >= arb("-0.0210947787")) and (B + tailB <= arb("-0.0210947786"))
ok &= (M0 <= 36) and (M1 + tailM1 <= arb("8.4"))
print("etaO_numerics:", "OK (rigorous)" if ok else "FAILED")
