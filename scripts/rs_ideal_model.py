"""Approximate model (not a proof): the best relative error an explicit formula for psi can give
at x when the only zero input is RH up to H = 3.061e10 [Platt 2012] plus the zero density
N'(t) = log(t/2pi)/(2pi) (no error term), using Rosser-Schoenfeld first-order averaging over
[x, x(1+d)]:

    eps(x) = min_d  d/2 + Z(d)/sqrt(x),
    Z(d)   = 2 * ( sum_{gamma < 2/d} 1/gamma + sum_{gamma > 2/d} 2/(d gamma^2) )

(both signs of gamma; 2/d << H in the range below, so every zero used is on the line).
It is compared with what `theta_explicit` needs from below, theta(x) > x - x/log^3 x, i.e.
eps(x) + 1.4262/sqrt(x) < 1/log^3 x, and with the room in [H, (2.14)], psi(y) <= 1.0004 y.

Used in NOTES.md, "Büthe and sources available by 2014".
"""

import math

G1 = 14.134725  # first zero


def Z(d):
    T = 2.0 / d
    LT = math.log(T / (2 * math.pi))
    L1 = math.log(G1 / (2 * math.pi))
    head = (LT**2 - L1**2) / (4 * math.pi)  # int_{G1}^T log(t/2pi)/(2pi t) dt
    tail = (LT + 1) / (2 * math.pi)  # int_T^oo log(t/2pi)/(2pi) * 2/(d t^2) dt
    return 2 * (head + tail)


def eps(x):
    best = (math.inf, None)
    for k in range(2001):
        d = 10 ** (-10 + 8 * k / 2000)
        e = d / 2 + Z(d) / math.sqrt(x)
        if e < best[0]:
            best = (e, d)
    return best


if __name__ == "__main__":
    print(f"{'x':>8} {'eps_ideal':>10} {'delta':>8} {'need(θ lower, 1/log³)':>22} {'(2.14) room 4e-4':>17}")
    for lx in [8, 9, 10, 10.5, 11, 11.2, 11.3, 11.5, 12, 13, 14, 16, 17]:
        x = 10.0**lx
        e, d = eps(x)
        need = 1 / math.log(x) ** 3 - 1.4262 / math.sqrt(x)
        print(f"1e{lx:<6} {e:10.3e} {d:8.1e} {need:12.3e} {'ok' if e < need else 'FAIL':>8}"
              f" {'ok' if e < 4e-4 else 'FAIL':>12}")
