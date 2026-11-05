from mpmath import mp, mpf, quad, log, pi, digamma, zetazero, besselj, gamma, sqrt, mpc
mp.dps = 25
L = log(2) / 2; m = 4
def B(r):  # int_{-L}^{L} (1-(v/L)^2)^m e^{irv} dv  (closed form, spherical Bessel)
    k = r * L
    if abs(k) < mpf('1e-8'):
        return L * sqrt(pi) * gamma(m + 1) / gamma(m + mpf(3) / 2)
    return L * sqrt(pi) * gamma(m + 1) * (2 / k) ** (m + mpf(1) / 2) * besselj(m + mpf(1) / 2, k)
def h(r, T): return B(r - T) ** 2 + B(r + T) ** 2
def pts(T): return sorted(set([-T - 300, -T - 40, -T, -T + 40, 0, T - 40, T, T + 40, T + 300]))
def g0(T): return quad(lambda r: h(r, T).real, pts(T)) / (2 * pi)
def rhs(T):
    arch = quad(lambda r: h(r, T).real * digamma(mpf(1) / 4 + mpc(0, 1) * r / 2).real, pts(T)) / (2 * pi)
    poles = (h(mpc(0, 0.5), T) + h(mpc(0, -0.5), T)).real
    return poles - g0(T) * log(pi) + arch, poles, arch
zs = [zetazero(k).imag for k in range(1, 150)]
def lhs(T): return 2 * sum(h(gm, T).real for gm in zs)
for T in [0, 5, 14, 30, 60]:
    r, poles, arch = rhs(T)
    print(f"T={T:3}: zeros (gamma<{float(zs[-1]):.0f}) = {float(lhs(T)):.8f}   formula = {float(r):.8f}   (poles {float(poles):.4f}, arch {float(arch):.4f}, K/2pi = {float(g0(T)):.4f})")
