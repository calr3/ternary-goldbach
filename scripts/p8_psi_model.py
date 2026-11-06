# P8e: the exact Lean bounds psi_upper_W / psi_lower_W (Explicit/PsiWeil.lean), evaluated.
import math
LW = 2*571
c1 = 2/math.log(2) + 4.8
def JW(d): L = math.log(1/d); return 0.16385*L*L - 0.4271*L + 7.2032 + 57.73*d
def LineW(a, b, d): return math.exp(d*d/8)*(math.exp(a/2)+math.exp(b/2))*(JW(d) + math.exp(-d*d*1e20/2)*LW)
logB = math.log(9200*(3e10+22)*(1.25*(3e10+11))**9 + 20*(3e10+22)**3*(1.25*(3e10+11))**2)
Z3g = (logB - math.log(0.355))/math.log(10/3)
c3g = 10*4.4/3e10/math.log(10/3)
def TailB(a, d):
    rho = math.exp(-4.4*d*d*3e10)
    EB = 2*math.exp(d*d/2 + abs(a) - d*d*9e20/2)/3e10
    return EB*(2*Z3g/(1-rho) + 2*c3g/(1-rho)**2)
def Vg(a, b, d): return c1*82.6*math.exp(d*d/8)*(math.exp(-a/2)+math.exp(-b/2))*math.sqrt(2*math.pi)/d
def ErrW(a, b, d, x): return math.sqrt(x)*LineW(a, b, d) + x*TailB(a, d) + x**-0.5*Vg(a, b, d)/(2*math.pi)
def upper(x, d, K, y0):
    a, b = K*d, math.log(y0/x)
    return 4*y0*math.exp(a) + (math.exp(d*d/2 + a)*x + ErrW(a, b, d, x))/(1 - 2*math.exp(-K*K/2))
def lower(x, d, K, y0):
    a, b = -K*d, math.log(y0/x)
    return math.exp(-K*d)*x - 2*y0 - ErrW(a, b, d, x) - 4*x*math.exp(-K*K/2)
def best(x, ds=None):
    ds = ds or [10**(-k/8) for k in range(17, 77)]
    res = []
    for d in ds:
        if not (3e-10 <= d <= 1/208): continue
        K = 1.0
        for _ in range(40): K = math.sqrt(2*math.log(max(2*K/d, 3)))
        for y0 in [10**(j/4) for j in range(0, 60)]:
            if y0*math.exp(K*d) > x: break
            eu = upper(x, d, K, y0)/x - 1
            el = 1 - lower(x, d, K, y0)/x
            res.append((max(eu, el), eu, el, d, K, y0))
    return min(res)
if __name__ == "__main__":
    for lx in [6, 6.5, 7, 7.43, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]:
        x = 10**lx
        e, eu, el, d, K, y0 = best(x)
        print(f"x=1e{lx}: eps={e:.3e} (up {eu:.3e}, low {el:.3e}) d={d:.2e} K={K:.2f} y0={y0:.3g}  eps*sqrt(x)={e*math.sqrt(x):.1f}  x*eps/log^-3={e*math.log(x)**3:.3f}")

def range_params(X0, X1, npts=6):
    """one (δ, K, y0) for all x in [X0, X1]; returns worst ε√x over a grid of x."""
    xs = [X0*(X1/X0)**(i/(npts-1)) for i in range(npts)]
    bestc = None
    for k in range(17, 77):
        d = 10**(-k/8)
        if not (3e-10 <= d <= 1/208): continue
        K = 1.0
        for _ in range(40): K = math.sqrt(2*math.log(max(2*K/d, 3)))
        for j in range(0, 60):
            y0 = 10**(j/4)
            if y0*math.exp(K*d) > X0: break
            c = max(max(upper(x, d, K, y0)/x - 1, 1 - lower(x, d, K, y0)/x)*math.sqrt(x) for x in xs)
            if bestc is None or c < bestc[0]: bestc = (c, d, K, y0)
    return bestc
def table(step=10**0.5):
    X = 1e6
    while X < 1e17*0.999:
        X1 = min(X*step, 1e17)
        c, d, K, y0 = range_params(X, X1)
        print(f"[{X:.3g}, {X1:.3g}]: c={c:.2f} d={d:.3e} K={K:.3f} y0={y0:.4g}")
        X = X1

def sep_c(X0, X1, d, K, y0):
    """c such that ψ(x) ≤ x + c√x and ψ(x) ≥ x − c√x on [X0, X1], each term maximised separately."""
    q = 2*math.exp(-K*K/2)
    u0, u1 = math.sqrt(X0), math.sqrt(X1)
    a = K*d
    LWb = math.exp(d*d/8)*(math.exp(a/2) + math.sqrt(y0/X0))*(JW(d) + math.exp(-d*d*1e20/2)*LW)
    LWbl = math.exp(d*d/8)*(math.exp(-a/2) + math.sqrt(y0/X0))*(JW(d) + math.exp(-d*d*1e20/2)*LW)
    V0 = c1*82.6*math.exp(d*d/8)*math.sqrt(2*math.pi)/d/(2*math.pi)
    up = ((math.exp(d*d/2 + a)/(1-q) - 1)*u1 + LWb/(1-q) + TailB(a, d)*u1/(1-q)
          + 4*y0*math.exp(a)/u0 + V0/(1-q)*(math.exp(-a/2)/X0 + 1/math.sqrt(y0*X0)))
    lo = ((1 - math.exp(-a) + 4*math.exp(-K*K/2))*u1 + 2*y0/u0 + LWbl + TailB(a, d)*u1
          + V0*(math.exp(a/2)/X0 + 1/math.sqrt(y0*X0)))
    return max(up, lo)
def table_sep(step=10**0.5):
    X = 1e6
    while X < 1e17*0.999:
        X1 = min(X*step, 1e17)
        best = None
        for k in range(17, 77):
            d = 10**(-k/8)
            if not (3e-10 <= d <= 1/208): continue
            for K in [3.5 + 0.1*i for i in range(40)]:
                for j in range(0, 60):
                    y0 = 10**(j/4)
                    if y0*math.exp(K*d) > X: break
                    c = sep_c(X, X1, d, K, y0)
                    if best is None or c < best[0]: best = (c, d, K, y0)
        print(f"[{X:.3g}, {X1:.3g}]: c_sep={best[0]:.2f} d={best[1]:.3e} K={best[2]:.2f} y0={best[3]:.4g}")
        X = X1
