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
