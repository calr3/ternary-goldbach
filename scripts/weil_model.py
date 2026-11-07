# Model (floats) of the Lean chain line_sum_weilH -> J(delta), and the resulting psi error eps(x).
import math
from mpmath import mp, quad, sin, exp, log, pi, inf, mpf
mp.dps = 30
def setup(m, l, N, R):
    B2 = lambda u: (2*l)**(2*m) if u == 0 else (2*sin(l*u)/u)**(2*m)
    KR = quad(B2, [-R, 0, R])
    I0 = 2*2**(2*m)*mpf(R)**(1-2*m)/(2*m-1)
    I1 = 2*2**(2*m)*mpf(R)**(mpf(3)/2-2*m)/(2*m-mpf(3)/2)
    cN = 0.5*(log(N+0.25)-log(pi))
    Off = 4**m*exp(m*l)*1e-15
    def psiN(y): return log(N+0.25)+0.5*log(1+y*y/(N-0.75)**2)-sum((k+0.25)/((k+0.25)**2+y*y) for k in range(N))
    def aN(y): return -0.5*log(pi)+0.5*psiN(y/2)
    def polar(t): return 2*((2*l)**(2*m)*exp(m*l))/max(1, l*abs(t))**(2*m)
    def phi(t): return polar(t)+(aN(abs(t)+R)*KR+(cN+0.5*log(1+abs(t)))*I0+I1)/pi+Off
    return KR, I0, I1, phi, polar, aN
def gW(d, t0, u):
    v = max(u, t0); return exp(-d*d*v*v/2)/v
def J(d, m=4, l=0.0865, N=20, R=16, t0=2.39, parts=False):
    KR, I0, I1, phi, polar, aN = setup(m, l, N, R)
    G = lambda t: gW(d, t0, max(0, t-R))
    top = min(40/d, 1e10)
    pts = [0, R, R+t0, R+50, R+500] + [R+10**k for k in range(3, 11) if 10**k < top] + [top]
    pts = sorted(set(p for p in pts if p <= top))
    tot = 2*quad(lambda t: G(t)*phi(t), pts)/KR
    if parts:
        pol = 2*quad(lambda t: G(t)*polar(t), pts)/KR
        arch = 2*quad(lambda t: G(t)*aN(t+R), pts)/pi
        return tot, pol, arch
    return tot
def ideal(d):
    g = lambda t: exp(-d*d*t*t/2)/t
    return 2*quad(lambda t: g(t)*log(t/(2*pi))/(2*pi), [14.134725, 100, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9][:2+int(-math.log10(d))+2]+[40/d])
if __name__ == "__main__":
    for d in [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7]:
        tot, pol, arch = J(d, parts=True)
        i = ideal(d)
        print(f"d={d:g}: J={float(tot):.3f} (polar {float(pol):.3f}, arch {float(arch):.3f}) ideal={float(i):.3f} ratio={float(tot/i):.3f}")

def eps(x, d, Jd, K=None, y0=None):
    """relative errors (upper, lower) of psi_upper/lower_explicit with LineNew = C*J."""
    if K is None:
        K = 1.0
        for _ in range(50): K = math.sqrt(2*math.log(2*K/d)) if 2*K/d > 1 else 1.0
    if y0 is None: y0 = (73/d)**(2/3)
    a = K*d
    c1 = 2/math.log(2)+4.8
    def err(a, b):
        C = math.exp(d*d/8)*(math.exp(a/2)+math.exp(b/2))
        Vg = c1*82.6*math.exp(d*d/8)*(math.exp(-a/2)+math.exp(-b/2))*math.sqrt(2*math.pi)/d
        return math.sqrt(x)*C*Jd + x**-0.5*Vg/(2*math.pi)
    b = math.log(y0/x)
    q = 1-2*math.exp(-K*K/2)
    up = (4*y0*math.exp(a) + (math.exp(d*d/2+a)*x + err(a, b))/q)/x - 1
    lo = 1 - (math.exp(-a)*x - 2*y0 - err(-a, b) - 4*x*math.exp(-K*K/2))/x
    return up, lo
