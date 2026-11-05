# Model of the P5+P7 bound (crude Phi+) vs the ideal zero sum, weight g = e^{-d^2 t^2/2}/max(1/2,t).
import math
from scipy.integrate import quad
m, l = 4, 0.0865
def B2(u):
    if abs(u) < 1e-9: return (2*l)**(2*m)
    return (2*math.sin(l*u)/u)**(2*m)
def psiN(y, N=20):   # upper bound for Re psi(1/4 + i y)
    return math.log(N+0.25) + 0.5*math.log(1 + y*y/(N-0.75)**2) - sum((k+0.25)/((k+0.25)**2 + y*y) for k in range(N))
def a(y): return -0.5*math.log(math.pi) + 0.5*psiN(y/2)
def model(delta, R, t0):
    KR = quad(B2, -R, R, limit=400)[0]
    g = lambda t: math.exp(-delta*delta*t*t/2)/max(0.5, t)
    gh = lambda t: g(max(t, t0))
    def tail(t):  # int_{|u|>R} max(a(t+u),0) B2(u) du
        f = lambda u: max(a(t+u), 0)*B2(u)
        return quad(f, R, R+2000, limit=400)[0] + quad(f, -R-2000, -R, limit=400)[0]
    def phi(t): return 2*(2*l)**(2*m)*math.exp(m*l)/max(1, l*abs(t))**(2*m) + (a(abs(t)+R)*KR + tail(t))/math.pi
    Y = 12/delta
    ts = [i*0.5 for i in range(int(min(Y, 400)/0.5))]
    # integrate G*phi over t in [0, Y] (doubled); use coarse grid for large t
    tot = 0.0
    t = 0.0
    while t < Y:
        h = 0.25 if t < 400 else t*0.01
        tot += gh(max(0, t - R)) * phi(t) * h
        t += h
    bound = 2*tot/KR
    ideal = 2*quad(lambda t: g(t)*math.log(t/(2*math.pi))/(2*math.pi), 14.13, Y, limit=400)[0]
    return bound, ideal
for delta in [1e-3, 1e-5]:
    for R, t0 in [(12, 0), (20, 0), (12, 3), (12, 14)]:
        b, i = model(delta, R, t0)
        print(f"delta={delta:g} R={R} zero-free below {t0}: bound={b:.2f}  ideal={i:.2f}  ratio={b/i:.2f}")
