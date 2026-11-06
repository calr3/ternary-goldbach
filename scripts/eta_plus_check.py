"""Float64 check of `integral_etaPlus_sq_log` ([H, (9.94)], proved in MajorArcs/EtaPlusSqLog.lean):

    int_0^inf eta_+(t)^2 log(xt) dt = (0.640206 + O*(1.95e-6)) log x - 0.021095 + O*(5.3e-7),

with eta_+(t) = h_H(t) t e^{-t^2/2}, H = 200, h_H = h *_M F_H, F_H(y) = sin(H log y)/(pi log y),
h(t) = t^2 (2-t)^3 e^{t-1/2} on [0, 2] (Helfgott/Defs.lean, [H, (7.4)-(7.6)]).

In the variable v = log t, h_H(e^v) is the convolution of phi(v) = h(e^v) with sin(Hu)/(pi u), i.e.
phi with its Fourier transform cut off at |xi| <= H/(2 pi) cycles per unit.  We compute phi on a
fine periodic grid, cut its FFT, transform back, and integrate eta_+^2 and eta_+^2 log t in t.
This checks both the definition of eta_+ and the two constants of (9.94) to high accuracy (it is
not interval arithmetic).

Usage: python3 scripts/eta_plus_check.py   (a minute; needs numpy, mpmath)
"""
import numpy as np
from mpmath import mp, quad, exp, log

H = 200.0
vmin, vmax, n = -60.0, 30.0, 2 ** 24
v = np.linspace(vmin, vmax, n, endpoint=False)
dv = v[1] - v[0]
t = np.exp(v)
tc = np.minimum(t, 2.0)
phi = np.where(t <= 2, tc ** 2 * (2 - tc) ** 3 * np.exp(tc - 0.5), 0.0)
xi = np.fft.fftfreq(n, d=dv)                       # cycles per unit of v
hH = np.fft.ifft(np.where(np.abs(xi) <= H / (2 * np.pi), np.fft.fft(phi), 0)).real
etap = hH * t * np.exp(-t ** 2 / 2)
eto = phi * t * np.exp(-t ** 2 / 2)
# int_0^inf f(t) dt = int f(e^v) e^v dv
I0 = np.sum(etap ** 2 * t) * dv
I1 = np.sum(etap ** 2 * np.log(t) * t) * dv
D2 = np.sum((etap - eto) ** 2 * t) * dv
mp.dps = 30
eo = lambda s: s ** 3 * (2 - s) ** 3 * exp(-(s - 1) ** 2 / 2)
J0 = quad(lambda s: eo(s) ** 2, [0, 1, 2]); J1 = quad(lambda s: eo(s) ** 2 * log(s), [0, 1, 2])
print("int eta_o^2        = %.15f   (mpmath)" % J0)
print("int eta_o^2 log t  = %.15f   (mpmath)" % J1)
print("int eta_+^2        = %.12f   |diff from 0.640206| = %.2e  (allowed 1.95e-6)" % (I0, abs(I0 - 0.640206)))
print("int eta_+^2 log t  = %.12f   |diff from -0.021095| = %.2e (allowed 5.3e-7)" % (I1, abs(I1 + 0.021095)))
print("|eta_+ - eta_o|_2^2 = %.3e" % D2)
assert abs(I0 - 0.640206) < 1.95e-6 and abs(I1 + 0.021095) < 5.3e-7
print("OK")
