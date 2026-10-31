import numpy as np, math
N = 2*10**6
isp = np.ones(N+1, bool); isp[:2] = False
for p in range(2, int(N**0.5)+1):
    if isp[p]: isp[p*p::p] = False
primes = np.nonzero(isp)[0]
w = np.zeros(N+1)
for p in primes:
    p = int(p); pk = p
    while pk <= N:
        w[pk] += math.log(p) / pk; pk *= p
F = np.cumsum(w)
gam = 0.5772156649015329
I = 0.0
for k in range(1, N):
    a = math.log(k); b = math.log(k+1); c = F[k] + gam   # r = c - u
    if c <= a: I += ((b-c)**2 - (a-c)**2)/2
    elif c >= b: I += ((c-a)**2 - (c-b)**2)/2
    else: I += ((c-a)**2 + (b-c)**2)/2
print("int |r| dy/y =", I)
