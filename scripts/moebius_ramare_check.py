"""Float check of Ramaré's |m(x)| <= 0.03/log x on [11815, 1e8) (the published range of ramare_moebius)."""
import numpy as np, math
N = 10**8
mu = np.ones(N+1, dtype=np.int8)
mu[0] = 0
isp = np.ones(N+1, dtype=bool); isp[:2] = False
for p in range(2, int(N**0.5)+1):
    if isp[p]:
        isp[p*p::p] = False
primes = np.nonzero(isp)[0]
for p in primes:
    mu[p::p] *= -1
    pp = p*p
    if pp <= N: mu[pp::pp] = 0
k = np.arange(N+1, dtype=np.float64); k[0] = 1
m = np.cumsum(mu / k)
ks = np.arange(11815, N)
r = np.abs(m[ks]) * np.log(ks + 1.0)
i = np.argmax(r)
print("max |m(k)| log(k+1) on [11815, 1e8):", r[i], "at k =", ks[i])
