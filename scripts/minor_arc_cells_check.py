"""Cell/block check of the closed-form majorant used in Lean (repair 3; see NOTES).
ghat(y,n) = 1.398 max(g_y(n), h(y)) + 17 (670/n)^3/3; cells in y; blocks of ratio 1.25 in the level."""
from mpmath import mp, mpf, log, sqrt, exp, euler, pi
mp.dps=20
EG=exp(euler); kappa=49
def F(r): return EG*log(log(r))+mpf('2.50637')/log(log(r))
def R(z,t): return mpf('0.27125')*log(1+log(4*t)/(2*log(9*z**(mpf(1)/3)/(mpf('2.004')*t))))+mpf('0.41415')
def L(t): return F(t/2)*(mpf(13)/4*log(t)+mpf('7.82'))+mpf('13.66')*log(t)+mpf('37.55')
def gx(z,r): return ((R(z,2*r)*log(2*r)+mpf('0.8103'))*sqrt(F(r))+mpf('2.5'))/sqrt(2*r)+L(2*r)/r+mpf('3.8')*z**(-mpf(1)/6)
def h(z): return mpf('0.276')*z**(-mpf(1)/6)*log(z)**mpf(1.5)+1234*z**(-mpf(1)/3)*log(z)
K=mpf('1.398')
def ghat(y,n): return K*max(gx(y,n),h(y))+17*(670/n)**3/3
def Mcell(Y,Y2,rho=mpf('1.25'),verbose=False):
    """bound on M valid for y in [Y,Y2]: left-end ghat, s/D at left (decreasing), tail (1-h)s at right."""
    x=kappa*Y; x2=kappa*Y2; r0=150000
    s=lambda x: mpf('0.640209')*log(x)-mpf('0.021095')
    D=lambda x: log(2*sqrt(x/784))+mpf('1.33258')
    Q=sqrt(x/784); r2=int(min((2*Q)**mpf(0.6)/2-1, Q/20000))
    sD=s(x)/D(x)
    Ilow=mpf('8.6249')
    base=ghat(Y,r0)*((log(2*(r0+1))+mpf('1.36'))*sD-Ilow)
    # blocks: N_0=r0, N_{j+1}=ceil(rho N_j) until r2
    mid=0; N=r0
    while N<r2-1:
        N2=min(int(N*rho)+1, r2-1)
        # sum_{n=N+1}^{N2} ghat(n) log((n+1)/n) <= ghat(N+1)*log((N2+1)/(N+1))
        mid+=ghat(Y,N+1)*log(mpf(N2+1)/(N+1))
        N=N2
    mid*=sD
    c=log(2*r2)+mpf('1.36')   # h_{r2-1} = (log(2 r2)+1.36)/D
    tail=ghat(Y,r2)*(s(x2)-c*s(x2)/D(x2))
    M=base+mid+tail
    return M, (base,mid,tail,r2)
def Ztot(M, Eratio=mpf('1e-6')):
    t=mpf('0.004')
    return (1+t)*M+(1+1/t)*17*sqrt(pi/2)*Eratio*1
for (a,b) in [(25.0045,25.5),(25.5,26),(26,27),(27,28),(28,30),(30,34),(34,42),(42,58)]:
    M,parts=Mcell(mpf(10)**a,mpf(10)**b)
    print(a,b,'M=%.4f'%M, ['%.4f'%p for p in parts[:3]], parts[3], 'Z=%.4f'%Ztot(M))
