# Float model of the cell induction for |N(u)| <= nu u (Prelim/SchoenfeldStep.lean), with the inputs proved here.
# Reads /tmp/cde/ghtab.json written by scripts/gen_weights_walk.py.
# Model of the Lean cell step (exact structure of the inequalities to be proved).
import math, json
S=1e12
GH={m:(a/S,b/S,c/S,d/S) for m,a,b,c,d,k in json.load(open('/tmp/cde/ghtab.json'))}
GH[1]=(0,0,0,0)
kap=0.607927101855; cM=0.571; X0=10**8; EPL=4.92e-7
YS=sorted(int(math.floor(10**(s/16))) for s in range(19,97))
def sqf_isqrt(J): return 2*kap*math.sqrt(J)+4.5+1.5*math.log(J) if J>=1 else 0.0
def eps(v):  # v>=1e12
    L=math.log(v); return 1/L**3 + (EPL if 120<L<20000 else 0) + 1.4262/math.sqrt(v)
def Jsum(Am,Ap,Y):
    tot=0.0
    for a,b,c in [(Y+1,1e9,2.0),(1e9,3.2e10,35.5),(3.2e10,1e12,72.0)]:
        lo=max(a,Y+1)
        if lo>=b or Ap/lo<1: continue
        J=Ap/lo
        tot += c*(2*kap*math.sqrt(1/lo) + (4.5+1.5*math.log(J))/math.sqrt(Am))
    if Ap>1e12:
        # pieces of log v from 12 log10.. : [l_j, l_{j+1}) with m in (D/e^{l_{j+1}}, D/e^{l_j}]
        lmax=math.log(Ap); l=math.log(1e12)
        while l<lmax:
            l2=min(l+max(1.0,0.1*l), lmax)
            # count of m: Q1(D/e^l) - Q1(D/e^{l2}) <= kap*(l2-l) + 0.588  (or Q1(B)<=kap log B+1.166 if lower end<1)
            if lmax-l2 < 1e-9: w=kap*(lmax-l)+1.166
            else: w=kap*(l2-l)+0.588
            tot += eps(math.exp(l) if l<700 else float('inf') ) * w if l<700 else (1/l**3+(EPL if l<20000 else 0))*w
            l=l2
    return tot
def run(Lend=160.0, verbose=False):
    A=[X0]
    while math.log(A[-1])<Lend:
        L=math.log(A[-1]); h=0.5 if L<30 else 0.69
        A.append(int(A[-1]*math.exp(h)))
    I0=99+2*cM*math.sqrt(X0)
    C0=I0/math.log(X0+1)
    cells=[]; I=0.0; T=0.0; out=[]
    for i in range(len(A)-1):
        Am,Ap=A[i],A[i+1]; Lm=math.log(Am); Lp=math.log(Ap); delta=1-Am/Ap
        def eta_of(lo,hi):
            lo=max(lo,X0+1); v=[c[3] for c in cells if c[1]>lo and c[0]<=hi]; return max(v) if v else 0.0
        best=None
        for Y in YS:
            if Y>Am/100 or Y>1000000: continue
            K=0.0; s=1
            while 2**(s-1)<Y:
                al=2**(s-1); be=min(2**s,Y)
                Ulo=Am//be; Uhi=(Ap-1)//max(al,2)
                g=GH[be][1]-GH[al][0]; h=GH[be][3]-GH[al][2]
                w=0.0
                if Ulo<=X0: w+=cM*h/math.sqrt(Am)
                if Uhi>X0: w+=eta_of(Ulo,Uhi)*g
                K+=w; s+=1
            Ulo=Am//(Y+1); Uhi=(Ap-1)//(Y+1)
            Bd=0.0
            if Ulo<=X0: Bd+=2*math.sqrt(Y)*cM/math.sqrt(Am*(Y+1))
            if Uhi>X0: Bd+=2*math.sqrt(Y)*eta_of(Ulo,Uhi)/(Y+1)
            J=Jsum(Am,Ap,Y)
            Xp=(C0+I+1)/Am+K+J+Bd
            den=1-1/Lm-delta/Lm**2
            nu=Xp/den
            if best is None or nu<best[0]: best=(nu,Y,K,J,Bd)
        nu,Y,K,J,Bd=best
        eta=nu/Lm+(C0+I)/Am+nu*delta/Lm**2
        mi=Lp*(eta+max((I0+T)/Am,(I0+T+eta*(Ap-Am))/Ap)+Lp/Am)
        cells.append((Am,Ap,nu,eta)); out.append((i+1,Lm,Lp,Y,K,J,Bd,nu,eta*Lm,mi))
        I+=nu*(Ap-Am)/Lm**2; T+=eta*(Ap-Am)
    return out
if __name__=="__main__":
    out=run()
    print(len(out),"cells; max nu",max(o[7] for o in out),"max m",max(o[9] for o in out))
    for o in out[:4]+out[20:23]+out[-3:]: print(" ".join(f"{v:.4g}" for v in o))
    t=0.0009*(1/math.log(11815)-1/math.log(2160535))+ (0.017**2)*(1/math.log(2160535)-1/math.log(X0))
    for o in out: t+=o[9]**2*(1/o[1]-1/o[2])
    print("tau(cells part)",t, "max nu (L>=132)", max(o[7] for o in out if o[1]>=132))
