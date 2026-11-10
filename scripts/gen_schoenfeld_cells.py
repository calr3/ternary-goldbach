# Data for Prelim/SchoenfeldCells*.lean: the cells [A, B) of the induction (Sch.chkCell), from
# A = X0 + 1 = 10^8 + 1 up to log B >= 160, with a boundary at 10^12.  All checks of chkCell are
# replayed here in exact rational arithmetic (including the logarithm certificates Small.chkLow /
# Small.chkStep), so the kernel `decide` succeeds.
import math, re, sys, os, glob
from fractions import Fraction as F

X0 = 10**8
LEND = 160.0
DEN = 10**15            # denominator for nu, eta, I
PER_FILE = 20

# ---------- GHtab from WeightsMain.lean ----------
src = open("TernaryGoldbach/Prelim/WeightsMain.lean").read()
m = re.search(r"def GHtab : List \(ℕ × ℕ × ℕ × ℕ × ℕ\) := \[(.*?)\]\n", src, re.S)
GHtab = [tuple(int(x) for x in t.split(",")) for t in re.findall(r"\(([\d, ]+)\)", m.group(1))]
S12 = F(10**12)
def ghq(mm):
    if mm == 1: return (F(0),) * 4
    for e in GHtab:
        if e[0] == mm: return tuple(F(x) / S12 for x in e[1:])
    raise KeyError(mm)
GHkeys = {e[0] for e in GHtab}

# ---------- logarithm certificates (exact replay of Small.chkLow / Small.chkStep) ----------
FACT = [math.factorial(i) for i in range(13)]
def T12(f): return sum(f**i / FACT[i] for i in range(12))
def T12up(f): return T12(f) + f**12 * F(13, FACT[12] * 12)
def EHpow(a): return F(27182818286**a, 10**(10 * a))
def ELpow(a): return F(27182818283**a, 10**(10 * a))
def chkLow(cN, cD, L): return EHpow(cN // cD) * T12up(F(cN % cD, cD)) <= L
def chkStep(cN, cD, n, L): return F(L) < ELpow(cN * n // cD) * T12(F(cN * n % cD, cD))
def logLo(q, L): return q >= 0 and L > 0 and chkLow(q.numerator, q.denominator, L)
def logUp(q, L): return q >= 0 and L > 0 and chkStep(q.numerator, q.denominator, 1, L)
LD = 10**7
def lo_cert(L):
    q = F(math.floor(math.log(L) * LD) - 3, LD)
    assert logLo(q, L), L
    return q
def up_cert(L):
    q = F(math.ceil(math.log(L) * LD) + 3, LD) if L > 1 else F(3, LD)
    assert logUp(q, L), L
    return q

# ---------- the checker ----------
kq = F(607927101855, 10**12)
C0q = F(626)

def etaMax(s, cs, lo, hi):
    best = F(0)
    for b, eta in cs:
        if not (hi < s or b <= lo): best = max(best, eta)
        s = b
    return best
def Mrange(cs, lo, hi):
    return (F(571, 1000) if lo <= X0 else F(0), etaMax(X0 + 1, cs, lo, hi) if X0 < hi else F(0))
def endC(cs): return cs[-1][0] if cs else X0 + 1

def kChk(cs, A, B, al, bs):
    for be in bs:
        if not (1 <= al < be and (al == 1 or al in GHkeys) and be in GHkeys and 100 <= A // be
                and (B - 1) // (al + 1) < A and ghq(al)[2] <= ghq(be)[3]): return False
        al = be
    return True
def kVal(cs, A, B, sA, al, bs):
    tot = F(0)
    for be in bs:
        p = Mrange(cs, A // be, (B - 1) // (al + 1))
        tot += p[0] * (ghq(be)[3] - ghq(al)[2]) / sA + p[1] * (ghq(be)[1] - ghq(al)[0])
        al = be
    return tot
def jChk(B, a, r, u): return (B - 1) // a == 0 or (1 <= r and r * r <= a and logUp(u, (B - 1) // a))
def jVal(B, a, r, sA, coef, u):
    return F(0) if (B - 1) // a == 0 else coef * (2 * kq / r + (F(9, 2) + F(3, 2) * u) / sA)
def epsq(l, r): return 1 / l**3 + F(492, 10**9) + F(14262, 10000) / r
def vOK(A, v):
    V, l, u, r = v
    return 10**12 <= V <= A and l > 0 and logLo(l, V) and logUp(u, V) and 1 <= r and r * r <= V
def eChk(A, vs): return all(vOK(A, v) for v in vs) and all(vs[i][0] <= vs[i + 1][0] for i in range(len(vs) - 1))
def eVal(uB, vs):
    tot = F(0)
    for i, (V, l, u, r) in enumerate(vs):
        if i + 1 < len(vs): tot += epsq(l, r) * (kq * (vs[i + 1][2] - l) + F(588, 1000))
        else: tot += epsq(l, r) * (kq * (uB - l) + F(1166, 1000))
    return tot
def bVal(cs, A, B, Y, sA, rY):
    p = Mrange(cs, A // (Y + 1), (B - 1) // (Y + 1))
    return 2 * p[0] / sA + 2 * p[1] / rY

def Xq(cs, d):
    A, B, Y, sA = d["A"], d["B"], d["Y"], d["sA"]
    e = F(0) if B <= 10**12 else eVal(d["uB"], d["vs"])
    return (F(1, A) + kVal(cs, A, B, sA, 1, d["ks"]) + jVal(B, Y + 1, d["r1"], sA, 2, d["u1"]) +
            jVal(B, 10**9, d["r2"], sA, F(71, 2), d["u2"]) + jVal(B, 32000000001, d["r3"], sA, 72, d["u3"]) +
            e + bVal(cs, A, B, Y, sA, d["r1"]))

def chkCell(cs, I, d):
    A, B, Y, sA, L = d["A"], d["B"], d["Y"], d["sA"], d["L"]
    ks = d["ks"]
    ok = (X0 < A < B and 1 <= sA and sA * sA <= A and 1 < L and logLo(L, A) and 12 <= Y < 10**9 and
          100 <= A // (Y + 1) and (B - 1) // (Y + 1) < A and 1 <= d["r1"] and d["r1"]**2 <= Y + 1 and
          kChk(cs, A, B, 1, ks) and ks[-1] == Y and
          jChk(B, Y + 1, d["r1"], d["u1"]) and jChk(B, 10**9, d["r2"], d["u2"]) and
          jChk(B, 32000000001, d["r3"], d["u3"]))
    if not ok: return False
    if B > 10**12:
        vs = d["vs"]
        if not (vs and vs[0][0] == 10**12 and eChk(A, vs) and logUp(d["uB"], B - 1)): return False
    nu, eta, I2 = d["nu"], d["eta"], d["I2"]
    dl = (F(B) - A) / B
    return (nu >= 0 and Xq(cs, d) + (C0q + I) / A + nu * dl / L**2 <= nu * (1 - 1 / L) and
            nu / L + (C0q + I) / A + nu * dl / L**2 <= eta and I + nu * (F(B) - A) / L**2 <= I2)

def ceilF(x): return F(-((-x.numerator * DEN) // x.denominator), DEN)

# ---------- building the cells ----------
YS = sorted({int(math.floor(10**(s / 16))) for s in range(19, 97)} & GHkeys)
def blocks(Y):
    bs = []; s = 1
    while 2**(s - 1) < Y:
        bs.append(min(2**s, Y)); s += 1
    return bs
def vpoints(A):
    pts = [10**12]; l = math.log(10**12); lA = math.log(A)
    while True:
        l2 = l + max(1.0, 0.1 * l)
        if l2 >= lA - 1e-9: break
        pts.append(int(math.exp(l2)) if l2 < 700 else None); l = l2
    if pts[-1] < A: pts.append(A)
    return [(V, lo_cert(V), up_cert(V), math.isqrt(V)) for V in pts]

def make_cell(cs, I, A, B, Y):
    sA = math.isqrt(A)
    d = dict(A=A, B=B, Y=Y, sA=sA, L=lo_cert(A), ks=blocks(Y), r1=math.isqrt(Y + 1))
    for key, a in (("1", Y + 1), ("2", 10**9), ("3", 32000000001)):
        J = (B - 1) // a
        d["r" + key] = math.isqrt(a)
        d["u" + key] = up_cert(J) if J >= 1 else F(0)
    if B > 10**12:
        d["uB"] = up_cert(B - 1); d["vs"] = vpoints(A)
    else:
        d["uB"] = F(0); d["vs"] = []
    L = d["L"]; dl = (F(B) - A) / B
    X = Xq(cs, d)
    nu = ceilF((X + (C0q + I) / A) / (1 - 1 / L - dl / L**2) * (1 + F(1, 10**9)))
    d["nu"] = nu
    d["eta"] = ceilF(nu / L + (C0q + I) / A + nu * dl / L**2)
    d["I2"] = ceilF(I + nu * (F(B) - A) / L**2)
    return d

def bounds():
    A = [X0 + 1]
    while math.log(A[-1]) < LEND:
        L = math.log(A[-1]); h = 0.5 if L < 30 else 0.69
        nxt = int(A[-1] * math.exp(h))
        if A[-1] < 10**12 < nxt: nxt = 10**12
        A.append(nxt)
    return A

def run():
    As = bounds()
    cs = []; I = F(0); cells = []
    for i in range(len(As) - 1):
        A, B = As[i], As[i + 1]
        best = None
        for Y in YS:
            if Y < 12 or Y > A // 100 - 1 or Y > 1000000: continue
            d = make_cell(cs, I, A, B, Y)
            if best is None or d["nu"] < best["nu"]: best = d
        d = best
        assert chkCell(cs, I, d), i
        cells.append((cs, I, d))
        cs = cs + [(B, d["eta"])]; I = d["I2"]
        print(i + 1, f"logA={math.log(A):.2f} Y={d['Y']} nu={float(d['nu']):.5f} etaL={float(d['eta'])*math.log(A):.5f} I={float(I):.4g}",
              file=sys.stderr)
    return cells

def q(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"

def lean_cell(d):
    vs = "[" + ", ".join(f"({V}, {q(l)}, {q(u)}, {r})" for V, l, u, r in d["vs"]) + "]"
    ks = "[" + ", ".join(map(str, d["ks"])) + "]"
    return (f"{{ A := {d['A']}, B := {d['B']}, Y := {d['Y']}, sA := {d['sA']}, L := {q(d['L'])},\n"
            f"    ks := {ks},\n"
            f"    r1 := {d['r1']}, u1 := {q(d['u1'])}, r2 := {d['r2']}, u2 := {q(d['u2'])},\n"
            f"    r3 := {d['r3']}, u3 := {q(d['u3'])}, uB := {q(d['uB'])},\n"
            f"    vs := {vs},\n"
            f"    ν := {q(d['nu'])}, η := {q(d['eta'])}, I' := {q(d['I2'])} }}")

def write(cells, nmax=None):
    if nmax: cells = cells[:nmax]
    for f in glob.glob("TernaryGoldbach/Prelim/SchoenfeldCells*.lean"): os.remove(f)
    nfiles = (len(cells) + PER_FILE - 1) // PER_FILE
    for fi in range(nfiles):
        imp = "TernaryGoldbach.Prelim.SchoenfeldGen" if fi == 0 else f"TernaryGoldbach.Prelim.SchoenfeldCells{fi}"
        out = [f"""import {imp}

/-! Cells of the induction (generated by `scripts/gen_schoenfeld_cells.py`), part {fi + 1}. -/

open Finset

namespace TernaryGoldbach.Prelim.Sch

"""]
        if fi == 0:
            out.append("""def cs0 : List (ℕ × ℚ) := []

theorem st0 : McovR (X0 + 1) cs0 ∧ endC (X0 + 1) cs0 = 100000001 ∧
    ∑ n ∈ Ioo X0 100000001, |Nn n| * wN n ≤ ((0 : ℚ) : ℝ) := by
  refine ⟨trivial, rfl, ?_⟩
  rw [show Ioo X0 100000001 = ∅ by ext; simp [X0]; omega]; simp
""")
        for k in range(fi * PER_FILE, min((fi + 1) * PER_FILE, len(cells))):
            cs, I, d = cells[k]
            n = k + 1
            out.append(f"""def d{n} : CellD :=
  {lean_cell(d)}

theorem ck{n} : chkCell cs{n - 1} {"0" if n == 1 else f"d{n-1}.I'"} d{n} = true := by decide +kernel

def cs{n} : List (ℕ × ℚ) := cs{n - 1} ++ [(d{n}.B, d{n}.η)]

set_option maxRecDepth 100000 in
theorem st{n} [Fact TernaryGoldbach.PlattGRH] : McovR (X0 + 1) cs{n} ∧ endC (X0 + 1) cs{n} = d{n}.B ∧
    ∑ n ∈ Ioo X0 d{n}.B, |Nn n| * wN n ≤ (d{n}.I' : ℝ) :=
  cell_sound st{n - 1}.1 st{n - 1}.2.1 st{n - 1}.2.2 ck{n}
""")
        out.append("end TernaryGoldbach.Prelim.Sch\n")
        open(f"TernaryGoldbach/Prelim/SchoenfeldCells{fi + 1}.lean", "w").write("\n".join(out))
    print("files", nfiles, file=sys.stderr)

if __name__ == "__main__":
    cells = run()
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else None
    write(cells, nmax)
