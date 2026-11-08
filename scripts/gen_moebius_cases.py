# Generates Prelim/MoebiusCases.lean: |m(x)| log x <= K on ranges of x >= 2 160 535 from `case_gen`
# (Prelim/MoebiusCase.lean), and the stepped profile `mprof`.
# For each range [X0, X1): a cut Y (a boundary of the kernel table `SmallE.ETab`), groups of table
# chunks of ratio about R (`GOK`), the analytic bound `an_k` for the range of x, and the exact rational
# check of every numerical side condition (as Lean's norm_num / decide will see it).
import math, sys, io, contextlib
from fractions import Fraction as Q
sys.path.insert(0, 'scripts')
src = open('scripts/gen_e_walk.py').read()
src = src.split("for f in glob.glob(\"TernaryGoldbach/Prelim/SmallEData")[0]
with contextlib.redirect_stdout(io.StringIO()):
    exec(src)
    from cert_tables import ELpow, T12, EHpow, T12up
S = 10**12
GHI, GLO = 577219635862, 577211640885
CH = sorted((a, b, max(ehi + GHI, -(elo + GLO))) for a, b, elo, ehi, logs in chunks)
BND = [a for a, b, e in CH]

def chkLow(cN, cD, L):
    a = cN // cD; r = cN % cD; return EHpow(a) * T12up(Q(r, cD)) <= L
def chkStep(cN, cD, L):
    a = cN // cD; r = cN % cD; return Q(L) < ELpow(a) * T12(Q(r, cD))
def log_lo(L):
    c = math.floor(10**4 * math.log(L)) - 1
    while not chkLow(c, 10**4, L): c -= 1
    return c
def log_hi(L):
    c = math.ceil(10**4 * math.log(L)) + 1
    while not chkStep(c, 10**4, L): c += 1
    return c

def groups(Y, R):
    out = []; cur = None
    for a, b, e in CH:
        if b <= Y: continue
        assert a >= Y
        if cur is None: cur = [a, b, e]
        elif cur[1] >= cur[0] * R: out.append(tuple(cur)); cur = [a, b, e]
        else: cur[1] = b; cur[2] = max(cur[2], e)
    out.append(tuple(cur))
    assert out[-1][1] == 1000000
    return out
def gT(Y, gs, X0):
    t1 = sum(Q(e) * (V - U) / (U * S) for U, V, e in gs)
    t2 = sum(2 * Q(e) * V / S for U, V, e in gs)
    return t1 + t2 / X0

def dq(s):  # decimal string -> Fraction
    return Q(s)
FULL = [lambda X0: dq("11.82") * (Q(2, 1000) - Q(2, 7043) + Q(2 * 7043) / X0) + dq("1e-13") * (dq("3.9043") + Q(2 * 49603849) / X0),
        lambda X0: dq("13.6") * (Q(2, 7043) - Q(2, 31622) + Q(2 * 31622) / X0) + dq("0.0022500000001") * (dq("3.004") + Q(2 * 999950884) / X0),
        lambda X0: dq("112.7") * (Q(2, 31622) - Q(2, 39749) + Q(2 * 39749) / X0) + dq("1e-13") * (dq("0.4577") + Q(2 * 1579983001) / X0),
        lambda X0: dq("222.6") * (Q(2, 39749) - Q(2, 7000000) + Q(2 * 7000000) / X0) + dq("1e-13") * (dq("10.3425") + Q(2 * 49000000000000) / X0),
        lambda X0: Q(2 * 97, 7000000) + dq("1.234001e-6") * (Q(20001) - dq("31.5227") + 2) + dq("2.51") / dq("30.8295")**2]
TOP = [lambda L1: Q(2) * dq("11.82") / 1000 + dq("1e-13") * (1 + L1 - dq("13.8154")),
       lambda L1: Q(2) * dq("13.6") / 7043 + dq("0.0022500000001") * (1 + L1 - dq("17.7194")),
       lambda L1: Q(2) * dq("112.7") / 31622 + dq("1e-13") * (1 + L1 - dq("20.7231")),
       lambda L1: Q(2) * dq("222.6") / 39749 + dq("1e-13") * (1 + L1 - dq("21.1805")),
       lambda L1: Q(2 * 97, 7000000) + dq("1.234001e-6") * (1 + L1 - dq("31.5227")) + dq("2.51") / dq("30.8295")**2,
       lambda L1: Q(8200) / dq("1e13") + Q(33) / 20000**2 + Q(2) * dq("4.1") / 20000]
def Aan(k, X0, L1):
    if k == 6: return sum(FULL[i](Q(10**26)) for i in range(4)) + FULL[4](None) + TOP[5](None)
    return sum(FULL[i](X0) for i in range(k - 1)) + TOP[k - 1](L1)
def tail(Y, D0, s, s1, lY):
    return ((Q(1, 4345) + (Q(1, 4345) + dq("0.5672") / s)) * dq("0.5773") +
            (lY - dq("0.5772") + dq("0.5773") + (1 + dq("0.5773")) * (lY + Q(1, D0))) / 4345 +
            dq("0.5672") * (dq("2.0884") / s1 + 2 * (1 + dq("0.5773")) / s))

def plan(X0, k, L1, K, L0, Ys=(298, 501, 1001, 2009, 4957, 10091, 29937, 100129, 300129), Rs=(1.02, 1.05, 1.1)):
    best = None
    for Yr in Ys:
        Y = min(BND, key=lambda t: abs(t - Yr))
        D0 = X0 // Y
        if D0 < 101 or Y * (D0 + 1) > 1000000 * D0: continue
        s = math.isqrt(D0); s1 = math.isqrt(D0 + 1)
        lYc = log_hi(Y); lY = Q(lYc, 10**4)
        for R in Rs:
            gs = groups(Y, R)
            Tq = gT(Y, gs, Q(X0))
            T = Q(math.ceil(Tq * 10**6), 10**6)
            H = T + Aan(k, Q(X0), L1) + tail(Y, D0, s, s1, lY)
            ok = H <= K and K * dq("0.5773") <= (K - H) * L0
            if best is None or H < best[0]:
                best = (H, dict(Y=Y, R=R, gs=gs, D0=D0, s=s, s1=s1, lYc=lYc, T=T, ok=ok))
    return best

def dec(q, digits=6):
    """A decimal string >= q."""
    v = math.ceil(q * 10**digits)
    return f"{Q(v, 10**digits).numerator / Q(v, 10**digits).denominator:.{digits}f}" if False else str_dec(v, digits)
def str_dec(v, digits):
    sgn = "-" if v < 0 else ""; v = abs(v)
    ip, fp = divmod(v, 10**digits)
    return f"{sgn}{ip}.{fp:0{digits}d}"

# ranges: (name, X0 (nat), upper: ('nat', X1, strict) or ('log', L1), an index, K, profile step)
CASES = [
    ("c1", 2160535, ("nat", 3000000), 1, "0.14"),
    ("c2", 3000000, ("nat", 5000000), 1, "0.14"),
    ("c3", 5000000, ("nat", 10000000), 1, "0.14"),
    ("c4", 10000000, ("nat", 20000000), 1, "0.1"),
    ("c5", 20000000, ("nat", 49603849), 1, "0.1"),
    ("c6", 49603849, ("nat", 100000000), 2, "0.08"),
    ("c7", 100000000, ("nat", 999950884), 2, "0.08"),
    ("c8", 999950884, ("nat", 1579983001), 3, "0.08"),
    ("c9", 1579983001, ("nat", 10000000000), 4, "0.08"),
    ("c10", 10000000000, ("nat", 100000000000), 4, "0.065"),
    ("c11", 100000000000, ("nat", 49000000000000), 4, "0.065"),
    ("c12", 49000000000000, ("nat", 10**17), 5, "0.065"),
    ("c13", 10**17, ("log", 100), 5, "0.065"),
    ("c14", 10**43, ("log", 200), 5, "0.065"),
    ("c15", 10**86, ("log", 20001), 5, "0.09"),
    ("c16", 10**26, ("exp", None), 6, "0.09"),
]

def main():
    out = []; gout = []
    groupdefs = {}
    for name, X0, up, k, Ks in CASES:
        K = dq(Ks)
        L0c = log_lo(X0); L0 = Q(L0c, 10**4)
        if up[0] == "nat":
            L1c = log_hi(up[1]); L1 = Q(L1c, 10**4)
        elif up[0] == "log":
            L1 = Q(up[1]); L1c = None
        else:
            L1 = None; L1c = None
        H, p = plan(X0, k, L1, K, L0)
        print(name, X0, up, "an", k, "K", Ks, "H", float(H), "Y", p['Y'], "R", p['R'], "groups", len(p['gs']), "ok", p['ok'],
              "need L0>=", float(K * dq("0.5773") / (K - H)) if H < K else None, "L0", float(L0))
        assert p['ok']
        gkey = (p['Y'], p['R'])
        if gkey not in groupdefs:
            gname = f"gsY{p['Y']}R{str(p['R']).replace('.', '_')}"
            groupdefs[gkey] = gname
            lst = ", ".join(f"({V}, {e})" for U, V, e in p['gs'])
            gout.append(f"def {gname} : List (ℕ × ℕ) := [{lst}]\n\ntheorem {gname}_ok : GOK {p['Y']} {gname} = true := by decide +kernel\n")
        gname = groupdefs[gkey]
        T = p['T']; Ts = str_dec(int(T * 10**6), 6)
        # hypotheses on x
        if up[0] == "nat":
            hyp = f"(h0 : (({X0} : ℕ) : ℝ) ≤ x) (h1 : x < (({up[1]} : ℕ) : ℝ))"
        elif up[0] == "log":
            hyp = f"(h0 : (({X0} : ℕ) : ℝ) ≤ x) (h1 : Real.log x ≤ {up[1]})"
        else:
            hyp = f"(h0 : Real.exp 20001 ≤ x)"
        lines = [f"theorem {name} (hCDE : CDEMertens) {{x : ℝ}} {hyp} :\n    |mx x| * Real.log x ≤ {Ks} := by"]
        if up[0] == "exp":
            lines.append(f"  have h0' : (({X0} : ℕ) : ℝ) ≤ x := le_trans (by have := exp_20001_ge; norm_num at this ⊢; linarith) h0")
            h0n = "h0'"
        else:
            h0n = "h0"
        lines.append(f"  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) {h0n}")
        if up[0] == "nat":
            lines.append(f"  have hL1 : Real.log x ≤ {str_dec(L1c, 4)} := by\n"
                         f"    have := log_le_cert (L := {up[1]}) (cN := {L1c}) (by norm_num) (by decide +kernel)\n"
                         f"    have h2 := Real.log_le_log hx0 h1.le\n    norm_num at this h2 ⊢; linarith")
        elif up[0] == "log":
            lines.append(f"  have hL1 : Real.log x ≤ {up[1]} := h1")
        # analytic part
        if k == 1:
            lines.append(f"  have hA := an1 (x := x) (by norm_num at {h0n} ⊢; linarith) (by norm_num at h1 ⊢; linarith) hL1")
        elif k in (2, 3, 4):
            rel = {2: "x < ((999950884 : ℕ) : ℝ)", 3: "x ≤ ((1579983001 : ℕ) : ℝ)", 4: "x ≤ ((49000000000000 : ℕ) : ℝ)"}[k]
            lines.append(f"  have hA := an{k} (x := x) (by norm_num at {h0n} ⊢; linarith) (show {rel} by norm_num at h1 ⊢; linarith)\n"
                         f"    (X0 := (({X0} : ℕ) : ℝ)) (by norm_num) {h0n} hL1")
        elif k == 5:
            lines.append(f"  have hA := an5 (x := x) (by norm_num at {h0n} ⊢; linarith) (X0 := (({X0} : ℕ) : ℝ)) (by norm_num) {h0n} hL1")
        else:
            lines.append(f"  have hA := an6 h0")
        lines.append(f"  have hT : (gT1 {p['Y']} {gname} : ℝ) + (gT2 {gname} : ℝ) / (({X0} : ℕ) : ℝ) ≤ {Ts} := by\n"
                     f"    have h : gT1 {p['Y']} {gname} + gT2 {gname} / (({X0} : ℕ) : ℚ) ≤ {Ts} := by decide +kernel\n"
                     f"    have := (Rat.cast_le (K := ℝ)).2 h\n    push_cast at this ⊢; exact this")
        lines.append(f"  have hlY : Real.log (({p['Y']} : ℕ) : ℝ) ≤ {str_dec(p['lYc'], 4)} := by\n"
                     f"    have := log_le_cert (L := {p['Y']}) (cN := {p['lYc']}) (by norm_num) (by decide +kernel)\n"
                     f"    norm_num at this ⊢; linarith")
        lines.append(f"  have hc := case_gen hCDE (X0 := {X0}) (Y := {p['Y']}) (D0 := {p['D0']}) (s := {p['s']}) (s1 := {p['s1']})\n"
                     f"    (gs := {gname}) {h0n} (by norm_num) (by norm_num) {gname}_ok (by norm_num) (by norm_num) (by norm_num)\n"
                     f"    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlY hT hA")
        lines.append(f"  have hL0 : {str_dec(L0c, 4)} ≤ Real.log x := by\n"
                     f"    have := log_ge_cert (L := {X0}) (cN := {L0c}) (by norm_num) (by decide +kernel)\n"
                     f"    have h2 := Real.log_le_log (by norm_num) {h0n}\n    norm_num at this h2 ⊢; linarith")
        lines.append(f"  exact final_step hc hL0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n")
        out.append("\n".join(lines))
    hdr = """import TernaryGoldbach.Prelim.MoebiusCase

/-!
# `|m(x)| log x` for `x ≥ 2 160 535` (generated by `scripts/gen_moebius_cases.py`)

Ranges of `x`, each from `case_gen` with a cut `Y`, table groups (`gs…`, checked by the kernel) and
the analytic bound `an_k` of the range containing `x`.
-/

namespace TernaryGoldbach.Prelim

"""
    open("TernaryGoldbach/Prelim/MoebiusCases.lean", "w").write(hdr + "\n".join(gout) +
        "\nvariable [Fact TernaryGoldbach.PlattGRH]\n\n" + "\n".join(out) + "\nend TernaryGoldbach.Prelim\n")

if __name__ == "__main__":
    main()
