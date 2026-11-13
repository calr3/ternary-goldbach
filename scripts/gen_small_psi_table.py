# Generates Prelim/SmallPsiData1–6.lean and SmallPsiTableMain.lean with the argument `emit` (run from the
# repo root). Simulates `outer` exactly.
import math, sys
sys.path.insert(0, 'scripts')
from fractions import Fraction as Q
from sympy import primerange, isprime
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cert_tables import ELpow, T12, EHpow, T12up
S = 10**9
P1000 = list(primerange(2, 1001))
LQ = {}
def chkStep(cN, cD, n, L):
    a = cN*n//cD; r = cN*n % cD
    return Q(L) < ELpow(a)*T12(Q(r, cD))
def chkLow(cN, cD, L):
    a = cN//cD; r = cN % cD
    return EHpow(a)*T12up(Q(r, cD)) <= L
for q in P1000:
    lo = math.floor(S*math.log(q)) - 2; hi = math.ceil(S*math.log(q)) + 2
    while not chkLow(lo, S, q): lo -= 1
    while not chkStep(hi, S, 1, q): hi += 1
    LQ[q] = (lo, hi)
def logcert(e):
    lo = math.floor(S*math.log(e)) - 2; hi = math.ceil(S*math.log(e)) + 2
    while not chkLow(lo, S, e): lo -= 1
    while not chkStep(hi, S, 1, e): hi += 1
    return lo, hi
def spf(n):
    for p in P1000:
        if n < p*p: return 0
        if n % p == 0: return p
    return 0
def ispow(q, m):
    while m % q == 0: m //= q
    return m == 1
def inner(LL, LH, m, tlo, thi, plo, phi, k):
    for _ in range(k):
        m += 1
        q = spf(m)
        if q == 0: tlo += LL; thi += LH
        elif ispow(q, m): plo += LQ[q][0]; phi += LQ[q][1]
    return tlo, thi, plo, phi
def leSq(a, b, n, cN, cD):
    return a <= b or (a-b)**2*cD**2 <= S**2*cN**2*n
def winOK(n, e, tlo, plo, thi1, phi1, cN, cD, tN, tD):
    return leSq(thi1+phi1, S*n, n, cN, cD) and leSq(S*e, tlo+plo, n, cN, cD) and thi1 <= S*n and leSq(S*e, tlo, n, tN, tD)
def outer(cN, cD, tN, tD, st, gs):
    n, tlo, thi, plo, phi, LL, LH = st
    for (G, L1, H1) in gs:
        e = n + G
        LLe = LL + S*G//e if L1 == 0 else L1
        LHe = LH + (S*G + n - 1)//n if L1 == 0 else H1
        if L1 != 0: assert chkLow(L1, S, e) and chkStep(H1, S, 1, e)
        Lw = LLe if G == 1 else LL
        a, b, c, d = inner(Lw, LHe, n, tlo, thi, plo, phi, G)
        if not winOK(n, e, tlo, plo, b, d, cN, cD, tN, tD):
            raise Exception(f"check fails at window ({n}, {e}]")
        n, tlo, thi, plo, phi, LL, LH = e, a, b, c, d, LLe, LHe
    return (n, tlo, thi, plo, phi, LL, LH)
def windows(n0, n1, cert_below=20000, gfac=0.15, first_cert=True):
    gs = []; n = n0
    while n < n1:
        G = 1 if n < 1000 else max(1, int(gfac*math.sqrt(n)))
        G = min(G, n1 - n)
        e = n + G
        if n < cert_below or (first_cert and n == n0):
            L1, H1 = logcert(e)
        else:
            L1, H1 = 0, 0
        gs.append((G, L1, H1)); n = e
    return gs
if __name__ == "__main__":
    import time
    cN, cD, tN, tD = 1, 1, 23662, 10000
    st = (1, 0, 0, 0, 0, 0, 0)
    gs0 = windows(1, 12)
    st = outer(10**6, 1, 10**6, 1, st, gs0)
    print("state at 12:", st)
    t0 = time.time()
    gs = windows(12, 2000)
    st2 = outer(cN, cD, tN, tD, st, gs)
    print("state at 2000:", st2, time.time() - t0)

def full(cN=1, cD=1, tN=23662, tD=10000, chunk=10000, top=10**6, gfac=0.15):
    st = (1, 0, 0, 0, 0, 0, 0)
    gs0 = windows(1, 12)
    st = outer(10**6, 1, 10**6, 1, st, gs0)
    chunks = [(st, gs0, 'init')]
    bounds = [12, 300, 1000, 2500, 5000] + list(range(chunk, top, chunk)) + [top]
    for i in range(len(bounds) - 1):
        gs = windows(bounds[i], bounds[i+1], gfac=gfac)
        for j in range(0, len(gs), 250):
            sub = gs[j:j+250]
            if j > 0 and sub[0][1] == 0:   # re-certify the log at a sub-chunk start
                n = st[0]; G = sub[0][0]
                L1, H1 = logcert(n + G)
                sub = [(G, L1, H1)] + sub[1:]
            st1 = outer(cN, cD, tN, tD, st, sub)
            chunks.append((st, sub, st1))
            st = st1
    return chunks

def emit(per_file=21):
    ch = full()
    # chunk 0 = init (1 → 12) with trivial constants
    names = []
    files = []
    cur = []
    for k, (st, gs, st1) in enumerate(ch):
        if st1 == 'init':
            st0 = (1, 0, 0, 0, 0, 0, 0)
            st1 = st
            st = st0
            consts = "1000000 1 1000000 1"
        else:
            consts = "1 1 23662 10000"
        gsl = "[" + ", ".join(f"({a}, {b}, {c})" for a, b, c in gs) + "]"
        n, tlo, thi, plo, phi, LL, LH = st
        res = " ".join(map(str, st1))
        txt = f"""
set_option maxRecDepth 100000 in
def gs{k} : List (ℕ × ℕ × ℕ) := {gsl}

set_option maxRecDepth 100000 in
theorem chunk{k} : resEq (outer {consts} {n} {tlo} {thi} {plo} {phi} {LL} {LH} gs{k}) {res} = true := by
  decide +kernel

theorem sum{k} : {n} + (gs{k}.map (fun g => g.1)).sum ≤ 1000000 := by decide +kernel
"""
        cur.append(txt)
        names.append((k, consts, st, st1))
        if len(cur) == per_file:
            files.append(cur); cur = []
    if cur: files.append(cur)
    for i, f in enumerate(files):
        hdr = f"""import TernaryGoldbach.Prelim.SmallPsiTable

/-! Data for `SmallPsiTable` (generated by `scripts/gen_small_psi_table.py`), part {i+1}. -/

namespace TernaryGoldbach.Prelim.SmallTab
"""
        open(f'TernaryGoldbach/Prelim/SmallPsiData{i+1}.lean', 'w').write(hdr + "".join(f) + "\nend TernaryGoldbach.Prelim.SmallTab\n")
    # assembly: a chain of small stage lemmas
    imports = "\n".join(f"import TernaryGoldbach.Prelim.SmallPsiData{i+1}" for i in range(len(files)))
    out = [f"""{imports}

/-!
# `θ` and `ψ` on `[12, 10⁶]`, kernel-checked

`|ψ(t) − t| ≤ √t` and `t − 2.3662 √t ≤ θ(t) ≤ t` for real `12 ≤ t < 10⁶` (`small_table`), chaining
`outer_spec` through the chunks `chunk0`, …, `chunk{len(names)-1}` (stage lemmas `stage_k`).
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallTab

theorem Inv_one : Inv 1 0 0 0 0 := by
  have h1 : thS 1 = 0 := by unfold thS; simp [Finset.filter_singleton, Nat.not_prime_one]
  have h2 : ppS 1 = 0 := by unfold ppS; simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1, h2]
"""]
    for idx, (k, consts, st, st1) in enumerate(names):
        cN, cD, tN, tD = consts.split()
        n, tlo, thi, plo, phi, LL, LH = st
        n1, a, b, c, d, e, f = st1
        res = " ".join(map(str, st1))
        concl_state = f"Inv {n1} {a} {b} {c} {d} ∧ (({e} : ℕ) : ℝ) / S ≤ Real.log (({n1} : ℕ) : ℝ) ∧ Real.log (({n1} : ℕ) : ℝ) ≤ (({f} : ℕ) : ℝ) / S"
        if k == 0:
            out.append(f"""
theorem stage{k} : {concl_state} := by
  obtain ⟨-, I, L, H⟩ := outer_spec (cN := {cN}) (cD := {cD}) (tN := {tN}) (tD := {tD}) (by norm_num) (by norm_num)
    gs{k} {n} {tlo} {thi} {plo} {phi} {LL} {LH} {res} (by norm_num) sum{k} Inv_one (by simp) (by simp)
    (resEq_spec chunk{k})
  exact ⟨I, L, H⟩
""")
        else:
            prevR = "" if k == 1 else "Rp, "
            out.append(f"""
theorem stage{k} : (∀ t : ℝ, 12 ≤ t → t < {n1} → Rt 1 1 23662 10000 t) ∧ {concl_state} := by
  obtain ⟨{prevR}I0, L0, H0⟩ := stage{k-1}
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := {cN}) (cD := {cD}) (tN := {tN}) (tD := {tD}) (by norm_num) (by norm_num)
    gs{k} {n} {tlo} {thi} {plo} {phi} {LL} {LH} {res} (by norm_num) sum{k} I0 L0 H0 (resEq_spec chunk{k})
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
""")
            if k == 1:
                out.append(f"  exact R t (by exact_mod_cast h1) (by exact_mod_cast h2)\n")
            else:
                out.append(f"""  rcases lt_or_ge t {n} with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)
""")
    last = len(names) - 1
    out.append(f"""
/-- **`θ` and `ψ` on `[12, 10⁶)`**: `|ψ(t) − t| ≤ √t` and `t − 2.3662√t ≤ θ(t) ≤ t`. -/
theorem small_table {{t : ℝ}} (h1 : 12 ≤ t) (h2 : t < 1000000) : Rt 1 1 23662 10000 t :=
  stage{last}.1 t h1 h2

end TernaryGoldbach.Prelim.SmallTab
""")
    open('TernaryGoldbach/Prelim/SmallPsiTableMain.lean', 'w').write("".join(out))
    return len(files)
if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "emit":
    print(emit())
