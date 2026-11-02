"""Generates TernaryGoldbach/Prelim/RamareWalk.lean and RamareNum.lean.

Simulates the kernel walk of RamareWalk.lean (logs, H_n, the alternating sum to 2000 and the
prime sum of log p/(p^3 - p) to 20001, at D = 10^30), writes the checkpoint states, and fills the
decimal bounds of RamareNum.lean into RamareNum.tmpl.
"""
import os
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..")
import math
from fractions import Fraction as Fr
D=10**30
K=12
def incrLo(n): return sum(2*D//((2*k+1)*(2*n+1)**(2*k+1)) for k in range(K))
def incrHi(n): return incrLo(n)+K+3*D//(25*(2*n+1)**25)+1
def isPr(p): return p>=2 and all(p<d*d or p%d!=0 for d in range(2,148))
NA=2000
def step(n,s):
    Llo,Lhi,Hlo,Hhi,Aplo,Aphi,Anlo,Anhi,Tlo,Thi=s
    Llo+=incrLo(n); Lhi+=incrHi(n)
    Hlo+=D//(n+1); Hhi+=D//(n+1)+1
    if n+1<=NA:
        w=D//((n+1)**2)
        if (n+1)%2==1: Aplo+=Llo*w; Aphi+=Lhi*(w+1)
        else: Anlo+=Llo*w; Anhi+=Lhi*(w+1)
    if isPr(n+1):
        w3=D//(n*(n+1)*(n+2))
        Tlo+=Llo*w3; Thi+=Lhi*(w3+1)
    return (Llo,Lhi,Hlo,Hhi,Aplo,Aphi,Anlo,Anhi,Tlo,Thi)
s=(0,0,D,D,0,0,0,0,0,0)
bounds=[1,1000,2000,2001,2002]+list(range(3000,20001,1000))+[20001]
states={1:s}
n=1
for b in bounds[1:]:
    while n<b:
        s=step(n,s); n+=1
    states[n]=s

# ---- RamareWalk.lean ----
st={str(k):list(v) for k,v in states.items()}
def S(v): return "⟨" + ", ".join(str(x) for x in v) + "⟩"
src=r'''import TernaryGoldbach.Prelim.RamareHarm

/-!
# Kernel walk for `log n`, `H_n`, `∑_{k ≤ 2000} (−1)^{k+1} log k/k²` and `∑_{p ≤ n} log p/(p³ − p)`

With `D = 10³⁰`, the state at `n` bounds `D log n`, `D H_n`, `D² ∑_{k ≤ min(n, 2000)} log k/k²` over
odd and over even `k`, and `D² ∑_{p ≤ n} log p/(p³ − p)`. Each step adds the artanh bounds for
`log(1 + 1/n)` (12 terms, `Real.hasSum_log_one_add_inv`) and the rounded `D/(n+1)`, `D/(n+1)²`,
`D/(n(n+1)(n+2))`; primality of `n + 1 < 147²` is decided by trial division (`isPr_iff`). The kernel
checks the states at 24 points up to `n = 20001`.
-/

open Finset Real

namespace TernaryGoldbach.Prelim.RamPf

/-- `∑_{j<k} ⌊2·10³⁰/((2j+1)(2n+1)^{2j+1})⌋`. -/
def incrAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => incrAux k n + 2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))

def incrLo (n : ℕ) : ℕ := incrAux 12 n
def incrHi (n : ℕ) : ℕ := incrAux 12 n + 12 + 3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) + 1

theorem incrAux_le (n : ℕ) : ∀ k, (incrAux k n : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1)
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (incrAux_le n k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30) (n := (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    rw [one_div_pow]
    push_cast
    field_simp
    norm_num

theorem le_incrAux (n : ℕ) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1) ≤ (incrAux k n : ℝ) + k
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_incrAux n k
    have hpos : 0 < (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) := by positivity
    have h2 := Nat.lt_div_mul_add (a := 2 * 10 ^ 30) hpos
    have h3 : ((2 * 10 ^ 30 : ℕ) : ℝ) < ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) *
        (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) + (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hq : (0 : ℝ) < (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have h4 : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) ≤
        ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) + 1 := by
      have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) =
          ((2 * 10 ^ 30 : ℕ) : ℝ) / (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
        rw [one_div_pow]; push_cast; field_simp; norm_num
      rw [e, div_le_iff₀ hq]; linarith
    linarith

/-- **`incrLo/D ≤ log(1 + 1/n) ≤ incrHi/D`** for `n ≥ 1`. -/
theorem incr_bounds {n : ℕ} (hn : 1 ≤ n) :
    (incrLo n : ℝ) ≤ 10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ∧
      10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ≤ (incrHi n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hn0 12
  refine ⟨(incrAux_le n 12).trans (by nlinarith), ?_⟩
  have h3 := le_incrAux n 12
  -- the tail `(2/25) y^{25}/(1 − y²) ≤ 3/(25 (2n+1)^{25})`
  set y : ℝ := 1 / (2 * (n : ℝ) + 1) with hy
  have hy0 : 0 < y := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤ ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * n + 1) ^ 25 := by positivity
    have h2 := Nat.lt_div_mul_add (a := 3 * 10 ^ 30) hpos
    have hq : (0 : ℝ) < ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast hpos
    have h3' : ((3 * 10 ^ 30 : ℕ) : ℝ) < ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) *
        ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) + ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast h2
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) = ((3 * 10 ^ 30 : ℕ) : ℝ) / ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by
      rw [hy, one_div_pow]; push_cast; field_simp; norm_num
    rw [e, div_le_iff₀ hq]; linarith
  unfold incrHi
  push_cast
  push_cast at h3
  nlinarith

/-! ### The walk -/

/-- Trial division by `2 ≤ d ≤ 147` with `d² ≤ p`. -/
def isPr (p : ℕ) : Bool :=
  2 ≤ p && (List.range' 2 146).all (fun d => p < d * d || p % d != 0)

theorem isPr_iff {p : ℕ} (hp : p < 21609) : isPr p = true ↔ p.Prime := by
  unfold isPr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h.1, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
    have hm : m ≤ 147 := by nlinarith
    rcases h.2 m ⟨hm2, by omega⟩ with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
  · intro h
    refine ⟨h.two_le, fun d hd => ?_⟩
    by_cases hdd : p < d * d
    · exact Or.inl hdd
    · right
      intro hmod
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases h.eq_one_or_self_of_dvd d hdvd with h1 | h1
      · omega
      · subst h1; nlinarith

structure WS where
  Llo : ℕ
  Lhi : ℕ
  Hlo : ℕ
  Hhi : ℕ
  Aplo : ℕ
  Aphi : ℕ
  Anlo : ℕ
  Anhi : ℕ
  Tlo : ℕ
  Thi : ℕ
deriving DecidableEq

def wstep (n : ℕ) (s : WS) : WS :=
  let Llo := s.Llo + incrLo n
  let Lhi := s.Lhi + incrHi n
  let w := 10 ^ 30 / ((n + 1) ^ 2)
  { Llo := Llo, Lhi := Lhi,
    Hlo := s.Hlo + 10 ^ 30 / (n + 1), Hhi := s.Hhi + 10 ^ 30 / (n + 1) + 1,
    Aplo := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aplo + Llo * w else s.Aplo,
    Aphi := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aphi + Lhi * (w + 1) else s.Aphi,
    Anlo := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anlo + Llo * w else s.Anlo,
    Anhi := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anhi + Lhi * (w + 1) else s.Anhi,
    Tlo := if isPr (n + 1) then s.Tlo + Llo * (10 ^ 30 / (n * (n + 1) * (n + 2))) else s.Tlo,
    Thi := if isPr (n + 1) then s.Thi + Lhi * (10 ^ 30 / (n * (n + 1) * (n + 2)) + 1) else s.Thi }

/-- The walk, forcing the state at each step. -/
def walkW : ℕ → ℕ → WS → Option WS
  | _, 0, s => some s
  | n, len + 1, s =>
    if s.Llo + s.Lhi + s.Hlo + s.Hhi + s.Aplo + s.Aphi + s.Anlo + s.Anhi + s.Tlo + s.Thi < 10 ^ 200 then
      walkW (n + 1) len (wstep n s) else none

/-- `∑_{k ≤ min(n, 2000), k odd} log k/k²`. -/
noncomputable def AP (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, if k ≤ 2000 ∧ k % 2 = 1 then Real.log k / (k : ℝ) ^ 2 else 0

/-- `∑_{k ≤ min(n, 2000), k even} log k/k²`. -/
noncomputable def AN (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, if k ≤ 2000 ∧ k % 2 = 0 then Real.log k / (k : ℝ) ^ 2 else 0

/-- `∑_{p ≤ n} log p/(p³ − p)`. -/
noncomputable def TP (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, if k.Prime then Real.log k / ((k : ℝ) ^ 3 - k) else 0

/-- `H_n = ∑_{k ≤ n} 1/k`. -/
noncomputable def Hn (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, 1 / (k : ℝ)

/-- The invariant. -/
def Inv (n : ℕ) (s : WS) : Prop :=
  (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧ 10 ^ 30 * Real.log n ≤ s.Lhi ∧
  (s.Hlo : ℝ) ≤ 10 ^ 30 * Hn n ∧ 10 ^ 30 * Hn n ≤ s.Hhi ∧
  (s.Aplo : ℝ) ≤ 10 ^ 60 * AP n ∧ 10 ^ 60 * AP n ≤ s.Aphi ∧
  (s.Anlo : ℝ) ≤ 10 ^ 60 * AN n ∧ 10 ^ 60 * AN n ≤ s.Anhi ∧
  (s.Tlo : ℝ) ≤ 10 ^ 60 * TP n ∧ 10 ^ 60 * TP n ≤ s.Thi

theorem floor_div_bounds (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h2 := Nat.lt_div_mul_add (a := a) hb
  have hq : (0 : ℝ) < b := by exact_mod_cast hb
  have : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h2
  rw [div_le_iff₀ hq]; linarith

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) (hn' : n + 1 < 21609) {s : WS} (h : Inv n s) :
    Inv (n + 1) (wstep n s) := by
  obtain ⟨l1, l2, h1, h2, p1, p2, q1, q2, t1, t2⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  have hL1 : ((s.Llo + incrLo n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + incrHi n : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨f1, f2⟩ := floor_div_bounds (10 ^ 30) (n + 1) (by omega)
  obtain ⟨g1, g2⟩ := floor_div_bounds (10 ^ 30) ((n + 1) ^ 2) (by positivity)
  have hH : Hn (n + 1) = Hn n + 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [Hn, Hn, sum_Icc_succ_top (by omega)]
  have hAP : AP (n + 1) = AP n + if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then
      Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 else 0 := by
    rw [AP, AP, sum_Icc_succ_top (by omega)]
  have hAN : AN (n + 1) = AN n + if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then
      Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 else 0 := by
    rw [AN, AN, sum_Icc_succ_top (by omega)]
  have hTP : TP (n + 1) = TP n + if (n + 1).Prime then
      Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ)) else 0 := by
    rw [TP, TP, sum_Icc_succ_top (by omega)]
  have hpr : isPr (n + 1) = true ↔ (n + 1).Prime := isPr_iff hn'
  -- the term `D² log(n+1)/(n+1)²` between `Llo' w` and `Lhi' (w+1)`
  set Lo := s.Llo + incrLo n
  set Hi := s.Lhi + incrHi n
  set w := 10 ^ 30 / ((n + 1) ^ 2)
  have hw : ((10 ^ 30 : ℕ) : ℝ) / (((n + 1) ^ 2 : ℕ) : ℝ) = 10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  rw [hw] at g1 g2
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hLo0 : (0 : ℝ) ≤ Lo := Nat.cast_nonneg _
  have hT1 : ((Lo * w : ℕ) : ℝ) ≤ 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [Nat.cast_mul]
    have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) =
        (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
    rw [e]
    exact mul_le_mul hL1 g1 hw0 (by positivity)
  have hT2 : 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤ ((Hi * (w + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, show ((w + 1 : ℕ) : ℝ) = (w : ℝ) + 1 by push_cast; ring]
    have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) =
        (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
    rw [e]
    exact mul_le_mul hL2 g2 (by positivity) (by positivity)
  -- the term `D² log(n+1)/((n+1)³ − (n+1))`
  set w3 := 10 ^ 30 / (n * (n + 1) * (n + 2))
  obtain ⟨k1, k2⟩ := floor_div_bounds (10 ^ 30) (n * (n + 1) * (n + 2)) (by positivity)
  have hw3 : ((10 ^ 30 : ℕ) : ℝ) / ((n * (n + 1) * (n + 2) : ℕ) : ℝ) =
      10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ)) := by push_cast; ring_nf
  rw [hw3] at k1 k2
  have hw30 : (0 : ℝ) ≤ w3 := Nat.cast_nonneg _
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) < (n : ℝ) * (n + 1) * (n + 2) := by positivity
    nlinarith
  have hU1 : ((Lo * w3 : ℕ) : ℝ) ≤
      10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
    rw [Nat.cast_mul]
    have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) =
        (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
      ring
    rw [e]
    exact mul_le_mul hL1 k1 hw30 (by positivity)
  have hU2 : 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) ≤
      ((Hi * (w3 + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, show ((w3 + 1 : ℕ) : ℝ) = (w3 : ℝ) + 1 by push_cast; ring]
    have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) =
        (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
      ring
    rw [e]
    exact mul_le_mul hL2 k2 (by positivity) (by positivity)
  refine ⟨hL1, hL2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((s.Hlo + 10 ^ 30 / (n + 1) : ℕ) : ℝ) ≤ _
    have e : (10 : ℝ) ^ 30 * (Hn n + 1 / ((n + 1 : ℕ) : ℝ)) =
        10 ^ 30 * Hn n + ((10 ^ 30 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hH, e, Nat.cast_add s.Hlo]; linarith
  · show _ ≤ ((s.Hhi + 10 ^ 30 / (n + 1) + 1 : ℕ) : ℝ)
    have e : (10 : ℝ) ^ 30 * (Hn n + 1 / ((n + 1 : ℕ) : ℝ)) =
        10 ^ 30 * Hn n + ((10 ^ 30 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hH, e, Nat.cast_add (s.Hhi + 10 ^ 30 / (n + 1)) 1, Nat.cast_add s.Hhi, Nat.cast_one]; linarith
  · show ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aplo + Lo * w else s.Aplo : ℕ) : ℝ) ≤ _
    rw [hAP]; split_ifs
    · push_cast at hT1 ⊢; linarith
    · linarith
  · show _ ≤ ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aphi + Hi * (w + 1) else s.Aphi : ℕ) : ℝ)
    rw [hAP]; split_ifs
    · push_cast at hT2 ⊢; linarith
    · linarith
  · show ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anlo + Lo * w else s.Anlo : ℕ) : ℝ) ≤ _
    rw [hAN]; split_ifs
    · push_cast at hT1 ⊢; linarith
    · linarith
  · show _ ≤ ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anhi + Hi * (w + 1) else s.Anhi : ℕ) : ℝ)
    rw [hAN]; split_ifs
    · push_cast at hT2 ⊢; linarith
    · linarith
  · show ((if isPr (n + 1) then s.Tlo + Lo * w3 else s.Tlo : ℕ) : ℝ) ≤ _
    rw [hTP]
    by_cases hp : (n + 1).Prime
    · rw [if_pos (hpr.2 hp), if_pos hp, Nat.cast_add s.Tlo]; linarith
    · rw [if_neg (fun h' => hp (hpr.1 h')), if_neg hp]; linarith
  · show _ ≤ ((if isPr (n + 1) then s.Thi + Hi * (w3 + 1) else s.Thi : ℕ) : ℝ)
    rw [hTP]
    by_cases hp : (n + 1).Prime
    · rw [if_pos (hpr.2 hp), if_pos hp, Nat.cast_add s.Thi]; linarith
    · rw [if_neg (fun h' => hp (hpr.1 h')), if_neg hp]; linarith

theorem walkW_spec : ∀ (len n : ℕ) (s s' : WS), 1 ≤ n → n + len < 21609 → Inv n s →
    walkW n len s = some s' → Inv (n + len) s' := by
  intro len
  induction len with
  | zero => intro n s s' _ _ h hw; simp only [walkW, Option.some.injEq] at hw; subst hw; simpa using h
  | succ len ih =>
    intro n s s' hn hl h hw
    rw [walkW] at hw
    split_ifs at hw
    rw [show n + (len + 1) = n + 1 + len by ring]
    exact ih (n + 1) _ _ (by omega) (by omega) (Inv_step hn (by omega) h) hw

theorem Inv_one : Inv 1 ⟨0, 0, 10 ^ 30, 10 ^ 30, 0, 0, 0, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Hn, AP, AN, TP] <;> norm_num

'''
names=[]
for i in range(1,len(bounds)):
    a,b=bounds[i-1],bounds[i]
    src+=f"theorem wk_{i} : walkW {a} {b-a} {S(st[str(a)])} = some {S(st[str(b)])} := by decide +kernel\n"
src+="\ntheorem inv_1 : Inv 1 "+S(st["1"])+" := Inv_one\n"
for i in range(1,len(bounds)):
    a,b=bounds[i-1],bounds[i]
    src+=f"theorem inv_{b} : Inv {b} {S(st[str(b)])} := walkW_spec {b-a} {a} _ _ (by norm_num) (by norm_num) inv_{a} wk_{i}\n"
src+="\nend TernaryGoldbach.Prelim.RamPf\n"
open(os.path.join(ROOT, "TernaryGoldbach/Prelim/RamareWalk.lean"),"w").write(src)

# ---- RamareNum.lean ----
st={k:list(v) for k,v in states.items()}
D=10**30
P=10**20
def fl(x): # floor to 1e-20, as decimal string
    n=(x.numerator*P)//x.denominator
    return dec(n)
def ce(x):
    n=-((-x.numerator*P)//x.denominator)
    return dec(n)
def dec(n):
    s='-' if n<0 else ''; n=abs(n)
    return f"{s}{n//P}.{n%P:020d}"
def S(n): return st[n]
N=20000
Hlo,Hhi=Fr(S(N)[2],D),Fr(S(N)[3],D); LNlo,LNhi=Fr(S(N)[0],D),Fr(S(N)[1],D)
g_lo=fl(Hlo-LNhi-Fr(1,2*N)); g_hi=ce(Hhi-LNlo-Fr(1,2*(N+1)))
s2=S(2000)
c0lo=Fr(S(2001)[0],D)/2001**2; c0hi=Fr(S(2001)[1],D)/2001**2; c1lo=Fr(S(2002)[0],D)/2002**2
X_lo=fl(Fr(s2[4],D*D)-Fr(s2[7],D*D)+c0lo/2)
X_hi=ce(Fr(s2[5],D*D)-Fr(s2[6],D*D)+(2*c0hi-c1lo)/2)
T_lo=fl(Fr(S(N)[8],D*D)); T_hi=ce(Fr(S(N)[9],D*D)+(Fr(S(20001)[1],D)+Fr(1,2))/(2*20000*20001))
print(g_lo,g_hi,X_lo,X_hi,T_lo,T_hi)
pilo=Fr(314159265358979323846,10**20); pihi=Fr(314159265358979323847,10**20)
Zlo,Zhi=pilo**2/6,pihi**2/6
lo=Fr(g_lo)+Fr(6931471803,10**10)+2*Fr(X_lo)/Zlo+Fr(T_lo)
hi=Fr(g_hi)+Fr(6931471808,10**10)+2*Fr(X_hi)/Zhi+Fr(T_hi)
print(float(lo-Fr(13325822,10**7)), float(Fr(13325823,10**7)-hi))
def WSs(n): return "⟨" + ", ".join(str(x) for x in S(n)) + "⟩"
src=open(os.path.join(HERE, "RamareNum.tmpl")).read()
for k,v in {"G_LO":g_lo,"G_HI":g_hi,"X_LO":X_lo,"X_HI":X_hi,"T_LO":T_lo,"T_HI":T_hi}.items():
    src=src.replace("@"+k+"@",v)
open(os.path.join(ROOT, "TernaryGoldbach/Prelim/RamareNum.lean"),"w").write(src)
