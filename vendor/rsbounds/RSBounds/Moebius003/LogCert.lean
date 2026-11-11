/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Certified rational bounds for `log` and `√`

`logLo q ≤ log q ≤ logHi q` and `sqrtLo q ≤ √q ≤ sqrtHi q` for rational `q > 0`, by functions that
the kernel evaluates (`decide +kernel`): only structural recursion and `Nat`/`Int` arithmetic.

`log` uses `log q = e log 2 + log r` with `r = q/2^e ∈ [1, 2)`, `r` rounded outward to a multiple
of `2⁻⁴⁰`, and the series `log((1+t)/(1−t)) = 2 ∑ t^{2k+1}/(2k+1)` with `t = (r−1)/(r+1) ≤ 1/3`.
The square roots are found by Newton's method with fuel and then checked, so their soundness does
not depend on the convergence of the iteration.
-/

namespace TernaryGoldbach.RSBounds.Moebius003.LogCert

open Real Finset

/-! ### The series -/

/-- `∑_{k < n} t^{2k+1}/(2k+1)`. -/
def atanhSum (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum t n + t ^ (2 * n + 1) / (2 * n + 1)

theorem atanhSum_cast (t : ℚ) (n : ℕ) :
    (atanhSum t n : ℝ) = ∑ k ∈ range n, (t : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih => rw [atanhSum, sum_range_succ, ← ih]; push_cast; ring

theorem hasSum_atanh {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * t ^ (2 * k + 1))
      (Real.log ((1 + t) / (1 - t))) := by
  have := Real.hasSum_log_sub_log_of_abs_lt_one (x := t) (by rw [abs_of_nonneg h0]; exact h1)
  rwa [← Real.log_div (by linarith) (by linarith)] at this

theorem log_ge_atanhSum {t : ℚ} (h0 : 0 ≤ t) (h1 : t < 1) (n : ℕ) :
    2 * (atanhSum t n : ℝ) ≤ Real.log ((1 + t) / (1 - t)) := by
  have h0' : (0 : ℝ) ≤ t := by exact_mod_cast h0
  have h1' : (t : ℝ) < 1 := by exact_mod_cast h1
  have hs := hasSum_atanh h0' h1'
  have := sum_le_hasSum (range n) (fun i _ => by positivity) hs
  rw [atanhSum_cast, mul_sum]
  refine le_trans (le_of_eq ?_) this
  exact sum_congr rfl fun k _ => by ring

theorem log_le_atanhSum {t : ℚ} (h0 : 0 ≤ t) (h1 : t < 1) (n : ℕ) :
    Real.log ((1 + t) / (1 - t)) ≤
      2 * (atanhSum t n : ℝ) + 2 * (t : ℝ) ^ (2 * n + 1) / ((2 * n + 1) * (1 - (t : ℝ) ^ 2)) := by
  have h0' : (0 : ℝ) ≤ t := by exact_mod_cast h0
  have h1' : (t : ℝ) < 1 := by exact_mod_cast h1
  have hs := hasSum_atanh h0' h1'
  have htail := (hasSum_nat_add_iff' n).2 hs
  have ht2 : (t : ℝ) ^ 2 < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one (by positivity) ht2).mul_left
    (2 * (t : ℝ) ^ (2 * n + 1) / (2 * n + 1))
  have hle := hasSum_le (fun k => ?_) htail hg
  · rw [atanhSum_cast, mul_sum]
    have e1 : ∑ i ∈ range n, (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * (t : ℝ) ^ (2 * i + 1) =
        ∑ k ∈ range n, 2 * ((t : ℝ) ^ (2 * k + 1) / (2 * k + 1)) :=
      sum_congr rfl fun k _ => by ring
    rw [e1] at hle
    have e2 : 2 * (t : ℝ) ^ (2 * n + 1) / (2 * n + 1) * (1 - (t : ℝ) ^ 2)⁻¹ =
        2 * (t : ℝ) ^ (2 * n + 1) / ((2 * n + 1) * (1 - (t : ℝ) ^ 2)) := by
      field_simp
    rw [e2] at hle
    linarith
  · show (2 : ℝ) * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * (t : ℝ) ^ (2 * (k + n) + 1) ≤ _
    have hk : (2 * ((k + n : ℕ) : ℝ) + 1) ≥ 2 * n + 1 := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    rw [show 2 * (k + n) + 1 = (2 * n + 1) + 2 * k by ring, pow_add, pow_mul]
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    have : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * n + 1) :=
      one_div_le_one_div_of_le hpos hk
    calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * ((t : ℝ) ^ (2 * n + 1) * ((t : ℝ) ^ 2) ^ k)
        ≤ 2 * (1 / (2 * n + 1)) * ((t : ℝ) ^ (2 * n + 1) * ((t : ℝ) ^ 2) ^ k) := by gcongr
      _ = 2 * (t : ℝ) ^ (2 * n + 1) / (2 * n + 1) * ((t : ℝ) ^ 2) ^ k := by ring

/-! ### `log` of a rational in `[1, 2]` -/

/-- Number of series terms. -/
def nTerms : ℕ := 14

/-- `t = (r − 1)/(r + 1)`. -/
def tOf (r : ℚ) : ℚ := (r - 1) / (r + 1)

theorem one_add_tOf_div {r : ℚ} (hr : 0 < r) : (1 + (tOf r : ℝ)) / (1 - tOf r) = r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  simp only [tOf]; push_cast
  field_simp
  ring

theorem tOf_nonneg {r : ℚ} (hr : 1 ≤ r) : 0 ≤ tOf r := by
  unfold tOf; apply div_nonneg <;> linarith

theorem tOf_lt_one {r : ℚ} (hr : 0 < r) : tOf r < 1 := by
  unfold tOf; rw [div_lt_one (by linarith)]; linarith

/-- Lower bound for `log r`, `r ≥ 1`. -/
def logLoR (r : ℚ) : ℚ := 2 * atanhSum (tOf r) nTerms

/-- Upper bound for `log r`, `r ≥ 1`. -/
def logHiR (r : ℚ) : ℚ :=
  2 * atanhSum (tOf r) nTerms + 2 * (tOf r) ^ (2 * nTerms + 1) / ((2 * nTerms + 1) * (1 - (tOf r) ^ 2))

theorem logLoR_le {r : ℚ} (hr : 1 ≤ r) : (logLoR r : ℝ) ≤ Real.log r := by
  have := log_ge_atanhSum (tOf_nonneg hr) (tOf_lt_one (by linarith)) nTerms
  rw [one_add_tOf_div (by linarith)] at this
  simp only [logLoR]; push_cast; exact this

theorem le_logHiR {r : ℚ} (hr : 1 ≤ r) : Real.log r ≤ logHiR r := by
  have := log_le_atanhSum (tOf_nonneg hr) (tOf_lt_one (by linarith)) nTerms
  rw [one_add_tOf_div (by linarith)] at this
  simp only [logHiR]; push_cast; exact this

/-- `log 2` bounds. -/
def log2Lo : ℚ := logLoR 2
def log2Hi : ℚ := logHiR 2

theorem log2Lo_le : (log2Lo : ℝ) ≤ Real.log 2 := by
  have := logLoR_le (r := 2) (by norm_num); simpa [log2Lo] using this

theorem le_log2Hi : Real.log 2 ≤ log2Hi := by
  have := le_logHiR (r := 2) (by norm_num); simpa [log2Hi] using this

/-! ### `log` of a positive rational -/

/-- `⌊q⌋`, computed as `q.num / q.den`. -/
def qfloor (q : ℚ) : ℤ := q.num / q.den

/-- `⌈q⌉ = −⌊−q⌋`. -/
def qceil (q : ℚ) : ℤ := -qfloor (-q)

theorem qfloor_eq (q : ℚ) : qfloor q = ⌊q⌋ := (Rat.floor_def' (q := q)).symm

theorem qceil_eq (q : ℚ) : qceil q = ⌈q⌉ := by
  rw [qceil, qfloor_eq, Int.floor_neg, neg_neg]

/-- Precision of the rounding of `r`. -/
def prec : ℕ := 2 ^ 40

/-- For `q ≥ 1`: the exponent `e` with `2^e ≤ ⌊q⌋`. -/
def expo (q : ℚ) : ℕ := Nat.log2 (qfloor q).toNat

/-- Lower bound of `log q` for `q ≥ 1`. -/
def logLoGe1 (q : ℚ) : ℚ :=
  let e := expo q
  let r := q / 2 ^ e
  let r' : ℚ := max 1 (qfloor (r * prec) / prec)
  e * log2Lo + logLoR r'

/-- Upper bound of `log q` for `q ≥ 1`. -/
def logHiGe1 (q : ℚ) : ℚ :=
  let e := expo q
  let r := q / 2 ^ e
  let r' : ℚ := max 1 (qceil (r * prec) / prec)
  e * log2Hi + logHiR r'

/-- Lower bound of `log q` for `q > 0`. -/
def logLo (q : ℚ) : ℚ := if 1 ≤ q then logLoGe1 q else -logHiGe1 q⁻¹

/-- Upper bound of `log q` for `q > 0`. -/
def logHi (q : ℚ) : ℚ := if 1 ≤ q then logHiGe1 q else -logLoGe1 q⁻¹

theorem two_pow_expo_le {q : ℚ} (hq : 1 ≤ q) : ((2 : ℚ) ^ expo q) ≤ q := by
  unfold expo
  rw [qfloor_eq]
  have hf : 1 ≤ ⌊q⌋ := by rw [Int.le_floor]; exact_mod_cast hq
  have hn : (⌊q⌋).toNat ≠ 0 := by omega
  have h1 : 2 ^ Nat.log2 (⌊q⌋).toNat ≤ (⌊q⌋).toNat := Nat.log2_self_le hn
  have h2 : (((⌊q⌋).toNat : ℤ) : ℚ) ≤ q := by
    rw [Int.toNat_of_nonneg (by omega)]; exact Int.floor_le q
  calc ((2 : ℚ) ^ Nat.log2 (⌊q⌋).toNat) = ((2 ^ Nat.log2 (⌊q⌋).toNat : ℕ) : ℚ) := by push_cast; rfl
    _ ≤ ((⌊q⌋).toNat : ℚ) := by exact_mod_cast h1
    _ = (((⌊q⌋).toNat : ℤ) : ℚ) := by push_cast; rfl
    _ ≤ q := h2

theorem aux_lo {q r' : ℚ} {e : ℕ} (h1 : 1 ≤ r') (h2 : r' * 2 ^ e ≤ q) :
    (((e : ℚ) * log2Lo + logLoR r' : ℚ) : ℝ) ≤ Real.log q := by
  have hr0 : (0 : ℝ) < r' := by exact_mod_cast (by linarith : (0 : ℚ) < r')
  have hle : Real.log ((r' : ℝ) * 2 ^ e) ≤ Real.log q :=
    Real.log_le_log (by positivity) (by exact_mod_cast h2)
  rw [Real.log_mul hr0.ne' (by positivity), Real.log_pow] at hle
  have := logLoR_le h1
  have h3 := log2Lo_le
  push_cast
  have he : (0 : ℝ) ≤ e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 he]

theorem aux_hi {q r' : ℚ} {e : ℕ} (hq : 0 < q) (h1 : 1 ≤ r') (h2 : q ≤ r' * 2 ^ e) :
    Real.log q ≤ (((e : ℚ) * log2Hi + logHiR r' : ℚ) : ℝ) := by
  have hr0 : (0 : ℝ) < r' := by exact_mod_cast (by linarith : (0 : ℚ) < r')
  have hle : Real.log q ≤ Real.log ((r' : ℝ) * 2 ^ e) :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast h2)
  rw [Real.log_mul hr0.ne' (by positivity), Real.log_pow] at hle
  have := le_logHiR h1
  have h3 := le_log2Hi
  push_cast
  have he : (0 : ℝ) ≤ e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 he]

theorem log_eq_expo {q : ℚ} (hq : 1 ≤ q) :
    Real.log q = expo q * Real.log 2 + Real.log ((q / 2 ^ expo q : ℚ) : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by linarith : (0 : ℚ) < q)
  push_cast
  rw [Real.log_div hq'.ne' (by positivity), Real.log_pow]; ring

theorem logLoGe1_le {q : ℚ} (hq : 1 ≤ q) : (logLoGe1 q : ℝ) ≤ Real.log q := by
  have hpe := two_pow_expo_le hq
  unfold logLoGe1
  simp only
  apply aux_lo (le_max_left _ _)
  have hp : (0 : ℚ) < 2 ^ expo q := by positivity
  have hr1 : 1 ≤ q / 2 ^ expo q := by rw [le_div_iff₀ hp]; linarith
  have : max 1 ((qfloor (q / 2 ^ expo q * prec) : ℚ) / prec) ≤ q / 2 ^ expo q := by
    apply max_le hr1
    rw [div_le_iff₀ (by norm_num [prec]), qfloor_eq]
    exact Int.floor_le _
  calc max 1 ((qfloor (q / 2 ^ expo q * prec) : ℚ) / prec) * 2 ^ expo q
      ≤ q / 2 ^ expo q * 2 ^ expo q := by gcongr
    _ = q := by field_simp

theorem le_logHiGe1 {q : ℚ} (hq : 1 ≤ q) : Real.log q ≤ logHiGe1 q := by
  unfold logHiGe1
  simp only
  apply aux_hi (by linarith) (le_max_left _ _)
  have hp : (0 : ℚ) < 2 ^ expo q := by positivity
  have : q / 2 ^ expo q ≤ max 1 ((qceil (q / 2 ^ expo q * prec) : ℚ) / prec) := by
    apply le_max_of_le_right
    rw [le_div_iff₀ (by norm_num [prec]), qceil_eq]
    exact Int.le_ceil _
  calc q = q / 2 ^ expo q * 2 ^ expo q := by field_simp
    _ ≤ max 1 ((qceil (q / 2 ^ expo q * prec) : ℚ) / prec) * 2 ^ expo q := by gcongr

theorem logLo_le {q : ℚ} (hq : 0 < q) : (logLo q : ℝ) ≤ Real.log q := by
  unfold logLo
  split_ifs with h
  · exact logLoGe1_le h
  · push Not at h
    have h1 : 1 ≤ q⁻¹ := by rw [le_inv_comm₀ one_pos hq]; simpa using h.le
    have := le_logHiGe1 h1
    push_cast at this ⊢
    rw [Real.log_inv] at this
    linarith

theorem le_logHi {q : ℚ} (hq : 0 < q) : Real.log q ≤ logHi q := by
  unfold logHi
  split_ifs with h
  · exact le_logHiGe1 h
  · push Not at h
    have h1 : 1 ≤ q⁻¹ := by rw [le_inv_comm₀ one_pos hq]; simpa using h.le
    have := logLoGe1_le h1
    push_cast at this ⊢
    rw [Real.log_inv] at this
    linarith

/-! ### Square roots -/

/-- Newton's iteration for `⌊√n⌋`, with fuel. -/
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, n, g => if g * g ≤ n then g else isqrtAux f n ((g + n / g) / 2)

/-- An approximation of `⌊√n⌋` (exact when the fuel suffices). -/
def isqrt (n : ℕ) : ℕ := isqrtAux 200 n (2 ^ (Nat.log2 n / 2 + 1))

/-- Precision of the square roots. -/
def sprec : ℕ := 2 ^ 40

/-- A lower bound for `√q`. -/
def sqrtLo (q : ℚ) : ℚ :=
  let n := (qfloor (q * sprec ^ 2)).toNat
  let s : ℚ := (isqrt n : ℚ) / sprec
  if s * s ≤ q then s else 0

/-- An upper bound for `√q`, `q ≥ 0`. -/
def sqrtHi (q : ℚ) : ℚ :=
  let n := (qfloor (q * sprec ^ 2)).toNat
  let s : ℚ := ((isqrt n + 1 : ℕ) : ℚ) / sprec
  if q ≤ s * s ∧ 0 ≤ s then s else q + 1

theorem sqrtLo_le (q : ℚ) : (sqrtLo q : ℝ) ≤ Real.sqrt q := by
  unfold sqrtLo
  simp only
  split_ifs with h
  · have hs : (0 : ℚ) ≤ (isqrt (qfloor (q * sprec ^ 2)).toNat : ℚ) / sprec := by positivity
    have hq0 : (0 : ℚ) ≤ q := le_trans (mul_self_nonneg _) h
    rw [Real.le_sqrt (by exact_mod_cast hs) (by exact_mod_cast hq0)]
    · exact_mod_cast (by nlinarith : ((isqrt (qfloor (q * sprec ^ 2)).toNat : ℚ) / sprec) ^ 2 ≤ q)
  · simp

theorem le_sqrtHi {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ sqrtHi q := by
  unfold sqrtHi
  simp only
  split_ifs with h
  · rw [Real.sqrt_le_left (by exact_mod_cast h.2)]
    exact_mod_cast (by nlinarith [h.1] : q ≤ (((isqrt (qfloor (q * sprec ^ 2)).toNat + 1 : ℕ) : ℚ) / sprec) ^ 2)
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith

end TernaryGoldbach.RSBounds.Moebius003.LogCert
