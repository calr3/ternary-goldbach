import TernaryGoldbach.MinorArcs.T2Defs
import TernaryGoldbach.Prelim.SmallMertens

/-!
# `H₂ ≤ 2/π²` [H, (5.37)] and the corrected [H, (5.36)], checked by the kernel

By [H, (5.19)] (`integral_g2`), `T₂(S)` is a finite sum over `(s, r₁, r₂)` with `s max(r₁, r₂) ≤ S`
of `c(r₁, r₂)/s · (1 − max(1/2, s max(r₁, r₂)/S))`. On `[n, n+1)` each term is either constant or
of the form `a + b/S`, so `T₂(S) = α_n + β_n/S` with rationals `α_n, β_n` (`T2_eq`); the kernel
evaluates them for `n ≤ 15` (`ab_tab`, data from `scripts/gen_h2_tables.py`).

* `H2_le`: `α_n + β_n/S` is monotone in `S`, so `T₂ ≤ 1/2` on `[1, 16)` follows from the
  endpoints.
* `integral_H2_le`: `∫_n^b H₂(S)/S dS = (4/π²)(α_n log(b/n) + β_n (1/n − 1/b))` on each piece. With
  `d(T) = ∫₁ᵀ H₂/S − 0.15107 log T`:
  * on `[2, 15]`, `H₂ ≥ 0.15107`, so `d(T) ≤ d(⌊T⌋ + 1)`;
  * on `[1, 2]` and `[15, 16]`, elementary bounds for `log` are used;
  * for `T ≥ 16`, `d` is constant.

  The values `d(m)`, `3 ≤ m ≤ 16`, are bounded with `log j` to `10⁻⁹` (checked as in
  `Prelim/SmallMertens.lean`) and `π` to `10⁻²⁰` (Mathlib). The largest bound is `0.0230978`, on
  `[15, 16]`.
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs
open TernaryGoldbach.Prelim

namespace H2B

/-! ### `T₂ = α + β/S` on `[n, n+1)` -/

def muZ : List ℤ := [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1]
def sigN : List ℕ := [0, 1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24]

theorem mu_tab : ∀ r ∈ range 16, μ r = muZ.getD r 0 := by decide +kernel
theorem sig_tab : ∀ r ∈ range 16, σ 1 r = sigN.getD r 0 := by decide +kernel

/-- The coefficient `μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))` of `g₂` (for coprime odd `r₁, r₂`), from the tables. -/
def cf (r₁ r₂ : ℕ) : ℚ := if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
    ((muZ.getD r₁ 0 * muZ.getD r₂ 0 : ℤ) : ℚ) / ((sigN.getD r₁ 0 * sigN.getD r₂ 0 : ℕ) : ℚ) else 0

theorem cf_eq {r₁ r₂ : ℕ} (h₁ : r₁ ≤ 15) (h₂ : r₂ ≤ 15) :
    (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) = (cf r₁ r₂ : ℝ) := by
  unfold cf
  split_ifs
  · rw [mu_tab r₁ (mem_range.2 (by omega)), mu_tab r₂ (mem_range.2 (by omega)),
      sig_tab r₁ (mem_range.2 (by omega)), sig_tab r₂ (mem_range.2 (by omega))]
    push_cast; ring
  · simp

/-- The `(s, r₁, r₂)` term of `α_n`. -/
def aT (n s r₁ r₂ : ℕ) : ℚ :=
  cf r₁ r₂ * (if 2 * s * max r₁ r₂ ≤ n then 1 / (2 * (s : ℚ)) else 1 / (s : ℚ))

/-- The `(s, r₁, r₂)` term of `β_n`. -/
def bT (n s r₁ r₂ : ℕ) : ℚ :=
  cf r₁ r₂ * (if 2 * s * max r₁ r₂ ≤ n then 0 else -((max r₁ r₂ : ℕ) : ℚ))

def alphaQ (n : ℕ) : ℚ := ∑ s ∈ Icc 1 n,
  if Odd s then ∑ r₁ ∈ Icc 1 (n / s), ∑ r₂ ∈ Icc 1 (n / s), aT n s r₁ r₂ else 0

def betaQ (n : ℕ) : ℚ := ∑ s ∈ Icc 1 n,
  if Odd s then ∑ r₁ ∈ Icc 1 (n / s), ∑ r₂ ∈ Icc 1 (n / s), bT n s r₁ r₂ else 0

theorem term_eq {n s r₁ r₂ : ℕ} (hs : 1 ≤ s) (h₁ : r₁ ≤ 15) (h₂ : r₂ ≤ 15) {S : ℝ}
    (hn : (n : ℝ) ≤ S) (hn' : S < n + 1) (hS : 0 < S) :
    1 / (s : ℝ) * ((if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
        (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) * wM (S / s) r₁ r₂) =
      (aT n s r₁ r₂ : ℝ) + (bT n s r₁ r₂ : ℝ) / S := by
  rw [cf_eq h₁ h₂]
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hw : max ((r₁ : ℝ) / (S / s)) ((r₂ : ℝ) / (S / s)) = ((max r₁ r₂ : ℕ) : ℝ) * s / S := by
    rw [max_div_div_right (div_pos hS hs0).le, Nat.cast_max]; field_simp
  unfold wM aT bT
  rw [hw]
  split_ifs with hc
  · have h1 : ((2 * s * max r₁ r₂ : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
    have h2 : ((max r₁ r₂ : ℕ) : ℝ) * s / S ≤ 1 / 2 := by
      rw [div_le_iff₀ hS]; push_cast at h1 ⊢; linarith
    rw [max_eq_left h2]; push_cast; field_simp; ring
  · have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((2 * s * max r₁ r₂ : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 2 * s * max r₁ r₂)
    have h2 : 1 / 2 < ((max r₁ r₂ : ℕ) : ℝ) * s / S := by
      rw [lt_div_iff₀ hS]; push_cast at h1 ⊢; linarith
    rw [max_eq_right h2.le]; push_cast; field_simp; ring

/-- **`T₂(S) = α_n + β_n/S` on `[n, n+1)`**, `1 ≤ n ≤ 15`. -/
theorem T2_eq {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 15) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S < n + 1) :
    T2 S = alphaQ n + betaQ n / S := by
  have hS : 0 < S := lt_of_lt_of_le (by exact_mod_cast hn1) h1
  have hfl : ⌊S⌋₊ = n := (Nat.floor_eq_iff hS.le).2 ⟨h1, h2⟩
  unfold T2 alphaQ betaQ
  rw [hfl, Rat.cast_sum, Rat.cast_sum, sum_div, ← sum_add_distrib]
  refine sum_congr rfl fun s hs => ?_
  obtain ⟨hs1, hsn⟩ := mem_Icc.1 hs
  split_ifs with ho
  · have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
    simp_rw [mul_div_assoc]
    rw [integral_g2 (div_pos hS hs0), Nat.floor_div_natCast, hfl, mul_sum, Rat.cast_sum,
      Rat.cast_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun r₁ hr₁ => ?_
    rw [mul_sum, Rat.cast_sum, Rat.cast_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun r₂ hr₂ => ?_
    have hd : n / s ≤ 15 := (Nat.div_le_self n s).trans hn
    exact term_eq hs1 ((mem_Icc.1 hr₁).2.trans hd) ((mem_Icc.1 hr₂).2.trans hd) h1 h2 hS
  · simp

/-- `(α_n, β_n)` for `n ≤ 15` (`scripts/gen_h2_tables.py`). -/
def abT : List (ℚ × ℚ) := [(0/1, 0/1), (1/1, -1/1), (1/2, 0/1), (1/3, 1/2), (1/3, 1/2), (17/60, 3/4), (11/30, 1/4), (611/1680, 13/48), (611/1680, 13/48), (1553/5040, 37/48), (1679/5040, 25/48), (9637/27720, 13/36), (9637/27720, 13/36), (16712/45045, 29/504), (536929/1441440, 37/1008), (113819/360360, 1787/2016)]

def al (n : ℕ) : ℚ := (abT.getD n (0, 0)).1
def be (n : ℕ) : ℚ := (abT.getD n (0, 0)).2

theorem ab_tab1 : ∀ n ∈ Icc 1 8, alphaQ n = al n ∧ betaQ n = be n := by decide +kernel
theorem ab_tab2 : ∀ n ∈ Icc 9 12, alphaQ n = al n ∧ betaQ n = be n := by decide +kernel
theorem ab_tab3 : ∀ n ∈ Icc 13 15, alphaQ n = al n ∧ betaQ n = be n := by decide +kernel

theorem ab_tab {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 15) : alphaQ n = al n ∧ betaQ n = be n := by
  rcases le_or_gt n 8 with h | h
  · exact ab_tab1 n (mem_Icc.2 ⟨h1, h⟩)
  rcases le_or_gt n 12 with h' | h'
  · exact ab_tab2 n (mem_Icc.2 ⟨h, h'⟩)
  · exact ab_tab3 n (mem_Icc.2 ⟨h', h2⟩)

theorem T2_eq' {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 15) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S < n + 1) :
    T2 S = al n + be n / S := by
  rw [T2_eq hn1 hn h1 h2, (ab_tab hn1 hn).1, (ab_tab hn1 hn).2]

/-- Positivity and `≤ 1/2` at both ends of each piece. -/
theorem ends_ok : ∀ n ∈ Icc 1 15, 0 ≤ al n ∧ 0 ≤ al n + be n / n ∧ 0 ≤ al n + be n / (n + 1) ∧
    al n + be n / n ≤ 1 / 2 ∧ al n + be n / (n + 1) ≤ 1 / 2 := by decide +kernel

theorem between {α β p q x : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    α + β / x ≤ max (α + β / p) (α + β / q) ∧ min (α + β / p) (α + β / q) ≤ α + β / x := by
  have hx : 0 < x := hp.trans_le hpx
  rcases le_total 0 β with hβ | hβ
  · have h1 : β / x ≤ β / p := div_le_div_of_nonneg_left hβ hp hpx
    have h2 : β / q ≤ β / x := div_le_div_of_nonneg_left hβ hx hxq
    exact ⟨le_max_of_le_left (by linarith), min_le_of_right_le (by linarith)⟩
  · have h1 : (-β) / x ≤ (-β) / p := div_le_div_of_nonneg_left (by linarith) hp hpx
    have h2 : (-β) / q ≤ (-β) / x := div_le_div_of_nonneg_left (by linarith) hx hxq
    rw [neg_div, neg_div] at h1 h2
    exact ⟨le_max_of_le_right (by linarith), min_le_of_left_le (by linarith)⟩

theorem piece_bounds {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 15) {S : ℝ} (h1 : (n : ℝ) ≤ S)
    (h2 : S ≤ n + 1) : 0 ≤ (al n : ℝ) + be n / S ∧ (al n : ℝ) + be n / S ≤ 1 / 2 := by
  obtain ⟨-, p1, p2, q1, q2⟩ := ends_ok n (mem_Icc.2 ⟨hn1, hn⟩)
  have hb := between (α := (al n : ℝ)) (β := be n) (by exact_mod_cast hn1 : (0 : ℝ) < n) h1 h2
  have e1 := (Rat.cast_le (K := ℝ)).2 p1
  have e2 := (Rat.cast_le (K := ℝ)).2 p2
  have f1 := (Rat.cast_le (K := ℝ)).2 q1
  have f2 := (Rat.cast_le (K := ℝ)).2 q2
  push_cast at e1 e2 f1 f2
  exact ⟨(le_min e1 e2).trans hb.2, hb.1.trans (max_le f1 f2)⟩

theorem H2_piece {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 15) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S < n + 1) :
    H2 S = 4 / π ^ 2 * ((al n : ℝ) + be n / S) := by
  have hS16 : S < 16 := by have : (n : ℝ) ≤ 15 := by exact_mod_cast hn
                           linarith
  unfold H2
  rw [if_pos hS16, T2_eq' hn1 hn h1 h2, max_eq_left (piece_bounds hn1 hn h1 h2.le).1]

end H2B

open H2B in
/-- **[H, (5.37)]**: `H₂(S) ≤ 2/π²`, i.e. `T₂(S) ≤ 1/2` on `[1, 16)` (kernel-checked). -/
theorem H2_le (S : ℝ) : H2 S ≤ 2 / π ^ 2 := by
  have hpi : 0 < π ^ 2 := by positivity
  rcases lt_or_ge S 1 with hS | hS
  · rw [H2_eq_zero_of_lt_one hS]; positivity
  rcases lt_or_ge S 16 with h16 | h16
  · have hn1 : 1 ≤ ⌊S⌋₊ := Nat.le_floor (by exact_mod_cast hS)
    have hn15 : ⌊S⌋₊ ≤ 15 := Nat.le_of_lt_succ ((Nat.floor_lt (by linarith)).2 (by norm_num; linarith))
    have h1 : (⌊S⌋₊ : ℝ) ≤ S := Nat.floor_le (by linarith)
    have h2 : S < ⌊S⌋₊ + 1 := Nat.lt_floor_add_one S
    rw [H2_piece hn1 hn15 h1 h2]
    have := (piece_bounds hn1 hn15 h1 h2.le).2
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]; linarith
  · unfold H2; rw [if_neg (not_lt.2 h16)]
    have := Real.pi_lt_d2
    rw [le_div_iff₀ hpi]; nlinarith [Real.pi_pos]

/-- `S ↦ H₂(S)/S` is interval integrable on every interval (`H₂` is measurable, `0 ≤ H₂ ≤ 2/π²`,
`H₂ = 0` on `(-∞, 1)`). -/
theorem intervalIntegrable_H2_div' (a b : ℝ) :
    IntervalIntegrable (fun S => H2 S / S) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    ((measurable_H2.div measurable_id).aestronglyMeasurable) (2 / π ^ 2) ?_
  refine Filter.Eventually.of_forall fun S => ?_
  rw [Real.norm_eq_abs]
  rcases lt_or_ge S 1 with hS | hS
  · rw [H2_eq_zero_of_lt_one hS, zero_div, abs_zero]; positivity
  · rw [abs_div, abs_of_nonneg (H2_nonneg S), abs_of_pos (by linarith)]
    calc H2 S / S ≤ H2 S / 1 := div_le_div_of_nonneg_left (H2_nonneg S) one_pos hS
      _ = H2 S := div_one _
      _ ≤ _ := H2_le S

theorem intervalIntegrable_H2_div (T : ℝ) :
    IntervalIntegrable (fun S => H2 S / S) MeasureTheory.volume 1 T :=
  intervalIntegrable_H2_div' 1 T

namespace H2B

/-! ### The integral on each piece -/

theorem integral_piece {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 15) {a b : ℝ} (ha : (n : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ n + 1) :
    ∫ S in a..b, H2 S / S =
      4 / π ^ 2 * ((al n : ℝ) * Real.log (b / a) + be n * (1 / a - 1 / b)) := by
  set k := 4 / π ^ 2
  set α : ℝ := (al n : ℝ)
  set β : ℝ := (be n : ℝ)
  have ha0 : 0 < a := lt_of_lt_of_le (by exact_mod_cast hn1) ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hcongr : ∫ S in a..b, H2 S / S = ∫ S in a..b, k * (α + β / S) / S := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun S hS => ?_
    rw [H2_piece hn1 hn (ha.trans hS.1.le) (lt_of_lt_of_le hS.2 hb)]
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun S => k * (α * Real.log S - β * S⁻¹))
      (k * (α + β / x) / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    have h1 := (((Real.hasDerivAt_log hx0.ne').const_mul α).sub
      ((hasDerivAt_inv hx0.ne').const_mul β)).const_mul k
    convert h1 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun S => k * (α + β / S) / S) volume a b := by
    refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (ha0.trans_le hx.1).ne'
    fun_prop (disch := exact hx0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.log_div hb0.ne' ha0.ne']
  ring

theorem integral_ge16 {a b : ℝ} (ha : 16 ≤ a) (hab : a ≤ b) :
    ∫ S in a..b, H2 S / S = 0.15107 * Real.log (b / a) := by
  have ha0 : 0 < a := by linarith
  rw [intervalIntegral.integral_congr (g := fun S => 0.15107 * S⁻¹) (fun S hS => ?_)]
  · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 (by linarith)]
  · rw [Set.uIcc_of_le hab] at hS
    simp only
    unfold H2; rw [if_neg (by linarith [hS.1]), div_eq_mul_inv]

/-- `∫ₙⁿ⁺¹ H₂/S` for an integer `n`. -/
noncomputable def P (j : ℕ) : ℝ :=
  4 / π ^ 2 * ((al j : ℝ) * Real.log (((j : ℝ) + 1) / j) + be j * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)))

theorem integral_int : ∀ m : ℕ, 1 ≤ m → m ≤ 16 →
    ∫ S in (1 : ℝ)..m, H2 S / S = ∑ i ∈ range (m - 1), P (i + 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => by simp
  | m + 2, _, hm => by
    have ih := integral_int (m + 1) (by omega) (by omega)
    rw [show m + 1 - 1 = m by omega] at ih
    rw [show m + 2 - 1 = m + 1 by omega, sum_range_succ, ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_H2_div' 1 (m + 1 : ℕ))
        (intervalIntegrable_H2_div' ((m + 1 : ℕ) : ℝ) ((m + 2 : ℕ) : ℝ))]
    congr 1
    have e : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e, integral_piece (n := m + 1) (by omega) (by omega) le_rfl (by linarith) le_rfl, P]

/-! ### Rational data: `log j` and `k = 4/π²` -/

def loN : List ℕ := [0, 0, 693147177, 1098612285, 1386294358, 1609437909, 1791759466, 1945910146, 2079441538, 2197224574, 2302585089, 2397895269, 2484906646, 2564949354, 2639057326, 2708050198, 2772588719]
def hiN : List ℕ := [0, 1, 693147184, 1098612292, 1386294365, 1609437916, 1791759473, 1945910153, 2079441545, 2197224581, 2302585096, 2397895276, 2484906653, 2564949361, 2639057333, 2708050205, 2772588726]

theorem lo_ok : ∀ j ∈ Icc 1 16, Small.chkLow (loN.getD j 0) (10 ^ 9) j = true := by decide +kernel
theorem hi_ok : ∀ j ∈ Icc 1 16, Small.chkStep (hiN.getD j 0) (10 ^ 9) 1 j = true := by decide +kernel

def loQ (j : ℕ) : ℚ := (loN.getD j 0 : ℚ) / 10 ^ 9
def hiQ (j : ℕ) : ℚ := (hiN.getD j 0 : ℚ) / 10 ^ 9

theorem log_lo {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 16) : (loQ j : ℝ) ≤ Real.log j := by
  have := Small.le_log_of_chk (by norm_num) (by omega) (lo_ok j (mem_Icc.2 ⟨h1, h2⟩))
  have e : ((loQ j : ℚ) : ℝ) = ((loN.getD j 0 : ℕ) : ℝ) / ((10 ^ 9 : ℕ) : ℝ) := by
    unfold loQ; push_cast; ring
  rw [e]; exact this

theorem log_hi {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 16) : Real.log j < (hiQ j : ℝ) := by
  have := Small.log_lt_of_chk (by norm_num) (by omega) (hi_ok j (mem_Icc.2 ⟨h1, h2⟩))
  rw [Nat.cast_one, mul_one] at this
  have e : ((hiQ j : ℚ) : ℝ) = ((hiN.getD j 0 : ℕ) : ℝ) / ((10 ^ 9 : ℕ) : ℝ) := by
    unfold hiQ; push_cast; ring
  rw [e]; exact this

def kHi : ℚ := 4 / (314159265358979323846 / 10 ^ 20) ^ 2
def kLo : ℚ := 4 / (314159265358979323847 / 10 ^ 20) ^ 2
def c0 : ℚ := 15107 / 100000

theorem k_hi : 4 / π ^ 2 ≤ (kHi : ℝ) := by
  have h : (314159265358979323846 / 10 ^ 20 : ℝ) < π := by
    have := Real.pi_gt_d20; norm_num at this ⊢; linarith
  unfold kHi; push_cast
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by norm_num) h.le 2)

theorem k_lo : (kLo : ℝ) ≤ 4 / π ^ 2 := by
  have h : π < (314159265358979323847 / 10 ^ 20 : ℝ) := by
    have := Real.pi_lt_d20; norm_num at this ⊢; linarith
  unfold kLo; push_cast
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_left₀ Real.pi_pos.le h.le 2)

theorem c0_eq : ((c0 : ℚ) : ℝ) = 0.15107 := by unfold c0; push_cast; norm_num

/-- Upper bound for `P j / k`. -/
def Pu (j : ℕ) : ℚ := al j * (hiQ (j + 1) - loQ j) + be j * (1 / j - 1 / (j + 1))
def PU (m : ℕ) : ℚ := ∑ i ∈ range (m - 1), Pu (i + 1)

/-- The extra term on `[15, 16]`. -/
def E15 : ℚ := max 0 (kHi * (al 15 + be 15 / 15) - c0) / 16

theorem E15_nonneg : 0 ≤ E15 := div_nonneg (le_max_left _ _) (by norm_num)

/-- **The rational checks.** -/
theorem D_ok : ∀ m ∈ Icc 3 16, 0 ≤ PU m ∧
    kHi * PU m - c0 * loQ m + (if m = 15 then E15 else 0) ≤ 231 / 10000 := by decide +kernel

theorem mono_ok : ∀ n ∈ Icc 2 14, 0 ≤ be n ∧ c0 ≤ kLo * (al n + be n / (n + 1)) := by
  decide +kernel

theorem misc_ok : al 1 = 1 ∧ be 1 = -1 ∧ kHi * al 15 ≤ c0 ∧ kHi / 3 < c0 ∧
    kHi / 3 - 5 * c0 / 6 ≤ 231 / 10000 ∧ 2 * c0 ≤ kLo := by decide +kernel

/-! ### Assembling -/

theorem P_le {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 15) : P j ≤ 4 / π ^ 2 * (Pu j : ℝ) := by
  have hk : 0 < 4 / π ^ 2 := by positivity
  have ha : (0 : ℝ) ≤ al j := by exact_mod_cast (ends_ok j (mem_Icc.2 ⟨h1, h2⟩)).1
  have hj : (0 : ℝ) < j := by exact_mod_cast h1
  have hL : Real.log (((j : ℝ) + 1) / j) ≤ (hiQ (j + 1) : ℝ) - loQ j := by
    rw [Real.log_div (by positivity) hj.ne']
    have := log_hi (j := j + 1) (by omega) (by omega)
    have := log_lo h1 (by omega)
    push_cast at *; linarith
  unfold P Pu
  apply mul_le_mul_of_nonneg_left _ hk.le
  push_cast
  have := mul_le_mul_of_nonneg_left hL ha
  linarith

theorem D_le {m : ℕ} (h3 : 3 ≤ m) (h16 : m ≤ 16) :
    (∫ S in (1 : ℝ)..m, H2 S / S) - 0.15107 * Real.log m ≤
      (kHi * PU m - c0 * loQ m : ℚ) := by
  obtain ⟨hPU, -⟩ := D_ok m (mem_Icc.2 ⟨h3, h16⟩)
  rw [integral_int m (by omega) h16]
  have hsum : ∑ i ∈ range (m - 1), P (i + 1) ≤ 4 / π ^ 2 * (PU m : ℝ) := by
    unfold PU; push_cast; rw [mul_sum]
    exact sum_le_sum fun i hi => P_le (by omega) (by have := mem_range.1 hi; omega)
  have hk := mul_le_mul_of_nonneg_right k_hi (by exact_mod_cast hPU : (0 : ℝ) ≤ PU m)
  have hl := log_lo (j := m) (by omega) h16
  have hc : (0.15107 : ℝ) * (loQ m : ℝ) ≤ 0.15107 * Real.log m := by nlinarith
  push_cast
  rw [c0_eq]
  linarith

end H2B

open H2B in
/-- **[H, (5.36)], corrected**: `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T + 0.0231` for `T ≥ 1`.

[H, (5.36)] states this without the `+ 0.0231`. That is false: it inherits an error in [H, (5.32)]
for `v = 2`, where `∫₁⁴ T₂(S)/S dS = 0.53344 > 0.37273 log 4` (see `HYPOTHESES.md`). The supremum of
`∫₁ᵀ H₂/S − 0.15107 log T` is `0.023059…`, at `T ≈ 15.58`. -/
theorem integral_H2_le {T : ℝ} (hT : 1 ≤ T) :
    ∫ S in (1 : ℝ)..T, H2 S / S ≤ 0.15107 * Real.log T + 0.0231 := by
  obtain ⟨ma1, mb1, m15, mk3, mk5, mk2⟩ := misc_ok
  have kh := k_hi
  have kl := k_lo
  have hk0 : 0 < 4 / π ^ 2 := by positivity
  have hc : ((c0 : ℚ) : ℝ) = 0.15107 := c0_eq
  have hT0 : 0 < T := by linarith
  have hD : ∀ m : ℕ, 3 ≤ m → m ≤ 16 →
      (∫ S in (1 : ℝ)..m, H2 S / S) - 0.15107 * Real.log m + (if m = 15 then (E15 : ℝ) else 0) ≤
        0.0231 := by
    intro m h3 h16
    have h1 := D_le h3 h16
    have h2 := (D_ok m (mem_Icc.2 ⟨h3, h16⟩)).2
    have h2' : ((kHi * PU m - c0 * loQ m + (if m = 15 then E15 else 0) : ℚ) : ℝ) ≤
        ((231 / 10000 : ℚ) : ℝ) := by exact_mod_cast h2
    split_ifs at h2' ⊢ <;> push_cast at h1 h2' ⊢ <;> linarith
  rcases le_or_gt T 2 with hT2 | hT2
  · -- `[1, 2]`: `T₂ = 1 − 1/S`
    rw [integral_piece (n := 1) le_rfl (by norm_num) (by norm_num) hT (by norm_num; linarith)]
    rw [ma1, mb1, div_one]
    push_cast
    set k := 4 / π ^ 2
    have hkc : k / 3 < 0.15107 := by
      have : ((kHi / 3 : ℚ) : ℝ) < ((c0 : ℚ) : ℝ) := by exact_mod_cast mk3
      push_cast at this; rw [hc] at this; linarith
    have hk2 : k / 3 - 5 * 0.15107 / 6 ≤ (0.0231 : ℝ) := by
      have : ((kHi / 3 - 5 * c0 / 6 : ℚ) : ℝ) ≤ ((231 / 10000 : ℚ) : ℝ) := by exact_mod_cast mk5
      push_cast at this; rw [hc] at this; linarith
    have hlog := Real.log_le_sub_one_of_pos hT0
    have hk2c : 2 * 0.15107 ≤ k := by
      have : ((2 * c0 : ℚ) : ℝ) ≤ ((kLo : ℚ) : ℝ) := by exact_mod_cast mk2
      push_cast at this; rw [hc] at this; linarith
    have hkc' : 0.15107 ≤ k := by linarith
    rcases le_or_gt T (3 / 2) with h32 | h32
    · -- `(k − c) log T − k (1 − 1/T) ≤ (T − 1)(k/3 − c) ≤ 0`
      have hinv : (2 / 3 : ℝ) ≤ 1 / T := by rw [le_div_iff₀ hT0]; linarith
      have e1 : k * ((T - 1) * (2 / 3)) ≤ k * (1 - 1 / T) := by
        have h' : (T - 1) * (2 / 3) ≤ (T - 1) * (1 / T) :=
          mul_le_mul_of_nonneg_left hinv (by linarith)
        have e : 1 - 1 / T = (T - 1) * (1 / T) := by field_simp
        rw [e]; exact mul_le_mul_of_nonneg_left h' hk0.le
      have e2 : (k - 0.15107) * Real.log T ≤ (k - 0.15107) * (T - 1) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      nlinarith
    · -- `log T ≤ 2T/3 − 1/2` and `1/T ≤ 7/6 − T/3`
      have hl : Real.log T ≤ 2 * T / 3 - 1 / 2 := by
        have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * T / 3 by positivity)
        have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
        have e : Real.log T = Real.log (3 / 2) + Real.log (2 * T / 3) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
        linarith
      have hi : 1 / T ≤ 7 / 6 - T / 3 := by
        rw [div_le_iff₀ hT0]; nlinarith
      have e2 : (k - 0.15107) * Real.log T ≤ (k - 0.15107) * (2 * T / 3 - 1 / 2) :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      have e3 : k * (1 / T) ≤ k * (7 / 6 - T / 3) := mul_le_mul_of_nonneg_left hi hk0.le
      have e4 : (k - 2 * 0.15107) * T ≤ (k - 2 * 0.15107) * 2 :=
        mul_le_mul_of_nonneg_left hT2 (by linarith)
      nlinarith
  rcases lt_or_ge T 16 with hT16 | hT16
  · obtain ⟨n, hn⟩ : ∃ n, ⌊T⌋₊ = n := ⟨_, rfl⟩
    have hn2 : 2 ≤ n := by rw [← hn]; exact Nat.le_floor (by exact_mod_cast hT2.le)
    have hn15 : n ≤ 15 := by
      rw [← hn]; exact Nat.le_of_lt_succ ((Nat.floor_lt hT0.le).2 (by norm_num; linarith))
    have h1 : (n : ℝ) ≤ T := by rw [← hn]; exact Nat.floor_le hT0.le
    have h2 : T < n + 1 := by rw [← hn]; exact Nat.lt_floor_add_one T
    rcases lt_or_eq_of_le hn15 with hn14 | hn15'
    · -- `[n, n+1]`, `2 ≤ n ≤ 14`: `H₂ ≥ 0.15107`, so `d(T) ≤ d(n+1)`
      have hn14' : n ≤ 14 := by omega
      obtain ⟨hb0, hmono⟩ := mono_ok n (mem_Icc.2 ⟨hn2, hn14'⟩)
      have hD1 : (∫ S in (1 : ℝ)..((n + 1 : ℕ) : ℝ), H2 S / S) -
          0.15107 * Real.log ((n + 1 : ℕ) : ℝ) ≤ 0.0231 := by
        have h := hD (n + 1) (by omega) (by omega)
        have hE : (0 : ℝ) ≤ (E15 : ℝ) := Rat.cast_nonneg.2 E15_nonneg
        split_ifs at h <;> linarith
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_H2_div' 1 T) (intervalIntegrable_H2_div' T ((n + 1 : ℕ) : ℝ))
      have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [e, integral_piece (by omega) (by omega) h1 h2.le le_rfl] at hsplit
      rw [e] at hD1
      set k := 4 / π ^ 2
      set α : ℝ := (al n : ℝ)
      set β : ℝ := (be n : ℝ)
      have hβ : (0 : ℝ) ≤ β := Rat.cast_nonneg.2 hb0
      have hpos : (0 : ℝ) ≤ α + β / (n + 1) :=
        (piece_bounds (n := n) (by omega) hn15 (S := n + 1) (by linarith) le_rfl).1
      have hcm : (0.15107 : ℝ) ≤ k * (α + β / (n + 1)) := by
        have h := mono_ok n (mem_Icc.2 ⟨hn2, hn14'⟩)
        have : ((c0 : ℚ) : ℝ) ≤ ((kLo * (al n + be n / (n + 1)) : ℚ) : ℝ) := by exact_mod_cast hmono
        push_cast at this; rw [hc] at this
        exact this.trans (mul_le_mul_of_nonneg_right kl hpos)
      have hn0 : (0 : ℝ) < n + 1 := by positivity
      have hx := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) / T by positivity)
      have hL0 : 0 ≤ Real.log ((n + 1) / T) :=
        Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
      have hlogs : Real.log ((n + 1 : ℝ)) = Real.log T + Real.log ((n + 1) / T) := by
        rw [← Real.log_mul hT0.ne' (by positivity)]; congr 1; field_simp
      have hw : 1 / T - 1 / ((n : ℝ) + 1) = ((n + 1) / T - 1) / (n + 1) := by field_simp
      -- `c L ≤ k α L + k β L/(n+1) ≤ k α L + k β ((n+1)/T − 1)/(n+1)`
      have s1 : 0.15107 * Real.log ((n + 1) / T) ≤
          k * (α + β / (n + 1)) * Real.log ((n + 1) / T) := mul_le_mul_of_nonneg_right hcm hL0
      have s2 : β / (n + 1) * Real.log ((n + 1) / T) ≤ β / (n + 1) * ((n + 1) / T - 1) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      have s3 : k * (β / (n + 1) * Real.log ((n + 1) / T)) ≤ k * (β / (n + 1) * ((n + 1) / T - 1)) :=
        mul_le_mul_of_nonneg_left s2 hk0.le
      rw [hw] at hsplit
      rw [hlogs] at hD1
      have : β * (((n + 1) / T - 1) / (n + 1)) = β / (n + 1) * ((n + 1) / T - 1) := by ring
      rw [this] at hsplit
      nlinarith
    · -- `[15, 16]`: `log(T/15) ≥ 1 − 15/T`
      rw [hn15'] at h1 h2
      push_cast at h1 h2
      have hD15 := hD 15 (by norm_num) (by norm_num)
      rw [if_pos rfl] at hD15
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_H2_div' 1 ((15 : ℕ) : ℝ)) (intervalIntegrable_H2_div' ((15 : ℕ) : ℝ) T)
      rw [integral_piece (n := 15) (by norm_num) le_rfl le_rfl h1 (by push_cast; linarith)] at hsplit
      push_cast at hsplit hD15
      set k := 4 / π ^ 2
      set α : ℝ := (al 15 : ℝ)
      set β : ℝ := (be 15 : ℝ)
      have hw0 : 0 ≤ 1 - 15 / T := by rw [sub_nonneg, div_le_one hT0]; linarith
      have hw1 : 1 - 15 / T ≤ 1 / 16 := by
        rw [sub_le_comm, le_div_iff₀ hT0]; linarith
      have hL : 1 - (T / 15)⁻¹ ≤ Real.log (T / 15) := Real.one_sub_inv_le_log_of_pos (by positivity)
      rw [inv_div] at hL
      have hkα : k * α ≤ 0.15107 := by
        have : ((kHi * al 15 : ℚ) : ℝ) ≤ ((c0 : ℚ) : ℝ) := by exact_mod_cast m15
        push_cast at this; rw [hc] at this
        have hα : (0 : ℝ) ≤ α := Rat.cast_nonneg.2 (ends_ok 15 (mem_Icc.2 ⟨by norm_num, le_rfl⟩)).1
        exact (mul_le_mul_of_nonneg_right kh hα).trans this
      have hpos : (0 : ℝ) ≤ α + β / 15 := by
        have := (piece_bounds (n := 15) (by norm_num) le_rfl (S := 15) (by norm_num) (by norm_num)).1
        push_cast at this; exact this
      have hE : (k * (α + β / 15) - 0.15107) * (1 - 15 / T) ≤ (E15 : ℝ) := by
        have hm : k * (α + β / 15) - 0.15107 ≤ max 0 ((kHi : ℝ) * (α + β / 15) - 0.15107) :=
          le_max_of_le_right (by linarith [mul_le_mul_of_nonneg_right kh hpos])
        have hm0 : (0 : ℝ) ≤ max 0 ((kHi : ℝ) * (α + β / 15) - 0.15107) := le_max_left _ _
        have : (E15 : ℝ) = max 0 ((kHi : ℝ) * (α + β / 15) - 0.15107) / 16 := by
          unfold E15; push_cast; rw [hc]
        rw [this]
        calc (k * (α + β / 15) - 0.15107) * (1 - 15 / T)
            ≤ max 0 ((kHi : ℝ) * (α + β / 15) - 0.15107) * (1 - 15 / T) := by
              rcases le_total 0 (k * (α + β / 15) - 0.15107) with h | h
              · exact mul_le_mul_of_nonneg_right hm hw0
              · exact (mul_nonpos_of_nonpos_of_nonneg h hw0).trans (mul_nonneg hm0 hw0)
          _ ≤ max 0 ((kHi : ℝ) * (α + β / 15) - 0.15107) * (1 / 16) :=
              mul_le_mul_of_nonneg_left hw1 hm0
          _ = _ := by ring
      have hlogs : Real.log T = Real.log 15 + Real.log (T / 15) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
      have hw : 1 / (15 : ℝ) - 1 / T = (1 - 15 / T) / 15 := by field_simp
      rw [hw] at hsplit
      have s1 : (k * α - 0.15107) * Real.log (T / 15) ≤ (k * α - 0.15107) * (1 - 15 / T) :=
        mul_le_mul_of_nonpos_left hL (by linarith)
      rw [hlogs]
      nlinarith
  · -- `T ≥ 16`: `d` is constant
    have hD16 := hD 16 (by norm_num) le_rfl
    rw [if_neg (by norm_num), add_zero] at hD16
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_H2_div' 1 ((16 : ℕ) : ℝ)) (intervalIntegrable_H2_div' ((16 : ℕ) : ℝ) T)
    push_cast at hsplit hD16
    rw [integral_ge16 le_rfl hT16, Real.log_div hT0.ne' (by norm_num)] at hsplit
    rw [← hsplit]
    linarith

end TernaryGoldbach.MinorArcs
