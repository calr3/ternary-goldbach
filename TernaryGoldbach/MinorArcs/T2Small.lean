import TernaryGoldbach.MinorArcs.T2Basic
import TernaryGoldbach.MinorArcs.SmallG2

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# `T₂(S) ≤ 0.37273` for `16 ≤ S < 10⁴`, and `∫₁^{10⁴} g₂/y`, `∫₁^{10⁴} |g₂|`

From the kernel walk of `SmallG2.lean`:
* `|G̃(n) − D² g₂(n)| ≤ 2 D n³` (`abs_Gtil_sub_le`);
* for `16 ≤ n < 700` and `S ∈ [n, n+1)`, `T₂(S) = α_n + β_n/S` (`T2_eq_ac`) with
  `α_n = a(n) − a(⌊n/2⌋)/2`, `β_n = c(n) − c(⌊n/2⌋)`,
  `a(k) = ∑_{s ≤ k odd} g₂(⌊k/s⌋)/s`, `c(k) = ∑_{s ≤ k odd} (∑_{j < ⌊k/s⌋} g₂(j) − ⌊k/s⌋ g₂(⌊k/s⌋))`;
  `c(k) − c(k−1) = −∑_{t ∣ rad k} t (g₂(t) − g₂(t−1))` for odd `k` and `0` for even `k`, and
  `a(k) − a(k−1) = −(c(k) − c(k−1))/k`;
* for `700 ≤ n < 10⁴`, `T₂(S) ≤ ¼ ∫₁^S g₂/y + S⁻¹ ∫₁^S |g₂|` (`abs_T2_sub_le`) and the step function
  `g₂`.
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs.SmallG2

open TernaryGoldbach.MinorArcs

/-! ### `G̃` approximates `D² g₂` -/

/-- `A_d(n) = ∑_{r ≤ n, d ∣ r} f(r)`. -/
noncomputable def Ar (n d : ℕ) : ℝ := ∑ r ∈ (Icc 1 n).filter (d ∣ ·), fo r

theorem g2_nat (n : ℕ) : g2 n = ∑ d ∈ Icc 1 n, (μ d : ℝ) * Ar n d ^ 2 := by
  rw [g2_eq_sum_dvd, Nat.floor_natCast]; rfl

theorem abs_moebius_le' (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem abs_fo_le (r : ℕ) : |fo r| ≤ 1 := by
  unfold fo
  split_ifs
  · rcases Nat.eq_zero_or_pos (σ 1 r) with h | h
    · rw [h]; simp
    · have h1 : (1 : ℝ) ≤ σ 1 r := by exact_mod_cast h
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < σ 1 r)]
      exact (div_le_one (by linarith)).2 ((abs_moebius_le' r).trans h1)
  · simp

theorem DR : (D : ℝ) = 10 ^ 30 := by norm_num [D]

theorem abs_Fq_sub (r : ℕ) : |(Fq r : ℝ) - D * fo r| ≤ 1 := by
  unfold Fq fo
  by_cases ho : r % 2 = 1
  · have hodd : Odd r := Nat.odd_iff.2 ho
    rw [if_pos ho, if_pos hodd]
    have hs : 0 < σ 1 r := ArithmeticFunction.sigma_pos 1 r (by omega)
    have hs' : (0 : ℝ) < σ 1 r := by exact_mod_cast hs
    rw [Int.cast_mul, Int.cast_natCast]
    have e : (μ r : ℝ) * ((D / σ 1 r : ℕ) : ℝ) - D * ((μ r : ℝ) / σ 1 r) =
        (μ r : ℝ) * (((D / σ 1 r : ℕ) : ℝ) - D / σ 1 r) := by ring
    rw [e, abs_mul]
    have h1 : ((D / σ 1 r : ℕ) : ℝ) ≤ D / σ 1 r := Nat.cast_div_le
    have h2 : (D : ℝ) / σ 1 r < ((D / σ 1 r : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hs']
      have := Nat.lt_div_mul_add (a := D) hs
      have : (D : ℝ) < ((D / σ 1 r : ℕ) : ℝ) * σ 1 r + σ 1 r := by exact_mod_cast this
      linarith
    calc |(μ r : ℝ)| * |((D / σ 1 r : ℕ) : ℝ) - D / σ 1 r| ≤ 1 * 1 := by
          refine mul_le_mul (abs_moebius_le' r) ?_ (abs_nonneg _) zero_le_one
          rw [abs_le]; constructor <;> linarith
      _ = 1 := by ring
  · rw [if_neg ho, if_neg (by rw [Nat.odd_iff]; exact ho)]; simp

theorem abs_Fq_le (r : ℕ) : |(Fq r : ℝ)| ≤ D := by
  unfold Fq
  split_ifs
  · rw [Int.cast_mul, Int.cast_natCast, abs_mul]
    have h1 : ((D / σ 1 r : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.div_le_self D (σ 1 r)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ ((D / σ 1 r : ℕ) : ℝ) from Nat.cast_nonneg _)]
    calc |(μ r : ℝ)| * ((D / σ 1 r : ℕ) : ℝ) ≤ 1 * D :=
          mul_le_mul (abs_moebius_le' r) h1 (Nat.cast_nonneg _) zero_le_one
      _ = D := one_mul _
  · simp

theorem card_filter_dvd_le (n d : ℕ) : (((Icc 1 n).filter (d ∣ ·)).card : ℝ) ≤ n := by
  have := card_filter_le (Icc 1 n) (d ∣ ·)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  exact_mod_cast this

/-- **`|G̃(n) − D² g₂(n)| ≤ 2 D n³`**. -/
theorem abs_Gtil_sub_le (n : ℕ) : |(Gtil n : ℝ) - (D : ℝ) ^ 2 * g2 n| ≤ 2 * D * n ^ 3 := by
  have hD : (0 : ℝ) ≤ D := by positivity
  rw [g2_nat, Gtil, mul_sum]
  push_cast
  rw [← sum_sub_distrib]
  have hterm : ∀ d ∈ Icc 1 n, |(μ d : ℝ) * (Atil n d : ℝ) ^ 2 - (D : ℝ) ^ 2 * ((μ d : ℝ) * Ar n d ^ 2)|
      ≤ 2 * D * n ^ 2 := by
    intro d _
    have hc := card_filter_dvd_le n d
    have e1 : (Atil n d : ℝ) - D * Ar n d =
        ∑ r ∈ (Icc 1 n).filter (d ∣ ·), ((Fq r : ℝ) - D * fo r) := by
      unfold Atil Ar; push_cast; rw [mul_sum, ← sum_sub_distrib]
    have b1 : |(Atil n d : ℝ) - D * Ar n d| ≤ n := by
      rw [e1]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun r _ => abs_Fq_sub r).trans ?_)
      simpa using hc
    have b2 : |(Atil n d : ℝ)| ≤ n * D := by
      unfold Atil; push_cast
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun r _ => abs_Fq_le r).trans ?_)
      rw [sum_const, nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc hD
    have b3 : |(D : ℝ) * Ar n d| ≤ n * D := by
      unfold Ar
      rw [abs_mul, abs_of_nonneg hD, mul_comm]
      refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
        ((sum_le_sum fun r _ => abs_fo_le r).trans ?_)) hD
      simpa using hc
    have e2 : (μ d : ℝ) * (Atil n d : ℝ) ^ 2 - (D : ℝ) ^ 2 * ((μ d : ℝ) * Ar n d ^ 2) =
        (μ d : ℝ) * (((Atil n d : ℝ) - D * Ar n d) * ((Atil n d : ℝ) + D * Ar n d)) := by ring
    rw [e2, abs_mul, abs_mul]
    have b4 : |(Atil n d : ℝ) + D * Ar n d| ≤ 2 * n * D :=
      (abs_add_le _ _).trans (by linarith)
    calc |(μ d : ℝ)| * (|(Atil n d : ℝ) - D * Ar n d| * |(Atil n d : ℝ) + D * Ar n d|)
        ≤ 1 * (n * (2 * n * D)) := by
          refine mul_le_mul (abs_moebius_le' d) (mul_le_mul b1 b4 (abs_nonneg _) (by positivity))
            (by positivity) zero_le_one
      _ = 2 * D * n ^ 2 := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]; ring

/-! ### `g₂` as a step function -/

theorem g2_eq_of_mem {j : ℕ} {y : ℝ} (h1 : (j : ℝ) ≤ y) (h2 : y < j + 1) : g2 y = g2 j := by
  have h0 : (0 : ℝ) ≤ y := le_trans (Nat.cast_nonneg j) h1
  have : ⌊y⌋₊ = j := (Nat.floor_eq_iff h0).2 ⟨h1, h2⟩
  unfold g2; rw [this, Nat.floor_natCast]

theorem integral_step {j : ℕ} {a b : ℝ} (ha : (j : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ j + 1)
    (F : ℝ → ℝ → ℝ) : ∫ y in a..b, F (g2 y) y = ∫ y in a..b, F (g2 j) y := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ (j + 1 : ℝ) := by
    rw [ae_iff]; simp [measure_singleton]
  filter_upwards [hne] with y hy hmem
  rw [Set.uIoc_of_le hab] at hmem
  rw [g2_eq_of_mem (by linarith [hmem.1]) (lt_of_le_of_ne (hmem.2.trans hb) hy)]

theorem intervalIntegrable_g2 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable g2 volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact integrableOn_g2_Ioc a b (ha.trans hab)

theorem intervalIntegrable_g2_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => g2 y / y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Integrable.mul_bdd (integrableOn_g2_Ioc a b (by linarith))
    (by fun_prop : Measurable fun y : ℝ => y⁻¹).aestronglyMeasurable (c := 1)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => by
      have : 1 < y := lt_of_le_of_lt ha hy.1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ this.le))
    |>.congr (Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv])

theorem intervalIntegrable_abs_g2 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => |g2 y|) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_g2_Ioc a b (ha.trans hab)).abs

/-- `∫_j^b g₂/y = g₂(j) log(b/j)` for `j ≤ b ≤ j + 1`. -/
theorem integral_g2_div_step {j : ℕ} (hj : 1 ≤ j) {b : ℝ} (hb1 : (j : ℝ) ≤ b) (hb2 : b ≤ j + 1) :
    ∫ y in (j : ℝ)..b, g2 y / y = g2 j * Real.log (b / j) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [integral_step le_rfl hb1 hb2 (fun g y => g / y)]
  have e : ∀ y : ℝ, g2 j / y = g2 j * y⁻¹ := fun y => div_eq_mul_inv _ _
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hj0 (by linarith)]

/-- `∫_j^b |g₂| = |g₂(j)| (b − j)` for `j ≤ b ≤ j + 1`. -/
theorem integral_abs_g2_step {j : ℕ} {b : ℝ} (hb1 : (j : ℝ) ≤ b) (hb2 : b ≤ j + 1) :
    ∫ y in (j : ℝ)..b, |g2 y| = |g2 j| * (b - j) := by
  rw [integral_step le_rfl hb1 hb2 (fun g _ => |g|)]
  simp [mul_comm]

/-! ### `I`, `J` at integers and between them -/

/-- `I(n) = ∑_{1 ≤ m < n} g₂(m) log(1 + 1/m)`. -/
noncomputable def Ire (n : ℕ) : ℝ := ∑ m ∈ Ico 1 n, g2 m * Real.log (1 + 1 / m)

/-- `J(n) = ∑_{1 ≤ m < n} |g₂(m)|`. -/
noncomputable def Jre (n : ℕ) : ℝ := ∑ m ∈ Ico 1 n, |g2 m|

theorem log_div_nat {n : ℕ} (hn : 1 ≤ n) : Real.log (((n + 1 : ℕ) : ℝ) / n) = Real.log (1 + 1 / n) := by
  have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith
  congr 1; push_cast; field_simp

theorem integral_g2_div_nat : ∀ n : ℕ, 1 ≤ n → ∫ y in (1 : ℝ)..n, g2 y / y = Ire n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [Ire]
  | succ n hn ih =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
      (intervalIntegrable_g2_div le_rfl hn') (intervalIntegrable_g2_div hn' (by push_cast; linarith)),
      ih, integral_g2_div_step hn (by push_cast; linarith) (by push_cast; linarith), Ire, Ire,
      sum_Ico_succ_top hn, log_div_nat hn]

theorem integral_abs_g2_nat : ∀ n : ℕ, 1 ≤ n → ∫ y in (1 : ℝ)..n, |g2 y| = Jre n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [Jre]
  | succ n hn ih =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
      (intervalIntegrable_abs_g2 zero_le_one hn') (intervalIntegrable_abs_g2 (by linarith)
        (by push_cast; linarith)),
      ih, integral_abs_g2_step (by push_cast; linarith) (by push_cast; linarith), Jre, Jre,
      sum_Ico_succ_top hn]
    push_cast; ring

theorem I_le_max {n : ℕ} (hn : 1 ≤ n) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S ≤ n + 1) :
    ∫ y in (1 : ℝ)..S, g2 y / y ≤ max (Ire n) (Ire (n + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
    (intervalIntegrable_g2_div le_rfl hn') (intervalIntegrable_g2_div hn' h1),
    integral_g2_div_nat n hn, integral_g2_div_step hn h1 h2]
  have hl0 : 0 ≤ Real.log (S / n) := Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
  have hl1 : Real.log (S / n) ≤ Real.log (1 + 1 / n) := by
    refine Real.log_le_log (div_pos (by linarith) hn0) ?_
    rw [div_le_iff₀ hn0]; field_simp; linarith
  have e : Ire (n + 1) = Ire n + g2 n * Real.log (1 + 1 / n) := by
    rw [Ire, Ire, sum_Ico_succ_top hn]
  rcases le_or_gt 0 (g2 n) with hg | hg
  · exact le_trans (by rw [e]; nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

theorem J_div_le_max {n : ℕ} (hn : 1 ≤ n) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S ≤ n + 1) :
    S⁻¹ * ∫ y in (1 : ℝ)..S, |g2 y| ≤ max (Jre n / n) (Jre (n + 1) / (n + 1 : ℕ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hS0 : 0 < S := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
    (intervalIntegrable_abs_g2 zero_le_one hn') (intervalIntegrable_abs_g2 (by linarith) h1),
    integral_abs_g2_nat n hn, integral_abs_g2_step h1 h2]
  have e : Jre (n + 1) = Jre n + |g2 n| := by rw [Jre, Jre, sum_Ico_succ_top hn]
  rw [e]
  set J := Jre n
  set g := |g2 n|
  have hg : 0 ≤ g := abs_nonneg _
  push_cast
  rcases le_or_gt (g * n) J with hJ | hJ
  · -- decreasing in `S`
    refine le_trans ?_ (le_max_left _ _)
    rw [inv_mul_eq_div, div_le_div_iff₀ hS0 hn0]
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    rw [inv_mul_eq_div, div_le_div_iff₀ hS0 (by linarith)]
    nlinarith

theorem sum_cube_le {n : ℕ} (hn : n ≤ XX) :
    ∑ _m ∈ Ico 1 n, 2 * (D : ℝ) * (n : ℝ) ^ 3 ≤ (2 * (D : ℝ) * 10 ^ 16 : ℝ) := by
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hn10 : n ≤ 10000 := hn
  have hn' : (n : ℝ) ≤ 10000 := by exact_mod_cast hn10
  have h1 : ((n - 1 : ℕ) : ℝ) ≤ 10000 := by exact_mod_cast (Nat.sub_le n 1).trans hn10
  have hD : (0 : ℝ) ≤ D := by positivity
  have h3 : (n : ℝ) ^ 3 ≤ 10000 ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 3
  calc ((n - 1 : ℕ) : ℝ) * (2 * (D : ℝ) * (n : ℝ) ^ 3) ≤ 10000 * (2 * (D : ℝ) * 10000 ^ 3) := by
        gcongr
    _ = 2 * (D : ℝ) * 10 ^ 16 := by ring

theorem Ire_le {n : ℕ} (hn : n ≤ XX) : (D : ℝ) ^ 2 * Ire n ≤ Isp n + 2 * (D : ℝ) * 10 ^ 16 := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have hsum : (D : ℝ) ^ 2 * Ire n - Isp n ≤ ∑ _m ∈ Ico 1 n, 2 * (D : ℝ) * (n : ℝ) ^ 3 := by
    rw [Ire, Isp, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := mem_Ico.1 hm
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hm0 : 0 ≤ 1 / (m : ℝ) := by positivity
    have hl0 : 0 ≤ Real.log (1 + 1 / m) := Real.log_nonneg (by linarith)
    have hl1 : Real.log (1 + 1 / m) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / m by positivity)
      have : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm1'
      linarith
    have hG := abs_Gtil_sub_le m
    have hm3 : (m : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hm2.le) 3
    have e : (D : ℝ) ^ 2 * (g2 m * Real.log (1 + 1 / m)) - (Gtil m : ℝ) * Real.log (1 + 1 / m) =
        ((D : ℝ) ^ 2 * g2 m - Gtil m) * Real.log (1 + 1 / m) := by ring
    rw [e]
    have h1 : (D : ℝ) ^ 2 * g2 m - Gtil m ≤ 2 * (D : ℝ) * (m : ℝ) ^ 3 := by
      have := neg_abs_le ((Gtil m : ℝ) - (D : ℝ) ^ 2 * g2 m); linarith
    have h2 : 0 ≤ 2 * (D : ℝ) * (m : ℝ) ^ 3 := by positivity
    calc ((D : ℝ) ^ 2 * g2 m - Gtil m) * Real.log (1 + 1 / m) ≤ 2 * (D : ℝ) * (m : ℝ) ^ 3 * 1 := by
          rcases le_or_gt 0 ((D : ℝ) ^ 2 * g2 m - Gtil m) with h | h
          · exact mul_le_mul h1 hl1 hl0 h2
          · nlinarith
      _ ≤ 2 * (D : ℝ) * (n : ℝ) ^ 3 := by nlinarith
  have hc := sum_cube_le hn
  linarith

theorem Jre_le {n : ℕ} (hn : n ≤ XX) : (D : ℝ) ^ 2 * Jre n ≤ (Jsp n : ℝ) + 2 * (D : ℝ) * 10 ^ 16 := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have eJ : (Jsp n : ℝ) = ∑ m ∈ Ico 1 n, |(Gtil m : ℝ)| := by
    unfold Jsp; push_cast
    refine sum_congr rfl fun m _ => ?_
    simp [Nat.cast_natAbs, Int.cast_abs]
  have hsum : (D : ℝ) ^ 2 * Jre n - Jsp n ≤ ∑ _m ∈ Ico 1 n, 2 * (D : ℝ) * (n : ℝ) ^ 3 := by
    rw [Jre, eJ, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun m hm => ?_
    have hG := abs_Gtil_sub_le m
    have hm3 : (m : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (mem_Ico.1 hm).2.le) 3
    have hDD : (D : ℝ) ^ 2 * |g2 m| = |(D : ℝ) ^ 2 * g2 m| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (D : ℝ) ^ 2 by positivity)]
    rw [hDD]
    have := abs_sub_abs_le_abs_sub ((D : ℝ) ^ 2 * g2 m) (Gtil m : ℝ)
    rw [abs_sub_comm] at this
    nlinarith
  have hc := sum_cube_le hn
  linarith

theorem EIJ_R : ((EIJ : ℤ) : ℝ) = 10 ^ 17 * D := by unfold EIJ; push_cast; ring

/-- **`T₂(S) ≤ 0.37273` for `700 ≤ S < 10⁴`**. -/
theorem T2_le_mid {n : ℕ} (h1 : S0 ≤ n) (h2 : n < XX) (hg : GoodIJ n) {S : ℝ} (hS1 : (n : ℝ) ≤ S)
    (hS2 : S < n + 1) : T2 S ≤ 0.37273 := by
  have hS0' : S0 = 700 := rfl
  have hn1 : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hD : (0 : ℝ) < D := by rw [DR]; norm_num
  obtain ⟨I, I', hI, hI', hc⟩ := hg
  have hT := abs_T2_sub_le (show (1 : ℝ) ≤ S by linarith)
  have hT' : T2 S ≤ 1 / 4 * (∫ y in (1 : ℝ)..S, g2 y / y) + S⁻¹ * ∫ y in (1 : ℝ)..S, |g2 y| :=
    sub_le_iff_le_add'.1 (abs_le.1 hT).2
  have hIm := I_le_max hn1 hS1 hS2.le
  have hJm := J_div_le_max hn1 hS1 hS2.le
  -- the check, over `ℝ`
  unfold chkIJ at hc
  rw [decide_eq_true_eq] at hc
  have hcR : (((max I I' + EIJ) * n * (n + 1) + 4 * max (((Jsp n : ℕ) + EIJ) * (n + 1))
      (((Jsp (n + 1) : ℕ) + EIJ) * n)) * 100000 : ℤ) ≤ (4 * 37273 * (D : ℤ) ^ 2 * n * (n + 1) : ℤ) :=
    hc
  have hcR' : ((max (I : ℝ) I' + 10 ^ 17 * D) * n * (n + 1) + 4 * max (((Jsp n : ℝ) + 10 ^ 17 * D) * (n + 1))
      (((Jsp (n + 1) : ℝ) + 10 ^ 17 * D) * n)) * 100000 ≤ 149092 * (D : ℝ) ^ 2 * n * (n + 1) := by
    have := (Int.cast_le (R := ℝ)).2 hcR
    push_cast at this
    rw [EIJ_R] at this
    exact this
  -- `D² I ≤ I + E`, `D² J ≤ J + E`
  have hE : (2 : ℝ) * D * 10 ^ 16 ≤ 10 ^ 17 * D := by rw [DR]; norm_num
  have i1 : (D : ℝ) ^ 2 * Ire n ≤ I + 10 ^ 17 * D := by have := Ire_le (n := n) (by omega); linarith
  have i2 : (D : ℝ) ^ 2 * Ire (n + 1) ≤ I' + 10 ^ 17 * D := by
    have := Ire_le (n := n + 1) (by omega); linarith
  have j1 : (D : ℝ) ^ 2 * Jre n ≤ Jsp n + 10 ^ 17 * D := by have := Jre_le (n := n) (by omega); linarith
  have j2 : (D : ℝ) ^ 2 * Jre (n + 1) ≤ Jsp (n + 1) + 10 ^ 17 * D := by
    have := Jre_le (n := n + 1) (by omega); linarith
  set M1 := max (I : ℝ) I' + 10 ^ 17 * D
  set M2 := max (((Jsp n : ℝ) + 10 ^ 17 * D) * (n + 1)) (((Jsp (n + 1) : ℝ) + 10 ^ 17 * D) * n)
  have hD2 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hnn : (0 : ℝ) < n * (n + 1) := by positivity
  have a1 : 1 / 4 * max (Ire n) (Ire (n + 1)) ≤ M1 / (4 * D ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : (D : ℝ) ^ 2 * max (Ire n) (Ire (n + 1)) ≤ M1 := by
      rw [mul_max_of_nonneg _ _ hD2.le]
      exact max_le (i1.trans (by simp [M1])) (i2.trans (by simp [M1]))
    nlinarith
  have a2 : max (Jre n / n) (Jre (n + 1) / (n + 1 : ℕ)) ≤ M2 / ((D : ℝ) ^ 2 * (n * (n + 1))) := by
    rw [le_div_iff₀ (by positivity), max_mul_of_nonneg _ _ (by positivity)]
    refine max_le ?_ ?_
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      calc Jre n * ((D : ℝ) ^ 2 * (n * (n + 1))) = ((D : ℝ) ^ 2 * Jre n) * ((n : ℝ) + 1) * n := by
            ring
        _ ≤ ((Jsp n : ℝ) + 10 ^ 17 * D) * ((n : ℝ) + 1) * n := by gcongr
        _ ≤ M2 * n := by gcongr; exact le_max_left _ _
    · push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      calc Jre (n + 1) * ((D : ℝ) ^ 2 * (n * (n + 1))) =
            ((D : ℝ) ^ 2 * Jre (n + 1)) * (n : ℝ) * ((n : ℝ) + 1) := by ring
        _ ≤ ((Jsp (n + 1) : ℝ) + 10 ^ 17 * D) * (n : ℝ) * ((n : ℝ) + 1) := by gcongr
        _ ≤ M2 * ((n : ℝ) + 1) := by gcongr; exact le_max_right _ _
  have a3 : M1 / (4 * D ^ 2) + M2 / ((D : ℝ) ^ 2 * (n * (n + 1))) ≤ 0.37273 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  calc T2 S ≤ 1 / 4 * (∫ y in (1 : ℝ)..S, g2 y / y) + S⁻¹ * ∫ y in (1 : ℝ)..S, |g2 y| := hT'
    _ ≤ 1 / 4 * max (Ire n) (Ire (n + 1)) + max (Jre n / n) (Jre (n + 1) / (n + 1 : ℕ)) := by
        gcongr
    _ ≤ 0.37273 := by linarith

/-- `¼ ∫₁^{10⁴} g₂/y ≤ ¼ (Ifin + E)/D²` and `∫₁^{10⁴} |g₂| ≤ (Jfin + E)/D²`. -/
theorem I_J_XX : (D : ℝ) ^ 2 * ∫ y in (1 : ℝ)..10000, g2 y / y ≤ Ifin + 10 ^ 17 * D ∧
    (D : ℝ) ^ 2 * ∫ y in (1 : ℝ)..10000, |g2 y| ≤ Jfin + 10 ^ 17 * D := by
  obtain ⟨hI, hJ, -⟩ := walk_spec
  have hD : (0 : ℝ) < D := by rw [DR]; norm_num
  have hE : (2 : ℝ) * D * 10 ^ 16 ≤ 10 ^ 17 * D := by rw [DR]; norm_num
  have e1 := integral_g2_div_nat XX (show 1 ≤ 10000 by norm_num)
  have e2 := integral_abs_g2_nat XX (show 1 ≤ 10000 by norm_num)
  have hX : ((XX : ℕ) : ℝ) = 10000 := by norm_num [XX]
  rw [hX] at e1 e2
  rw [e1, e2]
  have h1 := Ire_le (n := XX) le_rfl
  have h2 := Jre_le (n := XX) le_rfl
  rw [hJ] at h2
  constructor <;> linarith

/-! ### `T₂(S) = α_n + β_n/S` on `[n, n+1)` -/

/-- `∑_{j < m} g₂(j)`. -/
noncomputable def Gcn (m : ℕ) : ℝ := ∑ j ∈ range m, g2 j

/-- `a(k) = ∑_{s ≤ k odd} g₂(⌊k/s⌋)/s`. -/
noncomputable def areal (k : ℕ) : ℝ := ∑ s ∈ Icc 1 k, if s % 2 = 1 then g2 ((k / s : ℕ) : ℝ) / s else 0

/-- `c(k) = ∑_{s ≤ k odd} (∑_{j < ⌊k/s⌋} g₂(j) − ⌊k/s⌋ g₂(⌊k/s⌋))`. -/
noncomputable def creal (k : ℕ) : ℝ :=
  ∑ s ∈ Icc 1 k, if s % 2 = 1 then Gcn (k / s) - ((k / s : ℕ) : ℝ) * g2 ((k / s : ℕ) : ℝ) else 0

theorem g2_zero' : g2 ((0 : ℕ) : ℝ) = 0 := g2_eq_zero_of_lt_one (by norm_num)

theorem g2_zero : g2 0 = 0 := g2_eq_zero_of_lt_one (by norm_num)

theorem integral_g2_nat : ∀ m : ℕ, ∫ y in (0 : ℝ)..m, g2 y = Gcn m := by
  intro m
  induction m with
  | zero => simp [Gcn]
  | succ m ih =>
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ))
      (intervalIntegrable_g2 le_rfl h0) (intervalIntegrable_g2 h0 (by push_cast; linarith)), ih,
      integral_step le_rfl (by push_cast; linarith) (by push_cast; linarith) (fun g _ => g), Gcn, Gcn,
      sum_range_succ]
    simp

theorem integral_g2_floor {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in (0 : ℝ)..x, g2 y = Gcn ⌊x⌋₊ + g2 (⌊x⌋₊ : ℝ) * (x - ⌊x⌋₊) := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (⌊x⌋₊ : ℝ))
    (intervalIntegrable_g2 le_rfl (Nat.cast_nonneg _)) (intervalIntegrable_g2 (Nat.cast_nonneg _) h1),
    integral_g2_nat, integral_step le_rfl h1 h2.le (fun g _ => g)]
  simp [mul_comm]

theorem floor_div_of_mem {n : ℕ} {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S < n + 1) (s : ℕ) :
    ⌊S / s⌋₊ = n / s := by
  have h0 : (0 : ℝ) ≤ S := le_trans (Nat.cast_nonneg n) h1
  rw [Nat.floor_div_natCast, (Nat.floor_eq_iff h0).2 ⟨h1, h2⟩]

/-- **`T₂(S) = a(n) − a(⌊n/2⌋)/2 + (c(n) − c(⌊n/2⌋))/S`** for `S ∈ [n, n+1)`. -/
theorem T2_eq_ac {n : ℕ} (hn : 1 ≤ n) {S : ℝ} (h1 : (n : ℝ) ≤ S) (h2 : S < n + 1) :
    T2 S = areal n - areal (n / 2) / 2 + (creal n - creal (n / 2)) / S := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : 0 < S := by linarith
  have hfl : ⌊S⌋₊ = n := (Nat.floor_eq_iff hS0.le).2 ⟨h1, h2⟩
  -- each term
  have hterm : ∀ s ∈ Icc 1 n, (if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * S / s) else 0) =
      S⁻¹ * ((if s % 2 = 1 then Gcn (n / s) - ((n / s : ℕ) : ℝ) * g2 ((n / s : ℕ) : ℝ) else 0) +
        S * (if s % 2 = 1 then g2 ((n / s : ℕ) : ℝ) / s else 0) -
        (if s % 2 = 1 then Gcn (n / 2 / s) - ((n / 2 / s : ℕ) : ℝ) * g2 ((n / 2 / s : ℕ) : ℝ) else 0) -
        S / 2 * (if s % 2 = 1 then g2 ((n / 2 / s : ℕ) : ℝ) / s else 0)) := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (mem_Icc.1 hs).1
    have hs0 : (0 : ℝ) < s := by linarith
    by_cases ho : s % 2 = 1
    · rw [if_pos (Nat.odd_iff.2 ho), if_pos ho, if_pos ho, if_pos ho, if_pos ho]
      have hz : 0 < S / s := by positivity
      simp_rw [mul_div_assoc]
      rw [integral_g2_mul hz, ← intervalIntegral.integral_interval_sub_left (a := (0 : ℝ))
        (intervalIntegrable_g2 le_rfl hz.le) (intervalIntegrable_g2 le_rfl (by positivity)),
        integral_g2_floor hz.le, integral_g2_floor (by positivity)]
      have f1 : ⌊S / s⌋₊ = n / s := floor_div_of_mem h1 h2 s
      have f2 : ⌊S / s / 2⌋₊ = n / 2 / s := by
        rw [show S / s / 2 = S / s / ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast, f1,
          Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
      rw [f1, f2]
      field_simp
      ring
    · rw [if_neg (by rw [Nat.odd_iff]; exact ho), if_neg ho, if_neg ho, if_neg ho, if_neg ho]
      ring
  unfold T2
  rw [hfl, sum_congr rfl hterm, ← mul_sum]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  -- the sums over `n/2/s` are `c(n/2)`, `a(n/2)`
  have hsub : Icc 1 (n / 2) ⊆ Icc 1 n := Icc_subset_Icc le_rfl (Nat.div_le_self n 2)
  have e1 : ∑ s ∈ Icc 1 n, (if s % 2 = 1 then Gcn (n / 2 / s) - ((n / 2 / s : ℕ) : ℝ) *
      g2 ((n / 2 / s : ℕ) : ℝ) else 0) = creal (n / 2) := by
    unfold creal
    refine (sum_subset hsub fun s hs hs' => ?_).symm
    have : n / 2 / s = 0 := Nat.div_eq_of_lt (by simp only [mem_Icc, not_and, not_le] at hs'; exact hs' (mem_Icc.1 hs).1)
    rw [this]; simp [Gcn, g2_zero]
  have e2 : ∑ s ∈ Icc 1 n, (if s % 2 = 1 then g2 ((n / 2 / s : ℕ) : ℝ) / s else 0) = areal (n / 2) := by
    unfold areal
    refine (sum_subset hsub fun s hs hs' => ?_).symm
    have : n / 2 / s = 0 := Nat.div_eq_of_lt (by simp only [mem_Icc, not_and, not_le] at hs'; exact hs' (mem_Icc.1 hs).1)
    rw [this]; simp [g2_zero]
  rw [e1, e2]
  unfold areal creal
  field_simp
  ring

/-! ### The increments of `a` and `c` -/

/-- `Δg₂(t) = g₂(t) − g₂(t − 1)`. -/
noncomputable def dg (t : ℕ) : ℝ := g2 (t : ℝ) - g2 ((t - 1 : ℕ) : ℝ)

/-- `∑_{t ∣ rad k} t Δg₂(t)`. -/
noncomputable def sigR (k : ℕ) : ℝ := ∑ t ∈ (∏ p ∈ k.primeFactors, p).divisors, (t : ℝ) * dg t

theorem Ar_succ (m d : ℕ) : Ar (m + 1) d = Ar m d + if d ∣ m + 1 then fo (m + 1) else 0 := by
  unfold Ar
  rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) by
    ext x; simp only [mem_insert, mem_Icc]; omega, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [add_zero]

theorem fo_eq_zero_of_not {t : ℕ} (h : ¬ (t % 2 = 1 ∧ Squarefree t)) : fo t = 0 := by
  unfold fo
  split_ifs with h1
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h2 => h ⟨Nat.odd_iff.1 h1, h2⟩)]
    simp
  · rfl

/-- `g₂` only changes at odd squarefree integers. -/
theorem dg_eq_zero {t : ℕ} (ht : 1 ≤ t) (h : ¬ (t % 2 = 1 ∧ Squarefree t)) : dg t = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  unfold dg
  rw [Nat.add_sub_cancel, g2_nat, g2_nat]
  have hf := fo_eq_zero_of_not h
  have e : ∀ d, Ar (m + 1) d = Ar m d := fun d => by rw [Ar_succ, hf]; simp
  simp_rw [e]
  rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) by
    ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp)]
  have : Ar m (m + 1) = 0 := by
    unfold Ar
    refine sum_eq_zero fun r hr => ?_
    obtain ⟨hr1, hr2⟩ := mem_filter.1 hr
    exact absurd (Nat.le_of_dvd (mem_Icc.1 hr1).1 hr2) (by have := (mem_Icc.1 hr1).2; omega)
  rw [this]; ring

theorem div_succ_eq {k s : ℕ} (hk : 1 ≤ k) : k / s = (k - 1) / s + if s ∣ k then 1 else 0 := by
  have := Nat.succ_div (a := k - 1) (b := s)
  rw [Nat.sub_add_cancel hk] at this
  exact this

/-- Divisors `t ∣ k` with `Δg₂(t) ≠ 0` divide `rad k`. -/
theorem sum_divisors_dg {k : ℕ} (hk : 1 ≤ k) :
    ∑ t ∈ k.divisors, (t : ℝ) * dg t = sigR k := by
  unfold sigR
  have hrad : (∏ p ∈ k.primeFactors, p) ∣ k := Nat.prod_primeFactors_dvd k
  refine (sum_subset (Nat.divisors_subset_of_dvd (by omega) hrad) fun t ht ht' => ?_).symm
  have ht1 : 1 ≤ t := Nat.pos_of_mem_divisors ht
  rw [dg_eq_zero ht1, mul_zero]
  rintro ⟨-, hsq⟩
  apply ht'
  rw [Nat.mem_divisors] at ht ⊢
  refine ⟨?_, (Nat.pos_of_dvd_of_pos hrad (by omega)).ne'⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff
    (Nat.pos_of_dvd_of_pos hrad (by omega)).ne', Nat.primeFactors_prod_primeFactors]
  exact Nat.primeFactors_mono ht.1 (by omega)

/-- `∑_{s ≤ k odd, s ∣ k} ⌊k/s⌋ Δg₂(⌊k/s⌋) = [k odd] sigR k`. -/
theorem sum_odd_dvd {k : ℕ} (hk : 1 ≤ k) :
    ∑ s ∈ Icc 1 k, (if s % 2 = 1 ∧ s ∣ k then ((k / s : ℕ) : ℝ) * dg (k / s) else 0) =
      if k % 2 = 1 then sigR k else 0 := by
  have hdiv : (Icc 1 k).filter (fun s => s ∣ k) = k.divisors := by
    ext s; simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), Nat.le_of_dvd (by omega) h⟩, h⟩
  split_ifs with ho
  · calc ∑ s ∈ Icc 1 k, (if s % 2 = 1 ∧ s ∣ k then ((k / s : ℕ) : ℝ) * dg (k / s) else 0)
        = ∑ s ∈ Icc 1 k, (if s ∣ k then ((k / s : ℕ) : ℝ) * dg (k / s) else 0) := by
          refine sum_congr rfl fun s _ => ?_
          by_cases hs : s ∣ k
          · have : s % 2 = 1 := by
              rcases Nat.even_or_odd s with he | hod
              · exfalso; have := (even_iff_two_dvd.1 he).trans hs; omega
              · exact Nat.odd_iff.1 hod
            simp [hs, this]
          · simp [hs]
      _ = ∑ s ∈ k.divisors, ((k / s : ℕ) : ℝ) * dg (k / s) := by rw [← sum_filter, hdiv]
      _ = ∑ t ∈ k.divisors, (t : ℝ) * dg t := Nat.sum_div_divisors k (fun t => (t : ℝ) * dg t)
      _ = sigR k := sum_divisors_dg hk
  · refine sum_eq_zero fun s _ => ?_
    split_ifs with h
    · rw [dg_eq_zero (Nat.div_pos (Nat.le_of_dvd (by omega) h.2) (by omega)), mul_zero]
      rintro ⟨h2, -⟩
      obtain ⟨q, hq⟩ := h.2
      have : k / s = q := by rw [hq, Nat.mul_div_cancel_left _ (by omega)]
      rw [this] at h2
      rw [hq] at ho
      have : (s * q) % 2 = 1 := by rw [Nat.mul_mod, h.1, h2]
      exact ho this
    · rfl

theorem creal_succ {k : ℕ} (hk : 1 ≤ k) :
    creal k = creal (k - 1) - if k % 2 = 1 then sigR k else 0 := by
  rw [← sum_odd_dvd hk]
  have hext : creal (k - 1) = ∑ s ∈ Icc 1 k,
      (if s % 2 = 1 then Gcn ((k - 1) / s) - (((k - 1) / s : ℕ) : ℝ) * g2 (((k - 1) / s : ℕ) : ℝ) else 0) := by
    unfold creal
    rw [show Icc 1 k = insert k (Icc 1 (k - 1)) by
      ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp; omega)]
    rw [Nat.div_eq_of_lt (show k - 1 < k by omega)]
    simp [Gcn]
  rw [hext]
  unfold creal
  rw [eq_sub_iff_add_eq, ← sum_add_distrib]
  refine sum_congr rfl fun s hs => ?_
  have hs1 := (mem_Icc.1 hs).1
  rw [div_succ_eq (s := s) hk]
  by_cases hsk : s ∣ k
  · have hq : 1 ≤ k / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsk) (by omega)
    rw [div_succ_eq (s := s) hk] at hq
    simp only [hsk, if_true] at hq ⊢
    set q := (k - 1) / s
    by_cases ho : s % 2 = 1
    · simp only [ho, true_and, if_true]
      unfold dg Gcn
      rw [Nat.add_sub_cancel, sum_range_succ]
      push_cast; ring
    · simp [ho]
  · simp [hsk]

theorem areal_succ {k : ℕ} (hk : 1 ≤ k) :
    areal k = areal (k - 1) + if k % 2 = 1 then sigR k / k else 0 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : (if k % 2 = 1 then sigR k / k else 0) =
      (∑ s ∈ Icc 1 k, (if s % 2 = 1 ∧ s ∣ k then ((k / s : ℕ) : ℝ) * dg (k / s) else 0)) / k := by
    rw [sum_odd_dvd hk]; split_ifs <;> simp
  rw [hs]
  have hext : areal (k - 1) = ∑ s ∈ Icc 1 k,
      (if s % 2 = 1 then g2 (((k - 1) / s : ℕ) : ℝ) / s else 0) := by
    unfold areal
    rw [show Icc 1 k = insert k (Icc 1 (k - 1)) by
      ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp; omega)]
    rw [Nat.div_eq_of_lt (show k - 1 < k by omega)]
    simp [g2_zero]
  rw [hext, sum_div, ← sum_add_distrib]
  unfold areal
  refine sum_congr rfl fun s hs => ?_
  have hs1 := (mem_Icc.1 hs).1
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  by_cases hsk : s ∣ k
  · have hq : 1 ≤ k / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsk) (by omega)
    have hks : ((k / s : ℕ) : ℝ) = k / s := by
      rw [Nat.cast_div hsk (by positivity)]
    have e := div_succ_eq (s := s) hk
    simp only [hsk, if_true] at e
    by_cases ho : s % 2 = 1
    · simp only [ho, hsk, true_and, if_true]
      unfold dg
      rw [show k / s - 1 = (k - 1) / s by omega, hks]
      field_simp
      ring
    · simp [ho]
  · have e := div_succ_eq (s := s) hk
    simp only [hsk, if_false, add_zero] at e
    simp [hsk, e]

/-! ### Errors, and `T₂ ≤ 0.37273` on `[16, 700)` -/

theorem abs_dg_sub_le {t : ℕ} (ht : 1 ≤ t) : |(D : ℝ) ^ 2 * dg t - dG t| ≤ 4 * D * (t : ℝ) ^ 3 := by
  have h1 := abs_Gtil_sub_le t
  have h2 := abs_Gtil_sub_le (t - 1)
  have hD : (0 : ℝ) ≤ D := by positivity
  have h3 : ((t - 1 : ℕ) : ℝ) ^ 3 ≤ (t : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le t 1) 3
  unfold dg dG
  push_cast
  have e : (D : ℝ) ^ 2 * (g2 t - g2 ((t - 1 : ℕ) : ℝ)) - ((Gtil t : ℝ) - Gtil (t - 1)) =
      -((Gtil t : ℝ) - D ^ 2 * g2 t) + ((Gtil (t - 1) : ℝ) - D ^ 2 * g2 ((t - 1 : ℕ) : ℝ)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  nlinarith

theorem abs_sigR_sub_le {k : ℕ} (hk : 1 ≤ k) :
    |(D : ℝ) ^ 2 * sigR k - sigS k| ≤ 4 * D * (k : ℝ) ^ 5 := by
  have hD : (0 : ℝ) ≤ D := by positivity
  set r := ∏ p ∈ k.primeFactors, p
  have hr : r ∣ k := Nat.prod_primeFactors_dvd k
  have hrk : r ≤ k := Nat.le_of_dvd (by omega) hr
  have e : (D : ℝ) ^ 2 * sigR k - sigS k = ∑ t ∈ r.divisors, (t : ℝ) * ((D : ℝ) ^ 2 * dg t - dG t) := by
    unfold sigR sigS; push_cast; rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => by ring
  rw [e]
  have hterm : ∀ t ∈ r.divisors, |(t : ℝ) * ((D : ℝ) ^ 2 * dg t - dG t)| ≤ 4 * D * (k : ℝ) ^ 4 := by
    intro t ht
    have ht1 : 1 ≤ t := Nat.pos_of_mem_divisors ht
    have htk : (t : ℝ) ≤ k := by exact_mod_cast (Nat.divisor_le ht).trans hrk
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)]
    have := abs_dg_sub_le ht1
    have h3 : (t : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) htk 3
    calc (t : ℝ) * |(D : ℝ) ^ 2 * dg t - dG t| ≤ k * (4 * D * k ^ 3) := by
          refine mul_le_mul htk (this.trans (by nlinarith)) (abs_nonneg _) (Nat.cast_nonneg _)
      _ = 4 * D * k ^ 4 := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hc : (r.divisors.card : ℝ) ≤ k := by exact_mod_cast (Nat.card_divisors_le_self r).trans hrk
  calc (r.divisors.card : ℝ) * (4 * D * (k : ℝ) ^ 4) ≤ k * (4 * D * k ^ 4) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * D * k ^ 5 := by ring

theorem creal_zero : creal 0 = 0 := by simp [creal]
theorem areal_zero : areal 0 = 0 := by simp [areal]
theorem ctil_zero : ctil 0 = 0 := by simp [ctil]
theorem atil_zero : atil 0 = 0 := by simp [atil]

theorem abs_creal_sub_le : ∀ k : ℕ, |(D : ℝ) ^ 2 * creal k - ctil k| ≤ 4 * D * (k : ℝ) ^ 6 := by
  intro k
  induction k with
  | zero => simp [creal_zero, ctil_zero]
  | succ k ih =>
    have hD : (0 : ℝ) ≤ D := by positivity
    rw [creal_succ (by omega), ctil_succ, Nat.add_sub_cancel]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hb : (k : ℝ) ^ 6 + ((k + 1 : ℕ) : ℝ) ^ 5 ≤ ((k + 1 : ℕ) : ℝ) ^ 6 := by
      push_cast
      have : (k : ℝ) ^ 5 ≤ ((k : ℝ) + 1) ^ 5 := pow_le_pow_left₀ hk0 (by linarith) 5
      nlinarith [pow_nonneg hk0 5]
    split_ifs with ho
    · have h2 := abs_sigR_sub_le (k := k + 1) (by omega)
      push_cast
      have e : (D : ℝ) ^ 2 * (creal k - sigR (k + 1)) - ((ctil k : ℝ) - sigS (k + 1)) =
          ((D : ℝ) ^ 2 * creal k - ctil k) - ((D : ℝ) ^ 2 * sigR (k + 1) - sigS (k + 1)) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      push_cast at h2 hb
      nlinarith
    · push_cast
      simp only [sub_zero]
      refine ih.trans ?_
      have : (k : ℝ) ^ 6 ≤ ((k : ℝ) + 1) ^ 6 := pow_le_pow_left₀ hk0 (by linarith) 6
      nlinarith

theorem abs_ediv_sub (a : ℤ) {b : ℕ} (hb : 0 < b) : |(a : ℝ) / b - ((a / (b : ℤ) : ℤ) : ℝ)| ≤ 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Int.ediv_mul_le a (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
  have h2 := Int.lt_ediv_add_one_mul_self a (show (0 : ℤ) < b by exact_mod_cast hb)
  have h1' : ((a / (b : ℤ) : ℤ) : ℝ) * b ≤ a := by exact_mod_cast h1
  have h2' : (a : ℝ) < (((a / (b : ℤ) : ℤ) : ℝ) + 1) * b := by exact_mod_cast h2
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hb']; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hb']; nlinarith

theorem abs_areal_sub_le : ∀ k : ℕ, |(D : ℝ) ^ 2 * areal k - atil k| ≤ (4 * D + 1) * (k : ℝ) ^ 5 := by
  intro k
  induction k with
  | zero => simp [areal_zero, atil_zero]
  | succ k ih =>
    have hD : (0 : ℝ) ≤ D := by positivity
    rw [areal_succ (by omega), atil_succ, Nat.add_sub_cancel]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hb : (k : ℝ) ^ 5 + ((k + 1 : ℕ) : ℝ) ^ 4 ≤ ((k + 1 : ℕ) : ℝ) ^ 5 := by
      push_cast
      have : (k : ℝ) ^ 4 ≤ ((k : ℝ) + 1) ^ 4 := pow_le_pow_left₀ hk0 (by linarith) 4
      nlinarith [pow_nonneg hk0 4]
    split_ifs with ho
    · have h2 := abs_sigR_sub_le (k := k + 1) (by omega)
      have h3 := abs_ediv_sub (sigS (k + 1)) (b := k + 1) (by omega)
      have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      -- `|D² σ/(k+1) − ⌊σ̃/(k+1)⌋| ≤ 4 D (k+1)⁴ + 1`
      have h4 : |(D : ℝ) ^ 2 * (sigR (k + 1) / ((k + 1 : ℕ) : ℝ)) -
          ((sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 4 * D * ((k + 1 : ℕ) : ℝ) ^ 4 + 1 := by
        have e : (D : ℝ) ^ 2 * (sigR (k + 1) / ((k + 1 : ℕ) : ℝ)) -
            ((sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
            ((D : ℝ) ^ 2 * sigR (k + 1) - sigS (k + 1)) / ((k + 1 : ℕ) : ℝ) +
            ((sigS (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) - ((sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by
          field_simp; ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add ?_ h3)
        rw [abs_div, abs_of_pos hk1, div_le_iff₀ hk1]
        calc |(D : ℝ) ^ 2 * sigR (k + 1) - sigS (k + 1)| ≤ 4 * D * ((k + 1 : ℕ) : ℝ) ^ 5 := h2
          _ = 4 * D * ((k + 1 : ℕ) : ℝ) ^ 4 * ((k + 1 : ℕ) : ℝ) := by ring
      have e : (D : ℝ) ^ 2 * (areal k + sigR (k + 1) / ((k + 1 : ℕ) : ℝ)) -
          ((atil k + sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
          ((D : ℝ) ^ 2 * areal k - atil k) + ((D : ℝ) ^ 2 * (sigR (k + 1) / ((k + 1 : ℕ) : ℝ)) -
            ((sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by push_cast; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have h5 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by push_cast; linarith)
      calc |(D : ℝ) ^ 2 * areal k - atil k| + |(D : ℝ) ^ 2 * (sigR (k + 1) / ((k + 1 : ℕ) : ℝ)) -
            ((sigS (k + 1) / ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)|
          ≤ (4 * D + 1) * (k : ℝ) ^ 5 + (4 * D * ((k + 1 : ℕ) : ℝ) ^ 4 + 1) := add_le_add ih h4
        _ ≤ (4 * D + 1) * ((k : ℝ) ^ 5 + ((k + 1 : ℕ) : ℝ) ^ 4) := by nlinarith
        _ ≤ (4 * D + 1) * ((k + 1 : ℕ) : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hb (by positivity)
    · simp only [add_zero]
      refine ih.trans ?_
      have : (k : ℝ) ^ 5 ≤ ((k : ℝ) + 1) ^ 5 := pow_le_pow_left₀ hk0 (by linarith) 5
      push_cast
      nlinarith

theorem EA_R : ((EA : ℤ) : ℝ) = 10 ^ 19 * D := by unfold EA; push_cast; ring

/-- **`T₂(S) ≤ 0.37273` for `16 ≤ S < 700`** from the `α`/`β` check. -/
theorem T2_le_low {n : ℕ} (h1 : 16 ≤ n) (h2 : n < S0) (hg : GoodAB n) {S : ℝ} (hS1 : (n : ℝ) ≤ S)
    (hS2 : S < n + 1) : T2 S ≤ 0.37273 := by
  have hS0' : S0 = 700 := rfl
  have hD : (0 : ℝ) < D := by rw [DR]; norm_num
  have hS : 0 < S := by have : (16 : ℝ) ≤ n := by exact_mod_cast h1
                        linarith
  rw [T2_eq_ac (by omega) hS1 hS2]
  -- errors
  have hk6 : ∀ k : ℕ, k < 700 → 4 * (D : ℝ) * (k : ℝ) ^ 6 ≤ 10 ^ 19 * D / 2 := by
    intro k hk
    have : (k : ℝ) ≤ 700 := by exact_mod_cast hk.le
    have : (k : ℝ) ^ 6 ≤ 700 ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 6
    rw [DR] at *; nlinarith
  have hk5 : ∀ k : ℕ, k < 700 → (4 * (D : ℝ) + 1) * (k : ℝ) ^ 5 ≤ 10 ^ 19 * D := by
    intro k hk
    have : (k : ℝ) ≤ 700 := by exact_mod_cast hk.le
    have : (k : ℝ) ^ 5 ≤ 700 ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 5
    rw [DR] at *; nlinarith
  have ec1 := (abs_le.1 ((abs_creal_sub_le n).trans (hk6 n (by omega)))).2
  have ec2 := (abs_le.1 ((abs_creal_sub_le (n / 2)).trans (hk6 (n / 2) (by omega)))).1
  have ea1 := (abs_le.1 ((abs_areal_sub_le n).trans (hk5 n (by omega)))).2
  have ea2 := (abs_le.1 ((abs_areal_sub_le (n / 2)).trans (hk5 (n / 2) (by omega)))).1
  -- the check over `ℝ`
  unfold GoodAB chkABv at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨c1, c2⟩ := hg
  have c1' := (Int.cast_le (R := ℝ)).2 c1
  have c2' := (Int.cast_le (R := ℝ)).2 c2
  push_cast at c1' c2'
  rw [EA_R] at c1' c2'
  set A2 : ℝ := 2 * (atil n : ℝ) - atil (n / 2) + 3 * (10 ^ 19 * D)
  set B : ℝ := (ctil n : ℝ) - ctil (n / 2) + 10 ^ 19 * D
  have hA : 2 * (D : ℝ) ^ 2 * (areal n - areal (n / 2) / 2) ≤ A2 := by simp only [A2]; linarith
  have hB : (D : ℝ) ^ 2 * (creal n - creal (n / 2)) ≤ B := by simp only [B]; linarith
  -- affine in `S`
  have hn' : (n : ℝ) ≤ S := hS1
  have key : A2 * S + 2 * B ≤ 2 * 0.37273 * (D : ℝ) ^ 2 * S := by
    have l1 : (A2 * n + 2 * B) * 100000 ≤ 2 * 37273 * (D : ℝ) ^ 2 * n := by linarith
    have l2 : (A2 * (n + 1) + 2 * B) * 100000 ≤ 2 * 37273 * (D : ℝ) ^ 2 * (n + 1) := by linarith
    nlinarith
  have hD2 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  rw [← sub_nonneg]
  have : 0.37273 - (areal n - areal (n / 2) / 2 + (creal n - creal (n / 2)) / S) =
      (2 * 0.37273 * (D : ℝ) ^ 2 * S - (2 * (D : ℝ) ^ 2 * (areal n - areal (n / 2) / 2) * S +
        2 * ((D : ℝ) ^ 2 * (creal n - creal (n / 2))))) / (2 * (D : ℝ) ^ 2 * S) := by
    field_simp
  rw [this]
  refine div_nonneg ?_ (by positivity)
  nlinarith

/-- **`T₂(S) ≤ 0.37273` for `16 ≤ S < 10⁴`**. -/
theorem T2_le_small {S : ℝ} (h1 : 16 ≤ S) (h2 : S < 10000) : T2 S ≤ 0.37273 := by
  have hS0 : 0 ≤ S := by linarith
  set n := ⌊S⌋₊
  have hn1 : (n : ℝ) ≤ S := Nat.floor_le hS0
  have hn2 : S < n + 1 := Nat.lt_floor_add_one S
  have hn16 : 16 ≤ n := Nat.le_floor (by exact_mod_cast h1)
  have hnX : n < XX := by
    have : n < 10000 := Nat.floor_lt hS0 |>.2 (by exact_mod_cast h2)
    exact this
  obtain ⟨-, -, hk⟩ := walk_spec
  obtain ⟨hab, hij⟩ := hk n hn16 hnX
  rcases lt_or_ge n S0 with h | h
  · exact T2_le_low hn16 h (hab h) hn1 hn2
  · exact T2_le_mid h hnX (hij h) hn1 hn2

end TernaryGoldbach.MinorArcs.SmallG2
