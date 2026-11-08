import TernaryGoldbach.MinorArcs.T2Small
import TernaryGoldbach.MinorArcs.G2Tail

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens]

/-!
# [H, (5.31)]: `T₂(S) ≤ 0.37273` for `S ≥ 16`

* `16 ≤ S < 10⁴`: the kernel walk over `g₂(n)`, `n ≤ 10⁴` (`SmallG2.lean`, `T2Small.lean`): exactly
  `T₂ = α_n + β_n/S` for `S < 700`, and `T₂(S) ≤ ¼ ∫₁^S g₂/y + S⁻¹ ∫₁^S |g₂|` (`abs_T2_sub_le`) above;
* `S ≥ 10⁴`: the same inequality, `¼ ∫₁^{10⁴} g₂/y ≤ 0.3605763`, `∫₁^{10⁴} |g₂| ≤ 9.22` (kernel), and
  `∫_{10⁴}^S |g₂|/y ≤ 0.0082` (`G2Tail.lean`), so
  `T₂(S) ≤ 0.3605763 + 0.000922 + (5/4)·0.0082 ≤ 0.3718`.
-/

open Real Finset MeasureTheory

namespace TernaryGoldbach.MinorArcs

open SmallG2 G2Tail

/-- **[H, (5.31)]**: `T₂(S) ≤ 0.37273` for `S ≥ 16`. -/
theorem T2_le' {S : ℝ} (hS : 16 ≤ S) : T2 S ≤ 0.37273 := by
  rcases lt_or_ge S 10000 with h | h
  · exact T2_le_small hS h
  have hS0 : 0 < S := by linarith
  have hT := abs_T2_sub_le (show (1 : ℝ) ≤ S by linarith)
  have hT' : T2 S ≤ 1 / 4 * (∫ y in (1 : ℝ)..S, g2 y / y) + S⁻¹ * ∫ y in (1 : ℝ)..S, |g2 y| :=
    sub_le_iff_le_add'.1 (abs_le.1 hT).2
  obtain ⟨hI, hJ⟩ := I_J_XX
  have htail := tail_integral_le h
  -- split at `10⁴`
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_g2_div le_rfl (by norm_num : (1 : ℝ) ≤ 10000))
    (intervalIntegrable_g2_div (by norm_num) h)
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_abs_g2 zero_le_one (by norm_num : (1 : ℝ) ≤ 10000))
    (intervalIntegrable_abs_g2 (by norm_num) h)
  have h3 : ∫ y in (10000 : ℝ)..S, g2 y / y ≤ ∫ y in (10000 : ℝ)..S, |g2 y| / y :=
    intervalIntegral.integral_mono_on h (intervalIntegrable_g2_div (by norm_num) h)
      (G2Tail.intervalIntegrable_abs_g2_div (by norm_num) h) fun y hy =>
        div_le_div_of_nonneg_right (le_abs_self _) (by linarith [hy.1])
  have h4 : S⁻¹ * ∫ y in (10000 : ℝ)..S, |g2 y| ≤ ∫ y in (10000 : ℝ)..S, |g2 y| / y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h ((intervalIntegrable_abs_g2 (by norm_num) h).const_mul _)
      (G2Tail.intervalIntegrable_abs_g2_div (by norm_num) h) fun y hy => ?_
    have hy0 : 0 < y := by linarith [hy.1]
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hy0 hy.2
  have h5 : S⁻¹ * ∫ y in (1 : ℝ)..10000, |g2 y| ≤ (∫ y in (1 : ℝ)..10000, |g2 y|) / 10000 := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (intervalIntegral.integral_nonneg (by norm_num)
      fun y _ => abs_nonneg _) (by norm_num) h
  rw [← e1, ← e2] at hT'
  -- the numbers
  have hD : (D : ℝ) = 10 ^ 30 := DR
  rw [hD] at hI hJ
  have hIf : ((Ifin : ℤ) : ℝ) = 1442305043071741356929337106029717587029646414197648482569251 := by
    norm_num [Ifin]
  have hJf : ((Jfin : ℕ) : ℝ) = 9218553783470309560072038260070108962893361103201224033363762 := by
    norm_num [Jfin]
  rw [hIf] at hI
  rw [hJf] at hJ
  have hI' : ∫ y in (1 : ℝ)..10000, g2 y / y ≤ 1.4423050431 := by
    have := (le_div_iff₀' (by norm_num : (0 : ℝ) < (10 ^ 30) ^ 2)).2 hI
    refine this.trans ?_
    norm_num
  have hJ' : ∫ y in (1 : ℝ)..10000, |g2 y| ≤ 9.2185538 := by
    have := (le_div_iff₀' (by norm_num : (0 : ℝ) < (10 ^ 30) ^ 2)).2 hJ
    refine this.trans ?_
    norm_num
  rw [mul_add, mul_add] at hT'
  linarith

end TernaryGoldbach.MinorArcs
