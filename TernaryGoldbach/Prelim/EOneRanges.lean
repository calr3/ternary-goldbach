import TernaryGoldbach.Prelim.EOneNum

/-!
# Pointwise bounds for `E(y)` on all ranges `y ≥ 10⁶`

* `E_bound_A` (window `a = 3`) and `E_bound_A_half` (window `a = 1/2`): if `E₁Λ` varies by at most
  `A₀` from any integer point `m ∈ [Y e^{−0.003}, Y]` up to the top of the window, then
  `|E(Y)| ≤ A₀ + 1/M₂ + Z(Y)/M(1)`.
* The variation `A₀` comes from summation by parts (`E1_diff_gen`) with the pointwise errors of
  `ψ` of each range.
-/

open MeasureTheory Set Filter Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

/-- `Z(Y)/M(1) ≤ 68/√Y + 5.3·10⁶/Y^{3/2} + 10⁻¹³` for `a = 1/2`, `δ = 10⁻⁴`. -/
theorem Zsm_div_le_half {Y : ℝ} (hY : 1 ≤ Y) :
    (Zsm 0.5 1e-4 Y + (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4))) /
        (Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1)) ≤
      68 / √Y + 5.3e6 * Y ^ (-(3 / 2) : ℝ) + 1e-13 := by
  have hY0 : 0 < Y := by linarith
  have hLQ := LQW_le (a := 0.5) (δ := 1e-4) (H := 1e8)
  have hT := TailBH_le (a := 0.5) (by norm_num) (by norm_num)
  have hV := Vg_le (a := 0.5) (by norm_num)
  have he1 : Real.exp ((1e-4 : ℝ) ^ 2 / 2) ≤ 1.0001 := by
    have h := exp_small_le (t := (1e-4 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he1' : 1 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hh : 1.6487 ≤ Real.exp 0.5 ∧ Real.exp 0.5 ≤ 1.6488 := by
    constructor
    · have := Real.add_one_le_exp 0.5
      have h2 := Real.exp_bound' (x := 0.5) (by norm_num) (by norm_num) (n := 6) (by norm_num)
      have h1 := Real.exp_one_gt_d9
      have e : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 0.5]
    · have := exp_half_le; norm_num at this ⊢; linarith
  have h25 : Real.exp (0.5 / 2) ≤ 1.2841 := by
    have e : Real.exp (0.5 / 2) * Real.exp (0.5 / 2) = Real.exp 0.5 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (0.5 / 2)]
  have hM1 : 0.6487 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1) := by nlinarith
  have hLQ' : LQW 0.5 0 1e-4 1e8 ≤ 44 := by
    refine hLQ.trans ?_; nlinarith [Real.exp_pos (0.5 / 2)]
  have htail : (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤ 1e-14 := by
    have e1 : Real.exp (0.5 + 0.003) ≤ 1.7 := by
      rw [Real.exp_add]
      have := exp_small_le (t := 0.003) (by norm_num) (by norm_num)
      nlinarith [Real.exp_pos 0.003, Real.exp_pos 0.5]
    have e2 : Real.exp (-(0.003 / 1e-4)) ≤ 1e-13 := by
      have h32 := exp_neg32_le
      have e : Real.exp (-(0.003 / 1e-4)) = Real.exp (-32) * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [exp_two_le, Real.exp_pos 2, Real.exp_pos (-32)]
    have : (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤
        (22 + 36 * 1.7) * 1e-4 * 1e-13 := by gcongr
    linarith [show ((22 : ℝ) + 36 * 1.7) * 1e-4 * 1e-13 ≤ 1e-14 by norm_num]
  have hsY : Y ^ (-(1 / 2) : ℝ) = 1 / √Y := by
    rw [Real.rpow_neg hY0.le, ← Real.sqrt_eq_rpow, one_div]
  have hp0 : 0 ≤ Y ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hp1 : 0 ≤ Y ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hpi : 3.14 ≤ Real.pi := Real.pi_gt_d2.le
  unfold Zsm
  rw [div_le_iff₀ (by linarith)]
  have hZ1 : Y ^ (-(1 / 2) : ℝ) * LQW 0.5 0 1e-4 1e8 ≤ 44 * Y ^ (-(1 / 2) : ℝ) := by nlinarith
  have hZ3 : 2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg 0.5 0 1e-4 / (2 * Real.pi) ≤ 3.4e6 * Y ^ (-(3 / 2) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : Vg 0.5 0 1e-4 ≤ 3.2e7 := hV
    nlinarith
  have hT0 : 2 * TailBH 0.5 1e-4 1e8 / 1e8 ≤ 1e-22 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hsY' : 68 / √Y = 68 * Y ^ (-(1 / 2) : ℝ) := by rw [hsY]; ring
  rw [hsY']
  set M1 := Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1) with hM1d
  have hM1u : M1 ≤ 1.0001 * 0.6488 := by rw [hM1d]; nlinarith
  nlinarith

end TernaryGoldbach.Prelim
