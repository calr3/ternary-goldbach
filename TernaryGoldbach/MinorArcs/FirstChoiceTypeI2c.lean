import TernaryGoldbach.MinorArcs.FirstChoiceTypeI2b

variable [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# [H, (6.59)], our version: `S_{I,2}` at the first choice of parameters
-/

open Real

namespace TernaryGoldbach.MinorArcs

set_option maxHeartbeats 1600000 in
/-- **[H, (6.59)], our version**: for `q ≤ x^{1/3}/6`, at the parameters of (6.49),
`|S_{I,2}| ≤ 2.5106 x/√t + 2.8 · 2x/(δ₀φ(q)) + (15.267 log t + 21.46) · 2x/t + 0.556 x^{5/6}`. -/
theorem typeI2_first {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (3 / 4 * T ^ 2)) (hqT : (q : ℝ) ≤ T / 6) :
    ‖typeI2 α (T ^ 3) (U1 T (delta0 δ * q)) (V1 T)‖ ≤
      2.5106 * (T ^ 3 / √(delta0 δ * q)) + 2.8 * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) +
        (15.267 * Real.log (delta0 δ * q) + 21.46) * (2 * T ^ 3 / (delta0 δ * q)) +
        0.556 * (T ^ 2 * √T) := by
  obtain ⟨hδq, ht2, htT⟩ := first_choice_t hT h hqT
  have hq : 1 ≤ q := h.1
  set t := delta0 δ * q with ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hsT := sqrt_ge_2449 hT
  have hU := U1_ge hT ht0 htT
  have hU1 : (1 : ℝ) ≤ U1 T t := le_trans (by nlinarith) hU
  have hV1 := V1_ge hT0
  have hV2 := V1_le hT0
  have hUV := U1V1_le hT0 ht0
  have hUVx : (U1 T t : ℝ) * V1 T ≤ T ^ 3 := by
    refine hUV.trans (div_le_self (by positivity) ?_)
    have : (1 : ℝ) ≤ √t := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hqV : (q : ℝ) * V1 T ≤ 3 / 4 * T ^ 2 := by nlinarith
  have hQV : 16 * (V1 T : ℝ) ≤ 3 / 4 * T ^ 2 := by nlinarith
  have hV2e6 : (2.5e7 : ℝ) ≤ V1 T := by linarith
  have hmu := typeI2_mu_first (δ := δ) hT hq ht2 htT
  have hc0 := typeI2_c0_first hT hq hqT ht2 htT
  rw [← ht] at hmu
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hX : 0 ≤ 2 * T ^ 3 / t := by positivity
  have hS : 0 ≤ T ^ 3 / √t := by positivity
  have hK : 0 ≤ T ^ 2 * √T := by positivity
  by_cases hδ : |δ| ≤ 1 / (2 * c₂)
  · have hle := typeI2_le_small h (by positivity) hqV hQV hU1 hV2e6 hUVx hδ
    have hrest := typeI2_small_rest_first hT hq hqT ht2 htT
    refine hle.trans ?_
    nlinarith
  · push Not at hδ
    have hle := typeI2_le_large (ε := 0.07) h (by positivity) hqV hQV hU1 hV2e6 hUVx hδ.le
      (by norm_num) (by norm_num)
    have hrest := typeI2_large_rest_first hT hq hqT ht2 htT hδ.le
    simp only [] at hrest
    refine hle.trans ?_
    nlinarith

end TernaryGoldbach.MinorArcs
