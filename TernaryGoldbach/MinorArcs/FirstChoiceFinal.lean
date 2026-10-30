import TernaryGoldbach.MinorArcs.FirstChoiceTypeI2c
import TernaryGoldbach.MinorArcs.Assembly

/-!
# [B, §6.3.1, (6.63) and §6.4]: Theorem 3.1.1 for `q ≤ x^{1/3}/6`

With `T = x^{1/3}`, `t = δ₀q`:
`|S_{η₂}(α, x)| ≤ ((0.27125 C_{x,t} + 0.41415) log t + 0.8103) x/√(δ₀φ(q)) + 2.5 x/√t`
`+ 2x/(δ₀φ(q)) (13/4 log t + 7.82) + 2x/t (13.66 log t + 37.55) + 3.8 x^{5/6}`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

theorem Cxt_nonneg {T t : ℝ} (ht2 : 2 ≤ t) (htT : t ≤ T / 3) : 0 ≤ Cxt T t := by
  have ht0 : 0 < t := by linarith
  have hL := two_le_logL ht0 htT
  have : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  unfold Cxt
  exact Real.log_nonneg (by have : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * T / (2.004 * t))) := by
                              positivity
                            linarith)

set_option maxHeartbeats 1600000 in
/-- **[B, Theorem 3.1.1] for `q ≤ x^{1/3}/6`**, in terms of `T = x^{1/3}`, with the corrected
constant `0.8103` (for [B]'s `0.5`) and `3.8 x^{5/6}` (for [B]'s `3.36 x^{5/6}`). -/
theorem theorem_3_1_1_first {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (3 / 4 * T ^ 2)) (hqT : (q : ℝ) ≤ T / 6) :
    ‖S eta2 (T ^ 3) α‖ ≤
      ((0.27125 * Cxt T (delta0 δ * q) + 0.41415) * Real.log (delta0 δ * q) + 0.8103) /
          √(delta0 δ * Nat.totient q) * T ^ 3 +
        2.5 * T ^ 3 / √(delta0 δ * q) +
        2 * T ^ 3 / (delta0 δ * q) * ((q : ℝ) / Nat.totient q *
          (13 / 4 * Real.log (delta0 δ * q) + 7.82) + 13.66 * Real.log (delta0 δ * q) + 37.55) +
        3.8 * (T ^ 2 * √T) := by
  obtain ⟨hδq, ht2, htT⟩ := first_choice_t hT h hqT
  have hq : 1 ≤ q := h.1
  set t := delta0 δ * q with ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hd := delta0_ge δ
  have hsT := sqrt_ge_2449 hT
  have hT2 : 18 ≤ T ^ 2 := by nlinarith
  have hV4 : (V1 T : ℝ) ≤ T ^ 3 / 4 := by
    have := V1_le hT0
    have : 9 * T / 2 ≤ T ^ 3 / 4 := by
      have : T ^ 3 = T * T ^ 2 := by ring
      nlinarith
    linarith
  have hparts := norm_S_le_parts α (x := T ^ 3) (one_le_pow₀ (by linarith)) (U1 T t) (V1 T) hV4
  have hI1 := typeI1_first hT h hqT
  have hI2 := typeI2_first hT h hqT
  have hII := typeII_first hT h hqT
  rw [← ht] at hI1 hI2 hII
  have hmain := main_amgm hT ht2 htT (Cxt_nonneg ht2 htT)
  have hlog : 3 * Real.log (T ^ 3) ≤ 0.0001 * (T ^ 2 * √T) := by
    rw [Real.log_pow]; push_cast
    have := log_le_sqrt_sharp hT
    have : 9 * (0.0064 * √T) ≤ 0.0001 * (T ^ 2 * √T) := by
      have h0 : 0 ≤ √T := Real.sqrt_nonneg T
      have h1 : 576 ≤ T ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 h0]
    linarith
  -- The main term.
  have hx0 : 0 ≤ T ^ 3 / √(delta0 δ * Nat.totient q) := by positivity
  have hM : T ^ 3 / √(delta0 δ * Nat.totient q) *
      (√(Cxt T t * (Real.log t + 0.002) + Real.log (4 * t) / 2) *
        √(0.30214 * Real.log t + 0.67506)) ≤
      ((0.27125 * Cxt T t + 0.41415) * Real.log t + 0.8103) / √(delta0 δ * Nat.totient q) * T ^ 3 := by
    calc _ ≤ T ^ 3 / √(delta0 δ * Nat.totient q) *
          ((0.27125 * Cxt T t + 0.41415) * Real.log t + 0.8103) :=
          mul_le_mul_of_nonneg_left hmain hx0
      _ = _ := by ring
  -- `2x/(δ₀φ) ≥ 2x/t`.
  have hXφq : 2 * T ^ 3 / t ≤ 2 * T ^ 3 / (delta0 δ * Nat.totient q) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [ht]; exact mul_le_mul_of_nonneg_left hφq (by linarith)
  have hL : 2 * T ^ 3 / t * ((q : ℝ) / Nat.totient q * (13 / 4 * Real.log t + 7.82) +
      13.66 * Real.log t + 37.55) = 2 * T ^ 3 / (delta0 δ * Nat.totient q) *
        (13 / 4 * Real.log t + 7.82) + 2 * T ^ 3 / t * (13.66 * Real.log t + 37.55) := by
    rw [ht]; field_simp; ring
  rw [hL]
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hX : 0 ≤ 2 * T ^ 3 / t := by positivity
  have hS : 0 ≤ T ^ 3 / √t := by positivity
  have hK : 0 ≤ T ^ 2 * √T := by positivity
  have hS' : 2.5 * T ^ 3 / √t = 2.5 * (T ^ 3 / √t) := by ring
  rw [hS']
  -- `(3.25 log t + 5.21697)(2x/(δ₀φ) - 2x/t) ≥ 0`.
  have hspill : (13 / 4 * Real.log t + 5.21697) * (2 * T ^ 3 / t) ≤
      (13 / 4 * Real.log t + 5.21697) * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) :=
    mul_le_mul_of_nonneg_left hXφq (by positivity)
  nlinarith

end TernaryGoldbach.MinorArcs
