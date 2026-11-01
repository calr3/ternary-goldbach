import TernaryGoldbach.Explicit.GaussSmooth
import TernaryGoldbach.Explicit.EtaPlusSq
import TernaryGoldbach.Helfgott.Chebyshev

/-!
# From the smoothed sum to `ψ(x)`

With `φ = gsm a b δ` (`b = log(y₀/x)`):
* `a = K₀δ`: `Σ Λ(n) φ(n/x) ≥ (1 − 2e^{−K₀²/2}) (ψ(x) − ψ(y₀ e^{K₀δ}))` (pointwise);
* `a = −K₀δ`: `Σ Λ(n) φ(n/x) ≤ ψ(x) + 4x e^{−K₀²/2}` (via `φ(u) ≤ P(Z ≤ (a − log u)/δ)`, finite sums
  under the integral, `ψ(y) ≤ 4y` and a Chernoff majorant).
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.Helfgott (psi theta theta_le sum_pow_le_theta psi_sub_theta_le_sum)

/-! ## `ψ(N) ≤ 4N` (elementary) -/

theorem nat_sq_le_two_pow (k : ℕ) : k ^ 2 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := this
        _ ≤ 2 * (2 * 2 ^ n) := by omega
        _ = 2 * 2 ^ (n + 1) := by ring

theorem psi_le_four (N : ℕ) : psi N ≤ 4 * N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [psi]
  have h1 := psi_sub_theta_le_sum N
  have h2 : ∀ k ∈ Finset.Icc 2 (Nat.log 2 N), (∑ m ∈ range (N + 1),
      if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ (Nat.sqrt N : ℝ) * Real.log 4 := by
    intro k hk
    refine sum_pow_le_theta (Nat.sqrt_le_self N) fun m hm hmk => ?_
    rw [Nat.le_sqrt]
    have hk2 : 2 ≤ k := (Finset.mem_Icc.1 hk).1
    calc m * m = m ^ 2 := by ring
      _ ≤ m ^ k := Nat.pow_le_pow_right hm.pos hk2
      _ ≤ N := hmk
  have h3 := sum_le_sum h2
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at h3
  have hθ := theta_le N
  set k := Nat.log 2 N with hk
  have hkN : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hk2 : (k : ℝ) ^ 2 ≤ 2 * N := by
    have := nat_sq_le_two_pow k
    have : k ^ 2 ≤ 2 * N := le_trans this (by omega)
    exact_mod_cast this
  have hs : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hkk : ((k + 1 - 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : k + 1 - 2 ≤ k)
  have hl4 : Real.log 4 ≤ 1.3863 := by
    have := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- `k √N ≤ √2 N`
  have hkS : (k : ℝ) * √(N : ℝ) ≤ 1.4143 * N := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (k : ℝ) ≤ √(2 * N) := Real.le_sqrt_of_sq_le hk2
    calc (k : ℝ) * √(N : ℝ) ≤ √(2 * N) * √(N : ℝ) := mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ = √2 * N := by rw [Real.sqrt_mul (by norm_num), mul_assoc, Real.mul_self_sqrt hN0.le]
      _ ≤ 1.4143 * N := by
        have : √2 ≤ 1.4143 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        nlinarith
  have hsum : ((k + 1 - 2 : ℕ) : ℝ) * ((Nat.sqrt N : ℝ) * Real.log 4) ≤ (1.4143 * N) * Real.log 4 := by
    have : ((k + 1 - 2 : ℕ) : ℝ) * (Nat.sqrt N : ℝ) ≤ (k : ℝ) * √(N : ℝ) :=
      mul_le_mul hkk hs (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith
  have : psi N ≤ N * Real.log 4 + 1.4143 * N * Real.log 4 := by linarith
  nlinarith

/-- `ψ` at real arguments. -/
noncomputable def psiR (y : ℝ) : ℝ := psi ⌊y⌋₊

theorem psiR_mono : Monotone psiR := by
  intro y z h
  unfold psiR psi
  refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by
    have := Nat.floor_mono h; omega)) fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem psiR_le {y : ℝ} (hy : 0 ≤ y) : psiR y ≤ 4 * y := by
  unfold psiR
  have := psi_le_four ⌊y⌋₊
  have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  linarith

theorem psiR_nonneg (y : ℝ) : 0 ≤ psiR y := by
  unfold psiR psi
  exact sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-! ## Gaussian tails -/

/-- `∫_{−K}^{K} g ≥ 1 − 2e^{−K²/2}` (Chernoff). -/
theorem integral_gpdf_sym_ge {K : ℝ} (hK : 0 ≤ K) :
    1 - 2 * Real.exp (-(K ^ 2 / 2)) ≤ ∫ z in (-K)..K, gpdf z := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  have hmaj : ∀ z : ℝ, gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) -
      gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) ≤ (Ioc (-K) K).indicator gpdf z := by
    intro z
    have g0 := gpdf_nonneg z
    by_cases hz : z ∈ Ioc (-K) K
    · rw [indicator_of_mem hz]
      have := Real.exp_pos (K * z); have := Real.exp_pos (-K ^ 2); have := Real.exp_pos ((-K) * z)
      have : 0 ≤ gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) := by positivity
      have : 0 ≤ gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) := by positivity
      linarith
    · rw [indicator_of_notMem hz]
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hz
      rcases hz with h | h
      · -- `z ≤ −K`
        have : 1 ≤ Real.exp ((-K) * z) * Real.exp (-K ^ 2) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have : 0 ≤ gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) := by positivity
        nlinarith
      · have : 1 ≤ Real.exp (K * z) * Real.exp (-K ^ 2) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have : 0 ≤ gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) := by positivity
        nlinarith
  have hi1 : Integrable fun z : ℝ => gpdf z := integrable_gpdf
  have hi2 : Integrable fun z : ℝ => gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) :=
    (integrable_gpdf_mul_exp K).mul_const (Real.exp (-K ^ 2))
  have hi3 : Integrable fun z : ℝ => gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) :=
    (integrable_gpdf_mul_exp (-K)).mul_const (Real.exp (-K ^ 2))
  have hi12 : Integrable fun z : ℝ => gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) := hi1.sub hi2
  have hint : Integrable fun z : ℝ => gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) -
      gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) := hi12.sub hi3
  have hle := integral_mono hint (integrable_gpdf.indicator measurableSet_Ioc) hmaj
  have hval : ∫ z, (gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) -
      gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2)) =
      1 - Real.exp (K ^ 2 / 2) * Real.exp (-K ^ 2) - Real.exp ((-K) ^ 2 / 2) * Real.exp (-K ^ 2) := by
    calc ∫ z, (gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2) -
          gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2))
        = (∫ z, (gpdf z - gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2))) -
            ∫ z, gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) := integral_sub hi12 hi3
      _ = ((∫ z, gpdf z) - ∫ z, gpdf z * Real.exp (K * z) * Real.exp (-K ^ 2)) -
            ∫ z, gpdf z * Real.exp ((-K) * z) * Real.exp (-K ^ 2) := by rw [integral_sub hi1 hi2]
      _ = _ := by
        rw [integral_gpdf, integral_mul_const, integral_mul_const, integral_gpdf_mul_exp,
          integral_gpdf_mul_exp]
  rw [hval] at hle
  have e : Real.exp (K ^ 2 / 2) * Real.exp (-K ^ 2) = Real.exp (-(K ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((-K) ^ 2 / 2) * Real.exp (-K ^ 2) = Real.exp (-(K ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e, e2] at hle
  linarith

end TernaryGoldbach.Explicit
