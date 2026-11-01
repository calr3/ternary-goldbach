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

/-! ## The sandwich -/

theorem gsm_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (u : ℝ) : 0 ≤ gsm a b δ u := by
  unfold gsm
  refine intervalIntegral.integral_nonneg ?_ fun z _ => gpdf_nonneg z
  apply div_le_div_of_nonneg_right _ hδ.le; linarith

theorem gsm_le_one {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (u : ℝ) : gsm a b δ u ≤ 1 := by
  unfold gsm
  rw [intervalIntegral.integral_of_le (div_le_div_of_nonneg_right (by linarith) hδ.le)]
  calc ∫ z in Ioc ((b - Real.log u) / δ) ((a - Real.log u) / δ), gpdf z ≤ ∫ z, gpdf z :=
        setIntegral_le_integral integrable_gpdf (Eventually.of_forall gpdf_nonneg)
    _ = 1 := integral_gpdf

/-- The smoothing is `≥ 1 − 2e^{−K²/2}` on `[e^{b + Kδ}, e^{a − Kδ}]`. -/
theorem gsm_ge {a b δ K u : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (h1 : Real.log u ≤ a - K * δ)
    (h2 : b + K * δ ≤ Real.log u) : 1 - 2 * Real.exp (-(K ^ 2 / 2)) ≤ gsm a b δ u := by
  refine (integral_gpdf_sym_ge hK).trans ?_
  unfold gsm
  have hlo : (b - Real.log u) / δ ≤ -K := by rw [div_le_iff₀ hδ]; linarith
  have hhi : K ≤ (a - Real.log u) / δ := by rw [le_div_iff₀ hδ]; linarith
  exact intervalIntegral.integral_mono_interval hlo (by linarith) hhi
    (Eventually.of_forall fun z => gpdf_nonneg z) (continuous_gpdf.intervalIntegrable _ _)

theorem SsumG_one_ofReal (f : ℝ → ℝ) (x : ℝ) :
    SsumG (1 : DirichletCharacter ℂ 1) (fun u => (f u : ℂ)) x = ((∑' n : ℕ, Λ n * f (n / x) : ℝ) : ℂ) := by
  unfold SsumG
  rw [Complex.ofReal_tsum]
  congr 1; funext n
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  push_cast; ring

/-- **Upper sandwich** (`a = Kδ`, `e^b = y₀/x`). -/
theorem sandwich_upper {δ K y0 x : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hy0 : 0 < y0) (hx : 0 < x)
    (hYx : y0 * Real.exp (K * δ) ≤ x)
    (hsum : Summable fun n : ℕ => Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x)) :
    (1 - 2 * Real.exp (-(K ^ 2 / 2))) * (psiR x - psiR (y0 * Real.exp (K * δ))) ≤
      ∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) := by
  set Y := y0 * Real.exp (K * δ) with hY
  set c := 1 - 2 * Real.exp (-(K ^ 2 / 2))
  have hY0 : 0 < Y := by positivity
  have hab : Real.log (y0 / x) ≤ K * δ := by
    have : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity)
      ((div_le_one hx).2 (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
    have : 0 ≤ K * δ := by positivity
    linarith
  have hnn : ∀ n : ℕ, 0 ≤ Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (gsm_nonneg hδ hab _)
  have hfl : ⌊Y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hYx
  set S := Finset.Ioc ⌊Y⌋₊ ⌊x⌋₊ with hS
  have h1 : ∑ n ∈ S, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) ≤
      ∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) :=
    hsum.sum_le_tsum S fun n _ => hnn n
  have h2 : ∑ n ∈ S, Λ n * c ≤ ∑ n ∈ S, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) := by
    refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
    have hnY : Y < n := by
      have := Nat.lt_floor_add_one Y
      have : (⌊Y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn1
      linarith
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn2).trans (Nat.floor_le hx.le)
    have hn0 : (0 : ℝ) < n := by linarith
    refine gsm_ge hδ hK ?_ ?_
    · have : Real.log (n / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx).2 hnx)
      linarith
    · rw [← Real.log_exp (K * δ), ← Real.log_mul (by positivity) (Real.exp_pos _).ne']
      apply Real.log_le_log (by positivity)
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]; linarith
  have h3 : ∑ n ∈ S, Λ n = psiR x - psiR Y := by
    unfold psiR psi
    have e : S = Finset.Ico (⌊Y⌋₊ + 1) (⌊x⌋₊ + 1) := by
      rw [hS]; ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sub _ (by omega)]
  rw [← sum_mul, h3] at h2
  linarith

/-- `φ(u) ≤ P(Z ≤ (a − log u)/δ)`. -/
theorem gsm_le_Iic {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (u : ℝ) :
    gsm a b δ u ≤ ∫ z in Iic ((a - Real.log u) / δ), gpdf z := by
  unfold gsm
  rw [intervalIntegral.integral_of_le (div_le_div_of_nonneg_right (by linarith) hδ.le)]
  exact setIntegral_mono_set integrable_gpdf.integrableOn (Eventually.of_forall gpdf_nonneg)
    (Eventually.of_forall Ioc_subset_Iic_self)

/-- **Lower sandwich** (`a = −Kδ`). -/
theorem sandwich_lower {δ K b x : ℝ} (hδ : 0 < δ) (hKδ : δ ≤ K) (hx : 0 < x) (hb : b ≤ -(K * δ)) :
    ∑' n : ℕ, Λ n * gsm (-(K * δ)) b δ (n / x) ≤ psiR x + 4 * x * Real.exp (-(K ^ 2 / 2)) := by
  set a := -(K * δ) with ha
  have hab : b ≤ a := hb
  have hnn : ∀ n : ℕ, 0 ≤ Λ n * gsm a b δ (n / x) := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (gsm_nonneg hδ hab _)
  set hi : ℕ → ℝ := fun n => (a - Real.log (n / x)) / δ with hhi
  -- the majorant
  set G : ℝ → ℝ := fun z => gpdf z * psiR (x * Real.exp (a - δ * z)) with hG
  set lam := K - δ with hlam
  have hlam0 : 0 ≤ lam := by linarith
  have hGle : ∀ z, G z ≤ gpdf z * psiR x + 4 * x * Real.exp (a - lam * K) * (gpdf z * Real.exp (-(δ + lam) * z)) := by
    intro z
    have g0 := gpdf_nonneg z
    have hpt : psiR (x * Real.exp (a - δ * z)) ≤ psiR x + 4 * x * Real.exp (a - lam * K) * Real.exp (-(δ + lam) * z) := by
      have hpos : 0 ≤ 4 * x * Real.exp (a - lam * K) * Real.exp (-(δ + lam) * z) := by positivity
      rcases le_or_gt (-K) z with hz | hz
      · have : x * Real.exp (a - δ * z) ≤ x := by
          apply mul_le_of_le_one_right hx.le; rw [Real.exp_le_one_iff]; rw [ha]; nlinarith
        linarith [psiR_mono this]
      · have h4 := psiR_le (y := x * Real.exp (a - δ * z)) (by positivity)
        have : 4 * (x * Real.exp (a - δ * z)) ≤ 4 * x * Real.exp (a - lam * K) * Real.exp (-(δ + lam) * z) := by
          have e : 4 * x * Real.exp (a - lam * K) * Real.exp (-(δ + lam) * z) =
              4 * x * Real.exp (a - lam * K + -(δ + lam) * z) := by rw [Real.exp_add]; ring
          rw [e, show 4 * (x * Real.exp (a - δ * z)) = 4 * x * Real.exp (a - δ * z) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.2; nlinarith
        linarith [psiR_nonneg x]
    calc G z = gpdf z * psiR (x * Real.exp (a - δ * z)) := rfl
      _ ≤ gpdf z * (psiR x + 4 * x * Real.exp (a - lam * K) * Real.exp (-(δ + lam) * z)) :=
          mul_le_mul_of_nonneg_left hpt g0
      _ = _ := by ring
  have hmaj_int : Integrable fun z => gpdf z * psiR x + 4 * x * Real.exp (a - lam * K) * (gpdf z * Real.exp (-(δ + lam) * z)) :=
    (integrable_gpdf.mul_const _).add ((integrable_gpdf_mul_exp _).const_mul _)
  have hmaj_val : ∫ z, (gpdf z * psiR x + 4 * x * Real.exp (a - lam * K) * (gpdf z * Real.exp (-(δ + lam) * z))) =
      psiR x + 4 * x * Real.exp (-(K ^ 2 / 2)) := by
    rw [integral_add (integrable_gpdf.mul_const _) ((integrable_gpdf_mul_exp _).const_mul _), integral_mul_const,
      integral_gpdf, one_mul, integral_const_mul, integral_gpdf_mul_exp, mul_assoc, ← Real.exp_add]
    congr 3
    rw [hlam, ha]; ring
  have hGmeas : AEStronglyMeasurable G volume := by
    have h1 : Measurable fun z : ℝ => psiR (x * Real.exp (a - δ * z)) :=
      psiR_mono.measurable.comp (by fun_prop)
    exact (continuous_gpdf.measurable.mul h1).aestronglyMeasurable
  have hGint : Integrable G := by
    refine hmaj_int.mono' hGmeas (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gpdf_nonneg z) (psiR_nonneg _))]
    exact hGle z
  have hGbound : ∫ z, G z ≤ psiR x + 4 * x * Real.exp (-(K ^ 2 / 2)) := by
    rw [← hmaj_val]; exact integral_mono hGint hmaj_int hGle
  -- partial sums
  refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
  refine le_trans ?_ hGbound
  have hterm : ∀ n : ℕ, Λ n * gsm a b δ (n / x) ≤ Λ n * ∫ z, (Iic (hi n)).indicator gpdf z := by
    intro n
    refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
    rw [integral_indicator measurableSet_Iic]
    exact gsm_le_Iic hδ hab _
  refine (sum_le_sum fun n _ => hterm n).trans ?_
  have hint_n : ∀ n ∈ range N, Integrable fun z => Λ n * (Iic (hi n)).indicator gpdf z :=
    fun n _ => (integrable_gpdf.indicator measurableSet_Iic).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum _ hint_n]
  refine integral_mono (integrable_finset_sum _ hint_n) hGint fun z => ?_
  -- pointwise
  show ∑ n ∈ range N, Λ n * (Iic (hi n)).indicator gpdf z ≤ gpdf z * psiR (x * Real.exp (a - δ * z))
  have hY : 0 < x * Real.exp (a - δ * z) := by positivity
  calc ∑ n ∈ range N, Λ n * (Iic (hi n)).indicator gpdf z
      ≤ ∑ n ∈ range (⌊x * Real.exp (a - δ * z)⌋₊ + 1), Λ n * gpdf z := by
        rw [← sum_filter_add_sum_filter_not (range N) (fun n : ℕ => n ≤ ⌊x * Real.exp (a - δ * z)⌋₊)]
        have hz2 : ∑ n ∈ (range N).filter (fun n : ℕ => ¬ n ≤ ⌊x * Real.exp (a - δ * z)⌋₊),
            Λ n * (Iic (hi n)).indicator gpdf z = 0 := by
          refine sum_eq_zero fun n hn => ?_
          obtain ⟨-, hn⟩ := Finset.mem_filter.1 hn
          push Not at hn
          have hn1 : 1 ≤ n := by omega
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          rw [indicator_of_notMem, mul_zero]
          rw [Set.mem_Iic, not_le, hhi]
          simp only
          rw [div_lt_iff₀ hδ]
          have : x * Real.exp (a - δ * z) < n := by
            have := Nat.lt_floor_add_one (x * Real.exp (a - δ * z))
            have : ((⌊x * Real.exp (a - δ * z)⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
            linarith
          have := Real.log_lt_log hY this
          rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp] at this
          rw [Real.log_div hn0.ne' hx.ne']
          linarith
        rw [hz2, add_zero]
        refine (sum_le_sum fun n _ => ?_).trans (sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (gpdf_nonneg z))
        · refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
          exact indicator_le_self' (fun _ _ => (gpdf_nonneg z)) z
        · intro n hn
          rw [Finset.mem_filter] at hn
          rw [Finset.mem_range]; omega
    _ = gpdf z * psiR (x * Real.exp (a - δ * z)) := by
        rw [← sum_mul, mul_comm]; rfl

end TernaryGoldbach.Explicit
