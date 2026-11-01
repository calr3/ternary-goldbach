import TernaryGoldbach.Explicit.GMellin
import TernaryGoldbach.Explicit.RectResidue
import TernaryGoldbach.Explicit.LogDerivL

/-!
# The explicit formula ([B, Lemma 9.1.1] for `η(t) = t² e^{−t²/2}`)

Part A: `S = Σ_n Λ(n) χ(n) e(δn/x) η(n/x) = (1/2π) ∫ (−L'/L)(3/2 + it) G_δ(3/2 + it) x^{3/2+it} dt`
(Mellin inversion for each `n`, then the sum and the integral are interchanged).
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval

namespace TernaryGoldbach.Explicit

theorem integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|))) := by
  set K := max 1 (2 / c ^ 2) with hK
  refine (integrable_inv_one_add_sq.const_mul K).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le (abs_nonneg t))
  have h2 : 1 + c ^ 2 * t ^ 2 / 2 ≤ Real.exp (c * |t|) := by
    have : (c * |t|) ^ 2 = c ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
    nlinarith [mul_nonneg hc.le (abs_nonneg t)]
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK2 : 2 / c ^ 2 ≤ K := le_max_right _ _
  have h3 : 1 + t ^ 2 ≤ K * (1 + c ^ 2 * t ^ 2 / 2) := by
    have : t ^ 2 ≤ K * (c ^ 2 * t ^ 2 / 2) := by
      have hc2 : 0 < c ^ 2 := by positivity
      calc t ^ 2 = (2 / c ^ 2) * (c ^ 2 * t ^ 2 / 2) := by field_simp
        _ ≤ K * (c ^ 2 * t ^ 2 / 2) := mul_le_mul_of_nonneg_right hK2 (by positivity)
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (Real.exp_pos _) (by positivity), one_mul]
  nlinarith [Real.exp_pos (c * |t|)]

theorem continuous_G_line (δ σ : ℝ) (hσ : -2 < σ) : Continuous fun t : ℝ => Gr ((σ : ℂ) + t * I) δ 0 :=
  continuous_iff_continuousAt.2 fun t =>
    ((differentiableAt_G δ (by simpa using hσ)).continuousAt).comp (by fun_prop)

theorem integrable_G_line (δ σ : ℝ) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) :
    Integrable fun t : ℝ => Gr ((σ : ℂ) + t * I) δ 0 := by
  refine ((integrable_exp_neg_abs (c := 0.28) (by norm_num)).const_mul (Kδ δ)).mono'
    (continuous_G_line δ σ (by linarith)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have := norm_G_le_strip δ (s := (σ : ℂ) + t * I) (by simpa using h1) (by simpa using h2)
  simpa using this

/-- Mellin inversion for `fδ` on `ℜs = 3/2`. -/
theorem fδ_eq_mellinInv (δ : ℝ) {y : ℝ} (hy : 0 < y) :
    fδ δ y = (1 / (2 * π)) • ∫ t : ℝ, (y : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I)) •
      Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0 := by
  have hconv : MellinConvergent (fδ δ) ((3 / 2 : ℝ) : ℂ) :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -2) one_pos
      ((continuous_fδ δ).locallyIntegrable.locallyIntegrableOn _) (fδ_isBigO_top δ) (fδ_isBigO_bot δ)
      (by norm_num)
  have hvert : Complex.VerticalIntegrable (mellin (fδ δ)) (3 / 2) := by
    have e : mellin (fδ δ) = fun s => Gr s δ 0 := funext (mellin_fδ δ)
    rw [Complex.VerticalIntegrable, e]
    exact integrable_G_line δ (3 / 2) (by norm_num) le_rfl
  have h := mellinInv_mellin_eq (3 / 2) (fδ δ) hy hconv hvert (continuous_fδ δ).continuousAt
  rw [← h, mellinInv]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [mellin_fδ]

/-- `S_χ(δ, x) = Σ_n Λ(n) χ(n) e(δn/x) η(n/x)`, `η(t) = t² e^{−t²/2}`. -/
noncomputable def Ssum {N : ℕ} (χ : DirichletCharacter ℂ N) (δ x : ℝ) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) * χ n * fδ δ (n / x)

/-- `−L'/L(s) G_δ(s) x^s`. -/
noncomputable def Fline {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ x : ℝ) (s : ℂ) : ℂ :=
  -(deriv χ.LFunction s / χ.LFunction s) * Gr s δ 0 * (x : ℂ) ^ s

theorem norm_ratio_cpow {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(((n : ℝ) / x : ℝ) : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I))‖ = ((n : ℝ) / x) ^ (-(3 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- The integrand of the `n`-th term on `ℜs = 3/2`. -/
noncomputable def Fterm (δ x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (((n : ℝ) / x : ℝ) : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I)) * Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0

theorem fδ_eq_integral_Fterm (δ : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    fδ δ (n / x) = (1 / (2 * π) : ℂ) * ∫ t, Fterm δ x n t := by
  rw [fδ_eq_mellinInv δ (by positivity : (0:ℝ) < n / x), Complex.real_smul]
  congr 1
  push_cast; ring

theorem integrable_Fterm (δ : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    Integrable (Fterm δ x n) := by
  have hGi := integrable_G_line δ (3 / 2) (by norm_num) le_rfl
  have hGc := continuous_G_line δ (3 / 2) (by norm_num)
  refine (hGi.norm.const_mul (((n : ℝ) / x) ^ (-(3 / 2 : ℝ)))).mono' ?_ (Eventually.of_forall fun t => ?_)
  · refine (Continuous.mul ?_ hGc).aestronglyMeasurable
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (continuousAt_const_cpow (Complex.ofReal_ne_zero.2
      (by positivity : (0:ℝ) < n / x).ne')).comp (by fun_prop)
  · rw [Fterm, norm_mul, norm_ratio_cpow hn hx]

theorem integral_norm_Fterm (δ : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    ∫ t, ‖Fterm δ x n t‖ = ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) *
      ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖ := by
  have e : ∀ t, ‖Fterm δ x n t‖ = ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) *
      ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖ := by
    intro t
    rw [Fterm, norm_mul, norm_ratio_cpow hn hx, Real.div_rpow (Nat.cast_nonneg n) hx.le,
      Real.rpow_neg hx.le, div_inv_eq_mul]
  simp_rw [e]
  rw [integral_const_mul]

/-- `Σ_n Λ(n)χ(n) (n/x)^{−s} = x^s (−L'/L)(s)` on `ℜs = 3/2`. -/
theorem tsum_Fterm_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ : ℝ) {x : ℝ} (hx : 0 < x)
    (t : ℝ) : ∑' n : ℕ, (Λ n : ℂ) * χ n * Fterm δ x n t =
      Fline χ δ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I with hs
  have hs1 : 1 < s.re := by simp [hs]; norm_num
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs1
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs1,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1] at hL
  rw [neg_div] at hL
  rw [Fline, ← hL, LSeries, mul_assoc, ← tsum_mul_right]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', Fterm, ← hs, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg n) hx.le, Complex.cpow_neg, Complex.cpow_neg]
    have hn0 : ((n : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast hn.ne'
    have hx0 : ((x : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast hx.ne'
    simp only [Pi.mul_apply, Complex.ofReal_natCast] at hn0 ⊢
    field_simp

/-- **Part A**: `S = (1/2π) ∫ (−L'/L)(3/2+it) G_δ(3/2+it) x^{3/2+it} dt`. -/
theorem Ssum_eq_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    Ssum χ δ x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, Fline χ δ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  set F : ℕ → ℝ → ℂ := fun n t => (Λ n : ℂ) * χ n * Fterm δ x n t with hF
  have hterm : ∀ n : ℕ, (Λ n : ℂ) * χ n * fδ δ (n / x) = (1 / (2 * π) : ℂ) * ∫ t, F n t := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · rw [fδ_eq_integral_Fterm δ hx hn, hF]
      simp only
      rw [integral_const_mul]; ring
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : F 0 = fun _ => 0 := by ext t; simp [hF]
      rw [this]; exact integrable_zero _ _ _
    · exact (integrable_Fterm δ hx hn).const_mul _
  have hFs : Summable fun n => ∫ t, ‖F n t‖ := by
    have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
    have hΛ' : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      refine hΛ.norm.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      split_ifs with h0
      · simp [h0]
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        simp
    refine (hΛ'.mul_right (x ^ (3 / 2 : ℝ) * ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖)).of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · have e : ∀ t, ‖F n t‖ = (Λ n * ‖χ n‖) * ‖Fterm δ x n t‖ := by
        intro t
        rw [hF]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simp_rw [e]
      rw [integral_const_mul, integral_norm_Fterm δ hx hn]
      have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hG0 : 0 ≤ ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖ := integral_nonneg fun t => norm_nonneg _
      have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hn0 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by positivity
      calc Λ n * ‖χ n‖ * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖)
          ≤ Λ n * 1 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖) := by gcongr
        _ = Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖Gr (((3 / 2 : ℝ) : ℂ) + t * I) δ 0‖) := by ring
  rw [Ssum, tsum_congr hterm, tsum_mul_left, integral_tsum_of_summable_integral_norm hFi hFs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  exact tsum_Fterm_eq χ δ hx t

/-! ## Part B: no zeros in `−1 < ℜs < 0`, and the rectangle identity -/

theorem gammaFactor_ne_zero_strip {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (h1 : -1 < z.re)
    (h2 : z.re < 0) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at this; linarith
    · have : (1:ℝ) ≤ n := by exact_mod_cast hpos
      linarith
  · rw [ho.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at this; linarith
    · have : (1:ℝ) ≤ n := by exact_mod_cast hpos
      linarith

/-- **`L(z, χ) ≠ 0` for `−1 < ℜz < 0`** (`χ` primitive, `≠ 1`): the functional equation, with no
pole of the gamma factor there. -/
theorem LFunction_ne_zero_strip {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {z : ℂ} (h1 : -1 < z.re) (h2 : z.re < 0) : χ.LFunction z ≠ 0 := by
  have hN : N ≠ 1 := by
    rintro rfl; exact hχ1 (Subsingleton.elim _ _)
  set s := 1 - z with hs
  have hz : z = 1 - s := by rw [hs]; ring
  have hsre : 1 < s.re := by simp [hs]; linarith
  have hχi : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.1 h)
  have hGs0 : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
    rcases χ⁻¹.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ s =
      DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inr hN)]
    field_simp
  have hL : χ.LFunction z = (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
      (DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s) /
        DirichletCharacter.gammaFactor χ (1 - s) := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN), hz,
      hχ.completedLFunction_one_sub s, hΛ]
  rw [hL]
  have hNp : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast NeZero.ne N
  have hε : DirichletCharacter.rootNumber χ ≠ 0 := by
    intro h; have := norm_rootNumber hχ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hLs : χ⁻¹.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) hsre.le
  have hG1 : DirichletCharacter.gammaFactor χ (1 - s) ≠ 0 := by
    rw [← hz]; exact gammaFactor_ne_zero_strip χ h1 h2
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hNp hε) (mul_ne_zero hGs0 hLs)) hG1

/-- The rectangle `[−1/2, 3/2] × [−T, T]`: corners. -/
noncomputable def zT (T : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + (-T : ℝ) * I
noncomputable def wT (T : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + (T : ℝ) * I

@[simp] theorem zT_re (T : ℝ) : (zT T).re = -1 / 2 := by simp [zT]
@[simp] theorem zT_im (T : ℝ) : (zT T).im = -T := by simp [zT]
@[simp] theorem wT_re (T : ℝ) : (wT T).re = 3 / 2 := by simp [wT]
@[simp] theorem wT_im (T : ℝ) : (wT T).im = T := by simp [wT]

/-- The radius used for the factorization: `R_T = 2(T + 3)`. -/
noncomputable def RT (T : ℝ) : ℝ := 2 * (T + 3)

/-- The zeros strictly inside the rectangle `[−1/2, 3/2] × [−T, T]`, with multiplicity. -/
noncomputable def zerosRect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Finset ℂ :=
  (zerosIn χ.LFunction 2 (RT T) (RT T / 2)).filter
    (fun u => (zT T).re < u.re ∧ u.re < (wT T).re ∧ (zT T).im < u.im ∧ u.im < (wT T).im)

noncomputable def multRect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) (u : ℂ) : ℕ :=
  (divB χ.LFunction 2 (RT T) u).toNat

/-- **Part B**: the residue theorem on `[−1/2, 3/2] × [−T, T]`, if `L` has no zeros on the horizontal
sides. -/
theorem rect_identity {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 < T)
    (hbot : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], χ.LFunction ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) :
    rectInt (fun s => logDeriv χ.LFunction s * (Gr s δ 0 * (x : ℂ) ^ s)) (zT T) (wT T) =
      2 * π * I * ∑ u ∈ zerosRect χ T, (multRect χ T u : ℂ) * (Gr u δ 0 * (x : ℂ) ^ u) := by
  have hf : Differentiable ℂ χ.LFunction := DirichletCharacter.differentiable_LFunction hχ1
  have hf2 : χ.LFunction 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ Metric.ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, zT_im, wT_im, Set.uIcc_of_le (by norm_num),
      Set.uIcc_of_le (by linarith)] at hs
    rw [Metric.mem_ball, dist_eq_norm, RT]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
    have h1 : |s.re - 2| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2]
    have h2 : |s.im| ≤ T := by rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2]
    linarith
  have hbd : NoZerosOnSides χ.LFunction (zT T) (wT T) := by
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun y _ => ?_, fun y _ => ?_⟩
    · rw [zT_re, wT_re] at hσ; simpa using hbot σ hσ
    · rw [zT_re, wT_re] at hσ; simpa using htop σ hσ
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; norm_num)
    · exact LFunction_ne_zero_strip hχ hχ1 (by simp; norm_num) (by simp; norm_num)
  set U : Set ℂ := {s | -2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsubU : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, Set.uIcc_of_le (by norm_num)] at hs
    show -2 < s.re; linarith [hs.1.1]
  have hh : DifferentiableOn ℂ (fun s => Gr s δ 0 * (x : ℂ) ^ s) U := by
    intro s hs
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact ((differentiableAt_G δ hs).mul
      (differentiableAt_id.const_cpow (Or.inl hx0))).differentiableWithinAt
  exact rectInt_logDeriv_mul hf hR hf2 (by simp; norm_num) (by simp; linarith) hrect hbd hUo hsubU hh

/-! ## Part C: good heights -/

/-- In `[k, k+1]` there is a point at distance `≥ 1/(2M+2)` from each of `M` given reals. -/
theorem exists_far_point (A : Finset ℝ) (k : ℝ) :
    ∃ T ∈ Icc k (k + 1), ∀ a ∈ A, 1 / (2 * (A.card : ℝ) + 2) ≤ |T - a| := by
  set δ := 1 / (2 * (A.card : ℝ) + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  by_contra hcon
  push Not at hcon
  have hsub : Icc k (k + 1) ⊆ ⋃ a ∈ A, Ioo (a - δ) (a + δ) := by
    intro T hT
    obtain ⟨a, ha, h⟩ := hcon T hT
    rw [Set.mem_iUnion₂]
    refine ⟨a, ha, ?_⟩
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have h1 := MeasureTheory.measure_mono (μ := volume) hsub
  have h2 := MeasureTheory.measure_biUnion_finset_le (μ := volume) A fun a => Ioo (a - δ) (a + δ)
  simp only [Real.volume_Icc, Real.volume_Ioo, add_sub_cancel_left] at h1 h2
  have h3 : ∑ a ∈ A, ENNReal.ofReal (a + δ - (a - δ)) = A.card * ENNReal.ofReal (2 * δ) := by
    have e : ∀ a ∈ A, ENNReal.ofReal (a + δ - (a - δ)) = ENNReal.ofReal (2 * δ) := fun a _ => by
      congr 1; ring
    rw [Finset.sum_congr rfl e]; simp
  rw [h3] at h2
  have h4 := h1.trans h2
  have hlt : (A.card : ENNReal) * ENNReal.ofReal (2 * δ) < ENNReal.ofReal 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 ?_
    rw [hδ]
    have : (0:ℝ) < 2 * (A.card : ℝ) + 2 := by positivity
    rw [show (A.card : ℝ) * (2 * (1 / (2 * (A.card : ℝ) + 2))) = 2 * A.card / (2 * A.card + 2) by
      field_simp]
    rw [div_lt_one this]; linarith
  exact absurd h4 (not_le.2 hlt)

/-! ## Divisor bookkeeping for entire functions -/

theorem divB_eq_of_mem {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c c' u : ℂ} {R R' : ℝ}
    (hu : u ∈ Metric.closedBall c R) (hu' : u ∈ Metric.closedBall c' R') :
    divB f c R u = divB f c' R' u := by
  rw [divB, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c R)) hu,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c' R')) hu']

/-- `Σ_{u ∈ zerosIn f c R r} m_u ≤ Σᶠ divisor(closedBall c |r|)` (for `r ≤ R`). -/
theorem sum_zerosIn_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {R r : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) :
    ((∑ u ∈ zerosIn f c R r, (divB f c R u).toNat : ℕ) : ℝ) ≤
      ((∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall c |r|) u : ℤ) : ℝ) := by
  set D := MeromorphicOn.divisor f (Metric.closedBall c |r|)
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall c |r|) := fun z _ => hf.analyticAt z
  have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa) u
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c |r|)
  have hS : zerosIn f c R r ⊆ hfin.toFinset := by
    intro u hu
    obtain ⟨hur, hu0⟩ := mem_zerosIn hu
    have hu1 : u ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have hu2 : u ∈ Metric.closedBall c |r| := by
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr]; linarith
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [divB_eq_of_mem hf hu1 hu2] at hu0
    exact hu0
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  push_cast
  have e : ∀ u ∈ zerosIn f c R r, ((divB f c R u).toNat : ℝ) = (D u : ℝ) := by
    intro u hu
    obtain ⟨hur, -⟩ := mem_zerosIn hu
    have hu1 : u ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have hu2 : u ∈ Metric.closedBall c |r| := by
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr]; linarith
    rw [divB_eq_of_mem hf hu1 hu2]
    have := hDnn u
    exact_mod_cast Int.toNat_of_nonneg this
  rw [Finset.sum_congr rfl e]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS fun u _ _ => by exact_mod_cast hDnn u

/-- **`L'/L` on a horizontal segment**: if `z` (with `|z − (2 + iT)| ≤ 5/2`) is at distance `≥ δ` from
every zero `u` with `|u − (2 + iT)| < 5`, then
`|L'/L(z)| ≤ (log(B_T/0.355)/log 2)/δ + 4.8 log(B_T/0.355)`. -/
theorem norm_logDeriv_L_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (2 + T * I) (10 / 4)) {δ : ℝ}
    (hδ : 0 < δ) (hfar : ∀ u ∈ zerosIn χ.LFunction (2 + T * I) 10 (10 / 2), δ ≤ ‖z - u‖)
    (hLz : χ.LFunction z ≠ 0) :
    ‖logDeriv χ.LFunction z‖ ≤
      Real.log (BT N T / 0.355) / Real.log 2 / δ + 4.8 * Real.log (BT N T / 0.355) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ1
  have h1 := logDeriv_L_near hχ hχ1 hz hLz
  set Z := zerosIn χ.LFunction (2 + T * I) 10 (10 / 2)
  have hsum : ‖∑ u ∈ Z, ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ ≤
      (∑ u ∈ Z, (divB χ.LFunction (2 + T * I) 10 u).toNat : ℕ) / δ := by
    refine (norm_sum_le _ _).trans ?_
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (by positivity) hδ (hfar u hu)
  have hcnt := sum_zerosIn_le hf (c := 2 + T * I) (R := 10) (r := 10 / 2) (by norm_num) (by norm_num)
  have h5 := zero_count_5 hχ hχ1 T
  rw [show (10 : ℝ) / 2 = 5 by norm_num] at hcnt
  have hcnt' : ((∑ u ∈ Z, (divB χ.LFunction (2 + T * I) 10 u).toNat : ℕ) : ℝ) ≤
      Real.log (BT N T / 0.355) / Real.log 2 := by
    have : Z = zerosIn χ.LFunction (2 + T * I) 10 5 := by
      simp only [Z]; norm_num
    rw [this]; exact hcnt.trans h5
  calc ‖logDeriv χ.LFunction z‖
      ≤ ‖∑ u ∈ Z, ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ +
          ‖logDeriv χ.LFunction z - ∑ u ∈ Z, ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ := by
        have := norm_add_le (∑ u ∈ Z, ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u))
          (logDeriv χ.LFunction z - ∑ u ∈ Z, ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u))
        rwa [add_sub_cancel] at this
    _ ≤ Real.log (BT N T / 0.355) / Real.log 2 / δ + 4.8 * Real.log (BT N T / 0.355) := by
        refine add_le_add (hsum.trans ?_) h1
        exact div_le_div_of_nonneg_right hcnt' hδ.le

/-- A zero of `L` near `c` lies in `zerosIn`. -/
theorem mem_zerosIn_of_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {c u : ℂ}
    {R r : ℝ} (hrR : r ≤ R) (hu : ‖u - c‖ < r) (hLu : χ.LFunction u = 0) :
    u ∈ zerosIn χ.LFunction c R r := by
  have hf := DirichletCharacter.differentiable_LFunction hχ1
  have huR : u ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  rw [zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]
  refine ⟨?_, hu⟩
  rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall c R)) huR]
  intro h
  have hord : analyticOrderAt χ.LFunction u ≠ 0 := by
    rw [Ne, (hf.analyticAt u).analyticOrderAt_eq_zero]; exact not_not.2 hLu
  have hfin : analyticOrderAt χ.LFunction u ≠ ⊤ := by
    have h2 : χ.LFunction 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)
    have hc0 : analyticOrderAt χ.LFunction 2 ≠ ⊤ := by
      rw [(hf.analyticAt 2).analyticOrderAt_eq_zero.2 h2]; simp
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ χ.LFunction Set.univ)
      isPreconnected_univ (Set.mem_univ 2) (Set.mem_univ u) hc0
  apply hord
  revert h
  cases hk : analyticOrderAt χ.LFunction u with
  | top => exact absurd hk hfin
  | coe n => simp

/-- **`L'/L` on the line `ℜs = −1/2`**: `|L'/L(−1/2 + iy)| ≤ (2/log 2 + 4.8) log(B_y/0.355)`. -/
theorem norm_logDeriv_L_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (y : ℝ) :
    ‖logDeriv χ.LFunction (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Real.log (BT N y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (BT N y / 0.355) := by
  set z : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hz
  have hzc : z ∈ Metric.closedBall (2 + y * I) (10 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hz]
    have : ((-1 / 2 : ℝ) : ℂ) + y * I - (2 + y * I) = ((-5 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hLz : χ.LFunction z ≠ 0 := LFunction_ne_zero_strip hχ hχ1 (by simp [hz]; norm_num)
    (by simp [hz]; norm_num)
  refine norm_logDeriv_L_le hχ hχ1 hzc (by norm_num) (fun u hu => ?_) hLz
  have hLu : χ.LFunction u = 0 := by
    have hf := DirichletCharacter.differentiable_LFunction hχ1
    obtain ⟨hur, hu0⟩ := mem_zerosIn hu
    have huR : u ∈ Metric.closedBall (2 + y * I) 10 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall _ 10)) huR] at hu0
    by_contra hne
    exact hu0 (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
  have hre : u.re ≤ -1 ∨ 0 ≤ u.re := by
    by_contra hcon
    push Not at hcon
    exact LFunction_ne_zero_strip hχ hχ1 hcon.1 hcon.2 hLu
  have := Complex.abs_re_le_norm (z - u)
  have hzre : z.re = -1 / 2 := by simp [hz]
  rw [Complex.sub_re, hzre] at this
  rcases hre with h | h
  · rw [abs_of_nonneg (by linarith)] at this; linarith
  · rw [abs_of_nonpos (by linarith)] at this; linarith

/-- Jensen with radii `r < 10`: at most `log(B_T/0.355)/log(10/r)` zeros in `|ρ − (2 + iT)| ≤ r`. -/
theorem zero_count_r {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (T : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) :
    ((∑ᶠ u, MeromorphicOn.divisor χ.LFunction (Metric.closedBall (2 + T * I) |r|) u : ℤ) : ℝ) ≤
      Real.log (BT N T / 0.355) / Real.log (10 / r) := by
  have hc := norm_L_center_ge χ T
  have hc0 : χ.LFunction (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := one_le_BT (N := N) T
  have hf : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  have h := hf.sum_divisor_le (r := r) (R := 10) (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 10)]; exact hr10) (by linarith) hc0
    (fun w hw => norm_L_le_BT hχ hχ1 (Metric.sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < BT N T / ‖χ.LFunction (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (BT N T / ‖χ.LFunction (2 + T * I)‖) ≤ Real.log (BT N T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith))

theorem BT_mono {N : ℕ} [NeZero N] {T T' : ℝ} (h : |T| ≤ |T'|) : BT N T ≤ BT N T' := by
  unfold BT
  have hN : (0:ℝ) ≤ 512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by positivity
  refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hN)
    (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])) (Real.exp_pos _).le (by positivity)

theorem LB_mono {N : ℕ} [NeZero N] {T T' : ℝ} (h : |T| ≤ |T'|) :
    Real.log (BT N T / 0.355) ≤ Real.log (BT N T' / 0.355) := by
  have hB := one_le_BT (N := N) T
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (BT_mono h) (by norm_num))

theorem card_zerosIn_le {f : ℂ → ℂ} {c : ℂ} {R r : ℝ} (hf : Differentiable ℂ f) :
    ((zerosIn f c R r).card : ℝ) ≤ ((∑ u ∈ zerosIn f c R r, (divB f c R u).toNat : ℕ) : ℝ) := by
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall c R) := fun z _ => hf.analyticAt z
  have hDnn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa
  rw [Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun u hu => ?_
  have h0 := (mem_zerosIn hu).2
  have hnn : 0 ≤ divB f c R u := hDnn u
  have : 1 ≤ (divB f c R u).toNat := by omega
  exact_mod_cast this

/-- The height bound: `H_k = log(B_{k+1}/0.355)·((2A_k + 2)/log 2 + 4.8)`,
`A_k = 2 log(B_{k+1}/0.355)/log(10/6)`. -/
noncomputable def Hk (N : ℕ) (k : ℕ) : ℝ :=
  Real.log (BT N (k + 1) / 0.355) *
    ((2 * (2 * Real.log (BT N (k + 1) / 0.355) / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8)

/-- **Good heights**: in `[k, k+1]` there is `T` such that `L` has no zeros on the horizontal sides
`ℑs = ±T`, `−1/2 ≤ ℜs ≤ 3/2`, and `|L'/L| ≤ H_k` there. -/
theorem good_height {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (k : ℕ) :
    ∃ T ∈ Icc (k : ℝ) (k + 1), ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      (χ.LFunction ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 ∧
        χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (‖logDeriv χ.LFunction ((σ : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤ Hk N k ∧
        ‖logDeriv χ.LFunction ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ Hk N k) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ1
  set k' : ℝ := k + 1 / 2 with hk'
  set Wp := zerosIn χ.LFunction (2 + (k' : ℂ) * I) 12 6 with hWp
  set Wm := zerosIn χ.LFunction (2 + ((-k' : ℝ) : ℂ) * I) 12 6 with hWm
  set A : Finset ℝ := Wp.image Complex.im ∪ Wm.image (fun u => -u.im) with hA
  set LBk := Real.log (BT N (k + 1) / 0.355) with hLBk
  have hLB0 : 0 < LBk := by
    have := one_le_BT (N := N) ((k : ℝ) + 1)
    exact Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlog106 : 0 < Real.log (10 / 6) := Real.log_pos (by norm_num)
  -- `|A| ≤ A_k`
  have hcardW : ∀ (T0 : ℝ), |T0| ≤ (k : ℝ) + 1 →
      ((zerosIn χ.LFunction (2 + (T0 : ℂ) * I) 12 6).card : ℝ) ≤ LBk / Real.log (10 / 6) := by
    intro T0 hT0
    refine (card_zerosIn_le hf).trans ?_
    refine (sum_zerosIn_le hf (by norm_num) (by norm_num)).trans ?_
    refine (zero_count_r hχ hχ1 T0 (by norm_num) (by norm_num)).trans ?_
    exact div_le_div_of_nonneg_right (LB_mono (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ k + 1)]; exact hT0))
      hlog106.le
  have hk'abs : |k'| ≤ (k : ℝ) + 1 := by rw [hk', abs_of_nonneg (by positivity)]; linarith
  have hAcard : (A.card : ℝ) ≤ 2 * LBk / Real.log (10 / 6) := by
    have h1 : (A.card : ℝ) ≤ Wp.card + Wm.card := by
      have := Finset.card_union_le (Wp.image Complex.im) (Wm.image (fun u => -u.im))
      have h2 := Finset.card_image_le (s := Wp) (f := Complex.im)
      have h3 := Finset.card_image_le (s := Wm) (f := fun u : ℂ => -u.im)
      exact_mod_cast this.trans (add_le_add h2 h3)
    have hp : (Wp.card : ℝ) ≤ LBk / Real.log (10 / 6) := hcardW k' hk'abs
    have hm : (Wm.card : ℝ) ≤ LBk / Real.log (10 / 6) := hcardW (-k') (by rw [abs_neg]; exact hk'abs)
    have : (2 * LBk / Real.log (10 / 6)) = LBk / Real.log (10 / 6) + LBk / Real.log (10 / 6) := by ring
    linarith
  obtain ⟨T, hT, hfar⟩ := exists_far_point A k
  set δ := 1 / (2 * (A.card : ℝ) + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  set δk := 1 / (2 * (2 * LBk / Real.log (10 / 6)) + 2) with hδk
  have hδkδ : δk ≤ δ := by
    rw [hδk, hδ]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hδk0 : 0 < δk := by positivity
  have hTabs : |T| ≤ (k : ℝ) + 1 := by rw [abs_of_nonneg (by linarith [hT.1])]; exact hT.2
  refine ⟨T, hT, fun σ hσ => ?_⟩
  rw [Set.uIcc_of_le (by norm_num)] at hσ
  -- the two points
  have key : ∀ (S : ℝ), (S = T ∨ S = -T) →
      (∀ u ∈ zerosIn χ.LFunction (2 + (S : ℂ) * I) 10 (10 / 2), δ ≤ ‖((σ : ℂ) + (S : ℂ) * I) - u‖) := by
    intro S hS u hu
    have hLu : χ.LFunction u = 0 := by
      obtain ⟨hur, hu0⟩ := mem_zerosIn hu
      have huR : u ∈ Metric.closedBall (2 + (S : ℂ) * I) 10 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
        (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall _ 10)) huR] at hu0
      by_contra hne
      exact hu0 (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
    have hur := (mem_zerosIn hu).1
    have him := Complex.abs_im_le_norm (((σ : ℂ) + (S : ℂ) * I) - u)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_add, add_zero] at him
    rcases hS with hS | hS <;> subst S
    · -- `u ∈ Wp`, so `u.im ∈ A`
      have huW : u ∈ Wp := by
        refine mem_zerosIn_of_zero hχ1 (by norm_num) ?_ hLu
        have : ‖u - (2 + (k' : ℂ) * I)‖ ≤ ‖u - (2 + (T : ℂ) * I)‖ + ‖((T - k' : ℝ) : ℂ) * I‖ := by
          calc ‖u - (2 + (k' : ℂ) * I)‖ = ‖(u - (2 + (T : ℂ) * I)) + ((T - k' : ℝ) : ℂ) * I‖ := by
                congr 1; push_cast; ring
            _ ≤ _ := norm_add_le _ _
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        have hTk : |T - k'| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
        rw [show (10:ℝ) / 2 = 5 by norm_num] at hur
        linarith
      have := hfar u.im (Finset.mem_union_left _ (Finset.mem_image_of_mem _ huW))
      linarith
    · have huW : u ∈ Wm := by
        refine mem_zerosIn_of_zero hχ1 (by norm_num) ?_ hLu
        have : ‖u - (2 + ((-k' : ℝ) : ℂ) * I)‖ ≤ ‖u - (2 + ((-T : ℝ) : ℂ) * I)‖ +
            ‖((k' - T : ℝ) : ℂ) * I‖ := by
          calc ‖u - (2 + ((-k' : ℝ) : ℂ) * I)‖ =
              ‖(u - (2 + ((-T : ℝ) : ℂ) * I)) + ((k' - T : ℝ) : ℂ) * I‖ := by
                congr 1; push_cast; ring
            _ ≤ _ := norm_add_le _ _
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        have hTk : |k' - T| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
        rw [show (10:ℝ) / 2 = 5 by norm_num] at hur
        linarith
      have := hfar (-u.im) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ huW))
      rw [show T - -u.im = -(-T - u.im) by ring, abs_neg] at this
      linarith
  have hz : ∀ (S : ℝ), (S = T ∨ S = -T) →
      ((σ : ℂ) + (S : ℂ) * I) ∈ Metric.closedBall (2 + (S : ℂ) * I) (10 / 4) := by
    intro S _
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : (σ : ℂ) + (S : ℂ) * I - (2 + (S : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hne : ∀ (S : ℝ), (S = T ∨ S = -T) → χ.LFunction ((σ : ℂ) + (S : ℂ) * I) ≠ 0 := by
    intro S hS h0
    have hmem : ((σ : ℂ) + (S : ℂ) * I) ∈ zerosIn χ.LFunction (2 + (S : ℂ) * I) 10 (10 / 2) := by
      refine mem_zerosIn_of_zero hχ1 (by norm_num) ?_ h0
      have := hz S hS
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      linarith
    have := key S hS _ hmem
    rw [sub_self, norm_zero] at this
    linarith
  have hbound : ∀ (S : ℝ), (S = T ∨ S = -T) →
      ‖logDeriv χ.LFunction ((σ : ℂ) + (S : ℂ) * I)‖ ≤ Hk N k := by
    intro S hS
    have habs : |S| ≤ (k : ℝ) + 1 := by rcases hS with hS | hS <;> subst S <;> simp [hTabs]
    refine (norm_logDeriv_L_le hχ hχ1 (hz S hS) hδ0 (key S hS) (hne S hS)).trans ?_
    have hLB := LB_mono (N := N) (T := S) (T' := (k : ℝ) + 1)
      (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ k + 1)]; exact habs)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLBS0 : 0 ≤ Real.log (BT N S / 0.355) := by
      have := one_le_BT (N := N) S
      exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    unfold Hk
    rw [← hLBk] at hLB ⊢
    have h1 : Real.log (BT N S / 0.355) / Real.log 2 / δ ≤ LBk / Real.log 2 / δk := by
      gcongr
    have h2 : LBk / Real.log 2 / δk = LBk * ((2 * (2 * LBk / Real.log (10 / 6)) + 2) / Real.log 2) := by
      rw [hδk]; field_simp
    nlinarith
  exact ⟨⟨hne T (Or.inl rfl), hne (-T) (Or.inr rfl)⟩, hbound T (Or.inl rfl), hbound (-T) (Or.inr rfl)⟩

/-! ## Part C: the two vertical lines -/

/-- `h(s) = L'/L(s) G_δ(s) x^s` (the integrand of the residue theorem). -/
noncomputable def hInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ x : ℝ) (s : ℂ) : ℂ :=
  logDeriv χ.LFunction s * (Gr s δ 0 * (x : ℂ) ^ s)

theorem hInt_eq_neg_Fline {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ x : ℝ) (s : ℂ) :
    hInt χ δ x s = -Fline χ δ x s := by
  rw [hInt, Fline, logDeriv_apply]; ring

/-- `C₃ = Σ Λ(n) n^{−3/2}`. -/
noncomputable def C3 : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ))

theorem summable_C3 : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
  refine hΛ.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · simp [h0]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    simp

/-- `|L'/L(3/2 + iy)| ≤ C₃`. -/
theorem norm_logDeriv_L_right {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    ‖logDeriv χ.LFunction (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ C3 := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + y * I with hs
  have hs1 : 1 < s.re := by simp [hs]; norm_num
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs1
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs1,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1] at hL
  have e : logDeriv χ.LFunction s = -LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) s := by
    rw [hL, logDeriv_apply]; ring
  rw [e, norm_neg]
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine hsum.norm.tsum_le_tsum (fun n => ?_) summable_C3
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · simp [h0]
  · have hsre : s.re = 3 / 2 := by simp [hs]
    rw [hsre, Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
    have := DirichletCharacter.norm_le_one χ n
    have hp : 0 ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by positivity
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    calc ‖χ n‖ * Λ n * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ 1 * Λ n * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by gcongr
      _ = Λ n * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by ring

theorem norm_cpow_x {x : ℝ} (hx : 0 < x) (s : ℂ) : ‖(x : ℂ) ^ s‖ = x ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx s

theorem continuous_logDeriv_L_line {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (σ : ℝ) (hne : ∀ y : ℝ, χ.LFunction ((σ : ℂ) + y * I) ≠ 0) :
    Continuous fun y : ℝ => logDeriv χ.LFunction ((σ : ℂ) + y * I) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ1
  have hd : Continuous (deriv χ.LFunction) :=
    continuous_iff_continuousAt.2 fun z => (hf.analyticAt z).deriv.continuousAt
  have e : (fun y : ℝ => logDeriv χ.LFunction ((σ : ℂ) + y * I)) =
      fun y : ℝ => deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I) := by
    ext y; rw [logDeriv_apply]
  rw [e]
  exact (hd.comp (by fun_prop)).div (hf.continuous.comp (by fun_prop)) hne

/-- `h` is integrable on `ℜs = 3/2`. -/
theorem integrable_hInt_right {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => hInt χ δ x (((3 / 2 : ℝ) : ℂ) + y * I) := by
  have hGi := integrable_G_line δ (3 / 2) (by norm_num) le_rfl
  have hc : Continuous fun y : ℝ => hInt χ δ x (((3 / 2 : ℝ) : ℂ) + y * I) := by
    unfold hInt
    refine (continuous_logDeriv_L_line hχ1 (3 / 2) fun y =>
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; norm_num)).mul
      ((continuous_G_line δ (3 / 2) (by norm_num)).mul ?_)
    exact continuous_iff_continuousAt.2 fun y =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  refine (hGi.norm.const_mul (C3 * x ^ (3 / 2 : ℝ))).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [hInt, norm_mul, norm_mul, norm_cpow_x hx]
  have h1 := norm_logDeriv_L_right χ y
  have hre : (((3 / 2 : ℝ) : ℂ) + y * I).re = 3 / 2 := by simp
  rw [hre]
  have hx0 : 0 ≤ x ^ (3 / 2 : ℝ) := by positivity
  calc ‖logDeriv χ.LFunction (((3 / 2 : ℝ) : ℂ) + y * I)‖ *
        (‖Gr (((3 / 2 : ℝ) : ℂ) + y * I) δ 0‖ * x ^ (3 / 2 : ℝ))
      ≤ C3 * (‖Gr (((3 / 2 : ℝ) : ℂ) + y * I) δ 0‖ * x ^ (3 / 2 : ℝ)) := by gcongr
    _ = C3 * x ^ (3 / 2 : ℝ) * ‖Gr (((3 / 2 : ℝ) : ℂ) + y * I) δ 0‖ := by ring

/-- `D_N = log(512 q⁹ (q + 1)/0.355)`. -/
noncomputable def DN (N : ℕ) : ℝ := Real.log (512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) / 0.355)

/-- `log(B_T/0.355) ≤ D_N + 37 + 2.6|T|`. -/
theorem LB_le_linear {N : ℕ} [NeZero N] (T : ℝ) :
    Real.log (BT N T / 0.355) ≤ DN N + 37 + 2.6 * |T| := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hC : 0 < 512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) / 0.355 := by positivity
  have e : BT N T / 0.355 = (512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) / 0.355) * (|T| + 22) *
      Real.exp (π * (|T| + 10) / 2) := by
    unfold BT; ring
  rw [e, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hC.ne' (by positivity),
    Real.log_exp, ← DN]
  have h1 : Real.log (|T| + 22) ≤ |T| + 21 := by
    have := Real.log_le_sub_one_of_pos (show 0 < |T| + 22 by positivity); linarith
  have h2 : π * (|T| + 10) / 2 ≤ 1.6 * (|T| + 10) := by
    have := Real.pi_lt_d2; nlinarith [abs_nonneg T]
  linarith

/-- `h` is integrable on `ℜs = −1/2`. -/
theorem integrable_hInt_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I) := by
  have hc : Continuous fun y : ℝ => hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I) := by
    unfold hInt
    refine (continuous_logDeriv_L_line hχ1 (-1 / 2) fun y =>
      LFunction_ne_zero_strip hχ hχ1 (by simp; norm_num) (by simp; norm_num)).mul
      ((continuous_G_line δ (-1 / 2) (by norm_num)).mul ?_)
    exact continuous_iff_continuousAt.2 fun y =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  set c1 : ℝ := 2 / Real.log 2 + 4.8 with hc1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := c1 * (|DN N| + 37) * Kδ δ * x ^ (-1 / 2 : ℝ) with hA
  set B : ℝ := c1 * 2.6 / 0.14 * Kδ δ * x ^ (-1 / 2 : ℝ) with hB
  have hK : 0 ≤ Kδ δ := by
    have := norm_G_le_strip δ (s := (0 : ℂ)) (by norm_num) (by norm_num)
    have hp : 0 < Real.exp (-(0.28 * |(0:ℂ).im|)) := Real.exp_pos _
    by_contra hneg; push Not at hneg
    have : Kδ δ * Real.exp (-(0.28 * |(0:ℂ).im|)) < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (Gr 0 δ 0)]
  have hint : Integrable fun y : ℝ => A * Real.exp (-(0.28 * |y|)) + B * Real.exp (-(0.14 * |y|)) :=
    ((integrable_exp_neg_abs (by norm_num)).const_mul A).add
      ((integrable_exp_neg_abs (by norm_num)).const_mul B)
  refine hint.mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [hInt, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + y * I).re = -1 / 2 := by simp
  have him : (((-1 / 2 : ℝ) : ℂ) + y * I).im = y := by simp
  rw [hre]
  have h1 := norm_logDeriv_L_left hχ hχ1 y
  have hLB := LB_le_linear (N := N) y
  have hG := norm_G_le_strip δ (s := ((-1 / 2 : ℝ) : ℂ) + y * I) (by rw [hre]) (by rw [hre]; norm_num)
  rw [him] at hG
  have hLB0 : 0 ≤ Real.log (BT N y / 0.355) := by
    have := one_le_BT (N := N) y
    exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hlogd : ‖logDeriv χ.LFunction (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ c1 * (|DN N| + 37 + 2.6 * |y|) := by
    refine h1.trans ?_
    have e : Real.log (BT N y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (BT N y / 0.355) =
        c1 * Real.log (BT N y / 0.355) := by rw [hc1]; field_simp
    rw [e]
    have hc10 : 0 ≤ c1 := by rw [hc1]; have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog2.le; linarith
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (DN N)]) hc10
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
  have hy : |y| ≤ Real.exp (0.14 * |y|) / 0.14 := by
    rw [le_div_iff₀ (by norm_num)]
    have := Real.add_one_le_exp (0.14 * |y|); nlinarith [abs_nonneg y]
  have hexp : Real.exp (0.14 * |y|) * Real.exp (-(0.28 * |y|)) = Real.exp (-(0.14 * |y|)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc10 : 0 ≤ c1 := by rw [hc1]; have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog2.le; linarith
  calc ‖logDeriv χ.LFunction (((-1 / 2 : ℝ) : ℂ) + y * I)‖ *
        (‖Gr (((-1 / 2 : ℝ) : ℂ) + y * I) δ 0‖ * x ^ (-1 / 2 : ℝ))
      ≤ c1 * (|DN N| + 37 + 2.6 * |y|) * (Kδ δ * Real.exp (-(0.28 * |y|)) * x ^ (-1 / 2 : ℝ)) := by
        gcongr
    _ = A * Real.exp (-(0.28 * |y|)) + c1 * 2.6 * Kδ δ * x ^ (-1 / 2 : ℝ) *
          (|y| * Real.exp (-(0.28 * |y|))) := by rw [hA]; ring
    _ ≤ A * Real.exp (-(0.28 * |y|)) + c1 * 2.6 * Kδ δ * x ^ (-1 / 2 : ℝ) *
          (Real.exp (0.14 * |y|) / 0.14 * Real.exp (-(0.28 * |y|))) := by
        gcongr
    _ = A * Real.exp (-(0.28 * |y|)) + B * Real.exp (-(0.14 * |y|)) := by
        rw [hB, ← hexp]; ring

end TernaryGoldbach.Explicit
