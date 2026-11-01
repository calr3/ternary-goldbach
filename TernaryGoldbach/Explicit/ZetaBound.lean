import TernaryGoldbach.Explicit.ZetaPoly
import TernaryGoldbach.Explicit.ExplicitBound

/-!
# The explicit-formula bound for `ζ` (`q = 1`)

Under RH up to `T₀ ≥ max(10π|δ|, 50)`, for `x ≥ 1`:
`|Σ Λ(n) e(δn/x) η(n/x) − M(1) x| ≤ E₀ + E₁√x + E₂ x + V_ζ/(2π√x)`, `M(1) = ∫₀^∞ η(t) e(δt) dt = η̂(−δ)`,
from `explicit_formula_zeta`, `zero_sum_boundG` (with `B''_ζ`, `κ = 10`) and the line `ℜs = −1/2`.
-/

open Complex MeasureTheory Set Filter Metric FourierTransform
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- The tail bound for `G_δ` in the floor form used by `zero_sum_boundG`. -/
theorem norm_G_tail_floor {δ T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) {s : ℂ} (hr1 : -1 ≤ s.re)
    (hr2 : s.re ≤ 1) (hτ : T0 < |s.im|) :
    ‖Gr s δ 0‖ ≤ EB T0 * rhoB ^ ⌊(|s.im| - T0) / 4.4⌋₊ +
      EA T0 δ * rhoA δ ^ ⌊(|s.im| - T0) / 4.4⌋₊ := by
  have hT00 : 0 < T0 := by linarith [le_max_right (10 * π * |δ|) 50]
  set k := ⌊(|s.im| - T0) / 4.4⌋₊ with hk
  have hkle : (k : ℝ) * 4.4 ≤ |s.im| - T0 := by
    have h0 : 0 ≤ (|s.im| - T0) / 4.4 := div_nonneg (by linarith) (by norm_num)
    have := Nat.floor_le h0
    rwa [le_div_iff₀ (by norm_num)] at this
  have hGt := norm_G_tail s δ hr1 hr2 hT0 hτ.le
  have hB' : Real.exp (-0.1398 * (|s.im| - T0)) ≤ rhoB ^ k := by
    unfold rhoB; rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    nlinarith
  have hA' : EA T0 δ * Real.exp (-1.93 * ((|s.im| - T0) / (π * |δ|))) ≤ EA T0 δ * rhoA δ ^ k := by
    by_cases hδ : δ = 0
    · unfold EA; simp [hδ]
    · refine mul_le_mul_of_nonneg_left ?_ (EA_nonneg T0 δ)
      unfold rhoA; rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have hδ0 : 0 < |δ| := abs_pos.2 hδ
      have hP : 0 < π * |δ| := by positivity
      have h1 : (k : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (|s.im| - T0) / (π * |δ|) := by
        calc (k : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (k : ℝ) * 4.4 / (π * |δ|) := by
              apply div_le_div_of_nonneg_left (by positivity) hP; nlinarith [Real.pi_pos]
          _ ≤ _ := div_le_div_of_nonneg_right hkle hP.le
      have e : (k : ℝ) * -(1.93 * 4.4 / (π * (|δ| + 1))) =
          -1.93 * ((k : ℝ) * 4.4 / (π * (|δ| + 1))) := by ring
      rw [e]; nlinarith
  have := mul_le_mul_of_nonneg_left hB' (EB_nonneg hT00.le)
  linarith

/-- The vertical-line constant for `ζ`. -/
noncomputable def Vz (δ : ℝ) : ℝ :=
  112 * (2 / Real.log 2 + 4.8) * (40 * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2))

/-- **The line `ℜs = −1/2` for `ζ`**: `|∫ hZeta(−1/2 + iy) dy| ≤ x^{−1/2} V_ζ`. -/
theorem norm_integral_hZeta_le (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, hZeta (fδ δ) x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-(1 / 2) : ℝ) * Vz δ := by
  set θ := thetaD δ with hθ
  have hθ0 : 0 < θ := thetaD_pos δ
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₁1 : 2 / 3 ≤ c₁ := by
    have : 0 ≤ 2 / Real.log 2 := by positivity
    rw [hc₁]; linarith
  set g : ℝ → ℝ := fun y => x ^ (-(1 / 2) : ℝ) * 112 * c₁ *
    (40 * Real.exp (-(θ * |y|)) + 2.6 * (|y| * Real.exp (-(θ * |y|)))) with hg
  have hgi : Integrable g :=
    (((integrable_exp_neg_abs hθ0).const_mul 40).add
      ((integrable_abs_mul_exp hθ0).const_mul 2.6)).const_mul _
  have hpt : ∀ y : ℝ, ‖hZeta (fδ δ) x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
    intro y
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    have hsim : s.im = y := by simp [hs]
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; norm_num at hsre
    have hz : riemannZeta s ≠ 0 :=
      zeta_ne_zero_of_zetaF hs1 (zetaF_ne_zero_strip (by rw [hsre]; norm_num) (by rw [hsre]; norm_num))
    rw [hZeta, norm_mul, norm_mul, norm_cpow_x hx, hsre, mellin_fδ]
    have hld : logDeriv riemannZeta s = logDeriv zetaF s - 1 / (s - 1) := by
      rw [logDeriv_zetaF_eq hs1 hz]; ring
    have hL := norm_logDeriv_leftD ldatum_zeta y
    have hLB := log_Bz_le y
    have hL' : ‖logDeriv zetaF s‖ ≤ c₁ * (39 + 2.6 * |y|) := by
      refine hL.trans ?_
      have e : Real.log (Bz y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (Bz y / 0.355) =
          c₁ * Real.log (Bz y / 0.355) := by rw [hc₁]; ring
      rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) hc₁0
    have hinv : ‖1 / (s - 1)‖ ≤ 2 / 3 := by
      rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hs1))]
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hsre] at this
      norm_num at this ⊢; linarith
    have hld' : ‖logDeriv riemannZeta s‖ ≤ c₁ * (40 + 2.6 * |y|) := by
      rw [hld]; refine (norm_sub_le _ _).trans ?_; nlinarith
    have hGs := norm_G_uniform s δ (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
    rw [hsim] at hGs
    have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    have e2 : x ^ (-1 / 2 : ℝ) = x ^ (-(1 / 2) : ℝ) := by norm_num
    calc ‖logDeriv riemannZeta s‖ * (‖Gr s δ 0‖ * x ^ (-1 / 2 : ℝ))
        ≤ (c₁ * (40 + 2.6 * |y|)) * (112 * Real.exp (-(θ * |y|)) * x ^ (-1 / 2 : ℝ)) :=
          mul_le_mul hld' (mul_le_mul_of_nonneg_right hGs hxp) (by positivity) (by positivity)
      _ = g y := by rw [hg, e2]; ring
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hg, integral_const_mul, integral_add ((integrable_exp_neg_abs hθ0).const_mul _)
    ((integrable_abs_mul_exp hθ0).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_neg_mul_abs hθ0, integral_abs_mul_exp_neg_mul_abs hθ0]
  unfold Vz; rw [← hθ, ← hc₁]; ring

/-- `M(1) = ∫₀^∞ t² e^{−t²/2} e(δt) dt = η̂(−δ)` (`η` cut off at `0`). -/
theorem mellin_fδ_one (δ : ℝ) :
    mellin (fδ δ) 1 = 𝓕 (fun u : ℝ => ((if 0 < u then u ^ 2 * Real.exp (-u ^ 2 / 2) else 0 : ℝ) : ℂ)) (-δ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, mellin]
  set g : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * -δ) * Complex.I) •
    (((if 0 < v then v ^ 2 * Real.exp (-v ^ 2 / 2) else 0 : ℝ) : ℂ)) with hg
  have hR : ∫ v : ℝ, g v = ∫ v in Ioi (0:ℝ), g v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      have : ¬ 0 < u := hu
      simp [hg, this])).symm
  rw [hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hg, sub_self, Complex.cpow_zero, one_smul, if_pos ht, fδ, smul_eq_mul]
  push_cast; ring_nf

/-- The error term for `q = 1`. -/
noncomputable def errZ (T0 δ x : ℝ) : ℝ :=
  E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) + E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / √x +
    112 * Z3g BPz2 0 / x + Vz δ / (2 * π * (x * √x))

/-- **The explicit-formula bound for `ζ`**: under RH up to `T₀ ≥ max(10π|δ|, 50)`, for `x ≥ 1`,
`|Σ Λ(n) η(n/x) e(δn/x) − M(1) x| ≤ errZ(T₀, δ, x) x`. -/
theorem norm_SsumG_zeta_le (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fδ δ) x - mellin (fδ δ) 1 * x‖ ≤ errZ T0 δ x * x := by
  have hx0 : 0 < x := by linarith
  have h50 : 50 ≤ T0 := (le_max_right _ _).trans hT0
  have hT00 : 0 < T0 := by linarith
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta (goodSmoothing_fδ δ) hx0
  set I0 := ∫ y : ℝ, hZeta (fδ δ) x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  -- the zero sum
  have hG : ∀ ρ : ℂ, zetaF ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2 := by
    intro ρ h0 h1 h2 h3
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h2; simp at h2
    have : riemannZeta ρ = 0 := by
      rw [zetaF_of_ne hρ1] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hρ1
      · exact h
    exact hRH ρ this h1 h2 h3
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) *
      (mellin (fδ δ) u * (x : ℂ) ^ u)‖ ≤
      112 * Z3g BPz2 0 + √x * E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) +
        x * E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) := by
    intro T
    refine zero_sum_boundG polyDatum_zeta2 (fun T u hu => zerosRectD_zetaF_cases hu) h50 hG
      (mellin (fδ δ)) (G0 := 112) (by rw [mellin_fδ]; simpa using norm_G_uniform 0 δ (by simp) (by simp))
      (F := fline δ) (F' := flineD δ) (fun t => by rw [mellin_fδ, fline])
      (hasDerivAt_fline δ) (continuous_flineD δ) (by positivity) (by positivity)
      (integrable_norm_sq_fline δ) (integrable_norm_sq_flineD δ) (integral_norm_sq_fline_le δ)
      (integral_norm_sq_flineD_le δ) (EB_nonneg hT00.le) (EA_nonneg T0 δ) (Real.exp_pos _).le
      rhoB_lt_one (Real.exp_pos _).le (rhoA_lt_one δ) (fun s h1 h2 h3 => by
        rw [mellin_fδ]; exact norm_G_tail_floor hT0 (by linarith) h2.le h3) hx T
  have h1 : ‖mellin (fδ δ) 1 * x - SsumG (1 : DirichletCharacter ℂ 1) (fδ δ) x - (1 / (2 * π) : ℂ) * I0‖ ≤
      112 * Z3g BPz2 0 + √x * E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) +
        x * E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hbound (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vz δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_le δ hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) (fδ δ) x - mellin (fδ δ) 1 * x =
      -((mellin (fδ δ) 1 * x - SsumG (1 : DirichletCharacter ℂ 1) (fδ δ) x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by ring
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  unfold errZ
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hrp : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrp]
  set s := √x with hs_def
  rw [← hs]
  field_simp
  ring

/-! ## Monotonicity in `|δ|` -/

theorem E2g_mono_A {B : ℝ → ℝ} {κ T0 EB' EA1 EA2 ρB ρ1 ρ2 : ℝ} (hZ : 0 ≤ Z3g B T0)
    (hc : 0 ≤ c3g κ T0) (hEA1 : 0 ≤ EA1) (hEA : EA1 ≤ EA2) (hρ10 : 0 ≤ ρ1) (hρ : ρ1 ≤ ρ2)
    (hρ2 : ρ2 < 1) : E2g B κ T0 EB' EA1 ρB ρ1 ≤ E2g B κ T0 EB' EA2 ρB ρ2 := by
  unfold E2g
  have h1 := inv_one_sub_mono hρ hρ2
  have h0 : 0 ≤ 1 / (1 - ρ1) := by rw [one_div]; exact inv_nonneg.2 (by linarith)
  have h2 : 1 / (1 - ρ1) ^ 2 ≤ 1 / (1 - ρ2) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, div_pow, one_pow] at this
  have hX : 2 * Z3g B T0 / (1 - ρ1) + 2 * c3g κ T0 / (1 - ρ1) ^ 2 ≤
      2 * Z3g B T0 / (1 - ρ2) + 2 * c3g κ T0 / (1 - ρ2) ^ 2 := by
    rw [div_eq_mul_one_div (2 * Z3g B T0), div_eq_mul_one_div (2 * c3g κ T0),
      div_eq_mul_one_div (2 * Z3g B T0) (1 - ρ2), div_eq_mul_one_div (2 * c3g κ T0) ((1 - ρ2) ^ 2)]
    gcongr
  have hX0 : 0 ≤ 2 * Z3g B T0 / (1 - ρ1) + 2 * c3g κ T0 / (1 - ρ1) ^ 2 := by
    have : 0 < 1 - ρ1 := by linarith
    positivity
  have := mul_le_mul hEA hX hX0 (hEA1.trans hEA)
  linarith

theorem E2z_mono {T0 δ r : ℝ} (hT0 : 0 < T0) (hr : 0 < r) (hr1 : r ≤ 1) (hT : 10 * π * |δ| ≤ T0) :
    E2g BPz2 10 T0 (EB T0) (EA T0 (δ * r)) rhoB (rhoA (δ * r)) ≤
      E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) :=
  E2g_mono_A (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
    (div_nonneg (div_nonneg (by norm_num) hT0.le) (log_ratio_pos (by norm_num) (by norm_num)).le)
    (EA_nonneg T0 _) (EA_mono hr hr1 hT) (Real.exp_pos _).le (rhoA_mono hr hr1) (rhoA_lt_one δ)

theorem Vz_nonneg (δ : ℝ) : 0 ≤ Vz δ := by
  unfold Vz
  have := thetaD_pos δ
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  positivity

theorem Vz_mono {δ r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : Vz (δ * r) ≤ Vz δ := by
  unfold Vz
  have hθ := thetaD_anti (δ := δ) hr hr1
  have hθ0 := thetaD_pos δ
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  gcongr

theorem E1z_nonneg (T0 : ℝ) : 0 ≤ E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) := by
  unfold E1g ZLg
  exact mul_nonneg (div_nonneg (polyDatum_zeta2.log_pos _).le
    (log_ratio_pos (by norm_num) (by norm_num)).le) (by positivity)

theorem Z3z_nonneg : 0 ≤ Z3g BPz2 0 :=
  div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le

end TernaryGoldbach.Explicit
