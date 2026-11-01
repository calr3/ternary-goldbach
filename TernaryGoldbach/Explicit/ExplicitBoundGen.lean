import TernaryGoldbach.Explicit.ZetaBound
import TernaryGoldbach.Explicit.ZeroSumGen

/-!
# Explicit-formula bounds for a general admissible smoothing

For `χ` primitive `≠ 1` (`LDatum` `ldatum_L`, `PolyDatum` `polyDatum_L`) and for `ζ`, with the
smoothing-specific inputs as hypotheses: `|M(0)| ≤ G₀`, Plancherel bounds `Q₁, Q₂` on `ℜs = 1/2`, a
geometric tail above `T₀`, and `|M(−1/2 + iy)| ≤ K_v e^{−θ_v|y|}`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem polyDatum_L {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) : PolyDatum χ.LFunction (BP N) 11 where
  diff := DirichletCharacter.differentiable_LFunction hχ1
  center_ge := norm_L_center_ge χ
  bound := fun T w hw => norm_L_le_BP hχ hχ1 hw
  B_ge := fun T => le_trans (by norm_num) (one_le_BP (N := N) T)
  B_mono := fun T T' h => BP_mono N h
  growth := fun T0 m hT0 hm => log_BP_growth N hT0 hm
  κ_nonneg := by norm_num

/-- The vertical-line constant for a smoothing with `|M(−1/2 + iy)| ≤ K_v e^{−θ_v|y|}`. -/
noncomputable def VgL (D Kv θv : ℝ) : ℝ :=
  Kv * (2 / Real.log 2 + 4.8) * ((D + 37) * (2 / θv) + 2.6 * (2 / θv ^ 2))

/-- **The line `ℜs = −1/2`**, general smoothing, `χ`. -/
theorem norm_integral_hIntG_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {φ : ℝ → ℂ} {Kv θv : ℝ} (hθv : 0 < θv) (hKv : 0 ≤ Kv)
    (hv : ∀ y : ℝ, ‖mellin φ (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ Kv * Real.exp (-(θv * |y|)))
    {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, hIntG χ φ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-(1 / 2) : ℝ) * VgL (DN N) Kv θv := by
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hc₁0 : 0 ≤ c₁ := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hD : 0 ≤ DN N + 37 := by linarith [DN_nonneg N]
  set g : ℝ → ℝ := fun y => x ^ (-(1 / 2) : ℝ) * Kv * c₁ *
    ((DN N + 37) * Real.exp (-(θv * |y|)) + 2.6 * (|y| * Real.exp (-(θv * |y|)))) with hg
  have hgi : Integrable g :=
    (((integrable_exp_neg_abs hθv).const_mul (DN N + 37)).add
      ((integrable_abs_mul_exp hθv).const_mul 2.6)).const_mul _
  have hpt : ∀ y : ℝ, ‖hIntG χ φ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
    intro y
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    rw [hIntG, norm_mul, norm_mul, norm_cpow_x hx, hsre]
    have hL := norm_logDeriv_L_left hχ hχ1 y
    have hLB := LB_le_linear (N := N) y
    have hL' : ‖logDeriv χ.LFunction s‖ ≤ c₁ * (DN N + 37 + 2.6 * |y|) := by
      refine hL.trans ?_
      have e : Real.log (BT N y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (BT N y / 0.355) =
          c₁ * Real.log (BT N y / 0.355) := by rw [hc₁]; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hLB hc₁0
    have hGs := hv y
    have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    have e2 : x ^ (-1 / 2 : ℝ) = x ^ (-(1 / 2) : ℝ) := by norm_num
    calc ‖logDeriv χ.LFunction s‖ * (‖mellin φ s‖ * x ^ (-1 / 2 : ℝ))
        ≤ (c₁ * (DN N + 37 + 2.6 * |y|)) * (Kv * Real.exp (-(θv * |y|)) * x ^ (-1 / 2 : ℝ)) :=
          mul_le_mul hL' (mul_le_mul_of_nonneg_right hGs hxp) (by positivity) (by positivity)
      _ = g y := by rw [hg, e2]; ring
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hg, integral_const_mul, integral_add ((integrable_exp_neg_abs hθv).const_mul _)
    ((integrable_abs_mul_exp hθv).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_neg_mul_abs hθv, integral_abs_mul_exp_neg_mul_abs hθv]
  unfold VgL; rw [← hc₁]; ring

/-- **The line `ℜs = −1/2`**, general smoothing, `ζ`. -/
theorem norm_integral_hZeta_le_gen {φ : ℝ → ℂ} {Kv θv : ℝ} (hθv : 0 < θv) (hKv : 0 ≤ Kv)
    (hv : ∀ y : ℝ, ‖mellin φ (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ Kv * Real.exp (-(θv * |y|)))
    {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-(1 / 2) : ℝ) * VgL 3 Kv θv := by
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hc₁0 : 0 ≤ c₁ := by positivity
  set g : ℝ → ℝ := fun y => x ^ (-(1 / 2) : ℝ) * Kv * c₁ *
    ((3 + 37) * Real.exp (-(θv * |y|)) + 2.6 * (|y| * Real.exp (-(θv * |y|)))) with hg
  have hgi : Integrable g :=
    (((integrable_exp_neg_abs hθv).const_mul (3 + 37)).add
      ((integrable_abs_mul_exp hθv).const_mul 2.6)).const_mul _
  have hpt : ∀ y : ℝ, ‖hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
    intro y
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; norm_num at hsre
    have hz : riemannZeta s ≠ 0 :=
      zeta_ne_zero_of_zetaF hs1 (zetaF_ne_zero_strip (by rw [hsre]; norm_num) (by rw [hsre]; norm_num))
    rw [hZeta, norm_mul, norm_mul, norm_cpow_x hx, hsre]
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
    have hc₁1 : 2 / 3 ≤ c₁ := by
      have : 0 ≤ 2 / Real.log 2 := by positivity
      rw [hc₁]; linarith
    have hld' : ‖logDeriv riemannZeta s‖ ≤ c₁ * (3 + 37 + 2.6 * |y|) := by
      rw [hld]; refine (norm_sub_le _ _).trans ?_; nlinarith
    have hGs := hv y
    have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    have e2 : x ^ (-1 / 2 : ℝ) = x ^ (-(1 / 2) : ℝ) := by norm_num
    calc ‖logDeriv riemannZeta s‖ * (‖mellin φ s‖ * x ^ (-1 / 2 : ℝ))
        ≤ (c₁ * (3 + 37 + 2.6 * |y|)) * (Kv * Real.exp (-(θv * |y|)) * x ^ (-1 / 2 : ℝ)) :=
          mul_le_mul hld' (mul_le_mul_of_nonneg_right hGs hxp) (by positivity) (by positivity)
      _ = g y := by rw [hg, e2]; ring
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hg, integral_const_mul, integral_add ((integrable_exp_neg_abs hθv).const_mul _)
    ((integrable_abs_mul_exp hθv).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_neg_mul_abs hθv, integral_abs_mul_exp_neg_mul_abs hθv]
  unfold VgL; rw [← hc₁]; ring

theorem final_combine {x E0 E1 E2 V A : ℝ} (hx : 0 < x) (hA : A ≤ x ^ (-(1 / 2) : ℝ) * V / (2 * π)) :
    E0 + √x * E1 + x * E2 + A ≤ E0 + √x * E1 + x * E2 + x ^ (-(1 / 2) : ℝ) * V / (2 * π) := by
  linarith

/-- **Explicit-formula bound, general smoothing, `χ` primitive `≠ 1`.** -/
theorem norm_SsumG_le_gen {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 1 ≤ x)
    {T0 : ℝ} (hT0 : 50 ≤ T0)
    (hG : ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2)
    {G0 : ℝ} (hM0 : ‖mellin φ 0‖ ≤ G0)
    {F F' : ℝ → ℂ} (hMF : ∀ t : ℝ, mellin φ (((1 / 2 : ℝ) : ℂ) + t * I) = F t)
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {Q1 Q2 : ℝ} (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hF2 : Integrable fun t => ‖F t‖ ^ 2) (hF2' : Integrable fun t => ‖F' t‖ ^ 2)
    (hFQ : ∫ t, ‖F t‖ ^ 2 ≤ Q1) (hFQ' : ∫ t, ‖F' t‖ ^ 2 ≤ Q2)
    {EB' EA' ρB ρA : ℝ} (hEB : 0 ≤ EB') (hEA : 0 ≤ EA') (hρB0 : 0 ≤ ρB) (hρB1 : ρB < 1)
    (hρA0 : 0 ≤ ρA) (hρA1 : ρA < 1)
    (htail : ∀ s : ℂ, 0 < s.re → s.re < 1 → T0 < |s.im| →
      ‖mellin φ s‖ ≤ EB' * ρB ^ ⌊(|s.im| - T0) / 4.4⌋₊ + EA' * ρA ^ ⌊(|s.im| - T0) / 4.4⌋₊)
    {Kv θv : ℝ} (hθv : 0 < θv) (hKv : 0 ≤ Kv)
    (hv : ∀ y : ℝ, ‖mellin φ (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ Kv * Real.exp (-(θv * |y|))) :
    ‖SsumG χ φ x‖ ≤ G0 * Z3g (BP N) 0 + √x * E1g (BP N) T0 Q1 Q2 +
      x * E2g (BP N) 11 T0 EB' EA' ρB ρA + x ^ (-(1 / 2) : ℝ) * VgL (DN N) Kv θv / (2 * π) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_gen hχ hχ1 hφ hx0
  set I0 := ∫ y : ℝ, hIntG χ φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hcls : ∀ T : ℝ, ∀ u ∈ zerosRectD χ.LFunction T,
      χ.LFunction u = 0 ∧ (u = 0 ∨ (0 < u.re ∧ u.re < 1)) := by
    intro T u hu
    obtain ⟨h1, -, h3⟩ := zerosRect_cases hχ hχ1 (T := T) hu
    exact ⟨h1, h3⟩
  have hb : ∀ T : ℝ, ‖∑ u ∈ zerosRect χ T, (multRect χ T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      G0 * Z3g (BP N) 0 + √x * E1g (BP N) T0 Q1 Q2 + x * E2g (BP N) 11 T0 EB' EA' ρB ρA := fun T =>
    zero_sum_boundG (polyDatum_L hχ hχ1) hcls hT0 hG (mellin φ) hM0 hMF hF hF' hQ1 hQ2 hF2 hF2' hFQ
      hFQ' hEB hEA hρB0 hρB1 hρA0 hρA1 htail hx T
  have h1 : ‖-SsumG χ φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      G0 * Z3g (BP N) 0 + √x * E1g (BP N) T0 Q1 Q2 + x * E2g (BP N) 11 T0 EB' EA' ρB ρA :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hb (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * VgL (DN N) Kv θv / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hIntG_le hχ hχ1 hθv hKv hv hx0) (by positivity)
  have e : SsumG χ φ x = -((-SsumG χ φ x - (1 / (2 * π) : ℂ) * I0) + (1 / (2 * π) : ℂ) * I0) := by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (by linarith)

/-- **Explicit-formula bound, general smoothing, `ζ`.** -/
theorem norm_SsumG_zeta_le_gen {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 1 ≤ x)
    {T0 : ℝ} (hT0 : 50 ≤ T0)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2)
    {G0 : ℝ} (hM0 : ‖mellin φ 0‖ ≤ G0)
    {F F' : ℝ → ℂ} (hMF : ∀ t : ℝ, mellin φ (((1 / 2 : ℝ) : ℂ) + t * I) = F t)
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {Q1 Q2 : ℝ} (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hF2 : Integrable fun t => ‖F t‖ ^ 2) (hF2' : Integrable fun t => ‖F' t‖ ^ 2)
    (hFQ : ∫ t, ‖F t‖ ^ 2 ≤ Q1) (hFQ' : ∫ t, ‖F' t‖ ^ 2 ≤ Q2)
    {EB' EA' ρB ρA : ℝ} (hEB : 0 ≤ EB') (hEA : 0 ≤ EA') (hρB0 : 0 ≤ ρB) (hρB1 : ρB < 1)
    (hρA0 : 0 ≤ ρA) (hρA1 : ρA < 1)
    (htail : ∀ s : ℂ, 0 < s.re → s.re < 1 → T0 < |s.im| →
      ‖mellin φ s‖ ≤ EB' * ρB ^ ⌊(|s.im| - T0) / 4.4⌋₊ + EA' * ρA ^ ⌊(|s.im| - T0) / 4.4⌋₊)
    {Kv θv : ℝ} (hθv : 0 < θv) (hKv : 0 ≤ Kv)
    (hv : ∀ y : ℝ, ‖mellin φ (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ Kv * Real.exp (-(θv * |y|))) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) φ x - mellin φ 1 * x‖ ≤ G0 * Z3g BPz2 0 +
      √x * E1g BPz2 T0 Q1 Q2 + x * E2g BPz2 10 T0 EB' EA' ρB ρA +
        x ^ (-(1 / 2) : ℝ) * VgL 3 Kv θv / (2 * π) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hφ hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hG : ∀ ρ : ℂ, zetaF ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2 := by
    intro ρ h0 h1 h2 h3
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h2; simp at h2
    have : riemannZeta ρ = 0 := by
      rw [zetaF_of_ne hρ1] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hρ1
      · exact h
    exact hRH ρ this h1 h2 h3
  have hb : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      G0 * Z3g BPz2 0 + √x * E1g BPz2 T0 Q1 Q2 + x * E2g BPz2 10 T0 EB' EA' ρB ρA := fun T =>
    zero_sum_boundG polyDatum_zeta2 (fun T u hu => zerosRectD_zetaF_cases hu) hT0 hG (mellin φ) hM0
      hMF hF hF' hQ1 hQ2 hF2 hF2' hFQ hFQ' hEB hEA hρB0 hρB1 hρA0 hρA1 htail hx T
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      G0 * Z3g BPz2 0 + √x * E1g BPz2 T0 Q1 Q2 + x * E2g BPz2 10 T0 EB' EA' ρB ρA :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hb (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * VgL 3 Kv θv / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_le_gen hθv hKv hv hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) φ x - mellin φ 1 * x =
      -((mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (by linarith)

end TernaryGoldbach.Explicit
