import TernaryGoldbach.MinorArcs.FourierSums
import TernaryGoldbach.Helfgott.Eta2

/-!
# `|η̂₂''|_∞ ≤ 31.521` [B, (B.6)]: the analytic part

Integrating twice by parts on `[1/4, 1/2]` and `[1/2, 1]`, where `η₂ = 4 log 4u` and `η₂ = −4 log u`:
`(2πt)² η̂₂(t) = eta2DD t`, where

`eta2DD t = 16 e(−t/2) − 16 e(−t/4) − 4 e(−t) + 4 ∫_{1/4}^{1/2} e(−ut)/u² du − 4 ∫_{1/2}^1 e(−ut)/u² du`

(`eta2DD_eq`). With `z = e(−t/4)`, the first three terms are `−z(4z³ − 16z + 16)`, of norm at most
`31.4821` (`norm_trig_le`: the maximum of `|4z³ − 16z + 16|² = 512c³ − 256c² − 896c + 656`,
`c = ℜz`, is `991.1189`). One more integration by parts bounds the integrals by `1/(π|t|a²)`, so
`‖eta2DD t‖ ≤ 31.4821 + 80/(π|t|)`, which is `≤ 31.521` for `|t| ≥ 655` (`norm_eta2DD_large`).
This is [B]'s argument for `|t| ≥ 655`; the range `|t| ≤ 655` is a finite computation.

The same integration by parts gives `‖(2πt)² (η₂ log(4·))^(t)‖ ≤ 48 log 2` with no computation
(`norm_eta2log4_le`), which gives [B, (B.11)] from (B.6).
-/

open Real Complex MeasureTheory FourierTransform
open TernaryGoldbach.Helfgott (eta2)

namespace TernaryGoldbach.MinorArcs

/-- `E(u) = e(−ut)`. -/
theorem hasDerivAt_E (t u : ℝ) :
    HasDerivAt (fun u : ℝ => e (-(u * t))) (-(2 * π * I * t) * e (-(u * t))) u := by
  have h1 : HasDerivAt (fun u : ℝ => ((-(u * t) : ℝ) : ℂ)) ((-t : ℝ) : ℂ) u := by
    have := ((hasDerivAt_id u).mul_const t).neg
    simpa using this.ofReal_comp
  have h2 := (h1.const_mul (2 * π * I)).cexp
  unfold e
  convert h2 using 1
  push_cast; ring

theorem continuous_E (t : ℝ) : Continuous fun u : ℝ => e (-(u * t)) := by
  unfold e; fun_prop

/-- **Two integrations by parts** against `e(−ut)` on `[a, b]`, for `g ∈ C²`. -/
theorem ibp2 {a b t : ℝ} (ht : t ≠ 0) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hc : ContinuousOn g'' (Set.uIcc a b)) :
    ((2 * π * t) ^ 2 : ℂ) * ∫ u in a..b, e (-(u * t)) * (g u : ℂ) =
      2 * π * I * t * (e (-(b * t)) * g b - e (-(a * t)) * g a) +
        (e (-(b * t)) * g' b - e (-(a * t)) * g' a) - ∫ u in a..b, e (-(u * t)) * (g'' u : ℂ) := by
  set c : ℂ := -(2 * π * I * t) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, neg_ne_zero]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [*, Complex.I_ne_zero]
  set E : ℝ → ℂ := fun u => e (-(u * t))
  set V : ℝ → ℂ := fun u => E u / c
  have hV : ∀ x, HasDerivAt V (E x) x := by
    intro x
    have := (hasDerivAt_E t x).div_const c
    convert this using 1
    rw [eq_div_iff hc0]; simp only [E]; rw [hcdef]; ring
  have hgC : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u => (g u : ℂ)) (g' x : ℂ) x :=
    fun x hx => (hg x hx).ofReal_comp
  have hg'C : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u => (g' u : ℂ)) (g'' x : ℂ) x :=
    fun x hx => (hg' x hx).ofReal_comp
  have hcontE : Continuous E := continuous_E t
  have hcont_g' : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  have hint_E : IntervalIntegrable E volume a b := hcontE.intervalIntegrable a b
  have hint_g' : IntervalIntegrable (fun u => (g' u : ℂ)) volume a b :=
    (continuous_ofReal.comp_continuousOn hcont_g').intervalIntegrable
  have hint_g'' : IntervalIntegrable (fun u => (g'' u : ℂ)) volume a b :=
    (continuous_ofReal.comp_continuousOn hc).intervalIntegrable
  -- first integration by parts: `∫ g E = g V| − ∫ g' V`
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgC (fun x _ => hV x) hint_g' hint_E
  -- second: `∫ g' E = g' V| − ∫ g'' V`
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg'C (fun x _ => hV x) hint_g'' hint_E
  have e1 : ∫ u in a..b, E u * (g u : ℂ) = ∫ u in a..b, (g u : ℂ) * E u := by
    congr 1; ext u; ring
  have e2 : ∫ u in a..b, (g' u : ℂ) * V u = (∫ u in a..b, (g' u : ℂ) * E u) / c := by
    rw [← intervalIntegral.integral_div]; congr 1; ext u; simp only [V]; ring
  have e3 : ∫ u in a..b, (g'' u : ℂ) * V u = (∫ u in a..b, (g'' u : ℂ) * E u) / c := by
    rw [← intervalIntegral.integral_div]; congr 1; ext u; simp only [V]; ring
  have e4 : ∫ u in a..b, E u * (g'' u : ℂ) = ∫ u in a..b, (g'' u : ℂ) * E u := by
    congr 1; ext u; ring
  show ((2 * π * t) ^ 2 : ℂ) * ∫ u in a..b, E u * (g u : ℂ) = _
  rw [e1, h1, e2, h2, e3, e4]
  simp only [V, E]
  have hcc : ((2 * π * t) ^ 2 : ℂ) = -(c * c) := by
    rw [hcdef]; ring_nf; rw [Complex.I_sq]; ring
  rw [hcc]
  field_simp
  ring

/-- `∫ f = ∫_a^b f + ∫_b^c f` for `f` vanishing off `(a, c)`. -/
theorem integral_eq_pieces {f : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, x ∉ Set.Ioo a c → f x = 0) (hint : IntervalIntegrable f volume a c) :
    ∫ x, f x = (∫ x in a..b, f x) + ∫ x in b..c, f x := by
  have hac := hab.trans hbc
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc le_rfl hbc))
    (hint.mono_set (by rw [Set.uIcc_of_le hbc, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc hab le_rfl)),
    intervalIntegral.integral_of_le hac]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    fun x hx => hf x fun h => hx (Set.Ioo_subset_Ioc_self h)).symm

/-- `∫_a^b e(−ut) G'(u) du ≤ G(b) − G(a)` in norm, for `G' ≥ 0`. -/
theorem norm_integral_E_le {a b t : ℝ} (hab : a ≤ b) {G G' : ℝ → ℝ}
    (hG : ∀ x ∈ Set.uIcc a b, HasDerivAt G (G' x) x) (hc : ContinuousOn G' (Set.uIcc a b))
    (hs : ∀ x ∈ Set.Icc a b, 0 ≤ G' x) :
    ‖∫ u in a..b, e (-(u * t)) * (G' u : ℂ)‖ ≤ G b - G a := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hc.intervalIntegrable)]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hab] at hx
  simp only [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs x hx)]

/-- `J(a, b) = ∫_a^b e(−ut)/u² du`. -/
noncomputable def Jq (a b t : ℝ) : ℂ := ∫ u in a..b, e (-(u * t)) * (((u ^ 2)⁻¹ : ℝ) : ℂ)

/-- **The explicit form of `(2πt)² η̂₂(t)`.** -/
noncomputable def eta2DD (t : ℝ) : ℂ :=
  16 * e (-(1 / 2 * t)) - 16 * e (-(1 / 4 * t)) - 4 * e (-(1 * t)) +
    4 * Jq (1 / 4) (1 / 2) t - 4 * Jq (1 / 2) 1 t

theorem fourier_eta2_eq (t : ℝ) :
    𝓕 (fun u => (eta2 u : ℂ)) t =
      (∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) * ((4 * Real.log (4 * u) : ℝ) : ℂ)) +
        ∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) * ((-4 * Real.log u : ℝ) : ℂ) := by
  rw [fourier_eq_integral_e, integral_eq_pieces (a := 1 / 4) (b := 1 / 2) (c := 1) (by norm_num)
    (by norm_num)]
  · congr 1
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      simp only [Helfgott.eta2_eq_left hu.1 hu.2]
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      simp only [Helfgott.eta2_eq_right hu.1 hu.2]
  · intro x hx; rw [Helfgott.eta2_eq_zero hx]; simp
  · exact ((continuous_E t).mul (continuous_ofReal.comp Helfgott.continuous_eta2)).intervalIntegrable _ _

theorem hasDerivAt_inv_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => (u ^ 2)⁻¹) (-2 * (x ^ 3)⁻¹) x := by
  have := (hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)
  convert this using 1; field_simp; ring

theorem continuousOn_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℝ) :
    ContinuousOn (fun u : ℝ => k * (u ^ 2)⁻¹) (Set.uIcc a b) := by
  refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
  rw [Set.uIcc_of_le hab] at hx; have : 0 < x := ha.trans_le hx.1; positivity

/-- **`(2πt)² η̂₂(t) = eta2DD t`** (two integrations by parts on each piece). -/
theorem eta2DD_eq {t : ℝ} (ht : t ≠ 0) :
    ((2 * π * t) ^ 2 : ℂ) * 𝓕 (fun u => (eta2 u : ℂ)) t = eta2DD t := by
  have pos : ∀ {a b x : ℝ}, 0 < a → a ≤ b → x ∈ Set.uIcc a b → 0 < x := fun ha hab hx => by
    rw [Set.uIcc_of_le hab] at hx; exact ha.trans_le hx.1
  have d1 : ∀ x ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2),
      HasDerivAt (fun u => 4 * Real.log (4 * u)) (4 * x⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    have := (((hasDerivAt_id' x).const_mul 4).log (by positivity)).const_mul 4
    convert this using 1; field_simp
  have d1' : ∀ x ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt (fun u : ℝ => 4 * u⁻¹) (-4 * (x ^ 2)⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    convert (hasDerivAt_inv hx0.ne').const_mul 4 using 1; ring
  have d2 : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1, HasDerivAt (fun u => -4 * Real.log u) (-4 * x⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    exact (Real.hasDerivAt_log hx0.ne').const_mul (-4)
  have d2' : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1, HasDerivAt (fun u : ℝ => -4 * u⁻¹) (4 * (x ^ 2)⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    convert (hasDerivAt_inv hx0.ne').const_mul (-4) using 1; ring
  rw [fourier_eta2_eq, mul_add,
    ibp2 ht d1 d1' (continuousOn_inv_sq (by norm_num) (by norm_num) (-4)),
    ibp2 ht d2 d2' (continuousOn_inv_sq (by norm_num) (by norm_num) 4)]
  have hJ1 : ∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) * ((-4 * (u ^ 2)⁻¹ : ℝ) : ℂ) =
      -4 * Jq (1 / 4) (1 / 2) t := by
    rw [Jq, ← intervalIntegral.integral_const_mul]; congr 1; ext u; push_cast; ring
  have hJ2 : ∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) * ((4 * (u ^ 2)⁻¹ : ℝ) : ℂ) =
      4 * Jq (1 / 2) 1 t := by
    rw [Jq, ← intervalIntegral.integral_const_mul]; congr 1; ext u; push_cast; ring
  rw [hJ1, hJ2, eta2DD]
  have l1 : Real.log (4 * (1 / 4)) = 0 := by norm_num
  have l2 : Real.log (4 * (1 / 2)) = Real.log 2 := by norm_num
  have l3 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [l1, l2, l3, Real.log_one]
  push_cast
  ring

/-- `‖∫_a^b e(−ut)/u² du‖ ≤ 1/(π|t|a²)`, by one more integration by parts. -/
theorem norm_Jq_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    ‖Jq a b t‖ ≤ 1 / (π * |t| * a ^ 2) := by
  set c : ℂ := -(2 * π * I * t) with hcdef
  have hcn : ‖c‖ = 2 * π * |t| := by
    rw [hcdef, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; ring
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hcn]; have := abs_pos.2 ht; positivity
  set V : ℝ → ℂ := fun u => e (-(u * t)) / c
  have hV : ∀ x, HasDerivAt V (e (-(x * t))) x := by
    intro x
    have := (hasDerivAt_E t x).div_const c
    convert this using 1
    rw [eq_div_iff hc0]; rw [hcdef]; ring
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hab] at hx; exact ha.trans_le hx.1
  have hh : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => (((u ^ 2)⁻¹ : ℝ) : ℂ)) (((-2 * (x ^ 3)⁻¹ : ℝ)) : ℂ) x :=
    fun x hx => (hasDerivAt_inv_sq (hpos x hx).ne').ofReal_comp
  have hcont3 : ContinuousOn (fun u : ℝ => -2 * (u ^ 3)⁻¹) (Set.uIcc a b) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
    have := hpos x hx; positivity
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hh (fun x _ => hV x)
    ((continuous_ofReal.comp_continuousOn hcont3).intervalIntegrable)
    ((continuous_E t).intervalIntegrable a b)
  have eJ : Jq a b t = ∫ u in a..b, (((u ^ 2)⁻¹ : ℝ) : ℂ) * e (-(u * t)) := by
    rw [Jq]; congr 1; ext u; ring
  rw [eJ, h1]
  have nV : ∀ x, ‖V x‖ = 1 / (2 * π * |t|) := fun x => by
    simp only [V, norm_div, norm_e, hcn]
  -- the remaining integral
  have hI : ‖∫ x in a..b, (((-2 * (x ^ 3)⁻¹ : ℝ)) : ℂ) * V x‖ ≤
      ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) / (2 * π * |t|) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(u ^ 2)⁻¹ / (2 * π * |t|))
        (2 * (x ^ 3)⁻¹ / (2 * π * |t|)) x := by
      intro x hx
      convert ((hasDerivAt_inv_sq (hpos x hx).ne').neg).div_const (2 * π * |t|) using 1; ring
    have hcG : ContinuousOn (fun x : ℝ => 2 * (x ^ 3)⁻¹ / (2 * π * |t|)) (Set.uIcc a b) := by
      refine ContinuousOn.div_const (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop)
        fun x hx => ?_)) _
      have := hpos x hx; positivity
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 2 * (x ^ 3)⁻¹ / (2 * π * |t|)) (fun x hx => ?_),
      intervalIntegral.integral_eq_sub_of_hasDerivAt hG hcG.intervalIntegrable]
    · ring
    · have hx0 := hpos x hx
      have hneg : -2 * (x ^ 3)⁻¹ < 0 := by
        have : 0 < (x ^ 3)⁻¹ := by positivity
        linarith
      rw [norm_mul, nV, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
      ring
  have hb0 : 0 < b := ha.trans_le hab
  calc ‖(((b ^ 2)⁻¹ : ℝ) : ℂ) * V b - (((a ^ 2)⁻¹ : ℝ) : ℂ) * V a -
        ∫ x in a..b, (((-2 * (x ^ 3)⁻¹ : ℝ)) : ℂ) * V x‖
      ≤ ‖(((b ^ 2)⁻¹ : ℝ) : ℂ) * V b‖ + ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) * V a‖ +
          ‖∫ x in a..b, (((-2 * (x ^ 3)⁻¹ : ℝ)) : ℂ) * V x‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
    _ ≤ (b ^ 2)⁻¹ / (2 * π * |t|) + (a ^ 2)⁻¹ / (2 * π * |t|) +
          ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) / (2 * π * |t|) := by
        have n1 : ‖(((b ^ 2)⁻¹ : ℝ) : ℂ) * V b‖ = (b ^ 2)⁻¹ / (2 * π * |t|) := by
          rw [norm_mul, nV, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (pow_pos hb0 2))]; ring
        have n2 : ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) * V a‖ = (a ^ 2)⁻¹ / (2 * π * |t|) := by
          rw [norm_mul, nV, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (pow_pos ha 2))]; ring
        rw [n1, n2]; linarith [hI]
    _ = 1 / (π * |t| * a ^ 2) := by field_simp; ring

/-- `|4z³ − 16z + 16| ≤ 31.4821` on the unit circle. -/
theorem norm_trig_le (z : ℂ) (hz : ‖z‖ = 1) : ‖4 * z ^ 3 - 16 * z + 16‖ ≤ 31.4821 := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; nlinarith
  set x := z.re; set y := z.im
  have hz' : z = x + y * I := (Complex.re_add_im z).symm
  have hw : ‖4 * z ^ 3 - 16 * z + 16‖ ^ 2 = 512 * x ^ 3 - 256 * x ^ 2 - 896 * x + 656 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hz']
    simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re,
      ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    have hy : y ^ 2 = 1 - x ^ 2 := by linarith
    have h4 : y ^ 4 = (1 - x ^ 2) ^ 2 := by rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy]
    have h6 : y ^ 6 = (1 - x ^ 2) ^ 3 := by rw [show y ^ 6 = (y ^ 2) ^ 3 by ring, hy]
    ring_nf
    rw [h6, h4, hy]
    ring
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y]
  have hP : 512 * x ^ 3 - 256 * x ^ 2 - 896 * x + 656 ≤ 991.1226 := by
    nlinarith [mul_nonneg (sq_nonneg (x + 0.61507)) (by linarith : (0:ℝ) ≤ 1.7302 - x),
      sq_nonneg (x + 0.61507)]
  have h0 : 0 ≤ ‖4 * z ^ 3 - 16 * z + 16‖ := norm_nonneg _
  nlinarith

/-- **[B, (B.6)] for `|t| ≥ 655`**: `‖eta2DD t‖ ≤ 31.4821 + 80/(π|t|) ≤ 31.521`. -/
theorem norm_eta2DD_large {t : ℝ} (ht : 655 ≤ |t|) : ‖eta2DD t‖ ≤ 31.521 := by
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; norm_num at ht
  set z := e (-(1 / 4 * t))
  have hz : ‖z‖ = 1 := norm_e _
  have e2 : e (-(1 / 2 * t)) = z ^ 2 := by
    rw [sq, ← e_add]; congr 1; ring
  have e4 : e (-(1 * t)) = z ^ 4 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, ← e2, sq, ← e_add]; congr 1; ring
  have htrig : ‖16 * e (-(1 / 2 * t)) - 16 * e (-(1 / 4 * t)) - 4 * e (-(1 * t))‖ ≤ 31.4821 := by
    rw [e2, e4, show 16 * z ^ 2 - 16 * z - 4 * z ^ 4 = -z * (4 * z ^ 3 - 16 * z + 16) by ring,
      norm_mul, norm_neg, hz, one_mul]
    exact norm_trig_le z hz
  have hJ1 := norm_Jq_le (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num) ht0
  have hJ2 := norm_Jq_le (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) ht0
  have htp : 0 < |t| := abs_pos.2 ht0
  have hpi := Real.pi_gt_d6
  have hsum : 4 * (1 / (π * |t| * (1 / 4) ^ 2)) + 4 * (1 / (π * |t| * (1 / 2) ^ 2)) ≤ 0.0389 := by
    rw [show 4 * (1 / (π * |t| * (1 / 4) ^ 2)) + 4 * (1 / (π * |t| * (1 / 2) ^ 2)) = 80 / (π * |t|) by
      field_simp; ring, div_le_iff₀ (by positivity)]
    nlinarith
  calc ‖eta2DD t‖ ≤ ‖16 * e (-(1 / 2 * t)) - 16 * e (-(1 / 4 * t)) - 4 * e (-(1 * t))‖ +
        4 * ‖Jq (1 / 4) (1 / 2) t‖ + 4 * ‖Jq (1 / 2) 1 t‖ := by
        unfold eta2DD
        have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
        refine (norm_sub_le _ _).trans ?_
        refine (add_le_add_left (norm_add_le _ _) _).trans ?_
        rw [norm_mul, norm_mul, h4]
    _ ≤ 31.4821 + 0.0389 := by nlinarith
    _ ≤ 31.521 := by norm_num

/-! ### `η₂ · log(4·)`: the case `ρ = 4` of [B, (B.11)] -/

theorem fourier_eta2log4_eq (t : ℝ) :
    𝓕 (fun u => ((Real.log (4 * u) * eta2 u : ℝ) : ℂ)) t =
      (∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) * ((4 * Real.log (4 * u) ^ 2 : ℝ) : ℂ)) +
        ∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) * ((-4 * (Real.log (4 * u) * Real.log u) : ℝ) : ℂ) := by
  rw [fourier_eq_integral_e, integral_eq_pieces (a := 1 / 4) (b := 1 / 2) (c := 1) (by norm_num)
    (by norm_num)]
  · congr 1
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      simp only [Helfgott.eta2_eq_left hu.1 hu.2]; push_cast; ring
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      simp only [Helfgott.eta2_eq_right hu.1 hu.2]; push_cast; ring
  · intro x hx; rw [Helfgott.eta2_eq_zero hx]; simp
  · refine ((continuous_E t).mul (continuous_ofReal.comp ?_)).intervalIntegrable _ _
    refine continuous_iff_continuousAt.2 fun u => ?_
    by_cases hu : 0 < u
    · have h4 : (4 : ℝ) * u ≠ 0 := (mul_pos four_pos hu).ne'
      exact ((continuous_const.mul continuous_id).continuousAt.log h4).mul
        Helfgott.continuous_eta2.continuousAt
    · have h0 : ∀ᶠ v in nhds u, v < 1 / 4 := eventually_lt_nhds (by linarith)
      refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) u).congr
        (h0.mono fun v hv => ?_)
      show (0 : ℝ) = Real.log (4 * v) * eta2 v
      rw [Helfgott.eta2_eq_zero (fun h => by linarith [h.1]), mul_zero]

set_option maxHeartbeats 1000000 in
/-- **`‖(2πt)² (η₂ log(4·))^(t)‖ ≤ 48 log 2`** (no numerics: the jumps of the derivative are
`16 log 2` and `8 log 2`, and `∫|h''|` is `16 log 2` and `8 log 2` on the two pieces). -/
theorem norm_eta2log4_le (t : ℝ) :
    ‖((2 * π * t) ^ 2 : ℂ) * 𝓕 (fun u => ((Real.log (4 * u) * eta2 u : ℝ) : ℂ)) t‖ ≤
      48 * Real.log 2 := by
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht]; simp; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have pos : ∀ {a b x : ℝ}, 0 < a → a ≤ b → x ∈ Set.uIcc a b → 0 < x := fun ha hab hx => by
    rw [Set.uIcc_of_le hab] at hx; exact ha.trans_le hx.1
  have hl2 := Real.log_two_lt_d9
  have hl20 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- the pieces and their derivatives
  have d1 : ∀ x ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt (fun u => 4 * Real.log (4 * u) ^ 2)
      (8 * Real.log (4 * x) * x⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    have := ((((hasDerivAt_id' x).const_mul 4).log (by positivity)).pow 2).const_mul 4
    convert this using 1; field_simp; norm_num
  have d1' : ∀ x ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt (fun u => 8 * Real.log (4 * u) * u⁻¹)
      (8 * (1 - Real.log (4 * x)) * (x ^ 2)⁻¹) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    have := ((((hasDerivAt_id' x).const_mul 4).log (by positivity)).const_mul 8).mul
      (hasDerivAt_inv hx0.ne')
    convert this using 1; field_simp; ring
  have d2 : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1, HasDerivAt (fun u => -4 * (Real.log (4 * u) * Real.log u))
      (-4 * ((Real.log x + Real.log (4 * x)) * x⁻¹)) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    have := ((((hasDerivAt_id' x).const_mul 4).log (by positivity)).mul
      (Real.hasDerivAt_log hx0.ne')).const_mul (-4)
    convert this using 1; field_simp
  have d2' : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1,
      HasDerivAt (fun u => -4 * ((Real.log u + Real.log (4 * u)) * u⁻¹))
        (-4 * ((2 - Real.log x - Real.log (4 * x)) * (x ^ 2)⁻¹)) x := by
    intro x hx; have hx0 := pos (by norm_num) (by norm_num) hx
    have := (((Real.hasDerivAt_log hx0.ne').add
      (((hasDerivAt_id' x).const_mul 4).log (by positivity))).mul (hasDerivAt_inv hx0.ne')).const_mul (-4)
    convert this using 1
    simp only [Pi.add_apply]; field_simp; ring
  have c1 : ContinuousOn (fun x => 8 * (1 - Real.log (4 * x)) * (x ^ 2)⁻¹) (Set.uIcc (1 / 4 : ℝ) (1 / 2)) := by
    refine ContinuousOn.mul (continuousOn_const.mul (continuousOn_const.sub
      (ContinuousOn.log (by fun_prop) fun x hx => ?_))) (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
    · have := pos (by norm_num) (by norm_num) hx; positivity
    · have := pos (by norm_num) (by norm_num) hx; positivity
  have c2 : ContinuousOn (fun x => -4 * ((2 - Real.log x - Real.log (4 * x)) * (x ^ 2)⁻¹))
      (Set.uIcc (1 / 2 : ℝ) 1) := by
    refine continuousOn_const.mul (ContinuousOn.mul (ContinuousOn.sub (continuousOn_const.sub
      (ContinuousOn.log (by fun_prop) fun x hx => ?_)) (ContinuousOn.log (by fun_prop) fun x hx => ?_))
      (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_))
    all_goals have := pos (by norm_num) (by norm_num) hx; positivity
  have l1 : Real.log (4 * (1 / 4)) = 0 := by norm_num
  have l2 : Real.log (4 * (1 / 2)) = Real.log 2 := by norm_num
  have l3 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have l4 : Real.log (4 * 1) = 2 * Real.log 2 := by
    rw [mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hid : ((2 * π * t) ^ 2 : ℂ) * 𝓕 (fun u => ((Real.log (4 * u) * eta2 u : ℝ) : ℂ)) t =
      16 * (Real.log 2 : ℂ) * e (-(1 / 2 * t)) - 8 * (Real.log 2 : ℂ) * e (-(1 * t)) -
        (∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) * ((8 * (1 - Real.log (4 * u)) * (u ^ 2)⁻¹ : ℝ) : ℂ)) -
        ∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) *
          ((-4 * ((2 - Real.log u - Real.log (4 * u)) * (u ^ 2)⁻¹) : ℝ) : ℂ) := by
    rw [fourier_eta2log4_eq, mul_add, ibp2 ht d1 d1' c1, ibp2 ht d2 d2' c2]
    simp only [l1, l2, l3, l4, Real.log_one]
    push_cast; ring
  rw [hid]
  have hI1 : ‖∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) *
      ((8 * (1 - Real.log (4 * u)) * (u ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 16 * Real.log 2 := by
    have h := norm_integral_E_le (t := t) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) d1' c1 (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      have : Real.log (4 * x) ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith [hx.2])
      have : 0 ≤ (x ^ 2)⁻¹ := by positivity
      have : 0 ≤ 1 - Real.log (4 * x) := by linarith
      positivity)
    simp only [l1, l2] at h
    refine h.trans (le_of_eq ?_); norm_num; ring
  have hI2 : ‖∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) *
      ((-4 * ((2 - Real.log u - Real.log (4 * u)) * (u ^ 2)⁻¹) : ℝ) : ℂ)‖ ≤ 8 * Real.log 2 := by
    have d2n : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1,
        HasDerivAt (fun u => -(-4 * ((Real.log u + Real.log (4 * u)) * u⁻¹)))
          (-(-4 * ((2 - Real.log x - Real.log (4 * x)) * (x ^ 2)⁻¹))) x := fun x hx => (d2' x hx).neg
    have h := norm_integral_E_le (t := t) (by norm_num : (1 / 2 : ℝ) ≤ 1) d2n c2.neg (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      have : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx.2
      have : Real.log (4 * x) ≤ 2 * Real.log 2 := by
        rw [← l4]; exact Real.log_le_log (by positivity) (by linarith [hx.2])
      have : 0 ≤ (x ^ 2)⁻¹ := by positivity
      have : 0 ≤ 2 - Real.log x - Real.log (4 * x) := by linarith
      have := mul_nonneg this ‹0 ≤ (x ^ 2)⁻¹›
      linarith)
    have e : ‖∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) *
        ((-(-4 * ((2 - Real.log u - Real.log (4 * u)) * (u ^ 2)⁻¹)) : ℝ) : ℂ)‖ =
        ‖∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) *
          ((-4 * ((2 - Real.log u - Real.log (4 * u)) * (u ^ 2)⁻¹) : ℝ) : ℂ)‖ := by
      rw [← norm_neg, ← intervalIntegral.integral_neg]; congr 1
      refine intervalIntegral.integral_congr fun u _ => ?_; push_cast; ring
    rw [e] at h
    simp only [l3, Real.log_one, l4] at h
    refine h.trans (le_of_eq ?_); norm_num; ring
  have hE : ∀ x, ‖e x‖ = 1 := norm_e
  have n16 : ‖16 * (Real.log 2 : ℂ) * e (-(1 / 2 * t))‖ = 16 * Real.log 2 := by
    rw [norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl20]; norm_num
  have n8 : ‖8 * (Real.log 2 : ℂ) * e (-(1 * t))‖ = 8 * Real.log 2 := by
    rw [norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl20]; norm_num
  calc _ ≤ ‖16 * (Real.log 2 : ℂ) * e (-(1 / 2 * t))‖ + ‖8 * (Real.log 2 : ℂ) * e (-(1 * t))‖ +
        16 * Real.log 2 + 8 * Real.log 2 :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          (norm_sub_le _ _) hI1)) hI2)
    _ = 48 * Real.log 2 := by rw [n16, n8]; ring

end TernaryGoldbach.MinorArcs
