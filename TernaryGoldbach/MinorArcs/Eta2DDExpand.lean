import TernaryGoldbach.MinorArcs.Eta2Fourier

/-!
# `‖η̂₂''(t)‖ ≤ 32` for `t ≥ 2`: three integrations by parts and a kernel-checked grid

Write `z = e(−t/4)` and `w = 1/(2πt)`. Integrating `J(a, b) = ∫_a^b e(−ut)/u² du` by parts three
times gives `eta2DD t = F(z, w) + R` (`norm_eta2DD_sub_Fz`), where

`F(z, w) = 16z² − 16z − 4z⁴ + 4 (B₀(z) (iw) + B₁(z) (iw)² + B₂(z) (iw)³)`,
`B₀ = 8z² − 16z − z⁴`, `B₁ = 32z² − 128z − 2z⁴`, `B₂ = 192z² − 1536z − 6z⁴`,

and `‖R‖ ≤ 6120 w³`. `F` is a polynomial with integer coefficients. We bound it for every `z` on the
unit circle and every `w ∈ [0, 2/25]`, so `z` and `w` are treated as independent. The circle is
parametrised rationally: `z = ±zm(m)`, `zm(m) = ((1 − m²) + 2mi)/(1 + m²)`, `m ∈ [−1, 1]`
(`exists_zm`). `‖zm(m) − zm(m')‖ ≤ 2|m − m'|` (`norm_zm_sub_le`), and `F` is Lipschitz in `z` and in
`w` (`norm_Fz_sub_z`, `norm_Fz_sub_w`).

The kernel checks the bound by recursive bisection of `[−1, 1] × [0, 2/25]` (`chk`). On each cell
it evaluates `F` exactly over `ℚ` at the centre (`FQ`), and adds the Lipschitz terms and the
remainder. `chk_sound` turns a successful check into the bound on the whole rectangle.
-/

open Real Complex MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-! ## Three integrations by parts -/

/-- One integration by parts against `E(u) = e(−ut)`, with `E' = cE`, `c = −2πit`:
`c ∫_a^b E g = [E g]_a^b − ∫_a^b E g'`. -/
theorem ibp1 {a b t : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x) (hc : ContinuousOn g' (Set.uIcc a b)) :
    (-(2 * π * I * t)) * ∫ u in a..b, e (-(u * t)) * (g u : ℂ) =
      (e (-(b * t)) * g b - e (-(a * t)) * g a) - ∫ u in a..b, e (-(u * t)) * (g' u : ℂ) := by
  have hgC : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u => (g u : ℂ)) (g' x : ℂ) x :=
    fun x hx => (hg x hx).ofReal_comp
  have hE : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => e (-(u * t)))
      (-(2 * π * I * t) * e (-(x * t))) x := fun x _ => hasDerivAt_E t x
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgC hE
    ((continuous_ofReal.comp_continuousOn hc).intervalIntegrable)
    ((continuous_const.mul (continuous_E t)).intervalIntegrable a b)
  rw [← intervalIntegral.integral_const_mul]
  have e1 : ∫ u in a..b, -(2 * π * I * t) * (e (-(u * t)) * (g u : ℂ)) =
      ∫ u in a..b, (g u : ℂ) * (-(2 * π * I * t) * e (-(u * t))) := by
    congr 1; ext u; ring
  have e2 : ∫ u in a..b, e (-(u * t)) * (g' u : ℂ) =
      ∫ u in a..b, (g' u : ℂ) * e (-(u * t)) := by
    congr 1; ext u; ring
  rw [e1, h, e2]; ring

theorem hasDerivAt_inv_cube {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => -2 * (u ^ 3)⁻¹) (6 * (x ^ 4)⁻¹) x := by
  have := ((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx)).const_mul (-2)
  convert this using 1; field_simp; ring

theorem hasDerivAt_inv_four {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => 6 * (u ^ 4)⁻¹) (-24 * (x ^ 5)⁻¹) x := by
  have := ((hasDerivAt_pow 4 x).inv (pow_ne_zero 4 hx)).const_mul 6
  convert this using 1; field_simp; ring

theorem hasDerivAt_inv_four' {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => -6 * (u ^ 4)⁻¹) (24 * (x ^ 5)⁻¹) x := by
  have := ((hasDerivAt_pow 4 x).inv (pow_ne_zero 4 hx)).const_mul (-6)
  convert this using 1; field_simp; ring

theorem continuousOn_inv_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℝ) (n : ℕ) :
    ContinuousOn (fun u : ℝ => k * (u ^ n)⁻¹) (Set.uIcc a b) := by
  refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
  rw [Set.uIcc_of_le hab] at hx; have : 0 < x := ha.trans_le hx.1; positivity

/-- `I w (−2πit) = 1` for `w = 1/(2πt)`. -/
theorem I_w_mul_c {t : ℝ} (ht : t ≠ 0) : -(2 * π * I * t) * (I * ((1 / (2 * π * t) : ℝ) : ℂ)) = 1 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp
  rw [Complex.I_sq]; ring

/-- **`J(a, b)` after three integrations by parts.** With `w = 1/(2πt)` and `E(u) = e(−ut)`:
`J(a, b) = iw [E/u²]_a^b + 2(iw)² [E/u³]_a^b + 6(iw)³ [E/u⁴]_a^b + R`,
`‖R‖ ≤ |w|³ · 6(a⁻⁴ − b⁻⁴)`. -/
theorem norm_Jq_sub_expand {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    ‖Jq a b t - ((I * ((1 / (2 * π * t) : ℝ) : ℂ)) *
        (e (-(b * t)) * ((b ^ 2)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 2)⁻¹ : ℝ)) +
      2 * (I * ((1 / (2 * π * t) : ℝ) : ℂ)) ^ 2 *
        (e (-(b * t)) * ((b ^ 3)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 3)⁻¹ : ℝ)) +
      6 * (I * ((1 / (2 * π * t) : ℝ) : ℂ)) ^ 3 *
        (e (-(b * t)) * ((b ^ 4)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 4)⁻¹ : ℝ)))‖ ≤
      |1 / (2 * π * t)| ^ 3 * (6 * ((a ^ 4)⁻¹ - (b ^ 4)⁻¹)) := by
  set w : ℝ := 1 / (2 * π * t) with hw
  set c : ℂ := -(2 * π * I * t) with hc
  have hcw : c * (I * (w : ℂ)) = 1 := I_w_mul_c ht
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hab] at hx; exact ha.trans_le hx.1
  have d0 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => (u ^ 2)⁻¹) (-2 * (x ^ 3)⁻¹) x :=
    fun x hx => hasDerivAt_inv_sq (hpos x hx).ne'
  have d1 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -2 * (u ^ 3)⁻¹) (6 * (x ^ 4)⁻¹) x :=
    fun x hx => hasDerivAt_inv_cube (hpos x hx).ne'
  have d2 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => 6 * (u ^ 4)⁻¹) (-24 * (x ^ 5)⁻¹) x :=
    fun x hx => hasDerivAt_inv_four (hpos x hx).ne'
  have h1 := ibp1 (t := t) d0 (continuousOn_inv_pow ha hab (-2) 3)
  have h2 := ibp1 (t := t) d1 (continuousOn_inv_pow ha hab 6 4)
  have h3 := ibp1 (t := t) d2 (continuousOn_inv_pow ha hab (-24) 5)
  set J0 := ∫ u in a..b, e (-(u * t)) * (((u ^ 2)⁻¹ : ℝ) : ℂ)
  set J1 := ∫ u in a..b, e (-(u * t)) * (((-2 * (u ^ 3)⁻¹ : ℝ)) : ℂ)
  set J2 := ∫ u in a..b, e (-(u * t)) * (((6 * (u ^ 4)⁻¹ : ℝ)) : ℂ)
  set J3 := ∫ u in a..b, e (-(u * t)) * (((-24 * (u ^ 5)⁻¹ : ℝ)) : ℂ)
  have k : ∀ {X Y : ℂ}, c * X = Y → X = I * w * Y := fun {X Y} h => by
    calc X = (c * (I * w)) * X := by rw [hcw, one_mul]
      _ = I * w * (c * X) := by ring
      _ = I * w * Y := by rw [h]
  have k1 := k h1
  have k2 := k h2
  have k3 := k h3
  have hJ : Jq a b t = J0 := rfl
  have hdiff : Jq a b t - ((I * (w : ℂ)) *
        (e (-(b * t)) * ((b ^ 2)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 2)⁻¹ : ℝ)) +
      2 * (I * (w : ℂ)) ^ 2 *
        (e (-(b * t)) * ((b ^ 3)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 3)⁻¹ : ℝ)) +
      6 * (I * (w : ℂ)) ^ 3 *
        (e (-(b * t)) * ((b ^ 4)⁻¹ : ℝ) - e (-(a * t)) * ((a ^ 4)⁻¹ : ℝ))) =
      -(I * (w : ℂ)) ^ 3 * J3 := by
    rw [hJ, k1, k2, k3]; push_cast; ring
  rw [hdiff, norm_mul, norm_neg, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- `‖J3‖ = ‖∫ E · 24 u⁻⁵‖ ≤ 6 (a⁻⁴ − b⁻⁴)`
  have hJ3 : J3 = -∫ u in a..b, e (-(u * t)) * (((24 * (u ^ 5)⁻¹ : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_neg]; simp only [J3]; congr 1; funext u; push_cast; ring
  rw [hJ3, norm_neg]
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -6 * (u ^ 4)⁻¹) (24 * (x ^ 5)⁻¹) x :=
    fun x hx => hasDerivAt_inv_four' (hpos x hx).ne'
  refine (norm_integral_E_le hab hG (continuousOn_inv_pow ha hab 24 5) fun x hx => ?_).trans
    (le_of_eq (by ring))
  have : 0 < x := ha.trans_le hx.1
  positivity

/-! ## The polynomial `F` -/

/-- `F(z, w) = 16z² − 16z − 4z⁴ + 4(B₀ (iw) + B₁ (iw)² + B₂ (iw)³)`. -/
noncomputable def Fz (z : ℂ) (w : ℝ) : ℂ :=
  16 * z ^ 2 - 16 * z - 4 * z ^ 4 +
    4 * ((8 * z ^ 2 - 16 * z - z ^ 4) * (I * w) + (32 * z ^ 2 - 128 * z - 2 * z ^ 4) * (I * w) ^ 2 +
      (192 * z ^ 2 - 1536 * z - 6 * z ^ 4) * (I * w) ^ 3)

/-- **`eta2DD t = F(e(−t/4), 1/(2πt)) + O*(6120 |w|³)`.** -/
theorem norm_eta2DD_sub_Fz {t : ℝ} (ht : t ≠ 0) :
    ‖eta2DD t - Fz (e (-(1 / 4 * t))) (1 / (2 * π * t))‖ ≤ 6120 * |1 / (2 * π * t)| ^ 3 := by
  set w : ℝ := 1 / (2 * π * t) with hw
  set z := e (-(1 / 4 * t))
  have e2 : e (-(1 / 2 * t)) = z ^ 2 := by
    rw [sq, ← e_add]; congr 1; ring
  have e4 : e (-(1 * t)) = z ^ 4 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, ← e2, sq, ← e_add]; congr 1; ring
  have h1 := norm_Jq_sub_expand (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num) ht
  have h2 := norm_Jq_sub_expand (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) ht
  rw [← hw] at h1 h2
  rw [e2] at h1
  rw [e2, e4] at h2
  set R1 := Jq (1 / 4) (1 / 2) t - _ with hR1
  set R2 := Jq (1 / 2) 1 t - _ with hR2
  have hE : eta2DD t - Fz z w = 4 * R1 - 4 * R2 := by
    rw [hR1, hR2, eta2DD, e2, e4, Fz]
    push_cast
    ring
  rw [hE]
  calc ‖4 * R1 - 4 * R2‖ ≤ 4 * ‖R1‖ + 4 * ‖R2‖ := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul]; norm_num
    _ ≤ 4 * (|w| ^ 3 * (6 * ((((1 : ℝ) / 4) ^ 4)⁻¹ - (((1 : ℝ) / 2) ^ 4)⁻¹))) +
        4 * (|w| ^ 3 * (6 * ((((1 : ℝ) / 2) ^ 4)⁻¹ - ((1 : ℝ) ^ 4)⁻¹))) := by gcongr
    _ = 6120 * |w| ^ 3 := by norm_num; ring

/-! ## The rational parametrisation of the circle -/

/-- `zm(m) = ((1 − m²) + 2mi)/(1 + m²)`. -/
noncomputable def zm (m : ℝ) : ℂ := ⟨(1 - m ^ 2) / (1 + m ^ 2), 2 * m / (1 + m ^ 2)⟩

theorem normSq_zm_sub (m m' : ℝ) :
    Complex.normSq (zm m - zm m') = 4 * (m - m') ^ 2 / ((1 + m ^ 2) * (1 + m' ^ 2)) := by
  have h1 : (0 : ℝ) < 1 + m ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + m' ^ 2 := by positivity
  rw [Complex.normSq_apply]
  simp only [zm, Complex.sub_re, Complex.sub_im]
  field_simp
  ring

theorem norm_zm (m : ℝ) : ‖zm m‖ = 1 := by
  have h1 : (0 : ℝ) < 1 + m ^ 2 := by positivity
  have h : Complex.normSq (zm m) = 1 := by
    rw [Complex.normSq_apply]; simp only [zm]; field_simp; ring
  have h2 : ‖zm m‖ ^ 2 = 1 := by rw [Complex.sq_norm, h]
  rw [← Real.sqrt_sq (norm_nonneg (zm m)), h2, Real.sqrt_one]

/-- `‖zm(m) − zm(m')‖ ≤ 2|m − m'|`. -/
theorem norm_zm_sub_le (m m' : ℝ) : ‖zm m - zm m'‖ ≤ 2 * |m - m'| := by
  have h1 : (1 : ℝ) ≤ 1 + m ^ 2 := by nlinarith [sq_nonneg m]
  have h2 : (1 : ℝ) ≤ 1 + m' ^ 2 := by nlinarith [sq_nonneg m']
  have hsq : ‖zm m - zm m'‖ ^ 2 ≤ (2 * |m - m'|) ^ 2 := by
    rw [Complex.sq_norm, normSq_zm_sub, mul_pow, sq_abs, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (1 + m ^ 2) * (1 + m' ^ 2) := by nlinarith
    nlinarith [sq_nonneg (m - m')]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

theorem eq_zm_of_re_nonneg {z : ℂ} (hz : ‖z‖ = 1) (hre : 0 ≤ z.re) :
    ∃ m ∈ Set.Icc (-1 : ℝ) 1, z = zm m := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; nlinarith
  set x := z.re
  set y := z.im
  have hx1 : 0 < 1 + x := by linarith
  refine ⟨y / (1 + x), ?_, ?_⟩
  · have hy : |y| ≤ 1 + x := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y - (1 + x)), sq_nonneg (y + (1 + x))]
    have : |y / (1 + x)| ≤ 1 := by
      rw [abs_div, abs_of_pos hx1, div_le_one hx1]; exact hy
    exact abs_le.1 this
  · have hd : 1 + (y / (1 + x)) ^ 2 = 2 / (1 + x) := by
      field_simp; nlinarith
    apply Complex.ext
    · simp only [zm]
      rw [hd]; field_simp; nlinarith
    · simp only [zm]
      rw [hd]; field_simp; rfl

/-- Every point of the unit circle is `±zm(m)` with `m ∈ [−1, 1]`. -/
theorem exists_zm {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ m ∈ Set.Icc (-1 : ℝ) 1, z = s * zm m := by
  rcases le_or_gt 0 z.re with h | h
  · obtain ⟨m, hm, rfl⟩ := eq_zm_of_re_nonneg hz h
    exact ⟨1, Or.inl rfl, m, hm, by simp⟩
  · obtain ⟨m, hm, hm'⟩ := eq_zm_of_re_nonneg (z := -z) (by rw [norm_neg, hz])
      (by simp only [Complex.neg_re]; linarith)
    refine ⟨-1, Or.inr rfl, m, hm, ?_⟩
    rw [← hm']; push_cast; ring

/-! ## Lipschitz bounds for `F` -/

theorem norm_cubic_le (a₀ a₁ a₂ a₃ w : ℝ) (hw : 0 ≤ w) :
    ‖(a₀ : ℂ) + a₁ * (I * w) + a₂ * (I * w) ^ 2 + a₃ * (I * w) ^ 3‖ ≤
      |a₀| + |a₁| * w + |a₂| * w ^ 2 + |a₃| * w ^ 3 := by
  have hn : ‖I * (w : ℂ)‖ = w := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))) (le_of_eq ?_))) (le_of_eq ?_))
  · rw [Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_mul, hn, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_mul, norm_pow, hn, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_mul, norm_pow, hn, Complex.norm_real, Real.norm_eq_abs]

theorem norm_sq_sub_le {z z' : ℂ} (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1) :
    ‖z ^ 2 - z' ^ 2‖ ≤ 2 * ‖z - z'‖ := by
  rw [show z ^ 2 - z' ^ 2 = (z + z') * (z - z') by ring, norm_mul]
  have : ‖z + z'‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hz, hz']; norm_num)
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem norm_four_sub_le {z z' : ℂ} (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1) :
    ‖z ^ 4 - z' ^ 4‖ ≤ 4 * ‖z - z'‖ := by
  rw [show z ^ 4 - z' ^ 4 = (z ^ 2 + z' ^ 2) * (z ^ 2 - z' ^ 2) by ring, norm_mul]
  have h1 : ‖z ^ 2 + z' ^ 2‖ ≤ 2 :=
    (norm_add_le _ _).trans (by rw [norm_pow, norm_pow, hz, hz']; norm_num)
  have h2 := norm_sq_sub_le hz hz'
  calc ‖z ^ 2 + z' ^ 2‖ * ‖z ^ 2 - z' ^ 2‖ ≤ 2 * (2 * ‖z - z'‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 4 * ‖z - z'‖ := by ring

/-- `Lz(w) = 64 + 144w + 800w² + 7776w³`. -/
def LzR (w : ℝ) : ℝ := 64 + 144 * w + 800 * w ^ 2 + 7776 * w ^ 3

/-- `F` is `Lz(w)`-Lipschitz in `z` on the unit circle. -/
theorem norm_Fz_sub_z {z z' : ℂ} (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖Fz z w - Fz z' w‖ ≤ LzR w * ‖z - z'‖ := by
  have hA2 := norm_cubic_le 16 32 128 768 w hw
  have hA1 := norm_cubic_le (-16) (-64) (-512) (-6144) w hw
  have hA4 := norm_cubic_le (-4) (-4) (-8) (-24) w hw
  set A2 : ℂ := ((16 : ℝ) : ℂ) + ((32 : ℝ) : ℂ) * (I * w) + ((128 : ℝ) : ℂ) * (I * w) ^ 2 +
    ((768 : ℝ) : ℂ) * (I * w) ^ 3
  set A1 : ℂ := ((-16 : ℝ) : ℂ) + ((-64 : ℝ) : ℂ) * (I * w) + ((-512 : ℝ) : ℂ) * (I * w) ^ 2 +
    ((-6144 : ℝ) : ℂ) * (I * w) ^ 3
  set A4 : ℂ := ((-4 : ℝ) : ℂ) + ((-4 : ℝ) : ℂ) * (I * w) + ((-8 : ℝ) : ℂ) * (I * w) ^ 2 +
    ((-24 : ℝ) : ℂ) * (I * w) ^ 3
  have hF : Fz z w - Fz z' w = A2 * (z ^ 2 - z' ^ 2) + A1 * (z - z') + A4 * (z ^ 4 - z' ^ 4) := by
    simp only [Fz, A2, A1, A4]; push_cast; ring
  rw [hF]
  have hs2 := norm_sq_sub_le hz hz'
  have hs4 := norm_four_sub_le hz hz'
  have hd : 0 ≤ ‖z - z'‖ := norm_nonneg _
  calc ‖A2 * (z ^ 2 - z' ^ 2) + A1 * (z - z') + A4 * (z ^ 4 - z' ^ 4)‖
      ≤ ‖A2‖ * ‖z ^ 2 - z' ^ 2‖ + ‖A1‖ * ‖z - z'‖ + ‖A4‖ * ‖z ^ 4 - z' ^ 4‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_) <;>
          simp only [norm_mul, le_refl]
    _ ≤ ‖A2‖ * (2 * ‖z - z'‖) + ‖A1‖ * ‖z - z'‖ + ‖A4‖ * (4 * ‖z - z'‖) := by gcongr
    _ = (2 * ‖A2‖ + ‖A1‖ + 4 * ‖A4‖) * ‖z - z'‖ := by ring
    _ ≤ LzR w * ‖z - z'‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hd
        unfold LzR
        norm_num [abs_of_nonneg] at hA2 hA1 hA4
        nlinarith

theorem LzR_mono {w w' : ℝ} (hw : 0 ≤ w) (h : w ≤ w') : LzR w ≤ LzR w' := by
  unfold LzR
  have h2 : w ^ 2 ≤ w' ^ 2 := pow_le_pow_left₀ hw h 2
  have h3 : w ^ 3 ≤ w' ^ 3 := pow_le_pow_left₀ hw h 3
  nlinarith

/-- `Lw(W) = 4(25 + 324W + 5202W²)`. -/
def LwR (W : ℝ) : ℝ := 4 * (25 + 324 * W + 5202 * W ^ 2)

theorem norm_B_le {z : ℂ} (hz : ‖z‖ = 1) (a b c : ℝ) :
    ‖(a : ℂ) * z ^ 2 + b * z + c * z ^ 4‖ ≤ |a| + |b| + |c| := by
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
    simp [norm_mul, norm_pow, hz]

/-- `F` is `Lw(W)`-Lipschitz in `w ∈ [0, W]`, for `‖z‖ = 1`. -/
theorem norm_Fz_sub_w {z : ℂ} (hz : ‖z‖ = 1) {w w' W : ℝ} (hw : 0 ≤ w) (hw' : 0 ≤ w')
    (hW : w ≤ W) (hW' : w' ≤ W) :
    ‖Fz z w - Fz z w'‖ ≤ LwR W * |w - w'| := by
  have hB0 := norm_B_le hz 8 (-16) (-1)
  have hB1 := norm_B_le hz 32 (-128) (-2)
  have hB2 := norm_B_le hz 192 (-1536) (-6)
  set B0 : ℂ := ((8 : ℝ) : ℂ) * z ^ 2 + ((-16 : ℝ) : ℂ) * z + ((-1 : ℝ) : ℂ) * z ^ 4
  set B1 : ℂ := ((32 : ℝ) : ℂ) * z ^ 2 + ((-128 : ℝ) : ℂ) * z + ((-2 : ℝ) : ℂ) * z ^ 4
  set B2 : ℂ := ((192 : ℝ) : ℂ) * z ^ 2 + ((-1536 : ℝ) : ℂ) * z + ((-6 : ℝ) : ℂ) * z ^ 4
  have hF : Fz z w - Fz z w' = 4 * (B0 * I * ((w - w' : ℝ) : ℂ) + B1 * I ^ 2 * ((w ^ 2 - w' ^ 2 : ℝ) : ℂ) +
      B2 * I ^ 3 * ((w ^ 3 - w' ^ 3 : ℝ) : ℂ)) := by
    simp only [Fz, B0, B1, B2]; push_cast; ring
  have hsq : |w ^ 2 - w' ^ 2| ≤ 2 * W * |w - w'| := by
    rw [show w ^ 2 - w' ^ 2 = (w + w') * (w - w') by ring, abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hcu : |w ^ 3 - w' ^ 3| ≤ 3 * W ^ 2 * |w - w'| := by
    rw [show w ^ 3 - w' ^ 3 = (w ^ 2 + w * w' + w' ^ 2) * (w - w') by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    nlinarith [mul_le_mul hW hW' hw' (by linarith : (0:ℝ) ≤ W)]
  rw [hF]
  have hI2 : ‖I ^ 2‖ = 1 := by rw [norm_pow, Complex.norm_I, one_pow]
  have hI3 : ‖I ^ 3‖ = 1 := by rw [norm_pow, Complex.norm_I, one_pow]
  calc ‖4 * (B0 * I * ((w - w' : ℝ) : ℂ) + B1 * I ^ 2 * ((w ^ 2 - w' ^ 2 : ℝ) : ℂ) +
        B2 * I ^ 3 * ((w ^ 3 - w' ^ 3 : ℝ) : ℂ))‖
      ≤ 4 * (‖B0‖ * |w - w'| + ‖B1‖ * |w ^ 2 - w' ^ 2| + ‖B2‖ * |w ^ 3 - w' ^ 3|) := by
        rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
          simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, hI2, hI3, mul_one,
            le_refl]
    _ ≤ 4 * (25 * |w - w'| + 162 * (2 * W * |w - w'|) + 1734 * (3 * W ^ 2 * |w - w'|)) := by
        have h0 : 0 ≤ |w - w'| := abs_nonneg _
        have hB0' : ‖B0‖ ≤ 25 := by norm_num at hB0; linarith
        have hB1' : ‖B1‖ ≤ 162 := by norm_num at hB1; linarith
        have hB2' : ‖B2‖ ≤ 1734 := by norm_num at hB2; linarith
        gcongr
    _ = LwR W * |w - w'| := by unfold LwR; ring

/-! ## The kernel check -/

/-- Complex numbers as pairs of rationals. -/
def cmul (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- `a z² + b z + c z⁴`. -/
def lc3 (a b c : ℚ) (z2 z z4 : ℚ × ℚ) : ℚ × ℚ :=
  (a * z2.1 + b * z.1 + c * z4.1, a * z2.2 + b * z.2 + c * z4.2)

def cadd (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 + q.1, p.2 + q.2)

/-- `F(s · zm(m), w)` over `ℚ`. -/
def FQ (s m w : ℚ) : ℚ × ℚ :=
  let z : ℚ × ℚ := (s * (1 - m ^ 2) / (1 + m ^ 2), s * (2 * m) / (1 + m ^ 2))
  let z2 := cmul z z
  let z4 := cmul z2 z2
  let iw : ℚ × ℚ := (0, w)
  let iw2 := cmul iw iw
  let iw3 := cmul iw2 iw
  cadd (lc3 16 (-16) (-4) z2 z z4)
    (cadd (cmul (lc3 32 (-64) (-4) z2 z z4) iw)
      (cadd (cmul (lc3 128 (-512) (-8) z2 z z4) iw2) (cmul (lc3 768 (-6144) (-24) z2 z z4) iw3)))

def toC (p : ℚ × ℚ) : ℂ := ⟨p.1, p.2⟩

theorem toC_cmul (p q : ℚ × ℚ) : toC (cmul p q) = toC p * toC q := by
  apply Complex.ext <;> simp [toC, cmul, Complex.mul_re, Complex.mul_im]

theorem toC_cadd (p q : ℚ × ℚ) : toC (cadd p q) = toC p + toC q := by
  apply Complex.ext <;> simp [toC, cadd]

theorem toC_lc3 (a b c : ℚ) (z2 z z4 : ℚ × ℚ) :
    toC (lc3 a b c z2 z z4) = (a : ℂ) * toC z2 + (b : ℂ) * toC z + (c : ℂ) * toC z4 := by
  apply Complex.ext <;> simp [toC, lc3]

theorem toC_FQ (s m w : ℚ) : toC (FQ s m w) = Fz ((s : ℝ) * zm m) w := by
  have hz : toC (s * (1 - m ^ 2) / (1 + m ^ 2), s * (2 * m) / (1 + m ^ 2)) = (s : ℝ) * zm m := by
    apply Complex.ext <;> simp [toC, zm] <;> ring
  have hiw : toC ((0 : ℚ), w) = I * ((w : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [toC]
  simp only [FQ, toC_cadd, toC_cmul, toC_lc3, hz, hiw, Fz]
  push_cast
  ring

theorem norm_sq_toC (p : ℚ × ℚ) : ‖toC p‖ ^ 2 = ((p.1 ^ 2 + p.2 ^ 2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [toC]; ring

def LzQ (w : ℚ) : ℚ := 64 + 144 * w + 800 * w ^ 2 + 7776 * w ^ 3
def LwQ (W : ℚ) : ℚ := 4 * (25 + 324 * W + 5202 * W ^ 2)

/-- The margin of a cell `[m₀, m₁] × [w₀, w₁]`. -/
def margin (m0 m1 w0 w1 : ℚ) : ℚ :=
  32 - LzQ w1 * (m1 - m0) - LwQ w1 * (w1 - w0) / 2 - 6120 * w1 ^ 3

def cellOK (s m0 m1 w0 w1 : ℚ) : Bool :=
  let F := FQ s ((m0 + m1) / 2) ((w0 + w1) / 2)
  let M := margin m0 m1 w0 w1
  decide (0 ≤ M) && decide (F.1 ^ 2 + F.2 ^ 2 ≤ M ^ 2)

/-- Recursive bisection: split along `m` or `w`, whichever contributes more to the margin. -/
def chk : ℕ → ℚ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, s, m0, m1, w0, w1 => cellOK s m0 m1 w0 w1
  | n + 1, s, m0, m1, w0, w1 =>
    cellOK s m0 m1 w0 w1 ||
      (if LwQ w1 * (w1 - w0) / 2 ≤ LzQ w1 * (m1 - m0) then
        chk n s m0 ((m0 + m1) / 2) w0 w1 && chk n s ((m0 + m1) / 2) m1 w0 w1
      else chk n s m0 m1 w0 ((w0 + w1) / 2) && chk n s m0 m1 ((w0 + w1) / 2) w1)

/-- The conclusion of a check. -/
def GoodB (s : ℚ) (m0 m1 w0 w1 : ℚ) : Prop :=
  ∀ m w : ℝ, (m0 : ℝ) ≤ m → m ≤ m1 → (w0 : ℝ) ≤ w → w ≤ w1 →
    ‖Fz ((s : ℝ) * zm m) w‖ + 6120 * w ^ 3 ≤ 32

theorem norm_s_zm {s : ℚ} (hs : s = 1 ∨ s = -1) (m : ℝ) : ‖((s : ℝ) : ℂ) * zm m‖ = 1 := by
  rw [norm_mul, norm_zm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases hs with rfl | rfl <;> norm_num

theorem cellOK_sound {s m0 m1 w0 w1 : ℚ} (hs : s = 1 ∨ s = -1) (hw0 : 0 ≤ w0)
    (h : cellOK s m0 m1 w0 w1 = true) : GoodB s m0 m1 w0 w1 := by
  intro m w hm0 hm1 hw0' hw1
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hF⟩ := h
  set mc : ℚ := (m0 + m1) / 2
  set wc : ℚ := (w0 + w1) / 2
  set F := FQ s mc wc
  set M := margin m0 m1 w0 w1
  have hw0R : (0 : ℝ) ≤ w0 := by exact_mod_cast hw0
  have hwc0 : (0 : ℝ) ≤ wc := by simp only [wc]; push_cast; linarith
  have hwc1 : (wc : ℝ) ≤ w1 := by simp only [wc]; push_cast; linarith
  have hw : 0 ≤ w := hw0R.trans hw0'
  -- the value at the centre
  have hFc : ‖Fz ((s : ℝ) * zm mc) wc‖ ≤ M := by
    rw [← toC_FQ]
    have h1 := norm_sq_toC F
    have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
    have hF' : ((F.1 ^ 2 + F.2 ^ 2 : ℚ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hF
    exact (sq_le_sq₀ (norm_nonneg _) hM').1 (h1 ▸ hF')
  -- Lipschitz in `w`, then in `z`
  have hz1 := norm_s_zm hs m
  have hzc := norm_s_zm hs mc
  have hLw := norm_Fz_sub_w hz1 hw hwc0 hw1 hwc1
  have hLz := norm_Fz_sub_z hz1 hzc hwc0
  have hzz : ‖((s : ℝ) : ℂ) * zm m - ((s : ℝ) : ℂ) * zm mc‖ ≤ (m1 - m0 : ℝ) := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs1 : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [hs1, one_mul]
    refine (norm_zm_sub_le _ _).trans ?_
    have : |m - (mc : ℝ)| ≤ (m1 - m0 : ℝ) / 2 := by
      simp only [mc]; push_cast; rw [abs_le]; constructor <;> linarith
    linarith
  have hwc : |w - (wc : ℝ)| ≤ (w1 - w0 : ℝ) / 2 := by
    simp only [wc]; push_cast; rw [abs_le]; constructor <;> linarith
  have hLzm : LzR wc ≤ LzQ w1 := by
    refine (LzR_mono hwc0 hwc1).trans (le_of_eq ?_); unfold LzR LzQ; push_cast; ring
  have hLw1 : LwR w1 = LwQ w1 := by unfold LwR LwQ; push_cast; ring
  have hMdef : (M : ℝ) = 32 - LzQ w1 * (m1 - m0) - LwQ w1 * (w1 - w0) / 2 - 6120 * (w1 : ℝ) ^ 3 := by
    simp only [M, margin]; push_cast; ring
  have hdm : (0 : ℝ) ≤ m1 - m0 := by linarith
  have hw3 : w ^ 3 ≤ (w1 : ℝ) ^ 3 := pow_le_pow_left₀ hw hw1 3
  have hLwpos : 0 ≤ LwR w1 := by unfold LwR; have : (0 : ℝ) ≤ w1 := by linarith
                                 positivity
  have hLzpos : 0 ≤ LzR wc := by unfold LzR; positivity
  calc ‖Fz ((s : ℝ) * zm m) w‖ + 6120 * w ^ 3
      ≤ (‖Fz ((s : ℝ) * zm m) wc‖ + LwR w1 * |w - wc|) + 6120 * w ^ 3 := by
        have := norm_sub_norm_le (Fz ((s : ℝ) * zm m) w) (Fz ((s : ℝ) * zm m) wc)
        linarith
    _ ≤ (‖Fz ((s : ℝ) * zm mc) wc‖ + LzR wc * (m1 - m0) + LwR w1 * ((w1 - w0) / 2)) +
        6120 * (w1 : ℝ) ^ 3 := by
        have := norm_sub_norm_le (Fz ((s : ℝ) * zm m) wc) (Fz ((s : ℝ) * zm mc) wc)
        have h1 : LzR wc * ‖((s : ℝ) : ℂ) * zm m - ((s : ℝ) : ℂ) * zm mc‖ ≤ LzR wc * (m1 - m0) :=
          mul_le_mul_of_nonneg_left hzz hLzpos
        have h2 : LwR w1 * |w - wc| ≤ LwR w1 * ((w1 - w0) / 2) :=
          mul_le_mul_of_nonneg_left hwc hLwpos
        linarith
    _ ≤ 32 := by
        have : LzR wc * (m1 - m0) ≤ LzQ w1 * (m1 - m0) := mul_le_mul_of_nonneg_right hLzm hdm
        rw [hLw1]; linarith

theorem chk_sound {s : ℚ} (hs : s = 1 ∨ s = -1) :
    ∀ (n : ℕ) (m0 m1 w0 w1 : ℚ), 0 ≤ w0 → chk n s m0 m1 w0 w1 = true → GoodB s m0 m1 w0 w1
  | 0, m0, m1, w0, w1, hw0, h => cellOK_sound hs hw0 h
  | n + 1, m0, m1, w0, w1, hw0, h => by
    simp only [chk, Bool.or_eq_true] at h
    rcases h with h | h
    · exact cellOK_sound hs hw0 h
    · intro m w hm0 hm1 hw0' hw1
      split_ifs at h with hsplit
      · simp only [Bool.and_eq_true] at h
        rcases le_total m (((m0 + m1) / 2 : ℚ) : ℝ) with hm | hm
        · exact chk_sound hs n _ _ _ _ hw0 h.1 m w hm0 hm hw0' hw1
        · exact chk_sound hs n _ _ _ _ hw0 h.2 m w hm hm1 hw0' hw1
      · simp only [Bool.and_eq_true] at h
        have hw0R : (0 : ℝ) ≤ w0 := by exact_mod_cast hw0
        rcases le_total w (((w0 + w1) / 2 : ℚ) : ℝ) with hw | hw
        · exact chk_sound hs n _ _ _ _ hw0 h.1 m w hm0 hm1 hw0' hw
        · have : (0 : ℚ) ≤ (w0 + w1) / 2 := by
            have : (w0 : ℝ) ≤ w1 := hw0'.trans hw1
            have : w0 ≤ w1 := by exact_mod_cast this
            linarith
          exact chk_sound hs n _ _ _ _ this h.2 m w hm0 hm1 hw hw1

end TernaryGoldbach.MinorArcs
