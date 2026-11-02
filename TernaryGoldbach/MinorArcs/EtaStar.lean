import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.Eta2

/-!
# `S_{η_*}` as an average of `S_{η₂}` [H, (11.9)]

`η_*(t) = (η₂ *_M φ)(κt)`, so `S_{η_*}(α, x) = ∫₀^∞ S_{η₂}(α, w x/κ) φ(w) dw/w`
(`S_etaStar_eq`).  This is how [H, Prop. 11.2.3] transfers Theorem 3.1.1 from `η₂` to `η_*`.

Proved, with no `sorry`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott

/-- The Mellin convolution in the other variable: for `t > 0`,
`∫₀^∞ f(r) g(t/r) dr/r = ∫₀^∞ f(t/w) g(w) dw/w` (substitute `r = t/w`). -/
theorem mellinConv_eq_swap (f g : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    mellinConv f g t = ∫ w in Ioi (0:ℝ), f (t / w) * g w / w := by
  unfold mellinConv
  have h1 := integral_comp_rpow_Ioi (fun w => f (t / w) * g w / w) (p := -1) (by norm_num)
  have h2 := integral_comp_mul_left_Ioi (fun r => f r * g (t / r) / r) 0 ht
  rw [mul_zero] at h2
  rw [← h1]
  have h3 : ∫ r in Ioi (0:ℝ), f r * g (t / r) / r =
      ∫ x in Ioi (0:ℝ), t * (f (t * x) * g (t / (t * x)) / (t * x)) := by
    rw [integral_const_mul, h2, smul_eq_mul, mul_inv_cancel_left₀ ht.ne']
  rw [h3]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  have e1 : x ^ (-1 - 1 : ℝ) = (x ^ 2)⁻¹ := by
    rw [show (-1 - 1 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]
  simp only [smul_eq_mul, e1, Real.rpow_neg_one, abs_neg, abs_one, one_mul]
  rw [div_inv_eq_mul, show t / (t * x) = x⁻¹ by field_simp]
  field_simp

/-- [H, (11.9)]: `S_{η_*}(α, x) = ∫₀^∞ S_{η₂}(α, w y) φ(w) dw/w` with `y = x/κ`. -/
theorem S_etaStar_eq {x : ℝ} (hx : 0 < x) (α : ℝ) :
    S etaStar x α = ∫ w in Ioi (0:ℝ), S eta2 (w * (x / κ)) α * ((phi w / w : ℝ) : ℂ) := by
  have hκ : (0 : ℝ) < κ := by rw [κ]; norm_num
  set y := x / κ with hy_def
  have hy : 0 < y := div_pos hx hκ
  set F : ℕ → ℝ → ℂ := fun n w =>
    ((Λ n * eta2 (n / (w * y)) * (phi w / w) : ℝ) : ℂ) * TernaryGoldbach.e (n * α) with hF
  have hphiw : ∀ w, 0 < w → phi w / w = w * Real.exp (-(1 / 2) * w ^ 2) := by
    intro w hw
    unfold phi
    field_simp
  -- `η_*(n/x)` as a `w`-integral
  have hstar : ∀ n : ℕ, etaStar (n / x) = ∫ w in Ioi (0:ℝ), eta2 (n / (w * y)) * (phi w / w) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_div]
      unfold etaStar mellinConv
      simp only [mul_zero, zero_div]
      refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
      have h1 : phi 0 = 0 := by simp [phi]
      have h2 : eta2 0 = 0 := by simp [eta2]
      simp [h1, h2]
    · unfold etaStar
      rw [mellinConv_eq_swap _ _ (by positivity)]
      refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
      rw [mul_div_assoc]
      congr 2
      rw [hy_def]
      field_simp
  have hstar0 : ∀ n : ℕ, 0 ≤ etaStar (n / x) := by
    intro n
    rw [hstar n]
    refine setIntegral_nonneg measurableSet_Ioi fun w (hw : 0 < w) => ?_
    have : 0 ≤ phi w := by unfold phi; positivity
    exact mul_nonneg (eta2_nonneg _) (div_nonneg this hw.le)
  -- measurability and domination
  have hmeas : ∀ n : ℕ, Measurable fun w : ℝ => eta2 (n / (w * y)) * (phi w / w) := by
    intro n
    have hphi : Continuous phi := by unfold phi; fun_prop
    exact (continuous_eta2.measurable.comp (measurable_const.div (measurable_id.mul_const y))).mul
      (hphi.measurable.div measurable_id)
  have hgauss : IntegrableOn (fun w : ℝ => w * Real.exp (-(1 / 2) * w ^ 2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn
  have hint_real : ∀ n : ℕ,
      IntegrableOn (fun w : ℝ => eta2 (n / (w * y)) * (phi w / w)) (Ioi 0) := by
    intro n
    refine Integrable.mono' (hgauss.const_mul 3) (hmeas n).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w (hw : 0 < w) => ?_)
    rw [hphiw w hw, Real.norm_eq_abs, abs_mul, abs_of_nonneg (eta2_nonneg _),
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (eta2_le _) (by positivity)
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    have : Integrable (fun w : ℝ => ((Λ n * (eta2 (n / (w * y)) * (phi w / w)) : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) := ((hint_real n).const_mul (Λ n)).ofReal
    refine (this.mul_const (TernaryGoldbach.e (n * α))).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [F, mul_assoc]
  have hFn : ∀ n, ∫ w in Ioi (0:ℝ), F n w =
      ((Λ n * etaStar (n / x) : ℝ) : ℂ) * TernaryGoldbach.e (n * α) := by
    intro n
    simp only [F]
    rw [integral_mul_const, integral_complex_ofReal, hstar n, ← integral_const_mul]
    congr 3
    funext w
    ring
  have hFnorm : ∀ n, ∫ w in Ioi (0:ℝ), ‖F n w‖ = ‖((Λ n * etaStar (n / x) : ℝ) : ℂ)‖ := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hstar0 n)), hstar n,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
    have : 0 ≤ phi w := by unfold phi; positivity
    simp only [F, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg (eta2_nonneg _),
      abs_of_nonneg (div_nonneg this hw.le)]
    ring
  have hsum : Summable fun n => ∫ w in Ioi (0:ℝ), ‖F n w‖ := by
    simp only [hFnorm]
    exact summable_etaStar hx
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  unfold S
  rw [tsum_congr fun n => (hFn n).symm, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  simp only [F]
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-- The triangle inequality in (11.9): `|S_{η_*}(α, x)| ≤ ∫₀^∞ |S_{η₂}(α, w y)| φ(w) dw/w`. -/
theorem norm_S_etaStar_le {x : ℝ} (hx : 0 < x) (α : ℝ) :
    ‖S etaStar x α‖ ≤ ∫ w in Ioi (0:ℝ), ‖S eta2 (w * (x / κ)) α‖ * (phi w / w) := by
  rw [S_etaStar_eq hx]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  have : 0 ≤ phi w := by unfold phi; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg this hw.le)]

end TernaryGoldbach.MinorArcs
