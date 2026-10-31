import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.SupNorms

/-!
# Sup norms of `η₊` without Appendix A

`|h_H(t)| ≤ 5Hε²/π + (6/π) e^{1/2}` (`abs_hH_le_eps`): after `y = t/u`,
`h_H(t) = ∫_0^2 h(u) F_H(t/u) du/u`; integrate by parts against `Γ(u) = -G_H(log(t/u))`, where
`G_H(z) = ∫_0^z sin(Hv)/(πv) dv` satisfies `|G_H| ≤ 3/π` (a second integration by parts beyond
`1/H`), and use that `h` has total variation `2h(1) = 2e^{1/2}`.  Hence `|h₂₀₀| ≤ 3.15`,
`|η₊| ≤ 1.94` and `t|η₊(t)| ≤ 2.32` ([B, (14.3), (14.24)] have `1.079955` and `1.19073`, from the
finer analysis of Appendix A; ours suffice for (14.28) as used here).
-/

open Real MeasureTheory Set intervalIntegral

namespace TernaryGoldbach.Helfgott

/-- The continuous version of `v ↦ F_H(e^v) = sin(Hv)/(πv)`. -/
noncomputable def sH (H v : ℝ) : ℝ := H / π * Real.sinc (H * v)

theorem continuous_sH (H : ℝ) : Continuous (sH H) :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

theorem sH_eq {H v : ℝ} (hH : H ≠ 0) (hv : v ≠ 0) : sH H v = Real.sin (H * v) / (π * v) := by
  unfold sH; rw [Real.sinc_of_ne_zero (mul_ne_zero hH hv)]
  have := Real.pi_pos
  field_simp

theorem sH_neg (H v : ℝ) : sH H (-v) = sH H v := by
  unfold sH; rw [mul_neg, Real.sinc_neg]

theorem abs_sH_le {H : ℝ} (hH : 0 ≤ H) (v : ℝ) : |sH H v| ≤ H / π := by
  unfold sH
  rw [abs_mul, abs_of_nonneg (by have := Real.pi_pos; positivity)]
  have := Real.abs_sinc_le_one (H * v)
  have : 0 ≤ H / π := by have := Real.pi_pos; positivity
  nlinarith

theorem abs_mul_neg_div_le {c H w : ℝ} (hc : 0 ≤ c) (hH : 0 < H) (hw : |w| ≤ 1) :
    |c * (-w / H)| ≤ c * (1 / H) := by
  rw [abs_mul, abs_of_nonneg hc, abs_div, abs_neg, abs_of_pos hH]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hw hH.le) hc

/-- `G_H(z) = ∫_0^z sin(Hv)/(πv) dv = Si(Hz)/π`. -/
noncomputable def GH (H z : ℝ) : ℝ := ∫ v in (0 : ℝ)..z, sH H v

theorem GH_bound_pos {H z : ℝ} (hH : 0 < H) (hz : 0 ≤ z) : |GH H z| ≤ 3 / π := by
  have hπ := Real.pi_pos
  set a := 1 / H with ha
  have ha0 : 0 < a := by positivity
  have hint : ∀ c d : ℝ, IntervalIntegrable (sH H) volume c d :=
    fun c d => (continuous_sH H).intervalIntegrable c d
  -- the part near `0`
  have hnear : ∀ w, 0 ≤ w → w ≤ a → |∫ v in (0:ℝ)..w, sH H v| ≤ 1 / π := by
    intro w hw0 hwa
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := w) (C := H / π)
      (f := sH H) (fun v _ => by rw [Real.norm_eq_abs]; exact abs_sH_le hH.le v)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hw0] at h
    refine h.trans ?_
    calc H / π * w ≤ H / π * a := mul_le_mul_of_nonneg_left hwa (by positivity)
      _ = 1 / π := by rw [ha]; field_simp
  rcases le_or_gt z a with hza | hza
  · exact (hnear z hz hza).trans (by
      have : (1 : ℝ) / π ≤ 3 / π := div_le_div_of_nonneg_right (by norm_num) hπ.le
      exact this)
  -- the far part, by parts
  have hsplit : GH H z = (∫ v in (0:ℝ)..a, sH H v) + ∫ v in a..z, sH H v :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a z)).symm
  have hfar : |∫ v in a..z, sH H v| ≤ 2 / π := by
    have hz0 : 0 < z := lt_trans ha0 hza
    -- `sH = (1/(πv)) · sin(Hv)` on `[a, z]`
    have hcongr : ∫ v in a..z, sH H v = ∫ v in a..z, (1 / (π * v)) * Real.sin (H * v) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hza.le] at hv
      have hv0 : 0 < v := lt_of_lt_of_le ha0 hv.1
      rw [sH_eq hH.ne' hv0.ne']; field_simp
    rw [hcongr]
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun v => 1 / (π * v)) (u' := fun v => -(1 / (π * v ^ 2)))
      (v := fun v => -Real.cos (H * v) / H) (v' := fun v => Real.sin (H * v))
      (a := a) (b := z)
      (by
        refine ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id) ?_
        intro v hv; rw [Set.uIcc_of_le hza.le] at hv
        have : 0 < v := lt_of_lt_of_le ha0 hv.1
        positivity)
      (by fun_prop)
      (by
        intro v hv
        rw [min_eq_left hza.le, max_eq_right hza.le] at hv
        have hv0 : 0 < v := lt_trans ha0 hv.1
        have h1 : HasDerivAt (fun v => π * v) π v := by
          simpa using (hasDerivAt_id v).const_mul π
        have h2 := h1.inv (by positivity)
        convert h2.const_mul 1 using 1
        · ext w; simp [div_eq_mul_inv]
        · field_simp)
      (by
        intro v _
        have h1 : HasDerivAt (fun v => H * v) H v := by simpa using (hasDerivAt_id v).const_mul H
        have h2 := (Real.hasDerivAt_cos (H * v)).comp v h1
        convert (h2.neg).div_const H using 1
        · ext w; simp [Function.comp]
        · field_simp)
      (by
        apply ContinuousOn.intervalIntegrable
        refine ContinuousOn.neg (ContinuousOn.div continuousOn_const ?_ ?_)
        · fun_prop
        · intro v hv; rw [Set.uIcc_of_le hza.le] at hv
          have : 0 < v := lt_of_lt_of_le ha0 hv.1
          positivity)
      (Continuous.intervalIntegrable (by fun_prop : Continuous fun v => Real.sin (H * v)) a z)
    rw [hibp]
    -- bound the three terms
    have hb1 : |1 / (π * z) * (-Real.cos (H * z) / H)| ≤ 1 / (π * H * z) := by
      refine (abs_mul_neg_div_le (by positivity) hH (Real.abs_cos_le_one _)).trans (le_of_eq ?_)
      field_simp
    have hb2 : |1 / (π * a) * (-Real.cos (H * a) / H)| ≤ 1 / π := by
      refine (abs_mul_neg_div_le (by positivity) hH (Real.abs_cos_le_one _)).trans (le_of_eq ?_)
      rw [ha]; field_simp
    have hcont : ContinuousOn (fun v : ℝ => -(1 / (π * v ^ 2)) * (-Real.cos (H * v) / H)) (Set.uIcc a z) := by
      refine ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.div continuousOn_const ?_ ?_)) ?_
      · fun_prop
      · intro v hv; rw [Set.uIcc_of_le hza.le] at hv
        have : 0 < v := lt_of_lt_of_le ha0 hv.1
        positivity
      · fun_prop
    have hcont2 : ContinuousOn (fun v : ℝ => 1 / (π * H) * (1 / v ^ 2)) (Set.uIcc a z) := by
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
      · fun_prop
      · intro v hv; rw [Set.uIcc_of_le hza.le] at hv
        have : 0 < v := lt_of_lt_of_le ha0 hv.1
        positivity
    have hb3 : |∫ v in a..z, -(1 / (π * v ^ 2)) * (-Real.cos (H * v) / H)| ≤
        1 / (π * H) * (1 / a - 1 / z) := by
      refine (intervalIntegral.abs_integral_le_integral_abs hza.le).trans ?_
      have hmono : ∫ v in a..z, |-(1 / (π * v ^ 2)) * (-Real.cos (H * v) / H)| ≤
          ∫ v in a..z, 1 / (π * H) * (1 / v ^ 2) := by
        refine intervalIntegral.integral_mono_on hza.le (hcont.abs.intervalIntegrable)
          hcont2.intervalIntegrable fun v hv => ?_
        have hv0 : 0 < v := lt_of_lt_of_le ha0 hv.1
        have e : -(1 / (π * v ^ 2)) * (-Real.cos (H * v) / H) =
            1 / (π * v ^ 2) * (-(-Real.cos (H * v)) / H) := by ring
        rw [e]
        refine (abs_mul_neg_div_le (by positivity) hH ?_).trans (le_of_eq ?_)
        · rw [abs_neg]; exact Real.abs_cos_le_one _
        · field_simp
      refine hmono.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hd : ∀ v ∈ Set.uIcc a z, HasDerivAt (fun v : ℝ => -(1 / v)) (1 / v ^ 2) v := by
        intro v hv
        rw [Set.uIcc_of_le hza.le] at hv
        have hv0 : v ≠ 0 := (lt_of_lt_of_le ha0 hv.1).ne'
        have := (hasDerivAt_inv hv0).neg
        convert this using 1
        · ext w; simp [one_div]
        · field_simp
      have hcont3 : ContinuousOn (fun v : ℝ => 1 / v ^ 2) (Set.uIcc a z) := by
        refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
        intro v hv; rw [Set.uIcc_of_le hza.le] at hv
        have : 0 < v := lt_of_lt_of_le ha0 hv.1
        positivity
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont3.intervalIntegrable]
      ring
    have hsum : 1 / (π * H * z) + 1 / π + 1 / (π * H) * (1 / a - 1 / z) = 2 / π := by
      rw [ha]; field_simp; ring
    rw [abs_le] at hb1 hb2 hb3 ⊢
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2]
  rw [hsplit]
  have h1 := hnear a ha0.le le_rfl
  have e : 1 / π + 2 / π = 3 / π := by ring
  rw [abs_le] at h1 hfar ⊢
  constructor <;> linarith [h1.1, h1.2, hfar.1, hfar.2]

theorem GH_neg (H z : ℝ) : GH H (-z) = -GH H z := by
  unfold GH
  have h1 : ∫ v in (0:ℝ)..-z, sH H v = ∫ v in (0:ℝ)..-z, sH H (-v) :=
    intervalIntegral.integral_congr fun v _ => (sH_neg H v).symm
  rw [h1, intervalIntegral.integral_comp_neg (fun v => sH H v), neg_neg, neg_zero,
    intervalIntegral.integral_symm]

theorem GH_bound {H : ℝ} (hH : 0 < H) (z : ℝ) : |GH H z| ≤ 3 / π := by
  rcases le_or_gt 0 z with hz | hz
  · exact GH_bound_pos hH hz
  · have := GH_bound_pos hH (z := -z) (by linarith)
    rwa [GH_neg, abs_neg] at this

/-- `h(u) = u²(2-u)³e^{u-1/2}` as a smooth function. -/
noncomputable def hP (u : ℝ) : ℝ := u ^ 2 * (2 - u) ^ 3 * Real.exp (u - 1 / 2)

/-- `h'(u) = e^{u-1/2} u (2-u)² (1-u)(4+u)`. -/
noncomputable def hP' (u : ℝ) : ℝ := Real.exp (u - 1 / 2) * u * (2 - u) ^ 2 * (1 - u) * (4 + u)

theorem hasDerivAt_hP (u : ℝ) : HasDerivAt hP (hP' u) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  have h2 : HasDerivAt (fun u : ℝ => (2 - u) ^ 3) (3 * (2 - u) ^ 2 * (-1)) u := by
    have hc : HasDerivAt (fun u : ℝ => 2 - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 2
    have := (hasDerivAt_pow 3 (2 - u)).comp u hc
    convert this using 1 <;> first | rfl | (push_cast; ring) | simp
  have h3 : HasDerivAt (fun u : ℝ => Real.exp (u - 1 / 2)) (Real.exp (u - 1 / 2)) u := by
    have := (Real.hasDerivAt_exp (u - 1 / 2)).comp u ((hasDerivAt_id u).sub_const (1 / 2))
    convert this using 1
    · rfl
    · simp
  have := (h1.mul h2).mul h3
  unfold hP hP'
  convert this using 1
  simp only [Pi.mul_apply]; ring

theorem continuous_hP' : Continuous hP' := by unfold hP'; fun_prop

theorem hBase_eq_hP {u : ℝ} (h0 : 0 ≤ u) (h2 : u ≤ 2) : hBase u = hP u := by
  unfold hBase hP; rw [if_pos ⟨h0, h2⟩]

theorem hP_one : hP 1 = Real.exp (1 / 2) := by unfold hP; norm_num

theorem hP_two : hP 2 = 0 := by unfold hP; norm_num

/-- `∫_ε^2 |h'| = 2h(1) - h(ε)` for `0 < ε ≤ 1`. -/
theorem integral_abs_hP' {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u in ε..2, |hP' u| = 2 * Real.exp (1 / 2) - hP ε := by
  have hc : Continuous fun u => |hP' u| := continuous_hP'.abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 3, HasDerivAt hP (hP' x) x := fun x _ => hasDerivAt_hP x
  have e1 : ∫ u in ε..1, |hP' u| = ∫ u in ε..1, hP' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hε1] at hu
    have hu0 : 0 ≤ u := le_trans hε0.le hu.1
    have : 0 ≤ hP' u := by
      unfold hP'
      have : 0 ≤ 1 - u := by linarith [hu.2]
      positivity
    exact abs_of_nonneg this
  have e2 : ∫ u in (1:ℝ)..2, |hP' u| = ∫ u in (1:ℝ)..2, -hP' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have : hP' u ≤ 0 := by
      unfold hP'
      have h1 : 0 ≤ Real.exp (u - 1 / 2) * u * (2 - u) ^ 2 := by
        have : 0 ≤ u := by linarith [hu.1]
        positivity
      have h2 : (1 - u) * (4 + u) ≤ 0 := by nlinarith [hu.1, hu.2]
      have : Real.exp (u - 1 / 2) * u * (2 - u) ^ 2 * (1 - u) * (4 + u) =
          (Real.exp (u - 1 / 2) * u * (2 - u) ^ 2) * ((1 - u) * (4 + u)) := by ring
      rw [this]; exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    exact abs_of_nonpos this
  rw [e1, e2, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_hP x)
      (continuous_hP'.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_hP x)
      (continuous_hP'.intervalIntegrable _ _), hP_one, hP_two]
  ring

theorem measurable_hBase : Measurable hBase := by
  unfold hBase
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

theorem measurable_F (H : ℝ) : Measurable (F H) := by
  unfold F; fun_prop

theorem continuous_GH (H : ℝ) : Continuous (GH H) := by
  unfold GH
  exact continuous_iff_continuousAt.2 fun z =>
    ((continuous_sH H).integral_hasStrictDerivAt 0 z).hasDerivAt.continuousAt

theorem hasDerivAt_GH (H z : ℝ) : HasDerivAt (GH H) (sH H z) z := by
  unfold GH
  exact ((continuous_sH H).integral_hasStrictDerivAt 0 z).hasDerivAt

/-- Substitution `y = t/u`: `h_H(t) = ∫_0^∞ h(u) F_H(t/u) du/u`. -/
theorem hH_eq_u {H t : ℝ} (ht : 0 < t) :
    hH H t = ∫ u in Set.Ioi (0:ℝ), hBase u * F H (t / u) / u := by
  unfold hH
  rw [← integral_comp_rpow_Ioi (fun y => hBase (t / y) * F H y / y) (p := -1) (by norm_num)]
  set k : ℝ → ℝ := fun u => hBase u * F H (t / u) * t / u with hk
  have h1 : ∫ x in Set.Ioi (0:ℝ), (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) •
      (fun y => hBase (t / y) * F H y / y) (x ^ (-1:ℝ)) = ∫ x in Set.Ioi (0:ℝ), k (t * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    simp only [hk, smul_eq_mul]
    rw [Real.rpow_neg_one, show ((-1:ℝ) - 1) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_natCast]
    have : t / (t * x) = x⁻¹ := by field_simp
    rw [this, div_inv_eq_mul]
    field_simp
    norm_num
  rw [h1, integral_comp_mul_left_Ioi k 0 ht, mul_zero, smul_eq_mul, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  simp only [hk]
  field_simp

/-- **`|h_H(t)| ≤ 5Hε²/π + (6/π) e^{1/2}`** for `t > 0`, `0 < ε ≤ 1`: integration by parts against
`Γ(u) = -G_H(log(t/u))`, `|G_H| ≤ 3/π`, and the total variation `2e^{1/2}` of `h`. -/
theorem abs_hH_le_eps {H t ε : ℝ} (hHpos : 0 < H) (ht : 0 < t) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |hH H t| ≤ 5 * H * ε ^ 2 / π + 6 / π * Real.exp (1 / 2) := by
  have hπ := Real.pi_pos
  set f : ℝ → ℝ := fun u => hBase u * F H (t / u) / u with hf
  have hmeas : Measurable f :=
    (measurable_hBase.mul ((measurable_F H).comp (measurable_const.div measurable_id))).div
      measurable_id
  have hfb : ∀ u, 0 ≤ u → |f u| ≤ 5 * H / π * u := by
    intro u hu
    rcases hu.eq_or_lt with h0 | hu0
    · subst h0; simp [hf]
    simp only [hf]
    rw [abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |hBase u| * |F H (t / u)| ≤ 5 * u ^ 2 * (H / π) :=
          mul_le_mul (abs_hBase_le u) (abs_F_le hHpos.le _) (abs_nonneg _) (by positivity)
      _ = 5 * H / π * u * u := by ring
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b := by
    intro a b ha hab
    refine (intervalIntegrable_const (c := 5 * H / π * b)).mono_fun' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Set.uIoc_of_le hab] at hu
    show ‖f u‖ ≤ 5 * H / π * b
    rw [Real.norm_eq_abs]
    refine (hfb u (ha.trans hu.1.le)).trans ?_
    exact mul_le_mul_of_nonneg_left hu.2 (by positivity)
  -- `h_H(t) = ∫_0^2 f`
  have h02 : hH H t = ∫ u in (0:ℝ)..2, f u := by
    rw [hH_eq_u ht, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2)]
    show ∫ u in Set.Ioi (0:ℝ), f u = ∫ u in Set.Ioc (0:ℝ) 2, f u
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) (f := f)
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))
      (Set.Ioc_subset_Ioi_self : Set.Ioc (0:ℝ) 2 ⊆ Set.Ioi 0) fun u hu => ?_)
    have h2 : 2 < u := by
      have := hu.2; simp only [Set.mem_Ioc, not_and, not_le] at this; exact this hu.1
    simp only [hf]; rw [hBase_eq_zero h2.le]; simp
  rw [h02, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 ε le_rfl hε0.le)
    (hint ε 2 hε0.le (by linarith))]
  -- near part
  have hnear : |∫ u in (0:ℝ)..ε, f u| ≤ 5 * H * ε ^ 2 / π := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε)
      (C := 5 * H / π * ε) (f := f) (fun u hu => by
        rw [Set.uIoc_of_le hε0.le] at hu
        rw [Real.norm_eq_abs]
        exact (hfb u hu.1.le).trans (mul_le_mul_of_nonneg_left hu.2 (by positivity)))
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hε0] at h
    refine h.trans (le_of_eq ?_); ring
  -- far part: integration by parts
  set Γ : ℝ → ℝ := fun u => -GH H (Real.log t - Real.log u) with hΓ
  set g : ℝ → ℝ := fun u => sH H (Real.log t - Real.log u) / u with hg
  have hcongr : ∫ u in ε..2, f u = ∫ u in ε..2, hP u * g u := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [hne] with u hut hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    have hu0 : 0 < u := lt_trans hε0 hu.1
    simp only [hf, hg]
    rw [hBase_eq_hP hu0.le hu.2, mul_div_assoc]
    congr 2
    have hlog : Real.log (t / u) ≠ 0 := by
      refine Real.log_ne_zero_of_pos_of_ne_one (by positivity) ?_
      intro h; apply hut; field_simp at h; linarith
    rw [← Real.log_div ht.ne' hu0.ne', sH_eq hHpos.ne' hlog]
    unfold F; ring
  have hΓc : ContinuousOn Γ (Set.uIcc ε 2) := by
    refine ContinuousOn.neg ((continuous_GH H).comp_continuousOn ?_)
    refine continuousOn_const.sub (Real.continuousOn_log.mono ?_)
    intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
    exact (ne_of_gt (lt_of_lt_of_le hε0 hu.1))
  have hgc : ContinuousOn g (Set.uIcc ε 2) := by
    refine ContinuousOn.div ((continuous_sH H).comp_continuousOn ?_) continuousOn_id ?_
    · refine continuousOn_const.sub (Real.continuousOn_log.mono ?_)
      intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
      exact (ne_of_gt (lt_of_lt_of_le hε0 hu.1))
    · intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
      exact (ne_of_gt (lt_of_lt_of_le hε0 hu.1))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := hP) (u' := hP') (v := Γ) (v' := g) (a := ε) (b := 2)
    (by unfold hP; fun_prop) hΓc
    (fun x _ => hasDerivAt_hP x)
    (by
      intro x hx
      rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hx
      have hx0 : 0 < x := lt_trans hε0 hx.1
      have hz : HasDerivAt (fun u => Real.log t - Real.log u) (-x⁻¹) x := by
        simpa using (Real.hasDerivAt_log hx0.ne').const_sub (Real.log t)
      have := ((hasDerivAt_GH H (Real.log t - Real.log x)).comp x hz).neg
      convert this using 1 <;> first | rfl |
        (show sH H (Real.log t - Real.log x) / x = _; field_simp))
    (continuous_hP'.intervalIntegrable _ _) hgc.intervalIntegrable
  have hfar : |∫ u in ε..2, f u| ≤ 6 / π * Real.exp (1 / 2) := by
    rw [hcongr, hibp, hP_two, zero_mul, zero_sub]
    have hΓb : ∀ u, |Γ u| ≤ 3 / π := fun u => by
      show |-GH H (Real.log t - Real.log u)| ≤ 3 / π
      rw [abs_neg]; exact GH_bound hHpos _
    have hPε : 0 ≤ hP ε := by
      unfold hP; have : 0 ≤ 2 - ε := by linarith
      positivity
    have h1 : |hP ε * Γ ε| ≤ hP ε * (3 / π) := by
      rw [abs_mul, abs_of_nonneg hPε]; exact mul_le_mul_of_nonneg_left (hΓb ε) hPε
    have h2 : |∫ u in ε..2, hP' u * Γ u| ≤ 3 / π * (2 * Real.exp (1 / 2) - hP ε) := by
      refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
      rw [← integral_abs_hP' hε0 hε1, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((continuous_hP'.continuousOn.mul hΓc).abs.intervalIntegrable)
        ((continuous_hP'.abs.intervalIntegrable _ _).const_mul _) fun u _ => ?_
      rw [abs_mul, mul_comm (3 / π)]
      exact mul_le_mul_of_nonneg_left (hΓb u) (abs_nonneg _)
    have e : hP ε * (3 / π) + 3 / π * (2 * Real.exp (1 / 2) - hP ε) = 6 / π * Real.exp (1 / 2) := by
      ring
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [abs_le] at hnear hfar ⊢
  constructor <;> linarith [hnear.1, hnear.2, hfar.1, hfar.2]

/-- **`|h₂₀₀(t)| ≤ 3.15`** for `t ≥ 0`. -/
theorem abs_hH200_le {t : ℝ} (ht : 0 ≤ t) : |hH 200 t| ≤ 3.15 := by
  rcases ht.eq_or_lt with h0 | ht
  · subst h0
    have : hH 200 0 = 0 := by unfold hH; simp [hBase]
    rw [this, abs_zero]; norm_num
  refine (abs_hH_le_eps (H := 200) (ε := 1 / 1000) (by norm_num) ht (by norm_num) (by norm_num)).trans ?_
  have hπ : 3.1415 < π := Real.pi_gt_d4
  have he : Real.exp (1 / 2) < 1.64873 := by
    have h := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have h1 : 5 * 200 * (1 / 1000 : ℝ) ^ 2 / π ≤ 0.001 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : 6 / π * Real.exp (1 / 2) ≤ 3.149 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- `|η₊(t)| ≤ 1.94` for `t ≥ 0` (cf. [B, (14.3)]: `1.079955`). -/
theorem abs_etaPlus_le_A {t : ℝ} (ht : 0 ≤ t) : |etaPlus t| ≤ 1.94 := by
  unfold etaPlus
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_hH200_le ht
  have h2 := mul_exp_neg_sq_half_le t
  have e : -(1 / 2) * t ^ 2 = -t ^ 2 / 2 := by ring
  rw [e] at h2
  have h3 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := by positivity
  calc |hH 200 t| * t * Real.exp (-t ^ 2 / 2) = |hH 200 t| * (t * Real.exp (-t ^ 2 / 2)) := by ring
    _ ≤ 3.15 * (1 / 1.625) := mul_le_mul h1 h2 h3 (by norm_num)
    _ ≤ 1.94 := by norm_num

/-- `t |η₊(t)| ≤ 2.32` for `t ≥ 0` (cf. [B, (14.24)]: `1.19073`). -/
theorem mul_abs_etaPlus_le_B {t : ℝ} (ht : 0 ≤ t) : t * |etaPlus t| ≤ 2.32 := by
  unfold etaPlus
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_hH200_le ht
  have h2 := phi_le_two_div_e t
  unfold phi at h2
  have h3 : 0 ≤ t ^ 2 * Real.exp (-t ^ 2 / 2) := by positivity
  calc t * (|hH 200 t| * t * Real.exp (-t ^ 2 / 2)) = |hH 200 t| * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
        ring
    _ ≤ 3.15 * 0.7358 := mul_le_mul h1 h2 h3 (by norm_num)
    _ ≤ 2.32 := by norm_num

end TernaryGoldbach.Helfgott
