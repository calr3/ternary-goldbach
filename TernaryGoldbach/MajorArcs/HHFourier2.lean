import TernaryGoldbach.MajorArcs.HHFourier

/-!
# A sharper `‖η₊ − η◦‖₂` via `g''`

`h` is `C²` on `(0, ∞)` (`h'' = 0` at `t = 2` too), so `g(u) = h(eᵘ)` has `g'' ∈ L¹ ∩ L²` and
`∫_{|ξ| > H/2π} |ĝ|² ≤ ‖g''‖₂²/H⁴` with `‖g''‖₂² = ∫₀² t (t h''(t) + h'(t))² dt ≤ 368` (true value `142.6…`).
Hence `‖η₊ − η◦‖₂² ≤ 368/(2·200⁴) ≤ 1.15·10⁻⁷` (`‖η₊ − η◦‖₂ ≤ 3.4·10⁻⁴`; [H, (14.5)]: `2.43·10⁻⁶`).
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (hBase hH etaPlus hP hP' hasDerivAt_hP continuous_hP' hBase_eq_hP)

/-- `p(t) = t(2 − t)²(1 − t)(4 + t)`, so `h'(t) = e^{t−1/2} p(t)`. -/
noncomputable def pP (t : ℝ) : ℝ := t * (2 - t) ^ 2 * (1 - t) * (4 + t)

noncomputable def pP' (t : ℝ) : ℝ := -5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16

/-- `h''(t) = e^{t−1/2} (p(t) + p'(t))`. -/
noncomputable def hP'' (t : ℝ) : ℝ := Real.exp (t - 1 / 2) * (pP t + pP' t)

theorem hasDerivAt_pP (t : ℝ) : HasDerivAt pP (pP' t) t := by
  have h : pP = fun t : ℝ => (-1 : ℝ) * t ^ 5 + 1 * t ^ 4 + 12 * t ^ 3 + (-28) * t ^ 2 + 16 * t ^ 1 := by
    ext t; unfold pP; ring
  rw [h]
  exact (((((hasDerivAt_pow 5 t).const_mul (-1 : ℝ)).add ((hasDerivAt_pow 4 t).const_mul (1 : ℝ))).add
    ((hasDerivAt_pow 3 t).const_mul (12 : ℝ))).add ((hasDerivAt_pow 2 t).const_mul (-28 : ℝ))).add
    ((hasDerivAt_pow 1 t).const_mul (16 : ℝ)) |>.congr_deriv (by unfold pP'; push_cast; ring)

theorem hP'_eq (t : ℝ) : hP' t = Real.exp (t - 1 / 2) * pP t := by unfold hP' pP; ring

theorem hasDerivAt_hP' (t : ℝ) : HasDerivAt hP' (hP'' t) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t - 1 / 2)) (Real.exp (t - 1 / 2)) t :=
    ((hasDerivAt_id' t).sub_const (1 / 2)).exp.congr_deriv (by ring)
  have : hP' = fun t => Real.exp (t - 1 / 2) * pP t := funext hP'_eq
  rw [this]
  exact (he.mul (hasDerivAt_pP t)).congr_deriv (by unfold hP''; ring)

theorem hP''_two : hP'' 2 = 0 := by unfold hP'' pP pP'; norm_num

theorem continuous_hP'' : Continuous hP'' := by unfold hP'' pP pP'; fun_prop

/-- `h''`, extended by `0` beyond `2`. -/
noncomputable def hBdd (t : ℝ) : ℝ := if t ≤ 2 then hP'' t else 0

theorem hBd_of_two_le {s : ℝ} (hs : 2 ≤ s) : hBd s = 0 := by
  unfold hBd
  split_ifs with h
  · have : s = 2 := le_antisymm h hs
    subst this; exact hP'_two
  · rfl

/-- `h'` is differentiable on `(0, ∞)` (across `t = 2` since `h''(2) = 0`). -/
theorem hasDerivAt_hBd {t : ℝ} (ht : 0 < t) : HasDerivAt hBd (hBdd t) t := by
  rcases lt_trichotomy t 2 with h | h | h
  · have : hBd =ᶠ[nhds t] hP' := by
      filter_upwards [Iio_mem_nhds h] with s hs
      unfold hBd; rw [if_pos hs.le]
    rw [hBdd, if_pos h.le]
    exact (hasDerivAt_hP' t).congr_of_eventuallyEq this
  · subst h
    rw [hBdd, if_pos le_rfl, hP''_two]
    have hl : HasDerivWithinAt hBd 0 (Iic 2) 2 := by
      have := (hasDerivAt_hP' 2).hasDerivWithinAt (s := Iic 2)
      rw [hP''_two] at this
      refine this.congr_of_eventuallyEq ?_ (by unfold hBd; rw [if_pos le_rfl])
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s ≤ 2 := hs
      unfold hBd; rw [if_pos hs']
    have hr : HasDerivWithinAt hBd 0 (Ici 2) 2 := by
      refine (hasDerivWithinAt_const (2:ℝ) (Ici 2) (0:ℝ)).congr_of_eventuallyEq ?_
        (hBd_of_two_le le_rfl)
      filter_upwards [self_mem_nhdsWithin] with s hs using hBd_of_two_le hs
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have : hBd =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with s hs using hBd_of_two_le hs.le
    rw [hBdd, if_neg (not_le.2 h)]
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq this

/-- `g''(u) = e^{2u} h''(eᵘ) + eᵘ h'(eᵘ)`. -/
noncomputable def gL'' (u : ℝ) : ℝ :=
  hBdd (Real.exp u) * Real.exp u * Real.exp u + hBd (Real.exp u) * Real.exp u

theorem hasDerivAt_gL' (u : ℝ) : HasDerivAt gL' (gL'' u) u := by
  have h1 := (hasDerivAt_hBd (Real.exp_pos u)).comp u (Real.hasDerivAt_exp u)
  have : gL' = fun u => hBd (Real.exp u) * Real.exp u := rfl
  rw [this]
  exact (h1.mul (Real.hasDerivAt_exp u)).congr_deriv (by unfold gL''; simp only [Function.comp])

theorem hBdd_eq {t : ℝ} (ht : 0 < t) : hBdd t = (Icc (0 : ℝ) 2).indicator hP'' t := by
  by_cases h2 : t ≤ 2
  · rw [indicator_of_mem (show t ∈ Icc (0:ℝ) 2 from ⟨ht.le, h2⟩), hBdd, if_pos h2]
  · rw [indicator_of_notMem (fun hm => h2 hm.2), hBdd, if_neg h2]

theorem gL''_G_eq {t : ℝ} (ht : 0 < t) :
    hBdd t * t + hBd t = (Icc (0 : ℝ) 2).indicator (fun t => hP'' t * t + hP' t) t := by
  rw [hBdd_eq ht, hBd_eq ht]
  by_cases h2 : t ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem h2, indicator_of_mem h2, indicator_of_mem h2]
  · rw [indicator_of_notMem h2, indicator_of_notMem h2, indicator_of_notMem h2]; ring

theorem gL''_G2_eq {t : ℝ} (ht : 0 < t) :
    t * (hBdd t * t + hBd t) ^ 2 =
      (Icc (0 : ℝ) 2).indicator (fun t => t * (hP'' t * t + hP' t) ^ 2) t := by
  rw [gL''_G_eq ht]
  by_cases h2 : t ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem h2, indicator_of_mem h2]
  · rw [indicator_of_notMem h2, indicator_of_notMem h2]; ring

theorem integrable_gL'' : Integrable gL'' := by
  have : gL'' = fun u => Real.exp u • (hBdd (Real.exp u) * Real.exp u + hBd (Real.exp u)) := by
    ext u; rw [smul_eq_mul, gL'']; ring
  rw [this]
  exact (integrable_comp_exp (fun t => hBdd t * t + hBd t)).2
    (integrableOn_Ioi_of_eq_indicator (by unfold hP'' pP pP' hP'; fun_prop) fun t ht => gL''_G_eq ht)

theorem integrable_gL''_sq : Integrable fun u => gL'' u ^ 2 := by
  have : (fun u => gL'' u ^ 2) = fun u => Real.exp u •
      (Real.exp u * (hBdd (Real.exp u) * Real.exp u + hBd (Real.exp u)) ^ 2) := by
    ext u; rw [smul_eq_mul, gL'']; ring
  rw [this]
  exact (integrable_comp_exp (fun t => t * (hBdd t * t + hBd t) ^ 2)).2
    (integrableOn_Ioi_of_eq_indicator (by unfold hP'' pP pP' hP'; fun_prop)
      fun t ht => gL''_G2_eq ht)

/-! ## `‖g''‖₂² ≤ 368` -/

theorem hasDerivAt_A2 (t : ℝ) :
    HasDerivAt (fun t : ℝ => (256 / 1 : ℝ) * t ^ 4 + (-4352 / 5 : ℝ) * t ^ 5 + (984 / 1 : ℝ) * t ^ 6 + (-1632 / 7 : ℝ) * t ^ 7 + (-279 / 1 : ℝ) * t ^ 8 + (144 / 1 : ℝ) * t ^ 9 + (45 / 2 : ℝ) * t ^ 10 + (-210 / 11 : ℝ) * t ^ 11 + (-3 / 4 : ℝ) * t ^ 12 + (10 / 13 : ℝ) * t ^ 13 + (1 / 14 : ℝ) * t ^ 14)
      (t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) + (-5*t^4 + 4*t^3 + 36*t^2 - 56*t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2) t := by
  exact ((((((((((((hasDerivAt_pow 4 t).const_mul (256 / 1 : ℝ)).add ((hasDerivAt_pow 5 t).const_mul (-4352 / 5 : ℝ))).add ((hasDerivAt_pow 6 t).const_mul (984 / 1 : ℝ))).add ((hasDerivAt_pow 7 t).const_mul (-1632 / 7 : ℝ))).add ((hasDerivAt_pow 8 t).const_mul (-279 / 1 : ℝ))).add ((hasDerivAt_pow 9 t).const_mul (144 / 1 : ℝ))).add ((hasDerivAt_pow 10 t).const_mul (45 / 2 : ℝ))).add ((hasDerivAt_pow 11 t).const_mul (-210 / 11 : ℝ))).add ((hasDerivAt_pow 12 t).const_mul (-3 / 4 : ℝ))).add ((hasDerivAt_pow 13 t).const_mul (10 / 13 : ℝ))).add ((hasDerivAt_pow 14 t).const_mul (1 / 14 : ℝ))).congr_deriv
    (by push_cast; ring)

theorem integral_A2 {a b : ℝ} :
    ∫ t in a..b, t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) +
        (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2 =
      ((256 / 1 : ℝ) * b ^ 4 + (-4352 / 5 : ℝ) * b ^ 5 + (984 / 1 : ℝ) * b ^ 6 + (-1632 / 7 : ℝ) * b ^ 7 +
        (-279 / 1 : ℝ) * b ^ 8 + (144 / 1 : ℝ) * b ^ 9 + (45 / 2 : ℝ) * b ^ 10 + (-210 / 11 : ℝ) * b ^ 11 +
        (-3 / 4 : ℝ) * b ^ 12 + (10 / 13 : ℝ) * b ^ 13 + (1 / 14 : ℝ) * b ^ 14) -
      ((256 / 1 : ℝ) * a ^ 4 + (-4352 / 5 : ℝ) * a ^ 5 + (984 / 1 : ℝ) * a ^ 6 + (-1632 / 7 : ℝ) * a ^ 7 +
        (-279 / 1 : ℝ) * a ^ 8 + (144 / 1 : ℝ) * a ^ 9 + (45 / 2 : ℝ) * a ^ 10 + (-210 / 11 : ℝ) * a ^ 11 +
        (-3 / 4 : ℝ) * a ^ 12 + (10 / 13 : ℝ) * a ^ 13 + (1 / 14 : ℝ) * a ^ 14) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_A2 t)
    ((by fun_prop : Continuous fun t : ℝ => t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) +
        (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2
      ).intervalIntegrable _ _)

theorem G2_eq_exp_mul (t : ℝ) :
    t * (hP'' t * t + hP' t) ^ 2 = Real.exp (2 * t - 1) * (t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) +
        (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2) := by
  unfold hP'' hP' pP pP'
  rw [show 2 * t - 1 = (t - 1 / 2) + (t - 1 / 2) by ring, Real.exp_add]; ring

theorem integral_G2_le_piece {a b c : ℝ} (hab : a ≤ b) (h0 : 0 ≤ a)
    (hc : ∀ t ∈ Icc a b, Real.exp (2 * t - 1) ≤ c) :
    ∫ t in a..b, t * (hP'' t * t + hP' t) ^ 2 ≤ c * ∫ t in a..b, t * (t * (t * (2 - t) ^ 2 * (1 - t) *
      (4 + t) + (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    ((by unfold hP'' hP' pP pP'; fun_prop : Continuous fun t => t * (hP'' t * t + hP' t) ^ 2).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => c * (t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) +
        (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 - 56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2)
      ).intervalIntegrable _ _) fun t ht => ?_
  rw [G2_eq_exp_mul]
  have hp : 0 ≤ t * (t * (t * (2 - t) ^ 2 * (1 - t) * (4 + t) + (-5 * t ^ 4 + 4 * t ^ 3 + 36 * t ^ 2 -
      56 * t + 16)) + t * (2 - t) ^ 2 * (1 - t) * (4 + t)) ^ 2 := by
    have : 0 ≤ t := le_trans h0 ht.1
    positivity
  exact mul_le_mul_of_nonneg_right (hc t ht) hp

theorem integral_G2_le : ∫ t in (0:ℝ)..2, t * (hP'' t * t + hP' t) ^ 2 ≤ 368 := by
  have hc : Continuous fun t => t * (hP'' t * t + hP' t) ^ 2 := by unfold hP'' hP' pP pP'; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have he1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have he3 : Real.exp 3 ≤ 20.1 := by
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by gcongr
      _ ≤ 20.1 := by norm_num
  have h1 := integral_G2_le_piece (a := 0) (b := 1) (c := Real.exp 1) (by norm_num) le_rfl
    fun t ht => Real.exp_le_exp.2 (by linarith [ht.2])
  have h2 := integral_G2_le_piece (a := 1) (b := 2) (c := Real.exp 3) (by norm_num)
    (by norm_num) fun t ht => Real.exp_le_exp.2 (by linarith [ht.2])
  rw [integral_A2] at h1 h2
  norm_num at h1 h2
  have he0 := Real.exp_pos 1
  nlinarith

/-- **`‖g''‖₂² ≤ 368`**. -/
theorem integral_gL''_sq_le : ∫ u, gL'' u ^ 2 ≤ 368 := by
  have e1 : (fun u => gL'' u ^ 2) = fun u => Real.exp u •
      (Real.exp u * (hBdd (Real.exp u) * Real.exp u + hBd (Real.exp u)) ^ 2) := by
    ext u; rw [smul_eq_mul, gL'']; ring
  rw [e1, integral_comp_exp (fun t => t * (hBdd t * t + hBd t) ^ 2)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => gL''_G2_eq ht)]
  rw [setIntegral_indicator measurableSet_Icc]
  have : Ioi (0 : ℝ) ∩ Icc 0 2 = Ioc 0 2 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]; constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.le, h2⟩
  rw [this, ← intervalIntegral.integral_of_le (by norm_num)]
  exact integral_G2_le

/-! ## `∫_{|ξ| > H/2π} |ĝ|² ≤ ‖g''‖₂²/H⁴` -/

theorem differentiable_gC' : Differentiable ℝ fun u => (gL' u : ℂ) :=
  fun u => ((hasDerivAt_gL' u).ofReal_comp).differentiableAt

theorem deriv_gC' : deriv (fun u => (gL' u : ℂ)) = fun u => (gL'' u : ℂ) := by
  ext u; exact ((hasDerivAt_gL' u).ofReal_comp).deriv

theorem tail_fourier_gC_le' {H : ℝ} (hH0 : 0 < H) :
    ∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ 368 / H ^ 4 := by
  set S := Icc (-(H / (2 * π))) (H / (2 * π)) with hS
  have hπ := Real.pi_pos
  set g'C : ℝ → ℂ := fun u => (gL' u : ℂ) with hg'C
  set g''C : ℝ → ℂ := fun u => (gL'' u : ℂ) with hg''C
  have hint' : Integrable g'C := integrable_gL'.ofReal
  have hint'' : Integrable g''C := integrable_gL''.ofReal
  have hL2'' : MemLp g''C 2 := by
    refine (memLp_two_iff_integrable_sq_norm hint''.aestronglyMeasurable).2 ?_
    have : (fun u => ‖g''C u‖ ^ 2) = fun u => gL'' u ^ 2 := by
      ext u; rw [hg''C, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this]; exact integrable_gL''_sq
  have hfd1 := Real.fourier_deriv integrable_gC differentiable_gC (by rw [deriv_gC]; exact hint')
  rw [deriv_gC] at hfd1
  have hfd2 := Real.fourier_deriv hint' differentiable_gC' (by rw [deriv_gC']; exact hint'')
  rw [deriv_gC'] at hfd2
  have hF'' := TernaryGoldbach.memLp_fourier hint'' hL2''
  have hint2 : Integrable fun ξ => ‖𝓕 g''C ξ‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hF''.aestronglyMeasurable).1 hF''
  have hpl := TernaryGoldbach.integral_norm_sq_fourier hint'' hL2''
  have hle : ∀ ξ ∈ Sᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ ‖𝓕 g''C ξ‖ ^ 2 / H ^ 4 := by
    intro ξ hξ
    have h1 : H ≤ 2 * π * |ξ| := by
      simp only [hS, mem_compl_iff, mem_Icc, not_and_or, not_le] at hξ
      have : H / (2 * π) ≤ |ξ| := by
        rcases hξ with h | h
        · have h0 : 0 ≤ H / (2 * π) := by positivity
          have hneg : ξ < 0 := by linarith
          rw [abs_of_neg hneg]; linarith
        · exact h.le.trans (le_abs_self ξ)
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have e1 : 𝓕 g'C ξ = (2 * π * I * ξ) • 𝓕 gC ξ := congrFun hfd1 ξ
    have e2 : 𝓕 g''C ξ = (2 * π * I * ξ) • 𝓕 g'C ξ := congrFun hfd2 ξ
    have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
      rw [show (2 * π * I * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hπ]
      norm_num
    have e3 : ‖𝓕 g''C ξ‖ = (2 * π * |ξ|) * ((2 * π * |ξ|) * ‖𝓕 gC ξ‖) := by
      rw [e2, e1, smul_eq_mul, smul_eq_mul, norm_mul (2 * π * I * ξ : ℂ),
        norm_mul (2 * π * I * ξ : ℂ), hn]
    rw [e3, le_div_iff₀ (by positivity)]
    have h4 : H ^ 4 ≤ (2 * π * |ξ|) ^ 4 := pow_le_pow_left₀ hH0.le h1 4
    have hn0 := norm_nonneg (𝓕 gC ξ)
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖𝓕 gC ξ‖)]
  have hmeas : MeasurableSet Sᶜ := measurableSet_Icc.compl
  calc ∫ ξ in Sᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ ∫ ξ in Sᶜ, ‖𝓕 g''C ξ‖ ^ 2 / H ^ 4 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (hint2.div_const _).integrableOn ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hle))
    _ ≤ ∫ ξ, ‖𝓕 g''C ξ‖ ^ 2 / H ^ 4 :=
        setIntegral_le_integral (hint2.div_const _) (Filter.Eventually.of_forall fun _ => by positivity)
    _ = (∫ u, ‖g''C u‖ ^ 2) / H ^ 4 := by rw [integral_div, hpl]
    _ ≤ 368 / H ^ 4 := by
        gcongr
        have : (fun u => ‖g''C u‖ ^ 2) = fun u => gL'' u ^ 2 := by
          ext u; rw [hg''C, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [this]; exact integral_gL''_sq_le

/-- **`‖η₊ − η◦‖₂² ≤ 368/(2·200⁴)`** (`≤ 1.15·10⁻⁷`). -/
theorem integral_sq_etaPlus_sub_etaO_le' :
    ∫ t, (etaPlus t - etaO t) ^ 2 ≤ 368 / 2 / 200 ^ 4 := by
  have hz : ∀ t ∉ Ioi (0:ℝ), (etaPlus t - etaO t) ^ 2 = 0 := fun t ht => by
    rw [etaPlus_of_nonpos (not_lt.1 ht), etaO_of_nonpos (not_lt.1 ht)]; ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← integral_comp_exp (fun t => (etaPlus t - etaO t) ^ 2)]
  have hpt : ∀ u, Real.exp u • (etaPlus (Real.exp u) - etaO (Real.exp u)) ^ 2 =
      ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (Real.exp u ^ 3 * Real.exp (-(Real.exp u) ^ 2)) := by
    intro u
    have he := Real.exp_pos u
    have hK := hH_eq_fourier_K (H := 200) (by norm_num) he
    rw [Real.log_exp] at hK
    rw [← hK, gC, gL, smul_eq_mul, etaPlus, etaO_eq he, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs,
      show -(Real.exp u) ^ 2 = (-(Real.exp u) ^ 2 / 2) + (-(Real.exp u) ^ 2 / 2) by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  have hL2 := memLp_gC.sub (memLp_gH 200)
  have hint : Integrable fun u => ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  calc ∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (Real.exp u ^ 3 * Real.exp (-(Real.exp u) ^ 2))
      ≤ ∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (1 / 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by positivity)
          (hint.mul_const _) (Filter.Eventually.of_forall fun u =>
            mul_le_mul_of_nonneg_left (cube_mul_exp_neg_sq_le (Real.exp_pos u).le) (sq_nonneg _))
    _ = (∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2) * (1 / 2) := integral_mul_const _ _
    _ ≤ 368 / 2 / 200 ^ 4 := by
        rw [integral_norm_sq_gC_sub]
        have := tail_fourier_gC_le' (H := 200) (by norm_num)
        linarith

end TernaryGoldbach.MajorArcs
