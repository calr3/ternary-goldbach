import TernaryGoldbach.MinorArcs.TypeI

/-!
# The Fourier transform of `log · η₂` [H, (B.17), Lemma B.2.4]

* `norm_fourier_logeta2_le`: `|(log·η₂)^(t)| ≤ |log·η₂|₁ = 2 - log 4` [H, (B.17)];
* `norm_fourier_logeta2_le_decay`: `(2πt)² |(log·η₂)^(t)| ≤ |(log·η₂)''|₁ = 96 log 2` [H, (B.18)].
-/

open Real Finset MeasureTheory Complex

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

theorem hasDerivAt_e_neg (t u : ℝ) :
    HasDerivAt (fun u : ℝ => e (-(u * t))) (-(2 * π * I * t) * e (-(u * t))) u := by
  have h : HasDerivAt (fun u : ℝ => (-(2 * π * I * t) : ℂ) * (u : ℂ)) (-(2 * π * I * t)) u := by
    simpa using ((hasDerivAt_id (u : ℝ)).ofReal_comp).const_mul (-(2 * π * I * t) : ℂ)
  have := h.cexp
  convert this using 1
  · funext u; simp only [e]; push_cast; ring_nf
  · simp only [e]; push_cast; ring_nf

theorem continuous_e_neg (t : ℝ) : Continuous fun u : ℝ => e (-(u * t)) := by
  unfold e; fun_prop

/-- Two integrations by parts: with `c = -2πit`,
`∫_a^b e(-ut) g(u) du = [e(-ut)(g/c - g'/c²)]_a^b + (1/c²) ∫_a^b g''(u) e(-ut) du`. -/
theorem integral_e_mul_ibp2 {a b t : ℝ} (ht : t ≠ 0) {g g' g'' : ℝ → ℝ}
    (h1 : ∀ u ∈ Set.uIcc a b, HasDerivAt g (g' u) u)
    (h2 : ∀ u ∈ Set.uIcc a b, HasDerivAt g' (g'' u) u) (h3 : ContinuousOn g'' (Set.uIcc a b)) :
    ∫ u in a..b, e (-(u * t)) * (g u : ℂ) =
      (e (-(b * t)) * ((g b : ℂ) / (-(2 * π * I * t)) - (g' b : ℂ) / (-(2 * π * I * t)) ^ 2) -
        e (-(a * t)) * ((g a : ℂ) / (-(2 * π * I * t)) - (g' a : ℂ) / (-(2 * π * I * t)) ^ 2)) +
      (∫ u in a..b, (g'' u : ℂ) * e (-(u * t))) / (-(2 * π * I * t)) ^ 2 := by
  set c : ℂ := -(2 * π * I * t)
  have hc : c ≠ 0 := by
    simp only [c, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      I_ne_zero) (by exact_mod_cast ht)
  set E : ℝ → ℂ := fun u => e (-(u * t))
  have hE : ∀ u, HasDerivAt (fun u => E u / c) (E u) u := fun u => by
    have := (hasDerivAt_e_neg t u).div_const c
    rw [show (-(2 * π * I * t) : ℂ) = c from rfl, mul_div_cancel_left₀ _ hc] at this
    exact this
  have hE2 : ∀ u, HasDerivAt (fun u => E u / c ^ 2) (E u / c) u := fun u => by
    have := (hasDerivAt_e_neg t u).div_const (c ^ 2)
    convert this using 1; simp only [E, c]; field_simp
  have hcE : Continuous E := continuous_e_neg t
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun u hu => (h2 u hu).continuousAt.continuousWithinAt
  -- First integration by parts.
  have I1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun u => (g u : ℂ)) (u' := fun u => (g' u : ℂ)) (v := fun u => E u / c) (v' := E)
    (fun u hu => (h1 u hu).ofReal_comp) (fun u _ => hE u)
    ((Complex.continuous_ofReal.comp_continuousOn hg'c).intervalIntegrable)
    (hcE.intervalIntegrable a b)
  -- Second integration by parts.
  have I2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun u => (g' u : ℂ)) (u' := fun u => (g'' u : ℂ)) (v := fun u => E u / c ^ 2)
    (v' := fun u => E u / c)
    (fun u hu => (h2 u hu).ofReal_comp) (fun u _ => hE2 u)
    ((Complex.continuous_ofReal.comp_continuousOn h3).intervalIntegrable)
    ((hcE.div_const c).intervalIntegrable a b)
  have hcomm : ∫ u in a..b, E u * (g u : ℂ) = ∫ u in a..b, (g u : ℂ) * E u :=
    intervalIntegral.integral_congr fun u _ => mul_comm _ _
  have hI2' : ∫ u in a..b, (g' u : ℂ) * (E u / c) =
      (g' b : ℂ) * (E b / c ^ 2) - (g' a : ℂ) * (E a / c ^ 2) -
        (∫ u in a..b, (g'' u : ℂ) * E u) / c ^ 2 := by
    rw [I2, ← intervalIntegral.integral_div]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  simp only [E] at hcomm I1 hI2' ⊢
  rw [hcomm, I1, hI2']
  ring


/-! ### `log · η₂` on its two pieces -/

/-- `g₁(u) = 4 log u log(4u)` (`log·η₂` on `[1/4, 1/2]`). -/
noncomputable def lg1 (u : ℝ) : ℝ := 4 * Real.log u * Real.log (4 * u)
noncomputable def lg1' (u : ℝ) : ℝ := 4 * (Real.log (4 * u) + Real.log u) / u
noncomputable def lg1'' (u : ℝ) : ℝ := 4 * (2 - Real.log (4 * u) - Real.log u) / u ^ 2
/-- `g₂(u) = -4 log² u` (`log·η₂` on `[1/2, 1]`). -/
noncomputable def lg2 (u : ℝ) : ℝ := -4 * Real.log u ^ 2
noncomputable def lg2' (u : ℝ) : ℝ := -8 * Real.log u / u
noncomputable def lg2'' (u : ℝ) : ℝ := -8 * (1 - Real.log u) / u ^ 2

theorem hasDerivAt_lg1 {u : ℝ} (hu : 0 < u) : HasDerivAt lg1 (lg1' u) u := by
  have h1 := (Real.hasDerivAt_log hu.ne').const_mul 4
  have h2 := ((hasDerivAt_id u).const_mul 4).log (by simp; positivity)
  convert h1.mul h2 using 1
  · ext v; simp [lg1, mul_assoc]
  · simp only [lg1', id]; field_simp; try ring

theorem hasDerivAt_lg1' {u : ℝ} (hu : 0 < u) : HasDerivAt lg1' (lg1'' u) u := by
  have h1 := ((hasDerivAt_id u).const_mul 4).log (by simp; positivity)
  have h2 := Real.hasDerivAt_log hu.ne'
  convert ((h1.add h2).const_mul 4).div (hasDerivAt_id u) hu.ne' using 1
  · ext v; simp [lg1']
  · simp only [lg1'', id, Pi.add_apply]; field_simp; ring

theorem hasDerivAt_lg2 {u : ℝ} (hu : 0 < u) : HasDerivAt lg2 (lg2' u) u := by
  convert ((Real.hasDerivAt_log hu.ne').pow 2).const_mul (-4) using 1
  · ext v; simp [lg2]
  · simp only [lg2']; field_simp; ring

theorem hasDerivAt_lg2' {u : ℝ} (hu : 0 < u) : HasDerivAt lg2' (lg2'' u) u := by
  convert ((Real.hasDerivAt_log hu.ne').const_mul (-8)).div (hasDerivAt_id u) hu.ne' using 1
  · ext v; simp [lg2']
  · simp only [lg2'', id]; field_simp; ring

theorem logeta2_eq_lg1 {u : ℝ} (h1 : 1 / 4 ≤ u) (h2 : u ≤ 1 / 2) :
    Real.log u * eta2 u = lg1 u := by
  rw [Helfgott.eta2_eq_left h1 h2, lg1]; ring

theorem logeta2_eq_lg2 {u : ℝ} (h1 : 1 / 2 ≤ u) (h2 : u ≤ 1) :
    Real.log u * eta2 u = lg2 u := by
  rw [Helfgott.eta2_eq_right h1 h2, lg2]; ring

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `f̂(t) = ∫_{1/4}^{1/2} e(-ut) g₁ + ∫_{1/2}^1 e(-ut) g₂`. -/
theorem fourier_logeta2_split (t : ℝ) :
    fourier (fun u => Real.log u * eta2 u) t =
      (∫ u in (1 / 4 : ℝ)..(1 / 2), e (-(u * t)) * (lg1 u : ℂ)) +
      ∫ u in (1 / 2 : ℝ)..1, e (-(u * t)) * (lg2 u : ℂ) := by
  have hsupp : ∫ u, e (-(u * t)) * ((Real.log u * eta2 u : ℝ) : ℂ) =
      ∫ u in (1 / 4 : ℝ)..1, e (-(u * t)) * ((Real.log u * eta2 u : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [Helfgott.eta2_eq_zero (fun h => hu ⟨h.1, h.2.le⟩)]; simp
  have hcont : Continuous fun u : ℝ => e (-(u * t)) * ((Real.log u * eta2 u : ℝ) : ℂ) := by
    refine (continuous_e_neg t).mul (Complex.continuous_ofReal.comp ?_)
    have : (fun u => Real.log u * eta2 u) = fun u => Real.log (max u (1 / 8)) * eta2 u := by
      ext u
      by_cases hu : u ∈ Set.Ioo (1 / 4 : ℝ) 1
      · rw [max_eq_left (by linarith [hu.1])]
      · rw [Helfgott.eta2_eq_zero hu]; ring
    rw [this]
    exact (Real.continuousOn_log.comp_continuous (by fun_prop : Continuous fun u : ℝ => max u (1/8))
      (fun u => Set.mem_compl_singleton_iff.2
        (lt_of_lt_of_le (by norm_num) (le_max_right u (1/8))).ne')).mul
      Helfgott.continuous_eta2
  unfold fourier
  rw [hsupp, ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    rw [logeta2_eq_lg1 hu.1 hu.2]
  · refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    rw [logeta2_eq_lg2 hu.1 hu.2]


theorem continuousAt_lg1'' {u : ℝ} (hu : 0 < u) : ContinuousAt lg1'' u := by
  have h4 : ContinuousAt (fun v => Real.log (4 * v)) u :=
    (Real.continuousAt_log (by positivity)).comp (continuousAt_const.mul continuousAt_id)
  have hl : ContinuousAt Real.log u := Real.continuousAt_log hu.ne'
  exact (continuousAt_const.mul ((continuousAt_const.sub h4).sub hl)).div
    (continuousAt_id.pow 2) (by positivity)

theorem continuousAt_lg2'' {u : ℝ} (hu : 0 < u) : ContinuousAt lg2'' u := by
  have hl : ContinuousAt Real.log u := Real.continuousAt_log hu.ne'
  exact (continuousAt_const.mul (continuousAt_const.sub hl)).div
    (continuousAt_id.pow 2) (by positivity)

theorem log_quarter : Real.log (1 / 4) = -(2 * Real.log 2) := by
  rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem log_half : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- `∫_a^b |g''| ≤ |g'(b) - g'(a)|` when `g''` has a constant sign: here `∫_{1/4}^{1/2} |g₁''| = 32 log 2`. -/
theorem integral_abs_lg1'' : ∫ u in (1 / 4 : ℝ)..(1 / 2), |lg1'' u| = 32 * Real.log 2 := by
  have hpos : ∀ u ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  rw [intervalIntegral.integral_congr (g := lg1'') fun u hu => by
    have h0 := hpos u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    refine abs_of_nonneg ?_
    have h1 : Real.log (4 * u) ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith [hu.2])
    have h2 : Real.log u ≤ 0 := Real.log_nonpos h0.le (by linarith [hu.2])
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    unfold lg1''; apply div_nonneg _ (by positivity); linarith]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hasDerivAt_lg1' (hpos u hu))
    (ContinuousOn.intervalIntegrable fun u hu => (continuousAt_lg1'' (hpos u hu)).continuousWithinAt)]
  simp only [lg1']
  rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num, show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.log_one,
    log_half, log_quarter]
  ring

theorem integral_abs_lg2'' : ∫ u in (1 / 2 : ℝ)..1, |lg2'' u| = 16 * Real.log 2 := by
  have hpos : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  rw [intervalIntegral.integral_congr (g := fun u => -lg2'' u) fun u hu => by
    have h0 := hpos u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    refine abs_of_nonpos ?_
    have h2 : Real.log u ≤ 0 := Real.log_nonpos h0.le hu.2
    unfold lg2''; apply div_nonpos_of_nonpos_of_nonneg _ (by positivity); nlinarith]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_lg2' (hpos u hu))
    (ContinuousOn.intervalIntegrable fun u hu => (continuousAt_lg2'' (hpos u hu)).continuousWithinAt)]
  simp only [lg2']
  rw [Real.log_one, log_half]; ring


theorem norm_integral_lg''_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) (g : ℝ → ℝ) :
    ‖∫ u in a..b, (g u : ℂ) * e (-(u * t))‖ ≤ ∫ u in a..b, |g u| := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **[H, Lemma B.2.4]**: `(2πt)² |(log·η₂)^(t)| ≤ |(log·η₂)''|₁ = 96 log 2`. -/
theorem norm_fourier_logeta2_le_decay (t : ℝ) :
    (2 * π * t) ^ 2 * ‖fourier (fun u => Real.log u * eta2 u) t‖ ≤ 96 * Real.log 2 := by
  have hl := log_two_pos'
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  have hp1 : ∀ u ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  have hp2 : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  rw [fourier_logeta2_split, integral_e_mul_ibp2 ht (fun u hu => hasDerivAt_lg1 (hp1 u hu))
      (fun u hu => hasDerivAt_lg1' (hp1 u hu)) (fun u hu => (continuousAt_lg1'' (hp1 u hu)).continuousWithinAt),
    integral_e_mul_ibp2 ht (fun u hu => hasDerivAt_lg2 (hp2 u hu))
      (fun u hu => hasDerivAt_lg2' (hp2 u hu)) (fun u hu => (continuousAt_lg2'' (hp2 u hu)).continuousWithinAt)]
  set c : ℂ := -(2 * π * I * t)
  have hc : c ≠ 0 := by
    simp only [c, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      I_ne_zero) (by exact_mod_cast ht)
  have hnc : ‖c‖ ^ 2 = (2 * π * t) ^ 2 := by
    simp only [c, norm_neg, norm_mul, Complex.norm_real, Complex.norm_ofNat, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
  set I1 := ∫ u in (1 / 4 : ℝ)..(1 / 2), (lg1'' u : ℂ) * e (-(u * t))
  set I2 := ∫ u in (1 / 2 : ℝ)..1, (lg2'' u : ℂ) * e (-(u * t))
  -- Boundary values.
  have v1 : lg1 (1 / 4) = 0 := by simp [lg1, show (4 : ℝ) * (1 / 4) = 1 by norm_num]
  have v2 : lg1 (1 / 2) = lg2 (1 / 2) := by
    simp only [lg1, lg2]; rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num, log_half]; ring
  have v3 : lg2 1 = 0 := by simp [lg2]
  have w1 : lg1' (1 / 4) = -(32 * Real.log 2) := by
    simp only [lg1']; rw [show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.log_one, log_quarter]; ring
  have w2 : lg1' (1 / 2) = 0 := by
    simp only [lg1']; rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num, log_half]; ring
  have w3 : lg2' (1 / 2) = 16 * Real.log 2 := by simp only [lg2']; rw [log_half]; ring
  have w4 : lg2' 1 = 0 := by simp [lg2']
  have hsum : e (-(1 / 2 * t)) * ((lg1 (1 / 2) : ℂ) / c - (lg1' (1 / 2) : ℂ) / c ^ 2) -
        e (-(1 / 4 * t)) * ((lg1 (1 / 4) : ℂ) / c - (lg1' (1 / 4) : ℂ) / c ^ 2) + I1 / c ^ 2 +
      ((e (-(1 * t)) * ((lg2 1 : ℂ) / c - (lg2' 1 : ℂ) / c ^ 2) -
        e (-(1 / 2 * t)) * ((lg2 (1 / 2) : ℂ) / c - (lg2' (1 / 2) : ℂ) / c ^ 2)) + I2 / c ^ 2) =
      ((16 * Real.log 2 : ℝ) * e (-(1 / 2 * t)) - (32 * Real.log 2 : ℝ) * e (-(1 / 4 * t)) +
        I1 + I2) / c ^ 2 := by
    rw [v1, v2, v3, w1, w2, w3, w4]; push_cast; field_simp; ring
  rw [hsum, norm_div, norm_pow, hnc, mul_div_cancel₀ _ (by positivity)]
  have hI1 : ‖I1‖ ≤ 32 * Real.log 2 :=
    (norm_integral_lg''_le (by norm_num) t lg1'').trans integral_abs_lg1''.le
  have hI2 : ‖I2‖ ≤ 16 * Real.log 2 :=
    (norm_integral_lg''_le (by norm_num) t lg2'').trans integral_abs_lg2''.le
  have hA : ‖((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t))‖ = 16 * Real.log 2 := by
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hB : ‖((32 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 4 * t))‖ = 32 * Real.log 2 := by
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t)) - ((32 * Real.log 2 : ℝ) : ℂ) *
        e (-(1 / 4 * t)) + I1 + I2‖
      ≤ ‖((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t))‖ + ‖((32 * Real.log 2 : ℝ) : ℂ) *
        e (-(1 / 4 * t))‖ + ‖I1‖ + ‖I2‖ := by
        have n1 := norm_add_le (((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t)) -
          ((32 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 4 * t)) + I1) I2
        have n2 := norm_add_le (((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t)) -
          ((32 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 4 * t))) I1
        have n3 := norm_sub_le (((16 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 2 * t)))
          (((32 * Real.log 2 : ℝ) : ℂ) * e (-(1 / 4 * t)))
        linarith
    _ ≤ 96 * Real.log 2 := by rw [hA, hB]; linarith


/-- **[H, (B.17)]**: `|(log·η₂)^(t)| ≤ |log·η₂|₁ = 2 - log 4`. -/
theorem norm_fourier_logeta2_le (t : ℝ) :
    ‖fourier (fun u => Real.log u * eta2 u) t‖ ≤ 2 - Real.log 4 := by
  have hp1 : ∀ u ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  have hp2 : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  have hn : ∀ (a b : ℝ) (g : ℝ → ℝ), a ≤ b →
      ‖∫ u in a..b, e (-(u * t)) * (g u : ℂ)‖ ≤ ∫ u in a..b, |g u| := fun a b g hab => by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
  -- Antiderivatives.
  set G1 : ℝ → ℝ := fun u => 4 * (u * (Real.log u ^ 2 - 2 * Real.log u + 2) +
    Real.log 4 * (u * (Real.log u - 1)))
  set G2 : ℝ → ℝ := fun u => -4 * (u * (Real.log u ^ 2 - 2 * Real.log u + 2))
  have dG1 : ∀ u ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt G1 (lg1 u) u := fun u hu => by
    have h0 := hp1 u hu
    have hl := Real.hasDerivAt_log h0.ne'
    have := (((hasDerivAt_id u).mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)).add
      (((hasDerivAt_id u).mul (hl.sub_const 1)).const_mul (Real.log 4))).const_mul 4
    convert this using 1
    · ext y; simp only [G1, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]
    · rw [lg1, Real.log_mul (by norm_num) h0.ne']
      simp only [id, Pi.sub_apply, Pi.pow_apply]; field_simp; ring
  have dG2 : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, HasDerivAt G2 (lg2 u) u := fun u hu => by
    have h0 := hp2 u hu
    have hl := Real.hasDerivAt_log h0.ne'
    have := ((hasDerivAt_id u).mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)).const_mul (-4)
    convert this using 1
    · ext y; simp only [G2, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]
    · rw [lg2]; simp only [id, Pi.sub_apply, Pi.pow_apply]; field_simp; ring
  have hc1 : ContinuousOn lg1 (Set.uIcc (1 / 4 : ℝ) (1 / 2)) := fun u hu =>
    (hasDerivAt_lg1 (hp1 u hu)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn lg2 (Set.uIcc (1 / 2 : ℝ) 1) := fun u hu =>
    (hasDerivAt_lg2 (hp2 u hu)).continuousAt.continuousWithinAt
  have J1 : ∫ u in (1 / 4 : ℝ)..(1 / 2), |lg1 u| = -(G1 (1 / 2) - G1 (1 / 4)) := by
    rw [intervalIntegral.integral_congr (g := fun u => -lg1 u) fun u hu => by
      have h0 := hp1 u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      refine abs_of_nonpos ?_
      have h1 : Real.log u ≤ 0 := Real.log_nonpos h0.le (by linarith [hu.2])
      have h2 : 0 ≤ Real.log (4 * u) := Real.log_nonneg (by linarith [hu.1])
      simp only [lg1]; nlinarith,
      intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt dG1
        hc1.intervalIntegrable]
  have J2 : ∫ u in (1 / 2 : ℝ)..1, |lg2 u| = -(G2 1 - G2 (1 / 2)) := by
    rw [intervalIntegral.integral_congr (g := fun u => -lg2 u) fun u _ => by
      refine abs_of_nonpos ?_
      simp only [lg2]; nlinarith [sq_nonneg (Real.log u)],
      intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt dG2
        hc2.intervalIntegrable]
  rw [fourier_logeta2_split]
  refine (norm_add_le _ _).trans ((add_le_add (hn _ _ lg1 (by norm_num))
    (hn _ _ lg2 (by norm_num))).trans (le_of_eq ?_))
  rw [J1, J2]
  simp only [G1, G2]
  rw [log_half, log_quarter, Real.log_one, log_four]
  ring

end TernaryGoldbach.MinorArcs
