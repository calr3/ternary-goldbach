import TernaryGoldbach.Explicit.WeilSplit

/-!
# The Weil identity: the archimedean and polar parts

With `H̃ = H_T + H_T(1 − ·)` (`WHt`), on the lines `ℜs = 1/2` and `3/2`:
* `J₂`: `∫ A(3/2 + iy) H̃(3/2 + iy) dy = ∫ A(1/2 + iy) H̃(1/2 + iy) dy` for the archimedean factor
  `A(s) = −½ log π + ½ψ(s/2)` (`J2_shift`; Cauchy on `[1/2, 3/2] × [−Y, Y]`, `Y → ∞`);
* `J₁`: `∫ (1/s + 1/(s − 1)) H̃(s) dy = 2π H̃(1)` on `ℜs = 3/2` (`J1_eq`; Cauchy's formula at `s = 1`,
  and the integrand is odd on `ℜs = 1/2` since `H̃(1 − s) = H̃(s)`).
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

variable {ℓ : ℝ} {m : ℕ}

theorem WHt_one_sub (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) (s : ℂ) : WHt ℓ m T₀ (1 - s) = WHt ℓ m T₀ s := by
  unfold WHt; rw [sub_sub_cancel]; ring

/-- `|H̃(s)| ≤ 4^m e^{2mℓ|σ−½|} (L(t − T₀)² + L(t + T₀)²)` for `m ≥ 2`. -/
theorem norm_WHt_le_sq (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) (s : ℂ) :
    ‖WHt ℓ m T₀ s‖ ≤ 4 ^ m * Real.exp (2 * m * ℓ * |s.re - 1 / 2|) *
      (lor (s.im - T₀) ^ 2 + lor (s.im + T₀) ^ 2) := by
  have h1 := norm_WH_le_lor_sq hℓ0 hℓ1 hm T₀ s
  have h2 := norm_WH_le_lor_sq hℓ0 hℓ1 hm T₀ (1 - s)
  have e1 : |(1 - s).re - 1 / 2| = |s.re - 1 / 2| := by
    rw [show (1 - s).re - 1 / 2 = -(s.re - 1 / 2) by simp; ring, abs_neg]
  have e2 : lor ((1 - s).im - T₀) = lor (s.im + T₀) := by
    rw [show (1 - s).im - T₀ = -(s.im + T₀) by simp; ring, lor_neg]
  rw [e1, e2] at h2
  calc ‖WHt ℓ m T₀ s‖ ≤ ‖WH ℓ m T₀ s‖ + ‖WH ℓ m T₀ (1 - s)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The Lorentzian majorant `K (L(y − T₀) + L(y + T₀))`. -/
noncomputable def LMaj (T₀ K : ℝ) (y : ℝ) : ℝ := K * (lor (y - T₀) + lor (y + T₀))

theorem integrable_LMaj (T₀ K : ℝ) : Integrable (LMaj T₀ K) := by
  have h2 : Integrable fun y : ℝ => lor (y + T₀) := by
    simpa [sub_neg_eq_add] using integrable_lor (-T₀)
  exact ((integrable_lor T₀).add h2).const_mul K

theorem tendsto_LMaj_atTop (T₀ K : ℝ) : Tendsto (LMaj T₀ K) atTop (𝓝 0) := by
  have h2 : Tendsto (fun y : ℝ => lor (y + T₀)) atTop (𝓝 0) := by
    simpa [sub_neg_eq_add] using tendsto_lor_atTop (-T₀)
  have := ((tendsto_lor_atTop T₀).add h2).const_mul K
  simp only [add_zero, mul_zero] at this
  unfold LMaj; exact this

theorem tendsto_LMaj_atBot (T₀ K : ℝ) : Tendsto (LMaj T₀ K) atBot (𝓝 0) := by
  have h2 : Tendsto (fun y : ℝ => lor (y + T₀)) atBot (𝓝 0) := by
    simpa [sub_neg_eq_add] using tendsto_lor_atBot (-T₀)
  have := ((tendsto_lor_atBot T₀).add h2).const_mul K
  simp only [add_zero, mul_zero] at this
  unfold LMaj; exact this

/-- `(A + B|y|) |H̃(σ + iy)| ≤ K (L(y − T₀) + L(y + T₀))` on `|σ − ½| ≤ 1`. -/
theorem mul_norm_WHt_le (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) {σ : ℝ} (hσ : |σ - 1 / 2| ≤ 1) (y : ℝ) :
    (A + B * |y|) * ‖WHt ℓ m T₀ ((σ : ℂ) + y * I)‖ ≤
      LMaj T₀ (4 ^ m * Real.exp (2 * m * ℓ) * (A + B) * (3 + 2 * |T₀|)) y := by
  have h := norm_WHt_le_sq hℓ0 hℓ1 hm T₀ ((σ : ℂ) + y * I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at h
  have he : Real.exp (2 * m * ℓ * |σ - 1 / 2|) ≤ Real.exp (2 * m * ℓ) :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) hσ)
  have h1 := one_add_abs_mul_lor_sq_le T₀ y
  have h2 := one_add_abs_mul_lor_sq_le (-T₀) y
  rw [sub_neg_eq_add, abs_neg] at h2
  have hAB : A + B * |y| ≤ (A + B) * (1 + |y|) := by nlinarith [abs_nonneg y]
  set E := 4 ^ m * Real.exp (2 * m * ℓ) with hE
  have hE0 : 0 ≤ E := by positivity
  have hl1 := (lor_pos (y - T₀)).le
  have hl2 := (lor_pos (y + T₀)).le
  calc (A + B * |y|) * ‖WHt ℓ m T₀ ((σ : ℂ) + y * I)‖ ≤
      ((A + B) * (1 + |y|)) * (E * (lor (y - T₀) ^ 2 + lor (y + T₀) ^ 2)) := by
        refine mul_le_mul hAB (h.trans ?_) (norm_nonneg _) (by positivity)
        rw [hE]; gcongr
    _ = (A + B) * E * ((1 + |y|) * lor (y - T₀) ^ 2 + (1 + |y|) * lor (y + T₀) ^ 2) := by ring
    _ ≤ (A + B) * E * ((3 + 2 * |T₀|) * lor (y - T₀) + (3 + 2 * |T₀|) * lor (y + T₀)) := by
        gcongr
    _ = LMaj T₀ (E * (A + B) * (3 + 2 * |T₀|)) y := by unfold LMaj; ring

/-! ### Digamma on the strip -/

theorem not_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ k : ℕ, z ≠ -(k : ℂ) := by
  intro k h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- `|ψ(s/2)| ≤ 8|s| + 60` for `1/2 ≤ ℜs ≤ 3/2`. -/
theorem norm_digamma_half_strip {s : ℂ} (h1 : 1 / 2 ≤ s.re) (_h2 : s.re ≤ 3 / 2) :
    ‖Complex.digamma (s / 2)‖ ≤ 8 * ‖s‖ + 60 := by
  set z := s / 2 with hz
  have hzre : z.re = s.re / 2 := by simp [hz]
  have hz0 : 0 < z.re := by rw [hzre]; linarith
  have hrec := Complex.digamma_apply_add_nat (not_neg_nat_of_re_pos hz0) 3
  have e : Complex.digamma z = Complex.digamma (z + 3) - ∑ k ∈ Finset.range 3, (z + k)⁻¹ := by
    rw [show ((3 : ℕ) : ℂ) = 3 by norm_num] at hrec
    rw [hrec]; ring
  have hinv : ∀ k ∈ Finset.range 3, ‖(z + k)⁻¹‖ ≤ 4 := by
    intro k _
    have hre : 1 / 4 ≤ (z + k).re := by
      simp only [Complex.add_re, Complex.natCast_re]; rw [hzre]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [norm_inv]
    have : 1 / 4 ≤ ‖z + k‖ := hre.trans (Complex.re_le_norm _)
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hsum : ‖∑ k ∈ Finset.range 3, (z + k)⁻¹‖ ≤ 12 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range 3, ‖(z + (k : ℂ))⁻¹‖ ≤ ∑ _k ∈ Finset.range 3, (4 : ℝ) := Finset.sum_le_sum hinv
      _ = 12 := by norm_num
  have h3re : 1 ≤ (z + 3).re := by simp; rw [hzre]; linarith
  have h3n : 3 ≤ ‖z + 3‖ := by
    have : 3 ≤ (z + 3).re := by simp; rw [hzre]; linarith
    exact this.trans (Complex.re_le_norm _)
  have hd := norm_digamma_le h3re h3n
  have hlog : Real.log (1 + ‖z + 3‖) ≤ ‖z + 3‖ := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + ‖z + 3‖); linarith
  have hz3 : ‖z + 3‖ ≤ ‖s‖ / 2 + 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [hz, norm_div, Complex.norm_ofNat]; norm_num
  rw [e]
  calc ‖Complex.digamma (z + 3) - ∑ k ∈ Finset.range 3, (z + k)⁻¹‖ ≤
      ‖Complex.digamma (z + 3)‖ + ‖∑ k ∈ Finset.range 3, (z + k)⁻¹‖ := norm_sub_le _ _
    _ ≤ 16 * (‖s‖ / 2 + 3) + 12 := by linarith
    _ = 8 * ‖s‖ + 60 := by ring

theorem differentiableAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (not_neg_nat_of_re_pos hw)).differentiableWithinAt
  have ha : AnalyticAt ℂ Complex.Gamma z := hG.analyticAt (hU.mem_nhds hz)
  have hd : DifferentiableAt ℂ (deriv Complex.Gamma) z := ha.deriv.differentiableAt
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos hz)
  have : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact hd.div ha.differentiableAt hne

/-- The archimedean factor `A(s) = −½ log π + ½ψ(s/2)`. -/
noncomputable def archF (s : ℂ) : ℂ := -(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2)

theorem differentiableAt_archF {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ archF s := by
  unfold archF
  refine (differentiableAt_const _).add ((differentiableAt_const _).mul ?_)
  exact (differentiableAt_digamma_of_re_pos (by simp; linarith)).comp s
    (differentiableAt_id.div_const 2)

theorem norm_archF_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : ‖archF s‖ ≤ 31 + 4 * ‖s‖ := by
  have hd := norm_digamma_half_strip h1 h2
  have hlog : ‖Complex.log π‖ ≤ 1.2 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_of_nonneg
      (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    exact log_pi_le
  unfold archF
  calc ‖-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2)‖ ≤
      ‖-(1 / 2) * Complex.log π‖ + ‖1 / 2 * Complex.digamma (s / 2)‖ := norm_add_le _ _
    _ = 1 / 2 * ‖Complex.log π‖ + 1 / 2 * ‖Complex.digamma (s / 2)‖ := by
        rw [norm_mul, norm_mul]; norm_num
    _ ≤ 31 + 4 * ‖s‖ := by linarith

theorem norm_line_le (σ y : ℝ) : ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-! ### `J₂`: the archimedean part moves to the critical line -/

theorem J2_shift (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) :
    ∫ y : ℝ, archF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) =
      ∫ y : ℝ, archF (((1 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I) := by
  set F : ℂ → ℂ := fun s => archF s * WHt ℓ m T₀ s with hF
  set K := 4 ^ m * Real.exp (2 * m * ℓ) * (37 + 4) * (3 + 2 * |T₀|) with hK
  have hbd : ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2), ∀ y : ℝ, ‖F ((σ : ℂ) + y * I)‖ ≤ LMaj T₀ K y := by
    intro σ hσ y
    have hσ' : |σ - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    have ha := norm_archF_le (s := (σ : ℂ) + y * I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2)
    have hn := norm_line_le σ y
    rw [abs_of_nonneg (by linarith [hσ.1] : (0 : ℝ) ≤ σ)] at hn
    have ha' : ‖archF ((σ : ℂ) + y * I)‖ ≤ 37 + 4 * |y| := by linarith [hσ.2]
    rw [hF, norm_mul]
    exact (mul_le_mul_of_nonneg_right ha' (norm_nonneg _)).trans
      (mul_norm_WHt_le hℓ0 hℓ1 hm T₀ (by norm_num) (by norm_num) hσ' y)
  have hcont : ∀ c : ℝ, 0 < c → Continuous fun y : ℝ => F ((c : ℂ) + y * I) := by
    intro c hc
    refine continuous_iff_continuousAt.2 fun y => ?_
    have h1 : DifferentiableAt ℂ F ((c : ℂ) + y * I) :=
      (differentiableAt_archF (by simp; exact hc)).mul (differentiable_WHt ℓ m T₀ _)
    exact h1.continuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  have hint : ∀ c ∈ Icc (1 / 2 : ℝ) (3 / 2), Integrable fun y : ℝ => F ((c : ℂ) + y * I) := by
    intro c hc
    exact (integrable_LMaj T₀ K).mono' (hcont c (by linarith [hc.1])).aestronglyMeasurable
      (ae_of_all _ fun y => hbd c hc y)
  have h := rectInt_limit (F := F) (a := 1 / 2) (b := 3 / 2) (by norm_num) (C := 0)
    (Eventually.of_forall fun Y => ?_) (hint _ ⟨le_rfl, by norm_num⟩) (hint _ ⟨by norm_num, le_rfl⟩)
    (tendsto_LMaj_atTop T₀ K) (tendsto_LMaj_atBot T₀ K) (Eventually.of_forall fun Y σ hσ => hbd σ hσ Y)
    (Eventually.of_forall fun Y σ hσ => hbd σ hσ Y)
  · rw [mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.1 h
  · refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn F _ _ fun u hu => ?_
    have := (Complex.mem_reProdIm.1 hu).1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at this
    rw [uIcc_of_le (by norm_num)] at this
    exact ((differentiableAt_archF (by linarith [this.1])).mul
      (differentiable_WHt ℓ m T₀ u)).differentiableWithinAt

/-! ### `J₁`: the pole at `s = 1` -/

/-- `g(s) = H̃(s)(2s − 1)/s`, so that `(1/s + 1/(s − 1)) H̃(s) = g(s)/(s − 1)`. -/
noncomputable def WG (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) (s : ℂ) : ℂ := WHt ℓ m T₀ s * (2 * s - 1) / s

/-- The polar integrand `(1/s + 1/(s − 1)) H̃(s) = g(s)(s − 1)⁻¹`. -/
noncomputable def WP (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) (s : ℂ) : ℂ := WG ℓ m T₀ s * (s - 1)⁻¹

theorem WP_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) :
    WP ℓ m T₀ s = (1 / s + 1 / (s - 1)) * WHt ℓ m T₀ s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  unfold WP WG; field_simp; ring

theorem WP_one_sub (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) (s : ℂ) : WP ℓ m T₀ (1 - s) = -WP ℓ m T₀ s := by
  unfold WP WG
  rw [WHt_one_sub]
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have h3 : (1 : ℂ) - s - 1 ≠ 0 := by rw [sub_sub_cancel_left]; exact neg_ne_zero.2 hs0
  field_simp
  ring

theorem norm_one_div_add_le {s : ℂ} (h0 : 1 / 2 ≤ ‖s‖) (h1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖1 / s + 1 / (s - 1)‖ ≤ 4 := by
  have hs0 : 0 < ‖s‖ := by linarith
  have hs1 : 0 < ‖s - 1‖ := by linarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, norm_one]
  have a : 1 / ‖s‖ ≤ 2 := by rw [div_le_iff₀ hs0]; linarith
  have b : 1 / ‖s - 1‖ ≤ 2 := by rw [div_le_iff₀ hs1]; linarith
  linarith

theorem J1_eq (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) :
    ∫ y : ℝ, WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) = 2 * π * WHt ℓ m T₀ 1 := by
  set K := 4 ^ m * Real.exp (2 * m * ℓ) * (4 + 2) * (3 + 2 * |T₀|) with hK
  -- on the lines `ℜs = 1/2, 3/2` and on horizontal segments with `|Y| ≥ 1`
  have hbd0 : ∀ σ y : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → 1 / 2 ≤ ‖(σ : ℂ) + y * I‖ →
      1 / 2 ≤ ‖(σ : ℂ) + y * I - 1‖ → ‖WP ℓ m T₀ ((σ : ℂ) + y * I)‖ ≤ LMaj T₀ (4 ^ m * Real.exp (2 * m * ℓ) *
        4 * (3 + 2 * |T₀|)) y := by
    intro σ y h1 h2 hn0 hn1
    have hs0 : (σ : ℂ) + y * I ≠ 0 := by intro h; rw [h, norm_zero] at hn0; linarith
    have hs1 : (σ : ℂ) + y * I ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn1; linarith
    have hσ' : |σ - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [WP_eq hs0 hs1, norm_mul]
    have := mul_norm_WHt_le hℓ0 hℓ1 hm T₀ (A := 4) (B := 0) (by norm_num) le_rfl hσ' y
    simp only [zero_mul, add_zero] at this
    exact (mul_le_mul_of_nonneg_right (norm_one_div_add_le hn0 hn1) (norm_nonneg _)).trans this
  have hline : ∀ c : ℝ, (c = 1 / 2 ∨ c = 3 / 2) → ∀ y : ℝ,
      ‖WP ℓ m T₀ ((c : ℂ) + y * I)‖ ≤ LMaj T₀ (4 ^ m * Real.exp (2 * m * ℓ) * 4 * (3 + 2 * |T₀|)) y := by
    intro c hc y
    have hre : ((c : ℂ) + y * I).re = c := by simp
    have hre1 : ((c : ℂ) + y * I - 1).re = c - 1 := by simp
    refine hbd0 c y (by rcases hc with rfl | rfl <;> norm_num) (by rcases hc with rfl | rfl <;> norm_num) ?_ ?_
    · refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [hre]; rcases hc with h | h <;> rw [h] <;> norm_num
    · refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [hre1]; rcases hc with h | h <;> rw [h] <;> norm_num
  have hcont : ∀ c : ℝ, (c = 1 / 2 ∨ c = 3 / 2) → Continuous fun y : ℝ => WP ℓ m T₀ ((c : ℂ) + y * I) := by
    intro c hc
    have hne0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := by
      intro y h; have := congrArg Complex.re h; simp at this; rcases hc with h | h <;> (rw [h] at this; norm_num at this)
    have hne1 : ∀ y : ℝ, (c : ℂ) + y * I - 1 ≠ 0 := by
      intro y h; have := congrArg Complex.re h; simp at this; rcases hc with h | h <;> (rw [h] at this; norm_num at this)
    unfold WP WG
    refine Continuous.mul (Continuous.div ?_ (by fun_prop) hne0) (Continuous.inv₀ (by fun_prop) hne1)
    exact ((differentiable_WHt ℓ m T₀).continuous.comp (by fun_prop)).mul (by fun_prop)
  have hint : ∀ c : ℝ, (c = 1 / 2 ∨ c = 3 / 2) → Integrable fun y : ℝ => WP ℓ m T₀ ((c : ℂ) + y * I) :=
    fun c hc => (integrable_LMaj T₀ _).mono' (hcont c hc).aestronglyMeasurable (ae_of_all _ (hline c hc))
  -- the horizontal segments, `|Y| ≥ 1`
  have hhor : ∀ Y : ℝ, 1 ≤ |Y| → ∀ σ ∈ Icc (1 / 2 : ℝ) (3 / 2), ‖WP ℓ m T₀ ((σ : ℂ) + Y * I)‖ ≤
      LMaj T₀ (4 ^ m * Real.exp (2 * m * ℓ) * 4 * (3 + 2 * |T₀|)) Y := by
    intro Y hY σ hσ
    refine hbd0 σ Y hσ.1 hσ.2 ?_ ?_
    · refine le_trans ?_ (Complex.abs_im_le_norm _); simp; linarith
    · refine le_trans ?_ (Complex.abs_im_le_norm _); simp; linarith
  -- the oddness on `ℜs = 1/2`
  have hodd : ∫ y : ℝ, WP ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I) = 0 := by
    have h := integral_neg_eq_self (fun y : ℝ => WP ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I)) volume
    have e : ∀ y : ℝ, WP ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -WP ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I) := by
      intro y
      rw [← WP_one_sub]; congr 1; push_cast; ring
    simp only [e, integral_neg] at h
    have : (2 : ℂ) * ∫ y : ℝ, WP ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I) = 0 := by
      rw [two_mul]; nth_rewrite 1 [← h]; ring
    simpa using this
  -- Cauchy's formula on the rectangles
  have hU : IsOpen {w : ℂ | 1 / 4 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hgd : DifferentiableOn ℂ (WG ℓ m T₀) {w : ℂ | 1 / 4 < w.re} := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
    unfold WG
    exact ((((differentiable_WHt ℓ m T₀) w).mul (by fun_prop)).div differentiableAt_id hw0).differentiableWithinAt
  have hC : ∀ᶠ Y in atTop, rectInt (WP ℓ m T₀) (((1 / 2 : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I)
      (((3 / 2 : ℝ) : ℂ) + (Y : ℂ) * I) = 2 * π * I * WHt ℓ m T₀ 1 := by
    filter_upwards [eventually_gt_atTop 0] with Y hY
    have hsub : [[(((1 / 2 : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I).re, (((3 / 2 : ℝ) : ℂ) + (Y : ℂ) * I).re]] ×ℂ
        [[(((1 / 2 : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I).im, (((3 / 2 : ℝ) : ℂ) + (Y : ℂ) * I).im]] ⊆
        {w : ℂ | 1 / 4 < w.re} := by
      intro u hu
      have := (Complex.mem_reProdIm.1 hu).1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at this
      rw [uIcc_of_le (by norm_num)] at this
      show 1 / 4 < u.re; linarith [this.1]
    have := rectInt_mul_inv_sub hU hsub hgd (ρ := 1) (by simp; norm_num) (by simp; norm_num)
      (by simp; linarith) (by simp; linarith)
    rw [show WG ℓ m T₀ 1 = WHt ℓ m T₀ 1 by unfold WG; norm_num] at this
    exact this
  have h := rectInt_limit (F := WP ℓ m T₀) (a := 1 / 2) (b := 3 / 2) (by norm_num) hC
    (hint _ (Or.inl rfl)) (hint _ (Or.inr rfl)) (tendsto_LMaj_atTop T₀ _) (tendsto_LMaj_atBot T₀ _)
    ((eventually_ge_atTop 1).mono fun Y hY => hhor Y (by rw [abs_of_nonneg (by linarith)]; exact hY))
    ((eventually_le_atBot (-1)).mono fun Y hY => hhor Y (by rw [abs_of_nonpos (by linarith)]; linarith))
  rw [hodd, sub_zero] at h
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have : I * ((∫ y : ℝ, WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I)) - 2 * π * WHt ℓ m T₀ 1) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hI
  · exact sub_eq_zero.1 h1

/-! ### Integrability on the lines (for the limit) -/

theorem integrable_archF_WHt (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) {c : ℝ}
    (hc : c ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    Integrable fun y : ℝ => archF ((c : ℂ) + y * I) * WHt ℓ m T₀ ((c : ℂ) + y * I) := by
  set K := 4 ^ m * Real.exp (2 * m * ℓ) * (37 + 4) * (3 + 2 * |T₀|) with hK
  have hbd : ∀ y : ℝ, ‖archF ((c : ℂ) + y * I) * WHt ℓ m T₀ ((c : ℂ) + y * I)‖ ≤ LMaj T₀ K y := by
    intro y
    have hσ' : |c - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
    have hre : ((c : ℂ) + y * I).re = c := by simp
    have ha := norm_archF_le (s := (c : ℂ) + y * I) (by rw [hre]; exact hc.1) (by rw [hre]; exact hc.2)
    have hn := norm_line_le c y
    rw [abs_of_nonneg (by linarith [hc.1] : (0 : ℝ) ≤ c)] at hn
    have ha' : ‖archF ((c : ℂ) + y * I)‖ ≤ 37 + 4 * |y| := by linarith [hc.2]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha' (norm_nonneg _)).trans
      (mul_norm_WHt_le hℓ0 hℓ1 hm T₀ (by norm_num) (by norm_num) hσ' y)
  have hcont : Continuous fun y : ℝ => archF ((c : ℂ) + y * I) * WHt ℓ m T₀ ((c : ℂ) + y * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have h1 : DifferentiableAt ℂ (fun s => archF s * WHt ℓ m T₀ s) ((c : ℂ) + y * I) :=
      (differentiableAt_archF (by simp; linarith [hc.1])).mul (differentiable_WHt ℓ m T₀ _)
    exact h1.continuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  exact (integrable_LMaj T₀ K).mono' hcont.aestronglyMeasurable (ae_of_all _ hbd)

theorem integrable_WP_three_halves (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) :
    Integrable fun y : ℝ => WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) := by
  have hne0 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 0 := by
    intro y h; have := congrArg Complex.re h; simp at this
  have hne1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := by
    intro y h; have := congrArg Complex.re h; simp at this; norm_num at this
  have hbd : ∀ y : ℝ, ‖WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      LMaj T₀ (4 ^ m * Real.exp (2 * m * ℓ) * 4 * (3 + 2 * |T₀|)) y := by
    intro y
    rw [WP_eq (hne0 y) (hne1 y), norm_mul]
    have h0 : 1 / 2 ≤ ‖((3 / 2 : ℝ) : ℂ) + y * I‖ :=
      le_trans (by simp; norm_num) (Complex.abs_re_le_norm _)
    have h1 : 1 / 2 ≤ ‖((3 / 2 : ℝ) : ℂ) + y * I - 1‖ :=
      le_trans (by simp; norm_num) (Complex.abs_re_le_norm _)
    have := mul_norm_WHt_le hℓ0 hℓ1 hm T₀ (A := 4) (B := 0) (by norm_num) le_rfl
      (σ := 3 / 2) (by norm_num) y
    simp only [zero_mul, add_zero] at this
    exact (mul_le_mul_of_nonneg_right (norm_one_div_add_le h0 h1) (norm_nonneg _)).trans this
  have hcont : Continuous fun y : ℝ => WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) := by
    unfold WP WG
    refine Continuous.mul (Continuous.div ?_ (by fun_prop) hne0)
      (Continuous.inv₀ (by fun_prop) fun y => sub_ne_zero.2 (hne1 y))
    exact ((differentiable_WHt ℓ m T₀).continuous.comp (by fun_prop)).mul (by fun_prop)
  exact (integrable_LMaj T₀ _).mono' hcont.aestronglyMeasurable (ae_of_all _ hbd)

end TernaryGoldbach.Explicit
