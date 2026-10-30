import TernaryGoldbach.MinorArcs.InnerSumsGen

/-!
# The smoothing functions `η_(ρ)(t) = log(ρt) η₂(t)` [B, (4.38), (6.2), App. B.2]

For `ρ ≥ 4`: continuity, compact support, `|η_(ρ)|₁ ≤ log ρ`, total variation
`≤ log ρ · |η₂'|₁` ([B, Lemma B.2.1]), `η̂_(ρ) = (log·η₂)^ + log ρ · η̂₂`, and
`smoothData_eta2log`: [B, (4.38)].  The bound `|η̂_(ρ)''|_∞ ≤ 31.521 log ρ` ([B, Lemma B.2.3],
a rigorous computation) is the trusted `sorry` `eta2log_fourier_bound`.
-/

open Real MeasureTheory FourierTransform

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- `η_(ρ)(t) = log(ρt) η₂(t)`. -/
noncomputable def eta2log (ρ t : ℝ) : ℝ := Real.log (ρ * t) * eta2 t

variable {ρ : ℝ} (hρ : 4 ≤ ρ)
include hρ

theorem eta2log_eq_clamp (t : ℝ) : eta2log ρ t = Real.log (ρ * max t (1 / 8)) * eta2 t := by
  unfold eta2log
  rcases le_or_gt t (1 / 8) with h | h
  · rw [Helfgott.eta2_eq_zero (fun h' => by linarith [h'.1]), mul_zero, mul_zero]
  · rw [max_eq_left h.le]

theorem continuous_eta2log : Continuous (eta2log ρ) := by
  have : eta2log ρ = fun t => Real.log (ρ * max t (1 / 8)) * eta2 t := funext (eta2log_eq_clamp hρ)
  rw [this]
  refine Continuous.mul ?_ Helfgott.continuous_eta2
  exact (continuous_const.mul (continuous_id.max continuous_const)).log fun t =>
    (mul_pos (by linarith) (lt_of_lt_of_le (by norm_num) (le_max_right t _))).ne'

omit hρ in
theorem hasCompactSupport_eta2log : HasCompactSupport (eta2log ρ) :=
  Helfgott.hasCompactSupport_eta2.mul_left

theorem abs_eta2log_le (t : ℝ) : |eta2log ρ t| ≤ Real.log ρ * eta2 t := by
  unfold eta2log
  by_cases ht : t ∈ Set.Ioo (1 / 4 : ℝ) 1
  · have h1 : 1 ≤ ρ * t := by nlinarith [ht.1]
    have h2 : ρ * t ≤ ρ := by nlinarith [ht.2]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Helfgott.eta2_nonneg t)]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) h2) (Helfgott.eta2_nonneg t)
  · rw [Helfgott.eta2_eq_zero ht]; simp

theorem integral_abs_eta2log_le : ∫ t, |eta2log ρ t| ≤ Real.log ρ := by
  have hint : Integrable (fun t => Real.log ρ * eta2 t) :=
    (continuous_const.mul Helfgott.continuous_eta2).integrable_of_hasCompactSupport
      Helfgott.hasCompactSupport_eta2.mul_left
  calc ∫ t, |eta2log ρ t| ≤ ∫ t, Real.log ρ * eta2 t :=
        integral_mono ((continuous_eta2log hρ).abs.integrable_of_hasCompactSupport
          hasCompactSupport_eta2log.abs) hint (abs_eta2log_le hρ)
    _ = Real.log ρ * ∫ t, |eta2 t| := by
        rw [integral_const_mul]; congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
          (abs_of_nonneg (Helfgott.eta2_nonneg t)).symm)
    _ = Real.log ρ := by rw [Helfgott.integral_abs_eta2, mul_one]

theorem monotoneOn_eta2log : MonotoneOn (eta2log ρ) (Set.Icc (1 / 4) (1 / 2)) := by
  intro s hs t ht hst
  unfold eta2log
  rw [Helfgott.eta2_eq_left hs.1 hs.2, Helfgott.eta2_eq_left ht.1 ht.2]
  have hs0 : 0 < s := by linarith [hs.1]
  have h1 : 0 ≤ Real.log (ρ * s) := Real.log_nonneg (by nlinarith [hs.1])
  have h2 : 0 ≤ 4 * Real.log (4 * s) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * s by linarith [hs.1]); linarith
  have h3 : Real.log (ρ * s) ≤ Real.log (ρ * t) := Real.log_le_log (by positivity) (by nlinarith)
  have h4 : 4 * Real.log (4 * s) ≤ 4 * Real.log (4 * t) := by
    have := Real.log_le_log (by positivity) (show 4 * s ≤ 4 * t by linarith); linarith
  exact mul_le_mul h3 h4 h2 (h1.trans h3)

theorem antitoneOn_eta2log : AntitoneOn (eta2log ρ) (Set.Icc (1 / 2) 1) := by
  intro s hs t ht hst
  unfold eta2log
  rw [Helfgott.eta2_eq_right hs.1 hs.2, Helfgott.eta2_eq_right ht.1 ht.2]
  have hs0 : 0 < s := by linarith [hs.1]
  have ht0 : 0 < t := by linarith [ht.1]
  -- With `A = log ρ`, `u = -log s ≥ v = -log t ≥ 0`, `u ≤ log 2 ≤ A/2`: `(A-v)v ≤ (A-u)u`.
  set A := Real.log ρ
  set u := -Real.log s
  set v := -Real.log t
  have hA : 2 * Real.log 2 ≤ A := by
    have := Real.log_le_log (by norm_num) hρ
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this; push_cast at this; linarith
  have hu : u ≤ Real.log 2 := by
    simp only [u]
    have := Real.log_le_log (by norm_num) (show (1 / 2 : ℝ) ≤ s from hs.1)
    rw [one_div, Real.log_inv] at this; linarith
  have hvu : v ≤ u := by simp only [u, v]; linarith [Real.log_le_log hs0 hst]
  have hv0 : 0 ≤ v := by simp only [v]; linarith [Real.log_nonpos ht0.le ht.2]
  have es : Real.log (ρ * s) * (-4 * Real.log s) = 4 * ((A - u) * u) := by
    rw [Real.log_mul (by linarith) hs0.ne']; simp only [A, u]; ring
  have et : Real.log (ρ * t) * (-4 * Real.log t) = 4 * ((A - v) * v) := by
    rw [Real.log_mul (by linarith) ht0.ne']; simp only [A, v]; ring
  rw [es, et]
  nlinarith

/-- **[B, Lemma B.2.1]**: the total variation of `η_(ρ)` is `8 log 2 · log(ρ/2) ≤ log ρ · |η₂'|₁`. -/
theorem eVariationOn_eta2log_le :
    eVariationOn (eta2log ρ) Set.univ ≤ ENNReal.ofReal (eta2'L1 * Real.log ρ) := by
  set f := eta2log ρ
  set φ : ℝ → ℝ := fun t => max (1 / 4) (min t 1)
  have hφ : MonotoneOn φ Set.univ := fun s _ t _ hst => max_le_max le_rfl (min_le_min hst le_rfl)
  have h0 : ∀ t, t ∉ Set.Ioo (1 / 4 : ℝ) 1 → f t = 0 := fun t ht => by
    simp only [f, eta2log]; rw [Helfgott.eta2_eq_zero ht, mul_zero]
  have hcomp : f ∘ φ = f := by
    funext t
    simp only [Function.comp, φ]
    rcases le_or_gt t (1 / 4) with h | h
    · rw [min_eq_left (by linarith), max_eq_left h, h0 _ (fun h' => by linarith [h'.1]),
        h0 _ (fun h' => by linarith [h'.1])]
    rcases le_or_gt t 1 with h' | h'
    · rw [min_eq_left h', max_eq_right h.le]
    · rw [min_eq_right h'.le, max_eq_right (by norm_num), h0 _ (fun h'' => by linarith [h''.2]),
        h0 _ (fun h'' => by linarith [h''.2])]
  have himg : φ '' Set.univ = Set.Icc (1 / 4) 1 := by
    ext y; simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Icc, φ]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨y, by rw [min_eq_left h2, max_eq_right h1]⟩
  have h1 := eVariationOn.comp_eq_of_monotoneOn f φ hφ
  rw [hcomp, himg] at h1
  rw [h1]
  have hsplit := eVariationOn.Icc_add_Icc f (s := Set.univ) (a := 1 / 4) (b := 1 / 2) (c := 1)
    (by norm_num) (by norm_num) (Set.mem_univ _)
  simp only [Set.univ_inter] at hsplit
  rw [← hsplit]
  have hL := (monotoneOn_eta2log hρ).eVariationOn_eq (a := 1 / 4) (b := 1 / 2)
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [Set.inter_self] at hL
  set ψ : ℝ → ℝ := fun t => 3 / 2 - t
  have hψ : AntitoneOn ψ (Set.Icc (1 / 2) 1) := fun s _ t _ hst => by simp only [ψ]; linarith
  have hR := eVariationOn.comp_eq_of_antitoneOn f ψ hψ
  have himg2 : ψ '' Set.Icc (1 / 2) 1 = Set.Icc (1 / 2) 1 := by
    ext y; simp only [Set.mem_image, Set.mem_Icc, ψ]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; exact ⟨3 / 2 - y, ⟨by linarith, by linarith⟩, by ring⟩
  rw [himg2] at hR
  have hmono : MonotoneOn (f ∘ ψ) (Set.Icc (1 / 2) 1) := by
    intro s hs t ht hst
    simp only [Function.comp, ψ]
    exact antitoneOn_eta2log hρ ⟨by linarith [ht.2], by linarith [ht.1]⟩
      ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
  have hR2 := hmono.eVariationOn_eq (a := 1 / 2) (b := 1) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [Set.inter_self, hR] at hR2
  rw [hL, hR2]
  simp only [Function.comp, ψ, f]
  rw [show (3 / 2 - 1 / 2 : ℝ) = 1 by norm_num, show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num]
  have hf14 : eta2log ρ (1 / 4) = 0 := h0 _ (fun h => by norm_num at h)
  have hf1 : eta2log ρ 1 = 0 := h0 _ (fun h => by norm_num at h)
  have hf12 : eta2log ρ (1 / 2) = Real.log (ρ / 2) * (4 * Real.log 2) := by
    simp only [eta2log]
    rw [Helfgott.eta2_eq_left (by norm_num) le_rfl, show ρ * (1 / 2) = ρ / 2 by ring,
      show (4 : ℝ) * (1 / 2) = 2 by norm_num]
  rw [hf14, hf1, hf12, sub_zero, ← ENNReal.ofReal_add (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ρ / 2 by linarith)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity) (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ρ / 2 by linarith)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.log (ρ / 2) ≤ Real.log ρ := Real.log_le_log (by linarith) (by linarith)
  have h2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  unfold eta2'L1
  nlinarith


/-- **Trusted fact** [B, Lemma B.2.3]: `|η̂_(ρ)''|_∞ < 31.521 log ρ` for `ρ ≥ 4`, written as
`(2πt)² |η̂_(ρ)(t)| ≤ c₀ log ρ`.  In [B] this is a rigorous computation (interval arithmetic);
it is not formalized here. -/
theorem eta2log_fourier_bound (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2log ρ u : ℂ)) t‖ ≤ c₀ * Real.log ρ := by
  sorry

/-- `η_(ρ)` satisfies [B, (4.38)]. -/
theorem smoothData_eta2log : SmoothData (eta2log ρ) (Real.log ρ) (eta2'L1 * Real.log ρ)
    (c₀ * Real.log ρ) :=
  ⟨continuous_eta2log hρ, hasCompactSupport_eta2log, integral_abs_eta2log_le hρ,
    by have := eta2'L1_pos; have := Real.log_nonneg (show (1 : ℝ) ≤ ρ by linarith); positivity,
    eVariationOn_eta2log_le hρ, eta2log_fourier_bound hρ⟩

theorem eta2log_eq_add (u : ℝ) : eta2log ρ u = Real.log u * eta2 u + Real.log ρ * eta2 u := by
  unfold eta2log
  by_cases hu : u ∈ Set.Ioo (1 / 4 : ℝ) 1
  · rw [Real.log_mul (by linarith) (by linarith [hu.1])]; ring
  · rw [Helfgott.eta2_eq_zero hu]; ring

/-- `η̂_(ρ) = (log·η₂)^ + log ρ · η̂₂`. -/
theorem ghat_eta2log (t : ℝ) :
    ghat (eta2log ρ) t = ghat (fun u => Real.log u * eta2 u) t + Real.log ρ * eta2hat t := by
  have hint1 : Integrable (fun v => e (-(v * t)) * (eta2log ρ v : ℂ)) :=
    ((continuous_e.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp (continuous_eta2log hρ))
      ).integrable_of_hasCompactSupport (hasCompactSupport_eta2log.comp_left
        (g := fun s : ℝ => (s : ℂ)) (by simp)).mul_left
  have hint2 : Integrable (fun v => e (-(v * t)) * (eta2 v : ℂ)) :=
    ((continuous_e.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp Helfgott.continuous_eta2)
      ).integrable_of_hasCompactSupport (Helfgott.hasCompactSupport_eta2.comp_left
        (g := fun s : ℝ => (s : ℂ)) (by simp)).mul_left
  have hfun : (fun v => e (-(v * t)) * ((Real.log v * eta2 v : ℝ) : ℂ)) =
      fun v => e (-(v * t)) * (eta2log ρ v : ℂ) - (Real.log ρ : ℂ) * (e (-(v * t)) * (eta2 v : ℂ)) := by
    funext v; rw [eta2log_eq_add hρ]; push_cast; ring
  rw [ghat, ghat, eta2hat, fourier_eq_integral_e, fourier_eq_integral_e, fourier_eq_integral_e, hfun,
    integral_sub hint1 (hint2.const_mul _), integral_const_mul]
  ring

end TernaryGoldbach.MinorArcs
