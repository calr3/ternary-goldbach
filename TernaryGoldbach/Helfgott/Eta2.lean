import TernaryGoldbach.Helfgott.Decay

/-!
# Explicit formulas for `η₂`

`η₂(t) = 4 log(4t)` on `[1/4, 1/2]`, `η₂(t) = -4 log t` on `[1/2, 1]`, and `|η₂|₁ = 1`
[H, (6.1)].  `η₂` is continuous and compactly supported, and its total variation is
`|η₂'|₁ = 8 log 2` (`eVariationOn_eta2`).

Proved, with no `sorry`.
-/

open Real MeasureTheory

namespace TernaryGoldbach.Helfgott

theorem eta2_eq_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) : eta2 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  have hl : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : Real.log (4 * t) = Real.log 2 + Real.log (2 * t) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]; ring_nf
  have h40 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  unfold eta2
  rw [ite_eq_left ht, abs_of_nonpos hl, max_eq_left (by linarith)]
  rw [h4]; ring

theorem eta2_eq_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : eta2 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hl : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) (by linarith)
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le h2
  unfold eta2
  rw [ite_eq_left ht, abs_of_nonneg hl, max_eq_left (by linarith)]
  rw [h2t]; ring

theorem continuousOn_eta2 : ContinuousOn eta2 (Set.Icc (1 / 4) 1) := by
  have hc : ContinuousOn (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0)
      (Set.Icc (1 / 4) 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.sup ?_ continuousOn_const)
    refine continuousOn_const.sub (ContinuousOn.abs ?_)
    exact (continuousOn_const.mul continuousOn_id).log fun t ht => by
      simp only [Set.mem_Icc] at ht; simp only [Pi.mul_apply, id]; nlinarith [ht.1]
  refine hc.congr fun t ht => ?_
  simp only [Set.mem_Icc] at ht
  simp only [eta2, ite_eq_left (show (0:ℝ) < t by linarith)]

/-- `|η₂|₁ = 1`. -/
theorem integral_abs_eta2 : ∫ t, |eta2 t| = 1 := by
  have habs : (fun t => |eta2 t|) = (Set.Icc (1 / 4 : ℝ) 1).indicator eta2 := by
    funext t
    by_cases ht : t ∈ Set.Icc (1 / 4 : ℝ) 1
    · rw [Set.indicator_of_mem ht, abs_of_nonneg (eta2_nonneg t)]
    · rw [Set.indicator_of_notMem ht, eta2_eq_zero (fun h => ht (Set.Ioo_subset_Icc_self h)),
        abs_zero]
  rw [habs, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hii : ∀ a b, 1 / 4 ≤ a → b ≤ 1 → a ≤ b → IntervalIntegrable eta2 volume a b := by
    intro a b ha hb hab
    refine (continuousOn_eta2.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hii _ _ le_rfl (by norm_num) (by norm_num)) (hii _ _ (by norm_num) le_rfl (by norm_num))]
  have hL : ∫ t in (1 / 4 : ℝ)..1 / 2, eta2 t = 2 * Real.log 2 - 1 := by
    rw [intervalIntegral.integral_congr (g := fun t => 4 * Real.log (4 * t)) fun t ht => by
      rw [Set.uIcc_of_le (by norm_num)] at ht; exact eta2_eq_left ht.1 ht.2]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t => Real.log t) (by norm_num : (4:ℝ) ≠ 0),
      integral_log]
    norm_num
    ring
  have hR : ∫ t in (1 / 2 : ℝ)..1, eta2 t = 2 - 2 * Real.log 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => -4 * Real.log t) fun t ht => by
      rw [Set.uIcc_of_le (by norm_num)] at ht; exact eta2_eq_right ht.1 ht.2]
    rw [intervalIntegral.integral_const_mul,
      integral_log]
    simp only [Real.log_one, one_div, Real.log_inv]
    ring
  rw [hL, hR]; ring

/-- `η₂(t) = 4 max(log 2 - |log(2 max(t, 1/8))|, 0)` for all `t`. -/
theorem eta2_eq_clamp (t : ℝ) :
    eta2 t = 4 * max (Real.log 2 - |Real.log (2 * max t (1 / 8))|) 0 := by
  rcases le_or_gt t (1 / 8) with ht | ht
  · rw [max_eq_right ht]
    have h1 : Real.log (2 * (1 / 8 : ℝ)) = -(2 * Real.log 2) := by
      rw [show (2 * (1 / 8 : ℝ)) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [h1, abs_neg, abs_of_pos (by linarith), max_eq_right (by linarith)]
    rw [eta2_eq_zero (fun h => by linarith [h.1])]; simp
  · rw [max_eq_left ht.le, eta2, ite_eq_left (by linarith)]

theorem continuous_eta2 : Continuous eta2 := by
  have : eta2 = fun t => 4 * max (Real.log 2 - |Real.log (2 * max t (1 / 8))|) 0 :=
    funext eta2_eq_clamp
  rw [this]
  refine continuous_const.mul (Continuous.max ?_ continuous_const)
  refine continuous_const.sub (Continuous.abs ?_)
  exact (continuous_const.mul (continuous_id.max continuous_const)).log fun t =>
    (mul_pos two_pos (lt_of_lt_of_le (by norm_num) (le_max_right t _))).ne'

theorem hasCompactSupport_eta2 : HasCompactSupport eta2 := by
  refine HasCompactSupport.intro (isCompact_Icc (a := 1 / 4) (b := 1)) fun t ht => ?_
  exact eta2_eq_zero fun h => ht (Set.Ioo_subset_Icc_self h)

theorem monotoneOn_eta2 : MonotoneOn eta2 (Set.Icc (1 / 4) (1 / 2)) := by
  intro s hs t ht hst
  rw [eta2_eq_left hs.1 hs.2, eta2_eq_left ht.1 ht.2]
  gcongr
  · linarith [hs.1]

theorem antitoneOn_eta2 : AntitoneOn eta2 (Set.Icc (1 / 2) 1) := by
  intro s hs t ht hst
  rw [eta2_eq_right hs.1 hs.2, eta2_eq_right ht.1 ht.2]
  have := Real.log_le_log (by linarith [hs.1]) hst
  linarith

/-- The total variation of `η₂` is `|η₂'|₁ = 8 log 2` [H, (6.1)]. -/
theorem eVariationOn_eta2 : eVariationOn eta2 Set.univ = ENNReal.ofReal (8 * Real.log 2) := by
  -- Reduce to `[1/4, 1]` by clamping.
  set φ : ℝ → ℝ := fun t => max (1 / 4) (min t 1)
  have hφ : MonotoneOn φ Set.univ := fun s _ t _ hst => max_le_max le_rfl (min_le_min hst le_rfl)
  have hcomp : eta2 ∘ φ = eta2 := by
    funext t
    simp only [Function.comp, φ]
    rcases le_or_gt t (1 / 4) with h | h
    · rw [min_eq_left (by linarith), max_eq_left h, eta2_eq_zero (fun h' => by linarith [h'.1]),
        eta2_eq_zero (fun h' => by linarith [h'.1])]
    rcases le_or_gt t 1 with h' | h'
    · rw [min_eq_left h', max_eq_right h.le]
    · rw [min_eq_right h'.le, max_eq_right (by norm_num), eta2_eq_zero (fun h'' => by linarith [h''.2]),
        eta2_eq_zero (fun h'' => by linarith [h''.2])]
  have himg : φ '' Set.univ = Set.Icc (1 / 4) 1 := by
    ext y; simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Icc, φ]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨y, by rw [min_eq_left h2, max_eq_right h1]⟩
  have h1 := eVariationOn.comp_eq_of_monotoneOn eta2 φ hφ
  rw [hcomp, himg] at h1
  rw [h1]
  have hsplit := eVariationOn.Icc_add_Icc eta2 (s := Set.univ) (a := 1 / 4) (b := 1 / 2) (c := 1)
    (by norm_num) (by norm_num) (Set.mem_univ _)
  simp only [Set.univ_inter] at hsplit
  rw [← hsplit]
  have hL := monotoneOn_eta2.eVariationOn_eq (a := 1 / 4) (b := 1 / 2)
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [Set.inter_self] at hL
  -- The decreasing half, via `t ↦ 3/2 - t`.
  set ψ : ℝ → ℝ := fun t => 3 / 2 - t
  have hψ : AntitoneOn ψ (Set.Icc (1 / 2) 1) := fun s _ t _ hst => by simp only [ψ]; linarith
  have hR := eVariationOn.comp_eq_of_antitoneOn eta2 ψ hψ
  have himg2 : ψ '' Set.Icc (1 / 2) 1 = Set.Icc (1 / 2) 1 := by
    ext y; simp only [Set.mem_image, Set.mem_Icc, ψ]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; exact ⟨3 / 2 - y, ⟨by linarith, by linarith⟩, by ring⟩
  rw [himg2] at hR
  have hmono : MonotoneOn (eta2 ∘ ψ) (Set.Icc (1 / 2) 1) := by
    intro s hs t ht hst
    simp only [Function.comp, ψ]
    exact antitoneOn_eta2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
      ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
  have hR2 := hmono.eVariationOn_eq (a := 1 / 2) (b := 1) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [Set.inter_self, hR] at hR2
  rw [hL, hR2]
  simp only [Function.comp, ψ]
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have v1 : eta2 (1 / 2) - eta2 (1 / 4) = 4 * Real.log 2 := by
    rw [eta2_eq_left (by norm_num) le_rfl, eta2_eq_left le_rfl (by norm_num)]
    rw [show (4 : ℝ) * (1 / 4) = 1 by norm_num, show (4 : ℝ) * (1 / 2) = 2 by norm_num,
      Real.log_one]; ring
  have v2 : eta2 (3 / 2 - 1) - eta2 (3 / 2 - 1 / 2) = 4 * Real.log 2 := by
    rw [show (3 / 2 - 1 / 2 : ℝ) = 1 by norm_num, show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num,
      eta2_eq_right le_rfl (by norm_num), eta2_eq_right (by norm_num) le_rfl, Real.log_one,
      one_div, Real.log_inv]; ring
  rw [v1, v2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

end TernaryGoldbach.Helfgott
