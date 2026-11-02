import Mathlib

/-!
# Periodization of integrals over short sets

For `g` continuous and `1`-periodic and `J ⊆ (−1, 2]` measurable,
`∫_J g = Σ_{k ∈ {−1, 0, 1}} ∫_{(0,1]} 1_J(α − k) g(α) dα` (`setIntegral_eq_sum_periodize`).

This turns integrals over arcs around `b/q` (lifted to `ℝ`) into integrals over `(0, 1]` of
`g` times a counting function, which is how [H, Prop. 12.1.1] compares arcs with `ℝ/ℤ`.

Proved, with no `sorry`.
-/

open MeasureTheory Set

namespace TernaryGoldbach

/-- The three translates `(−k, 1 − k]`, `k ∈ {−1, 0, 1}`, tile `(−1, 2]`. -/
theorem sum_indicator_Ioc_translates {β : ℝ} (hβ : β ∈ Ioc (-1 : ℝ) 2) :
    ∑ k ∈ ({-1, 0, 1} : Finset ℤ), (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (β + k) = 1 := by
  obtain ⟨h1, h2⟩ := hβ
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [indicator, mem_Ioc, Pi.one_apply, Int.cast_neg, Int.cast_one, Int.cast_zero]
  rcases le_or_gt β 0 with hb0 | hb0
  · rw [if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [h.1]),
      if_pos ⟨by linarith, by linarith⟩]; norm_num
  rcases le_or_gt β 1 with hb1 | hb1
  · rw [if_neg (by intro h; linarith [h.1]), if_pos ⟨by linarith, by linarith⟩,
      if_neg (by intro h; linarith [h.2])]; norm_num
  · rw [if_pos ⟨by linarith, by linarith⟩, if_neg (by intro h; linarith [h.2]),
      if_neg (by intro h; linarith [h.2])]; norm_num

/-- **Periodization**: `∫_J g = Σ_{k ∈ {−1,0,1}} ∫_{(0,1]} 1_J(α − k) g(α) dα` for `J ⊆ (−1, 2]`. -/
theorem setIntegral_eq_sum_periodize {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJsub : J ⊆ Ioc (-1) 2) :
    ∫ x in J, g x = ∑ k ∈ ({-1, 0, 1} : Finset ℤ),
      ∫ α in Ioc (0 : ℝ) 1, J.indicator 1 (α - k) * g α := by
  have hgk : ∀ (k : ℤ) (β : ℝ), g (β + k) = g β := fun k β => by
    simpa using hper.int_mul k β
  -- each term, after the substitution `α = β + k`
  have hterm : ∀ k : ℤ, ∫ α in Ioc (0 : ℝ) 1, J.indicator 1 (α - k) * g α =
      ∫ β, (Ioc (0 : ℝ) 1).indicator 1 (β + k) * (J.indicator g β) := by
    intro k
    rw [← integral_indicator measurableSet_Ioc]
    rw [← integral_add_right_eq_self _ (k : ℝ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only [indicator, Pi.one_apply, add_sub_cancel_right]
    split_ifs <;> simp_all
  simp_rw [hterm]
  have hint : ∀ k : ℤ, Integrable fun β => (Ioc (0 : ℝ) 1).indicator 1 (β + k) * J.indicator g β := by
    intro k
    have hgJ : IntegrableOn g (Icc (-1) 2) := hg.integrableOn_Icc
    have : Integrable (J.indicator g) := by
      rw [integrable_indicator_iff hJ]
      exact hgJ.mono_set (hJsub.trans Ioc_subset_Icc_self)
    refine this.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun β => ?_)
    · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_add_const _)
        |>.aestronglyMeasurable
    · simp only [indicator]; split_ifs <;> simp
  rw [← integral_finset_sum _ fun k _ => hint k, ← integral_indicator hJ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only
  rw [← Finset.sum_mul]
  by_cases hβ : β ∈ J
  · rw [sum_indicator_Ioc_translates (hJsub hβ), one_mul]
  · simp [hβ]

end TernaryGoldbach
