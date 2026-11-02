import TernaryGoldbach.MinorArcs.S1Lemma

/-!
# The functions `g₂`, `T₂` and `H₂` of [H, §5.1]

* `integral_g2`: [H, (5.19)], `∫_{1/2}^1 g₂(uy) du = ∑ μ(r₁)μ(r₂)/(σ(r₁)σ(r₂)) (1 - max(1/2, r_i/y))`;
* `T2`, `H2`: [H, (5.28)] and [H, (5.35)].

The bounds `H₂ ≤ 2/π²` and the corrected [H, (5.36)] are proved in `H2Bound.lean`.
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs
open TernaryGoldbach.Prelim

/-! ### The main term (5.19) -/

theorem integral_ite_le {M : ℝ} (hM : M ≤ 1) :
    ∫ u in (1 / 2 : ℝ)..1, (if M ≤ u then (1 : ℝ) else 0) = 1 - max (1 / 2) M := by
  have : (fun u : ℝ => if M ≤ u then (1 : ℝ) else 0) = (Set.Ici M).indicator 1 := by
    ext u; simp [Set.indicator, Set.mem_Ici]
  rw [this, intervalIntegral.integral_of_le (by norm_num), integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one]
  rcases le_or_gt M (1 / 2) with h | h
  · rw [max_eq_left h, measureReal_def, Measure.restrict_apply_univ,
      show Set.Ici M ∩ Set.Ioc (1 / 2 : ℝ) 1 = Set.Ioc (1 / 2 : ℝ) 1 from
        Set.inter_eq_right.2 (fun u (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) => le_trans h hu.1.le),
      Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
  · rw [max_eq_right h.le, show Set.Ici M ∩ Set.Ioc (1 / 2 : ℝ) 1 = Set.Icc M 1 by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩,
      measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]

/-- `g₂(t)` [H, Lemma 5.1.2]. -/
noncomputable def g2 (t : ℝ) : ℝ :=
  ∑ r₁ ∈ Icc 1 ⌊t⌋₊, ∑ r₂ ∈ Icc 1 ⌊t⌋₊,
    if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0

theorem monotone_ite_le (M : ℝ) : Monotone fun u : ℝ => if M ≤ u then (1 : ℝ) else 0 := by
  intro u v huv
  simp only
  split_ifs with h1 h2 <;> first | exact absurd (h1.trans huv) h2 | rfl | norm_num

/-- [H, (5.19)]: `∫_{1/2}^1 g₂(uy) du = ∑_{r₁,r₂ ≤ y} … (1 - max(1/2, r₁/y, r₂/y))`. -/
theorem integral_g2 {y : ℝ} (hy : 0 < y) :
    ∫ u in (1 / 2 : ℝ)..1, g2 (u * y) =
      ∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
        (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
          (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) * wM y r₁ r₂ := by
  set c : ℕ → ℕ → ℝ := fun r₁ r₂ => if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
    (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0
  have hpt : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, g2 (u * y) = ∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
      c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hfilt : Icc 1 ⌊u * y⌋₊ = (Icc 1 ⌊y⌋₊).filter (fun r : ℕ => (r : ℝ) ≤ u * y) := by
      ext r
      simp only [mem_Icc, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : (r : ℝ) ≤ u * y := (Nat.cast_le.2 h2).trans (Nat.floor_le (by nlinarith [hu.1]))
        exact ⟨⟨h1, Nat.le_floor (h3.trans (by nlinarith [hu.2]))⟩, h3⟩
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
    have hmax : ∀ r₁ r₂ : ℕ, max ((r₁ : ℝ) / y) (r₂ / y) ≤ u ↔
        (r₁ : ℝ) ≤ u * y ∧ (r₂ : ℝ) ≤ u * y := by
      intro r₁ r₂; rw [max_le_iff, div_le_iff₀ hy, div_le_iff₀ hy]
    rw [g2, hfilt, sum_filter]
    refine sum_congr rfl fun r₁ _ => ?_
    rw [sum_filter]
    simp only [hmax]
    by_cases h1 : (r₁ : ℝ) ≤ u * y
    · rw [if_pos h1]
      refine sum_congr rfl fun r₂ _ => ?_
      by_cases h2 : (r₂ : ℝ) ≤ u * y
      · simp [h1, h2, c]
      · simp [h2]
    · rw [if_neg h1]; symm
      exact sum_eq_zero fun r₂ _ => by simp [h1]
  have hint : ∀ r₁ r₂, IntervalIntegrable
      (fun u : ℝ => c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0))
      volume (1 / 2) 1 := fun r₁ r₂ =>
    ((monotone_ite_le _).intervalIntegrable).const_mul _
  have hint2 : ∀ r₁, IntervalIntegrable (fun u : ℝ => ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
      c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0)) volume (1 / 2) 1 := by
    intro r₁
    have := IntervalIntegrable.sum (Icc 1 ⌊y⌋₊) (fun r₂ _ => hint r₁ r₂)
    convert this using 1; ext u; simp [Finset.sum_apply]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finset_sum
    (fun r₁ _ => hint2 r₁)]
  refine sum_congr rfl fun r₁ hr₁ => ?_
  rw [intervalIntegral.integral_finset_sum (fun r₂ _ => hint r₁ r₂)]
  refine sum_congr rfl fun r₂ hr₂ => ?_
  rw [intervalIntegral.integral_const_mul, integral_ite_le, wM]
  have h1 : (r₁ : ℝ) ≤ y := (Nat.cast_le.2 (mem_Icc.1 hr₁).2).trans (Nat.floor_le hy.le)
  have h2 : (r₂ : ℝ) ≤ y := (Nat.cast_le.2 (mem_Icc.1 hr₂).2).trans (Nat.floor_le hy.le)
  exact max_le ((div_le_one hy).2 h1) ((div_le_one hy).2 h2)

/-! ### The triple sum and `H₂` -/

/-- The triple sum `T₂(S) = ∑_{s ≤ S odd} (1/s) ∫_{1/2}^1 g₂(uS/s) du` [H, (5.28)]. -/
noncomputable def T2 (S : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 ⌊S⌋₊, if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * S / s) else 0

/-- `H₂(S)` [H, (5.35)]: `(4/π²) max(T₂(S), 0)` for `S < 16`, `0.15107` for `S ≥ 16`. (The book uses
its computable upper bound `G₂(S)` in place of `T₂(S)`; `G₂ ≥ T₂` and `G₂ ≥ 0`, so `G₂ ≥ max(T₂, 0)`,
and the book's (5.37) about `H₂` remains valid for ours. Its (5.36) is false and is used here
in corrected form; see `integral_H2_le`.) -/
noncomputable def H2 (S : ℝ) : ℝ := if S < 16 then 4 / π ^ 2 * max (T2 S) 0 else 0.15107

theorem H2_nonneg (S : ℝ) : 0 ≤ H2 S := by
  unfold H2; split_ifs
  · have := le_max_right (T2 S) 0; positivity
  · norm_num

theorem measurable_g2 : Measurable g2 := by
  have : g2 = (fun N : ℕ => ∑ r₁ ∈ Finset.Icc 1 N, ∑ r₂ ∈ Finset.Icc 1 N,
      if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
        (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

theorem measurable_T2 : Measurable T2 := by
  set F : ℕ × ℝ → ℝ := fun p => ∑ s ∈ Finset.Icc 1 p.1,
    if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * p.2 / s) else 0
  have hF : Measurable F := by
    refine measurable_from_prod_countable_right fun n => ?_
    simp only [F]
    apply Finset.measurable_sum
    intro s _
    by_cases hs : Odd s
    · simp only [hs, if_true]
      refine Measurable.const_mul ?_ _
      simp_rw [intervalIntegral.integral_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
      have hf : MeasureTheory.StronglyMeasurable (fun p : ℝ × ℝ => g2 (p.2 * p.1 / s)) :=
        (measurable_g2.comp (by fun_prop)).stronglyMeasurable
      exact (hf.integral_prod_right' (ν := MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))).measurable
    · simp only [hs, if_false]; exact measurable_const
  have : T2 = F ∘ fun S => (⌊S⌋₊, S) := rfl
  rw [this]
  exact hF.comp (Nat.measurable_floor.prodMk measurable_id)

theorem measurable_H2 : Measurable H2 := by
  unfold H2
  exact Measurable.ite measurableSet_Iio
    ((measurable_T2.max measurable_const).const_mul _) measurable_const

theorem H2_eq_zero_of_lt_one {S : ℝ} (hS : S < 1) : H2 S = 0 := by
  have hT : T2 S = 0 := by
    unfold T2
    rw [Nat.floor_eq_zero.2 hS]; simp
  unfold H2; rw [if_pos (by linarith), hT]; simp

end TernaryGoldbach.MinorArcs
