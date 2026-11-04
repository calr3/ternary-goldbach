import TernaryGoldbach.MinorArcs.T2Defs
import TernaryGoldbach.MinorArcs.G2Moebius

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# `T₂(S) ≈ ¼ ∫₁^S g₂(y) dy/y`

With `∫_{1/2}^1 g₂(uz) du = z⁻¹ ∫_{z/2}^z g₂`,
`T₂(S) = S⁻¹ ∑_{s ≤ S odd} ∫_{S/2s}^{S/s} g₂ = S⁻¹ ∫₀^S g₂(y) N(y) dy`, where `N(y)` counts the odd
`s ∈ (S/2y, S/y]`, so `|N(y) − S/(4y)| ≤ 1`. Hence (`abs_T2_sub_le`)

`|T₂(S) − ¼ ∫₁^S g₂(y)/y dy| ≤ S⁻¹ ∫₁^S |g₂|`.

This replaces the Euler–Maclaurin argument of [H, (5.29)–(5.30)].
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs

/-! ### Basic facts about `g₂` -/

theorem g2_eq_zero_of_lt_one {y : ℝ} (hy : y < 1) : g2 y = 0 := by
  unfold g2; rw [Nat.floor_eq_zero.2 hy]; simp

theorem abs_g2_le (y : ℝ) : |g2 y| ≤ (⌊y⌋₊ : ℝ) ^ 2 := by
  unfold g2
  have h1 : ∀ r₁ ∈ Icc 1 ⌊y⌋₊, ∀ r₂ ∈ Icc 1 ⌊y⌋₊,
      |(if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0)|
        ≤ 1 := by
    intro r₁ hr₁ r₂ hr₂
    split_ifs
    · have hs₁ : (1 : ℝ) ≤ σ 1 r₁ := by
        have := ArithmeticFunction.sigma_pos 1 r₁ (by have := (mem_Icc.1 hr₁).1; omega)
        exact_mod_cast this
      have hs₂ : (1 : ℝ) ≤ σ 1 r₂ := by
        have := ArithmeticFunction.sigma_pos 1 r₂ (by have := (mem_Icc.1 hr₂).1; omega)
        exact_mod_cast this
      have hm₁ : |(μ r₁ : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hm₂ : |(μ r₂ : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (σ 1 r₁ : ℝ) * σ 1 r₂),
        div_le_one (by positivity)]
      nlinarith [abs_nonneg (μ r₁ : ℝ), abs_nonneg (μ r₂ : ℝ)]
    · simp
  calc |∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊, _|
      ≤ ∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r₁ hr₁ => ?_)
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r₂ hr₂ => h1 r₁ hr₁ r₂ hr₂)
    _ = (⌊y⌋₊ : ℝ) ^ 2 := by simp; ring

theorem integrableOn_g2_Ioc (a b : ℝ) (hb : 0 ≤ b) : IntegrableOn g2 (Set.Ioc a b) := by
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top measurable_g2.aestronglyMeasurable
    ((⌊b⌋₊ : ℝ) ^ 2) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_g2_le y).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2)
  exact_mod_cast Nat.floor_le_floor hy.2

/-- `∫_{1/2}^1 g₂(uz) du = z⁻¹ ∫_{z/2}^z g₂`. -/
theorem integral_g2_mul {z : ℝ} (hz : 0 < z) :
    ∫ u in (1 / 2 : ℝ)..1, g2 (u * z) = z⁻¹ * ∫ y in z / 2..z, g2 y := by
  rw [intervalIntegral.integral_comp_mul_right g2 hz.ne', smul_eq_mul]
  congr 2 <;> ring

/-! ### Counting odd numbers -/

theorem card_odd_range (n : ℕ) : ((range (n + 1)).filter Odd).card = (n + 1) / 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]; obtain ⟨k, hk⟩ := h; omega
    · rw [ih]; rw [Nat.not_odd_iff_even] at h; obtain ⟨k, hk⟩ := h; omega

theorem card_odd_Ioc {m n : ℕ} (h : m ≤ n) :
    ((Ioc m n).filter Odd).card = (n + 1) / 2 - (m + 1) / 2 := by
  have e : (Ioc m n).filter Odd = ((range (n + 1)).filter Odd) \ ((range (m + 1)).filter Odd) := by
    ext s; simp only [mem_filter, mem_Ioc, mem_sdiff, mem_range]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h3⟩, fun h => by omega⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      refine ⟨⟨?_, by omega⟩, h3⟩
      by_contra hc
      exact h2 ⟨by omega, h3⟩
  have hsub : range (m + 1) ⊆ range (n + 1) := fun x hx => by
    simp only [mem_range] at hx ⊢; omega
  rw [e, card_sdiff_of_subset (filter_subset_filter _ hsub),
    card_odd_range, card_odd_range]

/-- `|#{odd s ∈ (α, 2α]} − α/2| ≤ 1`. -/
theorem abs_card_odd_sub_le {α : ℝ} (hα : 0 ≤ α) :
    |(((Ioc ⌊α⌋₊ ⌊2 * α⌋₊).filter Odd).card : ℝ) - α / 2| ≤ 1 := by
  have hle : ⌊α⌋₊ ≤ ⌊2 * α⌋₊ := Nat.floor_le_floor (by linarith)
  rw [card_odd_Ioc hle]
  set m := ⌊α⌋₊; set n := ⌊2 * α⌋₊
  have hm1 : (m : ℝ) ≤ α := Nat.floor_le hα
  have hm2 : α < m + 1 := Nat.lt_floor_add_one α
  have hn1 : (n : ℝ) ≤ 2 * α := Nat.floor_le (by linarith)
  have hn2 : 2 * α < n + 1 := Nat.lt_floor_add_one _
  have a1 : (n + 1) / 2 * 2 ≤ n + 1 := Nat.div_mul_le_self _ _
  have a2 : n ≤ (n + 1) / 2 * 2 := by omega
  have a3 : (m + 1) / 2 * 2 ≤ m + 1 := Nat.div_mul_le_self _ _
  have a4 : m ≤ (m + 1) / 2 * 2 := by omega
  have c1 : (((n + 1) / 2 : ℕ) : ℝ) * 2 ≤ n + 1 := by exact_mod_cast a1
  have c2 : (n : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) * 2 := by exact_mod_cast a2
  have c3 : (((m + 1) / 2 : ℕ) : ℝ) * 2 ≤ m + 1 := by exact_mod_cast a3
  have c4 : (m : ℝ) ≤ (((m + 1) / 2 : ℕ) : ℝ) * 2 := by exact_mod_cast a4
  have hsub : (m + 1) / 2 ≤ (n + 1) / 2 := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hsub, abs_le]
  constructor <;> linarith

/-! ### `T₂ = S⁻¹ ∫ g₂ N` -/

/-- `N_S(y)`: the number of odd `s ≤ S` with `S/(2s) < y ≤ S/s`. -/
noncomputable def Nodd (S y : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 ⌊S⌋₊, if Odd s then (Set.Ioc (S / (2 * s)) (S / s)).indicator (fun _ => (1 : ℝ)) y else 0

theorem T2_eq_integral {S : ℝ} (hS : 1 ≤ S) :
    T2 S = S⁻¹ * ∫ y in Set.Ioc (0 : ℝ) S, g2 y * Nodd S y := by
  have hS0 : 0 < S := by linarith
  have hint : ∀ s ∈ Icc 1 ⌊S⌋₊, IntegrableOn (fun y => if Odd s then
      (Set.Ioc (S / (2 * s)) (S / s)).indicator g2 y else 0) (Set.Ioc 0 S) := by
    intro s _
    split_ifs
    · exact ((integrableOn_g2_Ioc 0 S hS0.le).indicator measurableSet_Ioc)
    · exact integrableOn_zero
  have hterm : ∀ s ∈ Icc 1 ⌊S⌋₊, (if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * S / s)
      else 0) = S⁻¹ * ∫ y in Set.Ioc (0 : ℝ) S,
        (if Odd s then (Set.Ioc (S / (2 * s)) (S / s)).indicator g2 y else 0) := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (mem_Icc.1 hs).1
    have hsS : (s : ℝ) ≤ S := ((Nat.cast_le.2 (mem_Icc.1 hs).2).trans (Nat.floor_le hS0.le))
    split_ifs with ho
    · have hz : 0 < S / s := by positivity
      simp_rw [mul_div_assoc]
      rw [integral_g2_mul hz, intervalIntegral.integral_of_le (by linarith [div_pos hz two_pos]),
        setIntegral_indicator measurableSet_Ioc]
      have hsub : Set.Ioc (0 : ℝ) S ∩ Set.Ioc (S / (2 * s)) (S / s) = Set.Ioc (S / s / 2) (S / s) := by
        rw [Set.inter_eq_right.2]
        · congr 1; ring
        · intro y hy
          refine ⟨lt_of_le_of_lt (by positivity) hy.1, hy.2.trans ?_⟩
          rw [div_le_iff₀ (by linarith)]; nlinarith
      rw [hsub]; field_simp
    · simp
  unfold T2
  rw [sum_congr rfl hterm, ← mul_sum, ← integral_finset_sum _ hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  simp only [Nodd, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  split_ifs
  · by_cases hy : y ∈ Set.Ioc (S / (2 * s)) (S / s)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  · rw [mul_zero]

/-- For `1 ≤ y ≤ S`, `N_S(y)` counts the odd numbers in `(α, 2α]`, `α = S/2y`. -/
theorem Nodd_eq {S y : ℝ} (hy : 1 ≤ y) (hyS : y ≤ S) :
    Nodd S y = (((Ioc ⌊S / (2 * y)⌋₊ ⌊2 * (S / (2 * y))⌋₊).filter Odd).card : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hS0 : 0 < S := by linarith
  set α := S / (2 * y) with hα
  have hα0 : 0 ≤ α := by positivity
  have h2α : 2 * α = S / y := by rw [hα]; field_simp
  have e1 : ∀ s : ℕ, (if Odd s then (Set.Ioc (S / (2 * s)) (S / s)).indicator (fun _ => (1:ℝ)) y
      else 0) = if (Odd s ∧ S / (2 * s) < y ∧ y ≤ S / s) then 1 else 0 := by
    intro s
    by_cases ho : Odd s
    · simp only [ho, if_true, true_and, Set.indicator_apply, Set.mem_Ioc]
    · simp only [ho, if_false, false_and]
  unfold Nodd
  simp_rw [e1]
  rw [sum_boole]
  congr 1
  congr 1
  ext s
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, ho, h3, h4⟩
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    refine ⟨⟨(Nat.floor_lt hα0).2 ?_, (Nat.le_floor_iff (by positivity)).2 ?_⟩, ho⟩
    · rw [hα, div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ (by positivity)] at h3; linarith
    · rw [h2α, le_div_iff₀ hy0]; rw [le_div_iff₀ hs0] at h4; linarith
  · rintro ⟨⟨h1, h2⟩, ho⟩
    have h1' : α < s := (Nat.floor_lt hα0).1 h1
    have h2' : (s : ℝ) ≤ S / y := h2α ▸ (Nat.le_floor_iff (by positivity)).1 h2
    have hs0 : (0 : ℝ) < s := lt_of_le_of_lt hα0 h1'
    have hs1 : 1 ≤ s := by exact_mod_cast (show (1 : ℝ) ≤ s by
      have : (0 : ℕ) < s := by exact_mod_cast hs0
      exact_mod_cast this)
    refine ⟨⟨hs1, ?_⟩, ho, ?_, ?_⟩
    · refine Nat.le_floor (h2'.trans ?_)
      rw [div_le_iff₀ hy0]; nlinarith
    · rw [div_lt_iff₀ (by positivity)]; rw [hα, div_lt_iff₀ (by positivity)] at h1'; linarith
    · rw [le_div_iff₀ hs0]; rw [le_div_iff₀ hy0] at h2'; linarith

theorem abs_Nodd_sub_le {S y : ℝ} (hy : 1 ≤ y) (hyS : y ≤ S) : |Nodd S y - S / (4 * y)| ≤ 1 := by
  rw [Nodd_eq hy hyS]
  have hy0 : 0 < y := by linarith
  have hS0 : 0 < S := by linarith
  have h := abs_card_odd_sub_le (α := S / (2 * y)) (by positivity)
  have e : S / (2 * y) / 2 = S / (4 * y) := by ring
  rwa [e] at h

theorem measurable_Nodd (S : ℝ) : Measurable (Nodd S) := by
  unfold Nodd
  refine Finset.measurable_sum _ fun s _ => ?_
  split_ifs
  · exact measurable_const.indicator measurableSet_Ioc
  · exact measurable_const

theorem abs_Nodd_le (S y : ℝ) : |Nodd S y| ≤ ⌊S⌋₊ := by
  unfold Nodd
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ s ∈ Icc 1 ⌊S⌋₊, |(if Odd s then (Set.Ioc (S / (2 * s)) (S / s)).indicator
        (fun _ => (1 : ℝ)) y else 0)| ≤ ∑ s ∈ Icc 1 ⌊S⌋₊, (1 : ℝ) := by
        refine sum_le_sum fun s _ => ?_
        split_ifs
        · rw [Set.indicator_apply]; split_ifs <;> simp
        · simp
    _ = ⌊S⌋₊ := by simp

/-- **`|T₂(S) − ¼ ∫₁^S g₂(y)/y dy| ≤ S⁻¹ ∫₁^S |g₂|`** for `S ≥ 1`. -/
theorem abs_T2_sub_le {S : ℝ} (hS : 1 ≤ S) :
    |T2 S - 1 / 4 * (∫ y in (1 : ℝ)..S, g2 y / y)| ≤ S⁻¹ * ∫ y in (1 : ℝ)..S, |g2 y| := by
  have hS0 : 0 < S := by linarith
  have iG : IntegrableOn g2 (Set.Ioc 0 S) := integrableOn_g2_Ioc 0 S hS0.le
  have iG1 : IntegrableOn g2 (Set.Ioc 1 S) := integrableOn_g2_Ioc 1 S hS0.le
  have iGN : IntegrableOn (fun y => g2 y * Nodd S y) (Set.Ioc 0 S) :=
    Integrable.mul_bdd iG (measurable_Nodd S).aestronglyMeasurable
      (c := ⌊S⌋₊) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_Nodd_le S y)
  -- `∫_{(0,1]} g₂ N = 0`
  have h01 : ∫ y in Set.Ioc (0 : ℝ) 1, g2 y * Nodd S y = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    rw [g2_eq_zero_of_lt_one hy.2, zero_mul]
  have hsplit : ∫ y in Set.Ioc (0 : ℝ) S, g2 y * Nodd S y =
      ∫ y in Set.Ioc (1 : ℝ) S, g2 y * Nodd S y := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hS,
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (iGN.mono_set (Set.Ioc_subset_Ioc le_rfl hS)) (iGN.mono_set (Set.Ioc_subset_Ioc
          (by norm_num) le_rfl)), h01, zero_add]
  have iW : IntegrableOn (fun y => g2 y * (S / (4 * y))) (Set.Ioc 1 S) :=
    Integrable.mul_bdd iG1 (by fun_prop : Measurable fun y : ℝ => S / (4 * y)).aestronglyMeasurable
      (c := S) ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => by
        have hy1 : 1 < y := hy.1
        rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
        nlinarith))
  have iGN1 : IntegrableOn (fun y => g2 y * Nodd S y) (Set.Ioc 1 S) :=
    iGN.mono_set (Set.Ioc_subset_Ioc (by norm_num) le_rfl)
  rw [T2_eq_integral hS, hsplit, intervalIntegral.integral_of_le hS,
    intervalIntegral.integral_of_le hS]
  have hW : 1 / 4 * ∫ y in Set.Ioc (1 : ℝ) S, g2 y / y =
      S⁻¹ * ∫ y in Set.Ioc (1 : ℝ) S, g2 y * (S / (4 * y)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans one_pos hy.1
    field_simp
  rw [hW, ← mul_sub, ← integral_sub iGN1 iW, abs_mul, abs_of_pos (inv_pos.2 hS0)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hS0).le
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on (iGN1.sub iW).abs
    iG1.abs measurableSet_Ioc fun y hy => ?_)
  have hN := abs_Nodd_sub_le (S := S) hy.1.le hy.2
  rw [← mul_sub, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hN

end TernaryGoldbach.MinorArcs
