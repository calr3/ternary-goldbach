import TernaryGoldbach.MinorArcs.TypeILogProof
import TernaryGoldbach.Prelim.LambdaMu

/-!
# Proof of [B, Lemma 4.2.4] (the Type I sum with `Λ(v) μ(u)`; `η = η₂`)
-/

open Real Finset
open ArithmeticFunction (moebius vonMangoldt)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- `c(a) = ∑_{v | a, v ≤ V, a/v ≤ U} Λ(v) μ(a/v)` [B, (4.53)]. -/
noncomputable def coefI2 (U V : ℝ) (a : ℕ) : ℝ :=
  ∑ v ∈ a.divisors, if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then (Λ v : ℝ) * (μ (a / v) : ℝ) else 0

/-- `|c(a)| ≤ log a` [B, p. 73]. -/
theorem abs_coefI2_le (U V : ℝ) (a : ℕ) : |coefI2 U V a| ≤ Real.log a := by
  rw [coefI2, ← ArithmeticFunction.vonMangoldt_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  split_ifs
  · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have : |(μ (a / v) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := v), abs_nonneg ((μ (a / v) : ℝ))]
  · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg

/-- `typeI2` grouped by `a = uv`: `∑_{a ≤ ⌊U⌋⌊V⌋, a odd} c(a) T_{a,∘}(α)`. -/
theorem typeI2_eq {α x : ℝ} (hx : 0 < x) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    typeI2 α x U V = ∑ a ∈ Icc 1 (⌊V⌋₊ * ⌊U⌋₊),
      if Odd a then (coefI2 U V a : ℂ) * Todd α x a else 0 := by
  set NU := ⌊U⌋₊
  set NV := ⌊V⌋₊
  -- Step 1: the inner sums are `T_{vu,∘}`.
  have h1 : typeI2 α x U V = ∑ p ∈ Icc 1 NV ×ˢ Icc 1 NU,
      if Odd p.1 ∧ Odd p.2 then ((Λ p.1 : ℝ) * (μ p.2 : ℝ) : ℂ) * Todd α x (p.1 * p.2) else 0 := by
    rw [typeI2, sum_product]
    refine sum_congr rfl fun v hv => ?_
    by_cases hvo : Odd v
    · rw [if_pos hvo, mul_sum]
      refine sum_congr rfl fun u hu => ?_
      by_cases huo : Odd u
      · rw [if_pos huo, if_pos ⟨hvo, huo⟩]
        have hvu : 1 ≤ v * u := Nat.one_le_iff_ne_zero.2
          (Nat.mul_ne_zero (by have := (mem_Icc.1 hv).1; omega) (by have := (mem_Icc.1 hu).1; omega))
        rw [← inner_eq_Todd hx hvu]
        push_cast
        simp only [mul_assoc]
      · rw [if_neg huo, if_neg (fun h => huo h.2), mul_zero]
    · rw [if_neg hvo]
      exact (sum_eq_zero fun u _ => by rw [if_neg (fun h => hvo h.1)]).symm
  rw [h1]
  -- Step 2: group by `a = vu`.
  rw [← sum_fiberwise_of_maps_to (t := Icc 1 (NV * NU)) (g := fun p : ℕ × ℕ => p.1 * p.2)
    (fun p hp => by
      simp only [mem_product, mem_Icc] at hp ⊢
      exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul hp.1.2 hp.2.2⟩)]
  refine sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
  -- The fibre over `a`, matched with the divisors `v` of `a` with `v ≤ V`, `a/v ≤ U`.
  have hfib : ∑ p ∈ (Icc 1 NV ×ˢ Icc 1 NU).filter (fun p : ℕ × ℕ => p.1 * p.2 = a),
      (if Odd p.1 ∧ Odd p.2 then ((Λ p.1 : ℝ) * (μ p.2 : ℝ) : ℂ) * Todd α x (p.1 * p.2) else 0) =
      ∑ v ∈ a.divisors.filter (fun v : ℕ => (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U),
        (if Odd a then ((Λ v : ℝ) * (μ (a / v) : ℝ) : ℂ) * Todd α x a else 0) := by
    refine sum_nbij' (fun p => p.1) (fun v => (v, a / v)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      simp only [mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨p.2, h5.symm⟩, by omega⟩, (Nat.le_floor_iff hV).1 h2, ?_⟩
      rw [hdiv]; exact (Nat.le_floor_iff hU).1 h4
    · intro v hv
      simp only [mem_filter, Nat.mem_divisors] at hv
      obtain ⟨⟨hva, ha0⟩, h1, h2⟩ := hv
      have hv1 : 1 ≤ v := Nat.pos_of_dvd_of_pos hva (by omega)
      have hav : v * (a / v) = a := Nat.mul_div_cancel' hva
      simp only [mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨hv1, Nat.le_floor h1⟩, ?_, Nat.le_floor h2⟩, hav⟩
      rcases Nat.eq_zero_or_pos (a / v) with h | h
      · rw [h, mul_zero] at hav; omega
      · exact h
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      ext <;> simp [hdiv]
    · intro v _; rfl
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      have hodd : Odd p.1 ∧ Odd p.2 ↔ Odd a := by rw [← h5, Nat.odd_mul]
      simp only [hdiv, h5]
      by_cases ho : Odd a
      · rw [if_pos (hodd.2 ho), if_pos ho]
      · rw [if_neg (fun h => ho (hodd.1 h)), if_neg ho]
  rw [hfib, coefI2, sum_filter]
  by_cases ho : Odd a
  · rw [if_pos ho, Complex.ofReal_sum, sum_mul]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  · rw [if_neg ho]
    exact sum_eq_zero fun v _ => by split_ifs <;> rfl

end TernaryGoldbach.MinorArcs
