import TernaryGoldbach.Prelim.MoebiusDecay

/-!
# Schoenfeld's identity for `∑ μ(n) log n`

With `M(k) = ∑_{n ≤ k} μ(n)`, `N(k) = ∑_{n ≤ k} μ(n) log n` and `ρ(k) = ∑_{j ≤ k} (Λ(j) − 1)`
(`ρ(k) = ψ(k) − k`), for `1 ≤ Y ≤ N` (L. Schoenfeld, Acta Arith. 15 (1969), (19)):
`N(N) + 1 = M(N) − ∑_{1 < k ≤ Y} (Λ(k) − 1) M(N/k) − ∑_{m ≤ N/(Y+1)} μ(m) ρ(N/m) + ρ(Y) M(N/(Y+1))`
(`schoenfeld_identity`; all quotients are integer quotients).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim.Sch

/-- `M(k) = ∑_{n ≤ k} μ(n)`. -/
noncomputable def Mn (k : ℕ) : ℝ := ∑ m ∈ Ioc 0 k, (μ m : ℝ)
/-- `N(k) = ∑_{n ≤ k} μ(n) log n`. -/
noncomputable def Nn (k : ℕ) : ℝ := ∑ m ∈ Ioc 0 k, (μ m : ℝ) * Real.log m
/-- `ρ(k) = ∑_{j ≤ k} (Λ(j) − 1)`. -/
noncomputable def ρn (k : ℕ) : ℝ := ∑ j ∈ Ioc 0 k, (Λ j - 1)

/-- `∑_{k ≤ N} M(N/k) = 1`. -/
theorem sum_Mn_div {N : ℕ} (hN : 1 ≤ N) : ∑ k ∈ Ioc 0 N, Mn (N / k) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ) N
  rw [coe_zeta_mul_coe_moebius] at h
  have h1 : ∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℝ) n = 1 := by
    simp only [one_apply]
    rw [Finset.sum_ite_eq' (Ioc 0 N) 1 (fun _ => (1 : ℝ))]
    simp only [mem_Ioc, if_pos (show 0 < 1 ∧ 1 ≤ N from ⟨by norm_num, hN⟩)]
  rw [h1] at h
  rw [h]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (mem_Ioc.1 hk).1; omega
  simp only [natCoe_apply, zeta_apply, hk0, if_false, Nat.cast_one, one_mul, intCoe_apply, Mn]

/-- `∑_{k ≤ N} Λ(k) M(N/k) = −N(N)`. -/
theorem sum_Lambda_Mn_div (N : ℕ) : ∑ k ∈ Ioc 0 N, Λ k * Mn (N / k) = -Nn N := by
  have h := sum_Ioc_mul_eq_sum_sum (Λ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ) N
  have hLm : (Λ : ArithmeticFunction ℝ) * μ = -pmul (μ : ArithmeticFunction ℝ) log := by
    rw [pmul_moebius_log, neg_neg]
  rw [hLm] at h
  simp only [ArithmeticFunction.neg_apply, pmul_apply, intCoe_apply, log_apply, sum_neg_distrib] at h
  unfold Nn Mn
  rw [h]

/-- `N(N) + 1 = −∑_{k ≤ N} (Λ(k) − 1) M(N/k)`. -/
theorem Nn_add_one {N : ℕ} (hN : 1 ≤ N) : Nn N + 1 = -∑ k ∈ Ioc 0 N, (Λ k - 1) * Mn (N / k) := by
  have h1 := sum_Mn_div hN
  have h2 := sum_Lambda_Mn_div N
  simp only [sub_mul, one_mul, sum_sub_distrib]
  linarith

/-- The pairs `k > Y`: `∑_{Y < k ≤ N} (Λ(k) − 1) M(N/k) = ∑_{m ≤ N/(Y+1)} μ(m) (ρ(N/m) − ρ(Y))`. -/
theorem sum_large_k {N Y : ℕ} :
    ∑ k ∈ Ioc Y N, (Λ k - 1) * Mn (N / k) =
      ∑ m ∈ Ioc 0 (N / (Y + 1)), (μ m : ℝ) * (ρn (N / m) - ρn Y) := by
  let f : ArithmeticFunction ℝ := ⟨fun k => if Y < k then Λ k - 1 else 0, by simp⟩
  have h1 := sum_Ioc_mul_eq_sum_sum f (μ : ArithmeticFunction ℝ) N
  have h2 := sum_Ioc_mul_eq_sum_sum (μ : ArithmeticFunction ℝ) f N
  rw [mul_comm f] at h1
  rw [h1] at h2
  -- the left side of `h2` is our sum
  have eL : ∑ n ∈ Ioc 0 N, f n * ∑ m ∈ Ioc 0 (N / n), (μ : ArithmeticFunction ℝ) m =
      ∑ k ∈ Ioc Y N, (Λ k - 1) * Mn (N / k) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 N) (fun k => Y < k)]
    have : ∑ x ∈ (Ioc 0 N).filter (fun k => ¬ Y < k), f x * ∑ m ∈ Ioc 0 (N / x), (μ : ArithmeticFunction ℝ) m = 0 :=
      sum_eq_zero fun x hx => by
        have := (mem_filter.1 hx).2
        simp only [f, coe_mk, if_neg this, zero_mul]
    rw [this, add_zero]
    have hset : (Ioc 0 N).filter (fun k => Y < k) = Ioc Y N := by ext x; simp; omega
    rw [hset]
    refine sum_congr rfl fun k hk => ?_
    have := (mem_Ioc.1 hk).1
    simp only [f, coe_mk, if_pos this, Mn, intCoe_apply]
  -- the right side
  have eR : ∑ n ∈ Ioc 0 N, (μ : ArithmeticFunction ℝ) n * ∑ m ∈ Ioc 0 (N / n), f m =
      ∑ m ∈ Ioc 0 (N / (Y + 1)), (μ m : ℝ) * (ρn (N / m) - ρn Y) := by
    have hinner : ∀ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / n), f m =
        if n ≤ N / (Y + 1) then ρn (N / n) - ρn Y else 0 := by
      intro n hn
      have hn0 : 0 < n := (mem_Ioc.1 hn).1
      rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 (N / n)) (fun k => Y < k)]
      have z : ∑ x ∈ (Ioc 0 (N / n)).filter (fun k => ¬ Y < k), f x = 0 :=
        sum_eq_zero fun x hx => by simp only [f, coe_mk, if_neg (mem_filter.1 hx).2]
      rw [z, add_zero]
      split_ifs with hle
      · have hY : Y + 1 ≤ N / n := by
          rw [Nat.le_div_iff_mul_le hn0]
          have := (Nat.le_div_iff_mul_le (by omega : 0 < Y + 1)).1 hle
          linarith [mul_comm n (Y + 1)]
        have hset : (Ioc 0 (N / n)).filter (fun k => Y < k) = Ioc Y (N / n) := by ext x; simp; omega
        rw [hset]
        have : ρn (N / n) = ρn Y + ∑ j ∈ Ioc Y (N / n), (Λ j - 1) := by
          unfold ρn; rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) (by omega)]
        rw [this]; simp only [f, coe_mk]
        rw [sum_congr rfl fun x hx => if_pos (mem_Ioc.1 hx).1]; ring
      · have hY : N / n ≤ Y := by
          by_contra hc; push Not at hc
          apply hle
          rw [Nat.le_div_iff_mul_le (by omega)]
          have := (Nat.le_div_iff_mul_le hn0).1 hc
          linarith [mul_comm n (Y + 1)]
        apply sum_eq_zero; intro x hx; simp at hx; omega
    rw [sum_congr rfl fun n hn => by rw [hinner n hn]]
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hset : (Ioc 0 N).filter (fun n => n ≤ N / (Y + 1)) = Ioc 0 (N / (Y + 1)) := by
      ext x; simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 (Nat.div_le_self _ _)⟩, h3⟩
    rw [hset]
    simp only [intCoe_apply]
  rw [eL, eR] at h2
  exact h2

/-- **Schoenfeld's identity** (1969, (19)). -/
theorem schoenfeld_identity {N Y : ℕ} (hY1 : 1 ≤ Y) (hYN : Y ≤ N) :
    Nn N + 1 = Mn N - ∑ k ∈ Ioc 1 Y, (Λ k - 1) * Mn (N / k) -
      ∑ m ∈ Ioc 0 (N / (Y + 1)), (μ m : ℝ) * ρn (N / m) + ρn Y * Mn (N / (Y + 1)) := by
  have hN : 1 ≤ N := le_trans hY1 hYN
  rw [Nn_add_one hN, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) hYN, sum_large_k,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hY1]
  have h1 : ∑ k ∈ Ioc 0 1, (Λ k - 1) * Mn (N / k) = -Mn N := by
    simp [Nat.div_one]
  have h2 : ∑ m ∈ Ioc 0 (N / (Y + 1)), (μ m : ℝ) * (ρn (N / m) - ρn Y) =
      ∑ m ∈ Ioc 0 (N / (Y + 1)), (μ m : ℝ) * ρn (N / m) - ρn Y * Mn (N / (Y + 1)) := by
    unfold Mn; rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun m _ => by ring
  rw [h1, h2]; ring

end TernaryGoldbach.Prelim.Sch
