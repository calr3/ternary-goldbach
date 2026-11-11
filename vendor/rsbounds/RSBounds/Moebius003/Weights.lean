/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Rho
import RSBounds.Moebius003.Abel

/-!
# Lemma 6 of the note: the weights `a_k = |Λ(k) − 1|`

* (a) `A(n) = ∑_{2 ≤ k ≤ n} a_k ≤ 2(n − 1)` for all `n ≥ 1`: by (L) for `n ≤ 2²⁰`, and beyond from
  the pointwise bound `|λ − 1| ≤ 1 + λ(1 − 2/log n)` (`0 ≤ λ ≤ log n`, `log n ≥ 1`), which gives
  `A(n) ≤ (n − 1) + (1 − 2/log n) ψ(n)`, with (P) and (S). This replaces the note's count of prime
  powers.
* (b) For `g ≥ 0` non-increasing on `[2, K]`: `∑_{2 ≤ k ≤ K} a_k g(k) ≤ 2 ∑_{2 ≤ k ≤ K} g(k)`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real

/-- `A(n) = ∑_{2 ≤ k ≤ n} |Λ(k) − 1|`. -/
noncomputable def A (n : ℕ) : ℝ := ∑ k ∈ Icc 2 n, |Λ k - 1|

theorem psi_nat_eq (n : ℕ) : Chebyshev.psi n = ∑ k ∈ Icc 2 n, Λ k := by
  rw [Chebyshev.psi, Nat.floor_natCast, ← Icc_one_eq_Ioc_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ n), sum_insert (by simp)]
  simp

theorem abs_sub_one_le {lam L : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L) (hL1 : 1 ≤ L) :
    |lam - 1| ≤ 1 + lam * (1 - 2 / L) := by
  have hLpos : 0 < L := by linarith
  rcases le_or_gt 1 lam with h | h
  · rw [abs_of_nonneg (by linarith)]
    have : lam * (2 / L) ≤ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hLpos]; linarith
    nlinarith
  · rw [abs_of_neg (by linarith)]
    have : lam * (2 / L) ≤ 2 * lam := by
      rw [mul_div_assoc', div_le_iff₀ hLpos]; nlinarith
    nlinarith

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  rw [this]
  have := Real.log_le_sub_one_of_pos hs
  linarith

theorem two_le_log {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  rw [show (2 : ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
  apply Real.log_le_log (Real.exp_pos 2)
  have : Real.exp 2 ≤ 2.7182818286 ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  have h2 : (2.7182818286 : ℝ) ^ 2 ≤ 8 := by norm_num
  linarith

/-- **Lemma 6(a)**. -/
theorem A_le (h : Inputs) {n : ℕ} (hn : 1 ≤ n) : A n ≤ 2 * ((n : ℝ) - 1) := by
  by_cases hsmall : n ≤ 2 ^ 20
  · exact h.W n hn hsmall
  push Not at hsmall
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set L := Real.log n with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
    linarith
  have hLpos : 0 < L := by linarith
  -- pointwise bound
  have hA : A n ≤ ((n : ℝ) - 1) + (1 - 2 / L) * Chebyshev.psi n := by
    rw [psi_nat_eq, A, mul_sum]
    have hcard : ((n : ℝ) - 1) = ∑ k ∈ Icc 2 n, (1 : ℝ) := by
      simp only [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcard, ← sum_add_distrib]
    refine sum_le_sum fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
    have h0 := vonMangoldt_nonneg (n := k)
    have h1 : Λ k ≤ L := (vonMangoldt_le_log).trans
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk2))
    have := abs_sub_one_le h0 h1 hL1
    linarith
  have hfac : 0 ≤ 1 - 2 / L ∨ 1 - 2 / L < 0 := le_or_gt _ _
  by_cases hmid : n ≤ 10 ^ 10
  · -- (P): `ψ(n) ≤ n + 0.8 √n`
    have hP := h.P n (by exact_mod_cast (by omega : 1500 ≤ n)) (by exact_mod_cast hmid)
    have hpsi : Chebyshev.psi n ≤ n + 4 / 5 * Real.sqrt n := by
      have := (abs_le.1 hP).2; linarith
    have hs : (1024 : ℝ) ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by norm_num) hnpos.le]
      have : (2 ^ 20 : ℝ) < n := by exact_mod_cast hsmall
      norm_num at this ⊢; linarith
    have hLs : L ≤ 2 * Real.sqrt n := log_le_two_sqrt hnpos
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have hpsi0 : 0 ≤ Chebyshev.psi n := Chebyshev.psi_nonneg _
    -- `2n/L ≥ √n ≥ 0.8√n + 1`
    have key : (4 / 5 * Real.sqrt n + 1) * L ≤ 2 * n := by nlinarith
    have hL2 : 2 ≤ L := two_le_log (by exact_mod_cast (by omega : 8 ≤ n))
    have hf0 : 0 ≤ 1 - 2 / L := by rw [sub_nonneg, div_le_one hLpos]; exact hL2
    have : (1 - 2 / L) * Chebyshev.psi n ≤ (1 - 2 / L) * (n + 4 / 5 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hpsi hf0
    have e : (1 - 2 / L) * (n + 4 / 5 * Real.sqrt n) =
        n + 4 / 5 * Real.sqrt n - 2 * n / L - 2 * (4 / 5 * Real.sqrt n) / L := by
      field_simp; ring
    have h2 : 4 / 5 * Real.sqrt n + 1 ≤ 2 * n / L := by rw [le_div_iff₀ hLpos]; exact key
    have h3 : 0 ≤ 2 * (4 / 5 * Real.sqrt n) / L := by positivity
    linarith
  · -- (S): `ψ(n) < n + C₅ n/log n`
    push Not at hmid
    have hS := h.S n (le_trans exp22_le (by exact_mod_cast hmid.le))
    have hpsi : Chebyshev.psi n ≤ n + 0.0077629 * n / L := by
      have := (abs_lt.1 hS).2; linarith
    have hLn : L ≤ n := by
      have := Real.log_le_sub_one_of_pos hnpos; linarith
    have hL2 : 2 ≤ L := two_le_log (by exact_mod_cast (by omega : 8 ≤ n))
    have hf0 : 0 ≤ 1 - 2 / L := by rw [sub_nonneg, div_le_one hLpos]; exact hL2
    have : (1 - 2 / L) * Chebyshev.psi n ≤ (1 - 2 / L) * (n + 0.0077629 * n / L) :=
      mul_le_mul_of_nonneg_left hpsi hf0
    have e : (1 - 2 / L) * (n + 0.0077629 * n / L) =
        n - (2 - 0.0077629) * n / L - 2 * (0.0077629 * n / L) / L := by
      field_simp; ring
    have h2 : 1 ≤ (2 - 0.0077629) * n / L := by
      rw [le_div_iff₀ hLpos]; nlinarith
    have h3 : 0 ≤ 2 * (0.0077629 * n / L) / L := by positivity
    linarith

theorem Icc_one_eq_insert {K : ℕ} (hK : 1 ≤ K) : Icc 1 K = insert 1 (Icc 2 K) := by
  ext k; simp only [mem_Icc, mem_insert]; omega

/-- **Lemma 6(b)**. -/
theorem sum_weight_le (h : Inputs) {K : ℕ} (g : ℕ → ℝ)
    (hg : ∀ k, 2 ≤ k → k < K → g (k + 1) ≤ g k) (hgK : 0 ≤ g K) :
    ∑ k ∈ Icc 2 K, |Λ k - 1| * g k ≤ 2 * ∑ k ∈ Icc 2 K, g k := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · rw [Icc_eq_empty (by omega)]; simp
  set f : ℕ → ℝ := fun k => if 2 ≤ k then |Λ k - 1| else 0 with hf
  set f' : ℕ → ℝ := fun k => if 2 ≤ k then 2 else 0 with hf'
  set g' : ℕ → ℝ := fun k => if 2 ≤ k then g k else g 2 with hg'
  have hsplit : ∀ (u : ℕ → ℝ), (∀ k, k < 2 → u k = 0) →
      ∑ k ∈ Icc 1 K, u k = ∑ k ∈ Icc 2 K, u k := by
    intro u hu
    rw [Icc_one_eq_insert (by omega : 1 ≤ K), sum_insert (by simp), hu 1 (by omega), zero_add]
  have hpart : ∀ i, 1 ≤ i → i ≤ K → ∑ k ∈ Icc 1 i, f k ≤ ∑ k ∈ Icc 1 i, f' k := by
    intro i hi1 hi2
    have e1 : ∑ k ∈ Icc 1 i, f k = A i := by
      rw [A]
      rcases Nat.lt_or_ge i 2 with hi | hi
      · interval_cases i; simp [hf]
      rw [Icc_one_eq_insert (by omega : 1 ≤ i), sum_insert (by simp)]
      simp only [hf, show ¬ (2 ≤ 1) by omega, if_false, zero_add]
      exact sum_congr rfl fun k hk => by rw [if_pos (mem_Icc.1 hk).1]
    have e2 : ∑ k ∈ Icc 1 i, f' k = 2 * ((i : ℝ) - 1) := by
      rcases Nat.lt_or_ge i 2 with hi | hi
      · interval_cases i; simp [hf']
      rw [Icc_one_eq_insert (by omega : 1 ≤ i), sum_insert (by simp)]
      simp only [hf', show ¬ (2 ≤ 1) by omega, if_false, zero_add]
      rw [sum_congr rfl fun k hk => if_pos (mem_Icc.1 hk).1]
      simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2]; exact A_le h hi1
  have hcmp := abel_compare f f' g' K hpart (by
    intro i hi1 hi2
    simp only [hg']
    rcases Nat.lt_or_ge i 2 with hi | hi
    · have : i = 1 := by omega
      subst this; simp
    · rw [if_pos (by omega), if_pos hi]; exact hg i hi hi2) (by simp only [hg']; rw [if_pos hK]; exact hgK)
  rw [hsplit (fun k => f k * g' k) (fun k hk => by simp [hf, show ¬ 2 ≤ k by omega]),
    hsplit (fun k => f' k * g' k) (fun k hk => by simp [hf', show ¬ 2 ≤ k by omega])] at hcmp
  have e1 : ∑ k ∈ Icc 2 K, f k * g' k = ∑ k ∈ Icc 2 K, |Λ k - 1| * g k :=
    sum_congr rfl fun k hk => by simp [hf, hg', (mem_Icc.1 hk).1]
  have e2 : ∑ k ∈ Icc 2 K, f' k * g' k = 2 * ∑ k ∈ Icc 2 K, g k := by
    rw [mul_sum]; exact sum_congr rfl fun k hk => by simp [hf', hg', (mem_Icc.1 hk).1]
  rw [e1, e2] at hcmp
  exact hcmp

end TernaryGoldbach.RSBounds.Moebius003
