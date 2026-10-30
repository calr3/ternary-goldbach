import TernaryGoldbach.Helfgott.NonPrime

/-!
# Elementary Chebyshev bounds

Helfgott uses the Rosser–Schoenfeld bounds `ψ(x) < 1.03883 x` and `ψ(x) - θ(x) < 1.4262 √x`
[RS62, Thms. 12, 13].  For `N ≥ 10²⁷` the following elementary bounds are enough for us:

* `theta_le`: `θ(N) ≤ N log 4` (from `primorial_le_four_pow`);
* `psi_sub_theta_le`: `ψ(N) - θ(N) ≤ 1.6 √N`;
* `psi_le`: `ψ(N) ≤ 1.387 N`.

For the middle one, each non-prime prime power `pᵏ ≤ N` has `2 ≤ k ≤ log₂ N`. The `k = 2`
terms contribute at most `θ(√N)`, and each `k ≥ 3` contributes at most `θ(N^{3/8})`.

Proved, with no `sorry`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Helfgott

theorem theta_le (N : ℕ) : theta N ≤ N * Real.log 4 := by
  classical
  have h1 : theta N = Real.log (primorial N) := by
    rw [theta, primorial, Nat.cast_prod, Real.log_prod (fun p hp => by
      have := (mem_filter.1 hp).2.pos; positivity), sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with hp
    · exact ArithmeticFunction.vonMangoldt_apply_prime hp
    · rfl
  rw [h1, ← Real.log_pow, show (4:ℝ) ^ N = ((4 ^ N : ℕ) : ℝ) by push_cast; ring]
  exact Real.log_le_log (by exact_mod_cast primorial_pos N) (by exact_mod_cast primorial_le_four_pow N)

open Classical in
theorem psi_sub_theta_le_sum (N : ℕ) :
    psi N - theta N ≤ ∑ k ∈ Icc 2 (Nat.log 2 N), ∑ m ∈ range (N + 1),
      if m.Prime ∧ m ^ k ≤ N then Real.log m else 0 := by
  have hsplit : psi N - theta N = ∑ n ∈ range (N + 1), if n.Prime then 0 else Λ n := by
    rw [psi, theta, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hnn : ∀ m : ℕ, 0 ≤ if m.Prime then Real.log m else 0 := fun m => by
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  -- Pointwise: each non-prime prime power `pᵏ ≤ N` is counted by the pair `(k, p)`.
  have hpt : ∀ n ∈ range (N + 1), (if n.Prime then 0 else Λ n) ≤
      ∑ k ∈ Icc 2 (Nat.log 2 N), ∑ m ∈ range (N + 1),
        if m.Prime ∧ m ^ k = n then Real.log m else 0 := by
    intro n hn
    have hnn' : ∀ k m, 0 ≤ if m.Prime ∧ m ^ k = n then Real.log (m : ℝ) else 0 := fun k m => by
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.1.one_lt.le)
      · exact le_rfl
    have hRHS : 0 ≤ ∑ k ∈ Icc 2 (Nat.log 2 N), ∑ m ∈ range (N + 1),
        if m.Prime ∧ m ^ k = n then Real.log (m : ℝ) else 0 :=
      sum_nonneg fun k _ => sum_nonneg fun m _ => hnn' k m
    split_ifs with hp
    · exact hRHS
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · have : k = 1 := by omega
          subst this; simp only [pow_one] at hp; exact absurd hp' hp
        · exact h
      have hN : p ^ k ≤ N := by simpa [Nat.lt_succ_iff] using hn
      have hkN : k ≤ Nat.log 2 N :=
        Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hp'.two_le k).trans hN)
      have hpN : p ≤ N := (Nat.le_self_pow (by omega) p).trans hN
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp']
      calc Real.log p = if p.Prime ∧ p ^ k = p ^ k then Real.log (p : ℝ) else 0 := by
            simp [hp']
        _ ≤ ∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k = p ^ k then Real.log (m : ℝ) else 0 :=
            single_le_sum (fun m _ => hnn' k m) (mem_range.2 (by omega))
        _ ≤ _ := single_le_sum (f := fun j => ∑ m ∈ range (N + 1),
              if m.Prime ∧ m ^ j = p ^ k then Real.log (m : ℝ) else 0)
            (fun j _ => sum_nonneg fun m _ => hnn' j m) (mem_Icc.2 ⟨hk2, hkN⟩)
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
      exact hRHS
  rw [hsplit]
  refine (sum_le_sum hpt).trans (le_of_eq ?_)
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  by_cases hm : m.Prime
  · simp only [hm, true_and]
    rw [sum_ite_eq (range (N + 1)) (m ^ k) (fun _ => Real.log (m : ℝ))]
    simp [Nat.lt_succ_iff]
  · simp [hm]

open Classical in
/-- The prime-power terms with exponent `k` are bounded by `θ(M) ≤ M log 4` whenever every prime
`m` with `mᵏ ≤ N` satisfies `m ≤ M`. -/
theorem sum_pow_le_theta {N k M : ℕ} (hMN : M ≤ N) (hM : ∀ m, m.Prime → m ^ k ≤ N → m ≤ M) :
    (∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ M * Real.log 4 := by
  refine le_trans ?_ (theta_le M)
  have hfilt : (range (N + 1)).filter (· ≤ M) = range (M + 1) := by
    ext m; simp only [mem_filter, mem_range]; omega
  rw [theta, ← hfilt, sum_filter]
  refine sum_le_sum fun m _ => ?_
  by_cases hp : m.Prime
  · by_cases hk : m ^ k ≤ N
    · simp [hp, hk, hM m hp hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hp, hk, and_false, ite_false, true_and]
      split_ifs <;> simp [ArithmeticFunction.vonMangoldt_apply_prime hp,
        Real.log_nonneg, hp.one_lt.le]
  · simp [hp]

/-- `ψ(N) - θ(N) ≤ 1.6 √N` for `N ≥ 10²⁷`. -/
theorem psi_sub_theta_le (N : ℕ) (hN : 10 ^ 27 ≤ N) : psi N - theta N ≤ 1.6 * √N := by
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  -- `w = N^{1/32}`, `u = w² = N^{1/16}`.
  set w := √(√(√(√(√(N : ℝ)))))
  have hw0 : 0 < w := by simp only [w]; positivity
  have hw32 : w ^ 32 = (N : ℝ) := by
    simp only [w]
    rw [show ∀ x : ℝ, x ^ 32 = ((((x ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 from fun x => by ring]
    simp only [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hN0.le]
  have hw16 : w ^ 16 = √(N : ℝ) := by
    rw [← hw32, show w ^ 32 = (w ^ 16) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hw69 : (6.9 : ℝ) ≤ w := by
    by_contra h
    push Not at h
    have : w ^ 32 < (6.9 : ℝ) ^ 32 := pow_lt_pow_left₀ h hw0.le (by norm_num)
    rw [hw32] at this
    linarith [show (6.9 : ℝ) ^ 32 ≤ 10 ^ 27 by norm_num]
  -- The split by exponent.
  set K := Nat.log 2 N
  set M3 := ⌊w ^ 12⌋₊
  have hM3 : (M3 : ℝ) ≤ w ^ 12 := Nat.floor_le (by positivity)
  have hM3N : M3 ≤ N := by
    have : (M3 : ℝ) ≤ N := hM3.trans (by
      rw [← hw32]; exact pow_le_pow_right₀ (by linarith) (by norm_num))
    exact_mod_cast this
  have hsq : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
  have hk2 := sum_pow_le_theta (k := 2) hsq fun m _ h => Nat.le_sqrt'.2 h
  have hk3 : ∀ k ∈ Icc 2 K, k ≠ 2 →
      (∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ M3 * Real.log 4 := by
    intro k hk hk2
    refine sum_pow_le_theta hM3N fun m hm hmk => Nat.le_floor ?_
    have h3 : m ^ 3 ≤ N := (Nat.pow_le_pow_right hm.pos (by simp at hk; omega)).trans hmk
    by_contra hlt
    push Not at hlt
    have : (w ^ 12) ^ 3 < (m : ℝ) ^ 3 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have h3r : (m : ℝ) ^ 3 ≤ N := by exact_mod_cast h3
    have : w ^ 32 ≤ (w ^ 12) ^ 3 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  set A := (Nat.sqrt N : ℝ) * Real.log 4
  set B := (M3 : ℝ) * Real.log 4
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB0 : 0 ≤ B := by positivity
  have hsum : psi N - theta N ≤ A + K * B := by
    refine (psi_sub_theta_le_sum N).trans ?_
    calc (∑ k ∈ Icc 2 K, ∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k ≤ N then Real.log m else 0)
        ≤ ∑ k ∈ Icc 2 K, ((if k = 2 then A else 0) + B) := by
          refine sum_le_sum fun k hk => ?_
          by_cases h : k = 2
          · subst h; simp only [ite_true]; linarith
          · simp only [h, ite_false, zero_add]; exact hk3 k hk h
      _ = (∑ k ∈ Icc 2 K, if k = 2 then A else 0) + (Icc 2 K).card * B := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ A + K * B := by
          have h1 : (∑ k ∈ Icc 2 K, if k = 2 then A else 0) ≤ A := by
            rw [sum_ite_eq' (Icc 2 K) 2 (fun _ => A)]
            split_ifs
            · exact le_rfl
            · positivity
          have h2 : ((Icc 2 K).card : ℝ) ≤ K := by
            rw [Nat.card_Icc]; exact_mod_cast (by omega : K + 1 - 2 ≤ K)
          nlinarith
  -- Numerics.
  have hA : A ≤ √N * Real.log 4 := mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hlog4
  have hK : (K : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega))
  have hlogN : Real.log N ≤ 32 * w := by
    rw [← hw32, Real.log_pow]; push_cast
    linarith [Real.log_le_sub_one_of_pos hw0]
  have hl2 := Real.log_two_gt_d9
  have hKw : (K : ℝ) ≤ 46.2 * w := by
    have : (K : ℝ) * 0.6931471803 ≤ 32 * w := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
    nlinarith
  have hlog4' : Real.log 4 ≤ 1.3862943617 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hKB : (K : ℝ) * B ≤ 0.15 * w ^ 16 * Real.log 4 := by
    simp only [B]
    have h13 : 46.2 * w ^ 13 ≤ 0.15 * w ^ 16 := by
      have : (6.9 : ℝ) ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by norm_num) hw69 3
      nlinarith [pow_pos hw0 13, show w ^ 16 = w ^ 3 * w ^ 13 by ring]
    calc (K : ℝ) * (M3 * Real.log 4) ≤ (46.2 * w) * (w ^ 12 * Real.log 4) := by
          gcongr
      _ = 46.2 * w ^ 13 * Real.log 4 := by ring
      _ ≤ 0.15 * w ^ 16 * Real.log 4 := by gcongr
  rw [hw16] at hKB
  have hs : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- `ψ(N) ≤ 1.387 N` for `N ≥ 10²⁷`. -/
theorem psi_le (N : ℕ) (hN : 10 ^ 27 ≤ N) : psi N ≤ 1.387 * N := by
  have h1 := psi_sub_theta_le N hN
  have h2 := theta_le N
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  have hsq : (10 : ℝ) ^ 13 ≤ √N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsN : √(N : ℝ) * √N = N := Real.mul_self_sqrt (by positivity)
  have hlog4 : Real.log 4 ≤ 1.3862943617 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hN0 : (0:ℝ) ≤ N := by positivity
  have : 1.6 * √(N : ℝ) ≤ 0.0001 * N := by nlinarith
  nlinarith

end TernaryGoldbach.Helfgott
