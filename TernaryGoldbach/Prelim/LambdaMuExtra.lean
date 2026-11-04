import TernaryGoldbach.Prelim.LambdaMu

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# [H, (2.16)] and [H, (2.18)]

From (2.17), (2.14) and finite checks (`scripts/psi_extra_check.py`).
-/

open Finset ArithmeticFunction


namespace TernaryGoldbach.Prelim

/-- **Numerical axiom** (`scripts/psi_extra_check.py`; max ratio `1.03583` at `k = 663`):
`∑_{n≤k} Λ(n) n < 1.03884 k²/2` for `663 ≤ k ≤ 2.5·10⁷`. -/
axiom lambda_mul_small (k : ℕ) (h1 : 663 ≤ k) (h2 : k ≤ 25000000) :
    ∑ n ∈ Icc 1 k, (Λ n : ℝ) * n < 1.03884 * (k : ℝ) ^ 2 / 2

/-- **Numerical axiom** (same script; max ratio `1.99906` at `k = 5 465 627`):
`∑_{n≤k} Λ(n)/√n < 2.0008 √k` for `1 ≤ k ≤ 6·10⁶`. -/
axiom lambda_sqrt_small (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 6000000) :
    ∑ n ∈ Icc 1 k, (Λ n : ℝ) / √n < 2.0008 * √(k : ℝ)

/-- **Numerical axiom** (same script; value `−3.6619`): at `K = 6·10⁶`,
`∑_{n≤K} Λ(n)/√n − ψ(K)/√(K+1) − 1.0004 √(K+1) ≤ −2`. -/
axiom lambda_sqrt_point :
    ∑ n ∈ Icc 1 6000000, (Λ n : ℝ) / √n - psiN 6000000 / √(6000001 : ℝ) -
      1.0004 * √(6000001 : ℝ) ≤ -2

/-- **[H, (2.16)]**: `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`. -/
theorem sum_vonMangoldt_mul_lt {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by
  rcases le_or_gt 2.5e7 y with h | h
  · have := sum_vonMangoldt_mul_lt' h
    have : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
    linarith
  · have hk1 : 663 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hk2 : ⌊y⌋₊ ≤ 25000000 := Nat.floor_le_of_le (by norm_num; linarith)
    have hax := lambda_mul_small _ hk1 hk2
    have hky : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have : (⌊y⌋₊ : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hky 2
    linarith

theorem sum_Ioo_tele (f : ℕ → ℝ) {K k : ℕ} (hKk : K < k) :
    ∑ n ∈ Ioo K k, (f (n + 1) - f n) = f k - f (K + 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge K k with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp), ih h]; ring
    · have : k = K := by omega
      subst this
      rw [Ioo_self_succ]; simp

/-- `n (1/√n − 1/√(n+1)) ≤ √(n+1) − √n`. -/
theorem mul_inv_sqrt_sub_le {n : ℝ} (hn : 0 < n) :
    n * (1 / √n - 1 / √(n + 1)) ≤ √(n + 1) - √n := by
  have h1 : 0 < √n := Real.sqrt_pos.2 hn
  have h2 : 0 < √(n + 1) := Real.sqrt_pos.2 (by linarith)
  have e1 : √n * √n = n := Real.mul_self_sqrt hn.le
  have e2 : √(n + 1) * √(n + 1) = n + 1 := Real.mul_self_sqrt (by linarith)
  have amgm : 2 * (√n * √(n + 1)) ≤ 2 * n + 1 := by nlinarith [sq_nonneg (√(n + 1) - √n)]
  have e : n * (1 / √n - 1 / √(n + 1)) = √n - n / √(n + 1) := by
    field_simp; nlinarith
  rw [e]
  have : 2 * √n ≤ (2 * n + 1) / √(n + 1) := by rw [le_div_iff₀ h2]; linarith
  have e3 : (2 * n + 1) / √(n + 1) = √(n + 1) + n / √(n + 1) := by field_simp; linarith
  linarith

/-- **[H, (2.18)]**: `∑_{n ≤ y} Λ(n)/√n < 2·1.0004 √y` for `y ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_lt {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √n < 2 * 1.0004 * √y := by
  set k := ⌊y⌋₊ with hk
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hy)
  have hky : (k : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hsk : √(k : ℝ) ≤ √y := Real.sqrt_le_sqrt hky
  rcases le_or_gt k 6000000 with h | h
  · have := lambda_sqrt_small k hk1 h; linarith
  set K := 6000000
  have hsplit : ∑ n ∈ Icc 1 k, (Λ n : ℝ) / √n =
      ∑ n ∈ Icc 1 K, (Λ n : ℝ) / √n + ∑ n ∈ Ioc K k, (Λ n : ℝ) * (1 / √n) := by
    have e1 : Icc 1 k = Ioc 0 k := Finset.Icc_add_one_left_eq_Ioc 0 k
    have e2 : Icc 1 K = Ioc 0 K := Finset.Icc_add_one_left_eq_Ioc 0 K
    have e3 : ∑ n ∈ Ioc K k, (Λ n : ℝ) / √n = ∑ n ∈ Ioc K k, (Λ n : ℝ) * (1 / √n) :=
      sum_congr rfl fun n _ => by ring
    rw [e1, e2, ← sum_Ioc_consecutive _ (by omega : 0 ≤ K) h.le, e3]
  have habel := abel_Ioc (fun n => 1 / √(n : ℝ)) K k h
  -- the middle sum
  have hmid : ∑ n ∈ Ioo K k, psiN n * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) ≤
      1.0004 * (√(k : ℝ) - √((K + 1 : ℕ) : ℝ)) := by
    calc _ ≤ ∑ n ∈ Ioo K k, 1.0004 * (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) := by
          refine sum_le_sum fun n hn => ?_
          have hn2 : 6000000 ≤ n := by have := (mem_Ioo.1 hn).1; omega
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hψ := (psi_bounds n).2 hn2
          have hw : 0 ≤ 1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ) := by
            have : √(n : ℝ) ≤ √((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
            have : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
            rw [sub_nonneg]; exact one_div_le_one_div_of_le this (by linarith)
          have := mul_inv_sqrt_sub_le hn0
          push_cast at this hw ⊢
          calc psiN n * (1 / √(n : ℝ) - 1 / √((n : ℝ) + 1)) ≤ 1.0004 * n * (1 / √(n : ℝ) - 1 / √((n : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_right hψ hw
            _ = 1.0004 * (n * (1 / √(n : ℝ) - 1 / √((n : ℝ) + 1))) := by ring
            _ ≤ 1.0004 * (√((n : ℝ) + 1) - √(n : ℝ)) := by gcongr
      _ = 1.0004 * (√(k : ℝ) - √((K + 1 : ℕ) : ℝ)) := by
          rw [← mul_sum, sum_Ioo_tele (fun n => √(n : ℝ)) h]
  have hψk : psiN k * (1 / √(k : ℝ)) ≤ 1.0004 * √(k : ℝ) := by
    have hψ := (psi_bounds k).2 h.le
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hs : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
    calc psiN k * (1 / √(k : ℝ)) ≤ 1.0004 * k * (1 / √(k : ℝ)) :=
          mul_le_mul_of_nonneg_right hψ (by positivity)
      _ = 1.0004 * √(k : ℝ) := by
          field_simp; rw [Real.sq_sqrt hk0.le]
  have hpt := lambda_sqrt_point
  have e1 : ((K + 1 : ℕ) : ℝ) = 6000001 := by norm_num
  rw [e1] at hmid habel
  rw [hsplit, habel]
  have : psiN K * (1 / √(6000001 : ℝ)) = psiN 6000000 / √(6000001 : ℝ) := by ring
  linarith

end TernaryGoldbach.Prelim
