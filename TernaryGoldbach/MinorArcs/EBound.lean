import TernaryGoldbach.Helfgott.HHBound
import TernaryGoldbach.Prelim.LambdaMu

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# [H, (14.28)] with our sup norms: `E ≤ 8·10⁻¹¹ x`

`E = ∑_{n ≤ √x or n not prime} Λ(n)² η₊(n/x)²`.  With `|η₊| ≤ A = 1.94`, `t|η₊(t)| ≤ B = 2.32`
(`Helfgott/HHBound.lean`), `ψ(y) < 1.03883 y` and `ψ(y) − θ(y) < 1.4262 √y` ((2.15), (5.5)):
* `n ≤ x`: `≤ A² (log x/2 · ψ(√x) + log x · (ψ − θ)(x))`;
* `n ∈ (2ʲx, 2ʲ⁺¹x]`, `n` not prime: `Λ(n)² η₊(n/x)² ≤ (ψ−θ)-weight · log(2ʲ⁺¹x) B²/4ʲ`, summed over `j`.
Total `≤ √x (24.12 log x + 18.01) ≤ 8·10⁻¹¹ x` for `x ≥ 4.9·10²⁶`.  ([H] gets `8.4029·10⁻¹² x`
from the sharper Appendix A norms; the minor-arc total tolerates our constant.)
-/

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (etaPlus)

/-- The `n`-th term of `E`. -/
noncomputable def eTerm (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2

/-- The non-prime part of `Λ`. -/
noncomputable def lamNP (n : ℕ) : ℝ := if n.Prime then 0 else (Λ n : ℝ)

theorem eTerm_nonneg (x : ℝ) (n : ℕ) : 0 ≤ eTerm x n := by
  unfold eTerm; split_ifs <;> positivity

theorem lamNP_nonneg (n : ℕ) : 0 ≤ lamNP n := by
  unfold lamNP; split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- `Σ_{a < n ≤ b} f(n)` over dyadic blocks. -/
theorem sum_Ioc_blocks (f : ℕ → ℝ) (a : ℕ → ℕ) (ha : Monotone a) (J : ℕ) :
    ∑ n ∈ Ioc (a 0) (a J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (a j) (a (j + 1)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ← ih, sum_Ioc_consecutive _ (ha (Nat.zero_le J)) (ha (Nat.le_succ J))]

/-- The lower part `n ≤ x`. -/
theorem eTerm_low {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ Icc 1 ⌊x⌋₊) :
    eTerm x n ≤ 1.94 ^ 2 * (Real.log x / 2 * (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) +
      Real.log x * lamNP n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.1 hn).2) (Nat.floor_le (by linarith))
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛlog : (Λ n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hη := Helfgott.abs_etaPlus_le_A (t := n / x) (by positivity)
  have hη2 : etaPlus (n / x) ^ 2 ≤ 1.94 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hη 2
  have hsq : (Λ n * etaPlus (n / x)) ^ 2 ≤ (Λ n : ℝ) * Λ n * 1.94 ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg (Λ n : ℝ)]
  have hA : (0 : ℝ) ≤ 1.94 ^ 2 := by norm_num
  have hNP := lamNP_nonneg n
  have hite : 0 ≤ (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) := by split_ifs <;> simp [hΛ0]
  by_cases hp : n.Prime ∧ √x < n
  · rw [eTerm, if_pos hp]; positivity
  rw [eTerm, if_neg hp]
  have key : (Λ n : ℝ) * Λ n ≤ Real.log x / 2 * (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) +
      Real.log x * lamNP n := by
    by_cases hs : (n : ℝ) ≤ √x
    · rw [if_pos hs]
      have : (Λ n : ℝ) ≤ Real.log x / 2 := by
        have : Real.log n ≤ Real.log √x := Real.log_le_log (by linarith) hs
        rw [Real.log_sqrt hx0.le] at this; linarith
      have := mul_le_mul_of_nonneg_right this hΛ0
      have := mul_nonneg hlx hNP
      linarith
    · rw [if_neg hs]
      have hnp : ¬ n.Prime := fun h => hp ⟨h, lt_of_not_ge hs⟩
      have hl : lamNP n = Λ n := by rw [lamNP, if_neg hnp]
      rw [hl]
      have : (Λ n : ℝ) ≤ Real.log x := hΛlog.trans (Real.log_le_log (by linarith) hnx)
      have := mul_le_mul_of_nonneg_right this hΛ0
      linarith
  calc (Λ n * etaPlus (n / x)) ^ 2 ≤ (Λ n : ℝ) * Λ n * 1.94 ^ 2 := hsq
    _ ≤ (Real.log x / 2 * (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) + Real.log x * lamNP n) * 1.94 ^ 2 :=
        mul_le_mul_of_nonneg_right key hA
    _ = _ := by ring

/-- A dyadic block `n ∈ (⌊2ʲx⌋, ⌊2ʲ⁺¹x⌋]`. -/
theorem eTerm_block {x : ℝ} (hx : 1 ≤ x) (j : ℕ) {n : ℕ}
    (hn : n ∈ Ioc ⌊2 ^ j * x⌋₊ ⌊2 ^ (j + 1) * x⌋₊) :
    eTerm x n ≤ lamNP n * (((j + 1) * Real.log 2 + Real.log x) * 2.32 ^ 2 / 4 ^ j) := by
  have hx0 : 0 < x := by linarith
  have h1 : 2 ^ j * x < n := (Nat.floor_lt (by positivity)).1 (mem_Ioc.1 hn).1
  have h2 : (n : ℝ) ≤ 2 ^ (j + 1) * x :=
    le_trans (by exact_mod_cast (mem_Ioc.1 hn).2) (Nat.floor_le (by positivity))
  have hpj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (by positivity) h1
  have hxn : x < n := lt_of_le_of_lt (le_mul_of_one_le_left hx0.le hpj) h1
  have hsx : √x < n := by
    have hs := Real.sq_sqrt hx0.le
    have hs0 := Real.sqrt_nonneg x
    have : √x ≤ x := by nlinarith
    linarith
  have hK : 0 ≤ ((j + 1) * Real.log 2 + Real.log x) * 2.32 ^ 2 / 4 ^ j := by
    have := Real.log_nonneg hx
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    positivity
  by_cases hp : n.Prime
  · rw [eTerm, if_pos ⟨hp, hsx⟩, lamNP, if_pos hp, zero_mul]
  rw [eTerm, if_neg (fun h => hp h.1), lamNP, if_neg hp]
  · -- not prime
    have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛlog : (Λ n : ℝ) ≤ (j + 1) * Real.log 2 + Real.log x := by
      refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
      have : Real.log n ≤ Real.log (2 ^ (j + 1) * x) := Real.log_le_log hn0 h2
      rw [Real.log_mul (by positivity) hx0.ne', Real.log_pow] at this
      push_cast at this; linarith
    have ht : 0 < (n : ℝ) / x := by positivity
    have hB := Helfgott.mul_abs_etaPlus_le_B ht.le
    -- `|η₊(n/x)| ≤ 2.32/(n/x) ≤ 2.32/2ʲ`
    have hη : |etaPlus (n / x)| ≤ 2.32 / 2 ^ j := by
      have h2j : (2 : ℝ) ^ j < n / x := by rw [lt_div_iff₀ hx0]; exact h1
      rw [le_div_iff₀ (by positivity)]
      calc |etaPlus (n / x)| * 2 ^ j ≤ |etaPlus (n / x)| * (n / x) :=
            mul_le_mul_of_nonneg_left h2j.le (abs_nonneg _)
        _ = n / x * |etaPlus (n / x)| := by ring
        _ ≤ 2.32 := hB
    have hη2 : etaPlus (n / x) ^ 2 ≤ 2.32 ^ 2 / 4 ^ j := by
      rw [← sq_abs]
      calc |etaPlus (n / x)| ^ 2 ≤ (2.32 / 2 ^ j) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hη 2
        _ = 2.32 ^ 2 / 4 ^ j := by
            rw [div_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    rw [mul_pow]
    have hq : 0 ≤ etaPlus (n / x) ^ 2 := sq_nonneg _
    calc (Λ n : ℝ) ^ 2 * etaPlus (n / x) ^ 2 = Λ n * (Λ n * etaPlus (n / x) ^ 2) := by ring
      _ ≤ Λ n * (((j + 1) * Real.log 2 + Real.log x) * (2.32 ^ 2 / 4 ^ j)) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          exact mul_le_mul hΛlog hη2 hq (by linarith [hΛ0])
      _ = Λ n * (((j + 1) * Real.log 2 + Real.log x) * 2.32 ^ 2 / 4 ^ j) := by ring

/-- `∑_{j<J} r^j ≤ 1/(1-r)` and `∑_{j<J} (j+1) r^j ≤ 1/(1-r)²` for `0 ≤ r < 1`. -/
theorem geom_sums_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (J : ℕ) :
    ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) ∧ ∑ j ∈ range J, ((j : ℝ) + 1) * r ^ j ≤ 1 / (1 - r) ^ 2 := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hs1 : Summable fun j : ℕ => r ^ j := summable_geometric_of_lt_one h0 h1
  have hs2 : Summable fun j : ℕ => (j : ℝ) * r ^ j := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have t1 : ∑' j : ℕ, r ^ j = 1 / (1 - r) := by rw [tsum_geometric_of_lt_one h0 h1, one_div]
  have t2 : ∑' j : ℕ, (j : ℝ) * r ^ j = r / (1 - r) ^ 2 := tsum_coe_mul_geometric_of_norm_lt_one hn
  have a1 : ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) := by
    rw [← t1]; exact hs1.sum_le_tsum _ (fun j _ => pow_nonneg h0 j)
  have a2 : ∑ j ∈ range J, (j : ℝ) * r ^ j ≤ r / (1 - r) ^ 2 := by
    rw [← t2]; exact hs2.sum_le_tsum _ (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg h0 j))
  refine ⟨a1, ?_⟩
  have e : ∑ j ∈ range J, ((j : ℝ) + 1) * r ^ j =
      ∑ j ∈ range J, (j : ℝ) * r ^ j + ∑ j ∈ range J, r ^ j := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun j _ => by ring
  have h1r : 0 < 1 - r := by linarith
  have e2 : r / (1 - r) ^ 2 + 1 / (1 - r) = 1 / (1 - r) ^ 2 := by field_simp; ring
  rw [e]; linarith

/-- `√(2^{j+1} y) = √2^{j+1} √y`. -/
theorem sqrt_two_pow_mul (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    √(2 ^ (j + 1) * y) = √2 ^ (j + 1) * √y := by
  rw [Real.sqrt_mul (by positivity)]
  congr 1
  rw [show (2 : ℝ) ^ (j + 1) = (√2 ^ (j + 1)) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

/-- Partial sums of `E`. -/
theorem E_partial {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑ n ∈ range M, eTerm x n ≤
      1.94 ^ 2 * (Real.log x / 2 * (1.03883 * √x) + Real.log x * (1.4262 * √x)) +
        1.4262 * 2.32 ^ 2 * √2 * √x *
          (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + Real.log x * (1 / (1 - √2 / 4))) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set a : ℕ → ℕ := fun j => ⌊2 ^ j * x⌋₊ with ha
  have hamono : Monotone a := fun i k hik => Nat.floor_le_floor (by
    have : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hik
    nlinarith)
  have ha0 : a 0 = ⌊x⌋₊ := by simp [ha]
  have haM : M ≤ a M := by
    apply Nat.le_floor
    have h1 : (M : ℝ) ≤ 2 ^ M := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h2 : (2 : ℝ) ^ M ≤ 2 ^ M * x := le_mul_of_one_le_right (by positivity) hx
    linarith
  -- reduce to `Icc 1 (a M)`
  have hE0 : eTerm x 0 = 0 := by simp [eTerm]
  have hsub : range M ⊆ insert 0 (Icc 1 (a M)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact mem_insert_of_mem (mem_Icc.2 ⟨h, by have := mem_range.1 hn; omega⟩)
  have hstep1 : ∑ n ∈ range M, eTerm x n ≤ ∑ n ∈ Icc 1 (a M), eTerm x n := by
    refine (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => eTerm_nonneg x n).trans (le_of_eq ?_)
    rw [sum_insert (by simp), hE0, zero_add]
  have hXa : ⌊x⌋₊ ≤ a M := by rw [← ha0]; exact hamono (Nat.zero_le M)
  have hsplit : ∑ n ∈ Icc 1 (a M), eTerm x n =
      ∑ n ∈ Icc 1 ⌊x⌋₊, eTerm x n + ∑ n ∈ Ioc ⌊x⌋₊ (a M), eTerm x n := by
    rw [show Icc 1 (a M) = Ioc 0 (a M) from rfl, show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ from rfl,
      sum_Ioc_consecutive _ (Nat.zero_le _) hXa]
  -- the low part
  have hlow : ∑ n ∈ Icc 1 ⌊x⌋₊, eTerm x n ≤
      1.94 ^ 2 * (Real.log x / 2 * (1.03883 * √x) + Real.log x * (1.4262 * √x)) := by
    refine (sum_le_sum fun n hn => eTerm_low hx hn).trans ?_
    rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    have hψ : ∑ n ∈ Icc 1 ⌊x⌋₊, (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) ≤ 1.03883 * √x := by
      rw [← sum_filter]
      have hsub2 : (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ √x) ⊆ Icc 1 ⌊√x⌋₊ := by
        intro n hn
        have h := mem_filter.1 hn
        exact mem_Icc.2 ⟨(mem_Icc.1 h.1).1, Nat.le_floor h.2⟩
      refine (sum_le_sum_of_subset_of_nonneg hsub2 fun n _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg).trans ?_
      exact (Prelim.sum_vonMangoldt_lt (Real.sqrt_pos.2 hx0)).le
    have hNP : ∑ n ∈ Icc 1 ⌊x⌋₊, lamNP n ≤ 1.4262 * √x :=
      (Prelim.sum_vonMangoldt_nonprime_lt hx0).le
    have : Real.log x / 2 * ∑ n ∈ Icc 1 ⌊x⌋₊, (if (n : ℝ) ≤ √x then (Λ n : ℝ) else 0) +
        Real.log x * ∑ n ∈ Icc 1 ⌊x⌋₊, lamNP n ≤
        Real.log x / 2 * (1.03883 * √x) + Real.log x * (1.4262 * √x) := by
      have := mul_le_mul_of_nonneg_left hψ (by linarith : 0 ≤ Real.log x / 2)
      have := mul_le_mul_of_nonneg_left hNP hlx
      linarith
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  -- the dyadic part
  set r : ℝ := √2 / 4 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have : √2 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rw [hr]; linarith
  have hblock : ∀ j, ∑ n ∈ Ioc (a j) (a (j + 1)), eTerm x n ≤
      1.4262 * 2.32 ^ 2 * √2 * √x * (((j : ℝ) + 1) * Real.log 2 + Real.log x) * r ^ j := by
    intro j
    set K := (((j : ℝ) + 1) * Real.log 2 + Real.log x) * 2.32 ^ 2 / 4 ^ j with hK
    have hK0 : 0 ≤ K := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      positivity
    refine (sum_le_sum fun n hn => eTerm_block hx j hn).trans ?_
    rw [← sum_mul]
    have hsub3 : Ioc (a j) (a (j + 1)) ⊆ Icc 1 (a (j + 1)) := by
      intro n hn; have := mem_Ioc.1 hn; exact mem_Icc.2 ⟨by omega, this.2⟩
    have hs : ∑ n ∈ Ioc (a j) (a (j + 1)), lamNP n ≤ 1.4262 * √(2 ^ (j + 1) * x) := by
      refine (sum_le_sum_of_subset_of_nonneg hsub3 fun n _ _ => lamNP_nonneg n).trans ?_
      exact (Prelim.sum_vonMangoldt_nonprime_lt (y := 2 ^ (j + 1) * x) (by positivity)).le
    rw [sqrt_two_pow_mul j hx0.le] at hs
    calc (∑ n ∈ Ioc (a j) (a (j + 1)), lamNP n) * K ≤ 1.4262 * (√2 ^ (j + 1) * √x) * K :=
          mul_le_mul_of_nonneg_right hs hK0
      _ = 1.4262 * 2.32 ^ 2 * √2 * √x * (((j : ℝ) + 1) * Real.log 2 + Real.log x) * r ^ j := by
          rw [hK, hr, div_pow, pow_succ]
          field_simp
  have hhigh : ∑ n ∈ Ioc ⌊x⌋₊ (a M), eTerm x n ≤ 1.4262 * 2.32 ^ 2 * √2 * √x *
      (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + Real.log x * (1 / (1 - √2 / 4))) := by
    rw [← ha0, sum_Ioc_blocks _ a hamono M]
    refine (sum_le_sum fun j _ => hblock j).trans ?_
    obtain ⟨g1, g2⟩ := geom_sums_le hr0 hr1 M
    have e : ∑ j ∈ range M, 1.4262 * 2.32 ^ 2 * √2 * √x *
        (((j : ℝ) + 1) * Real.log 2 + Real.log x) * r ^ j =
        1.4262 * 2.32 ^ 2 * √2 * √x * (Real.log 2 * ∑ j ∈ range M, ((j : ℝ) + 1) * r ^ j +
          Real.log x * ∑ j ∈ range M, r ^ j) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun j _ => by ring
    rw [e]
    have hc : 0 ≤ 1.4262 * 2.32 ^ 2 * √2 * √x := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    have := mul_le_mul_of_nonneg_left g2 this
    have := mul_le_mul_of_nonneg_left g1 hlx
    rw [hr] at *
    linarith
  rw [hsplit] at hstep1
  linarith

/-- **[H, (14.28)], our constant**: `E ≤ 8·10⁻¹¹ x` for `x ≥ 4.9·10²⁶`. -/
theorem E_le_14_28 {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤ 8e-11 * x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have htsum := Real.tsum_le_of_sum_range_le (fun n => eTerm_nonneg x n) (E_partial hx1)
  refine le_trans (le_of_eq ?_) (htsum.trans ?_)
  · rfl
  set s := √x with hs
  set L := Real.log x with hL
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hs13 : (2.2135e13 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  -- `L/s ≤ 61.5/2.2135e13`
  have hLs : L / s ≤ 61.5 / 2.2135e13 := by
    have he2 : Real.exp 2 ≤ (4.9e26 : ℝ) := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]; nlinarith [Real.exp_pos 1]
    have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.2 he2) (Set.mem_Ici.2 (he2.trans hx)) hx
    simp only at hanti
    have hl : Real.log (4.9e26 : ℝ) ≤ 61.5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have h2 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
      have e : Real.exp 61.5 = Real.exp 1 ^ 61 * Real.exp (1 / 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : (2.7182818283 : ℝ) ^ 61 ≤ Real.exp 1 ^ 61 := pow_le_pow_left₀ (by norm_num) h1.le 61
      have h4 : (4.9e26 : ℝ) ≤ 2.7182818283 ^ 61 * 1.625 := by norm_num
      have h5 : (0 : ℝ) ≤ 2.7182818283 ^ 61 := by norm_num
      nlinarith
    have hsq : (2.2135e13 : ℝ) ≤ √(4.9e26 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
    have hlpos : 0 ≤ Real.log (4.9e26 : ℝ) := Real.log_nonneg (by norm_num)
    refine hanti.trans ?_
    calc Real.log (4.9e26 : ℝ) / √(4.9e26 : ℝ) ≤ 61.5 / √(4.9e26 : ℝ) :=
          div_le_div_of_nonneg_right hl (Real.sqrt_nonneg _)
      _ ≤ 61.5 / 2.2135e13 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  -- numerical constants
  have hsq2 : √2 ≤ 1.41422 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq2' : 1.41421 ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hl2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1 : 1 / (1 - √2 / 4) ≤ 1.54693 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hq2 : 1 / (1 - √2 / 4) ^ 2 ≤ 2.393 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hc0 : 1.4262 * 2.32 ^ 2 * √2 ≤ 10.8561 := by nlinarith
  have hc00 : 0 ≤ 1.4262 * 2.32 ^ 2 * √2 := by positivity
  have hq10 : 0 ≤ 1 / (1 - √2 / 4) := by
    have : 0 < 1 - √2 / 4 := by linarith
    positivity
  have hq20 : 0 ≤ 1 / (1 - √2 / 4) ^ 2 := by positivity
  -- `RHS ≤ s (24.12 L + 18.01)`
  have hA : 1.94 ^ 2 * (L / 2 * (1.03883 * s) + L * (1.4262 * s)) ≤ 7.3226 * (s * L) := by
    have : 0 ≤ s * L := mul_nonneg hs0.le hL0
    nlinarith
  have hB : 1.4262 * 2.32 ^ 2 * √2 * s *
      (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + L * (1 / (1 - √2 / 4))) ≤
      s * (10.8561 * (0.6931471808 * 2.393) + 10.8561 * 1.54693 * L) := by
    have h1 : Real.log 2 * (1 / (1 - √2 / 4) ^ 2) ≤ 0.6931471808 * 2.393 :=
      mul_le_mul hl2 hq2 hq20 (by norm_num)
    have h2 : L * (1 / (1 - √2 / 4)) ≤ 1.54693 * L := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hq1 hL0
    have h3 : 0 ≤ Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + L * (1 / (1 - √2 / 4)) := by positivity
    have h4 : 1.4262 * 2.32 ^ 2 * √2 *
        (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + L * (1 / (1 - √2 / 4))) ≤
        10.8561 * (0.6931471808 * 2.393 + 1.54693 * L) :=
      mul_le_mul hc0 (by linarith) h3 (by norm_num)
    have e : 1.4262 * 2.32 ^ 2 * √2 * s *
        (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + L * (1 / (1 - √2 / 4))) =
        s * (1.4262 * 2.32 ^ 2 * √2 *
        (Real.log 2 * (1 / (1 - √2 / 4) ^ 2) + L * (1 / (1 - √2 / 4)))) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h4 hs0.le
    linarith
  -- `s (a L + b) ≤ 8e-11 s²`
  have hLs' : L ≤ 61.5 / 2.2135e13 * s := by rwa [div_le_iff₀ hs0] at hLs
  have hfin : 7.3226 * (s * L) + s * (10.8561 * (0.6931471808 * 2.393) + 10.8561 * 1.54693 * L) ≤
      8e-11 * (s * s) := by
    have e : 7.3226 * (s * L) + s * (10.8561 * (0.6931471808 * 2.393) + 10.8561 * 1.54693 * L) =
        s * ((7.3226 + 10.8561 * 1.54693) * L + 10.8561 * (0.6931471808 * 2.393)) := by ring
    rw [e, show (8e-11 : ℝ) * (s * s) = s * (8e-11 * s) by ring]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    have : (7.3226 + 10.8561 * 1.54693) * L ≤ (7.3226 + 10.8561 * 1.54693) * (61.5 / 2.2135e13 * s) :=
      mul_le_mul_of_nonneg_left hLs' (by norm_num)
    nlinarith
  rw [← hss]
  linarith

end TernaryGoldbach.MinorArcs
