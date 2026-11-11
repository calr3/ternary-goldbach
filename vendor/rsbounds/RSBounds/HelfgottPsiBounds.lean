import RSBounds.RosserSchoenfeld1975
import RSBounds.Schoenfeld1976TargetsExtra

/-!
# [H, (2.14)] and [H, (2.17)] with Helfgott's constants

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. The formalization
`calr3/ternary-goldbach` proves (2.14) and (2.17) for `y ≥ 2.5·10⁷` with the constants `1.0064`
and `1.022` (`Prelim.sum_vonMangoldt_le_a14`, `Prelim.sum_vonMangoldt_mul_lt_a17` on its `main`,
2026-11-07); its docstrings give [H]'s constants as `1.0004` and `1.0008`. This file proves
both statements, in that formalization's form, with [H]'s constants:

* `sum_vonMangoldt_le_a14`: `∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2.5·10⁷`
  (`psi_le_10004` gives it from `y ≥ 4·10⁶`);
* `sum_vonMangoldt_mul_lt_a17`: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y ≥ 2.5·10⁷`.

Inputs: PsiCert (`|ψ(x) − x| ≤ 0.8√x` for `1500 ≤ x ≤ 10¹⁰`, an explicit hypothesis here,
discharged in `HelfgottPsiBoundsFinal`) and the RS75 `b = 23` row
`RosserSchoenfeld1975.psi_error_b23` (`|ψ(x) − x| < 0.00020211 x` for `x ≥ e²³`), which assumes
`FiniteRH 1894438.5122`. That premise is implied by RH up to any larger height
(`Goals.FiniteRH.mono`), e.g. by the formalization's `RHBelow 1e8`, which is the same formula.

(2.17) comes from summation by parts at integers,
`∑_{n ≤ N} Λ(n) n = N ψ(N) − ∑_{n < N} ψ(n)`, with `n − ψ(n) ≤ 1500 + 0.8√N (+ 0.00020211 n)`
for `n ≤ N`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.HelfgottPsiBounds

open Goals

theorem exp_23_le : Real.exp 23 ≤ 10 ^ 10 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 23 ≤ (2.7182818286 : ℝ) ^ 23 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h.le 23
    _ ≤ 10 ^ 10 := by norm_num

/-- The formalization's form of `ψ`. -/
theorem sum_Icc_eq_psi (y : ℝ) : ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) = Chebyshev.psi y := by
  rw [Chebyshev.psi]
  congr 1

theorem psi_succ (n : ℕ) :
    Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi (n : ℝ) + Λ (n + 1) := by
  rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast,
    Finset.sum_Ioc_succ_top (Nat.zero_le n)]

theorem sqrt_ge {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 ≤ x) : c ≤ √x := by
  calc c = √(c ^ 2) := (Real.sqrt_sq hc).symm
    _ ≤ √x := Real.sqrt_le_sqrt h

/-- **(2.14) from `4·10⁶`**: `ψ(y) ≤ 1.0004 y`. -/
theorem psi_le_10004 (hcert : Schoenfeld1976.PsiCert) (hRH : FiniteRH 1894438.5122) {y : ℝ}
    (hy : 4e6 ≤ y) : Chebyshev.psi y ≤ 1.0004 * y := by
  rcases le_or_gt y (10 ^ 10) with h | h
  · have hc := (abs_le.1 (hcert y (by linarith) h)).2
    have hs : 2000 ≤ √y := sqrt_ge (by norm_num) (by norm_num; linarith)
    have hss : √y * √y = y := Real.mul_self_sqrt (by linarith)
    have hm := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg y)
    linarith
  · have hb := (abs_lt.1 (RosserSchoenfeld1975.psi_error_b23 hRH y (exp_23_le.trans h.le))).2
    linarith

/-- **[H, (2.14)]** with [H]'s constant, in the formalization's form:
`∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2.5·10⁷`. -/
theorem sum_vonMangoldt_le_a14 (hcert : Schoenfeld1976.PsiCert) (hRH : FiniteRH 1894438.5122)
    {y : ℝ} (hy : 2.5e7 ≤ y) : ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
  rw [sum_Icc_eq_psi]
  exact psi_le_10004 hcert hRH (by linarith)

/-! ### (2.17) -/

/-- Summation by parts: `∑_{n ≤ N} Λ(n) n = N ψ(N) − ∑_{n < N} ψ(n)`. -/
theorem sum_mul_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) * n =
      N * Chebyshev.psi (N : ℝ) - ∑ n ∈ range N, Chebyshev.psi (n : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, psi_succ]
    push_cast
    ring

theorem sum_range_cast (N : ℕ) : ∑ n ∈ range N, (n : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `n − ψ(n) ≤ 1500 + 0.8√N` for `n ≤ N`, `n ≤ 10¹⁰`. -/
theorem gap_le_small (hcert : Schoenfeld1976.PsiCert) {n N : ℕ} (hn : n ≤ N)
    (h10 : (n : ℝ) ≤ 10 ^ 10) :
    (n : ℝ) - Chebyshev.psi n ≤ 1500 + 4 / 5 * √(N : ℝ) := by
  have hsN : √(n : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hs0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  rcases lt_or_ge (n : ℝ) 1500 with h | h
  · have := Chebyshev.psi_nonneg (n : ℝ)
    linarith
  · have hc := (abs_le.1 (hcert n h h10)).1
    linarith

/-- `n − ψ(n) ≤ 1500 + 0.8√N + 0.00020211 n` for `n ≤ N`. -/
theorem gap_le (hcert : Schoenfeld1976.PsiCert) (hRH : FiniteRH 1894438.5122) {n N : ℕ}
    (hn : n ≤ N) :
    (n : ℝ) - Chebyshev.psi n ≤ 1500 + 4 / 5 * √(N : ℝ) + 0.00020211 * n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt (n : ℝ) (10 ^ 10) with h | h
  · have := gap_le_small hcert hn h
    linarith
  · have hb := (abs_lt.1 (RosserSchoenfeld1975.psi_error_b23 hRH n (exp_23_le.trans h.le))).1
    have hs0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    linarith

/-- **[H, (2.17)]** with [H]'s constant, in the formalization's form:
`∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y ≥ 2.5·10⁷`. -/
theorem sum_vonMangoldt_mul_lt_a17 (hcert : Schoenfeld1976.PsiCert)
    (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  set N := ⌊y⌋₊ with hNdef
  have hN : 25000000 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNR : (25000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) < N := by linarith
  have hy2 : (N : ℝ) * N ≤ y ^ 2 := by nlinarith
  set s := √(N : ℝ) with hsdef
  have hss : s * s = N := Real.mul_self_sqrt hN0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hparts := sum_mul_eq N
  have hgauss := sum_range_cast N
  have hsplit : ∑ n ∈ range N, Chebyshev.psi (n : ℝ) =
      ∑ n ∈ range N, (n : ℝ) - ∑ n ∈ range N, ((n : ℝ) - Chebyshev.psi n) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hparts, hsplit, hgauss]
  rcases le_or_gt (N : ℝ) (10 ^ 10) with h | h
  · -- `N ≤ 10¹⁰`: PsiCert throughout
    have hψ := (abs_le.1 (hcert N (by linarith) h)).2
    have hgap : ∑ n ∈ range N, ((n : ℝ) - Chebyshev.psi n) ≤ N * (1500 + 4 / 5 * s) := by
      have := Finset.sum_le_card_nsmul (range N) (fun n : ℕ => (n : ℝ) - Chebyshev.psi n)
        (1500 + 4 / 5 * s) (fun n hn => gap_le_small hcert (Finset.mem_range.1 hn).le
          (le_trans (by exact_mod_cast (Finset.mem_range.1 hn).le) h))
      simpa only [Finset.card_range, nsmul_eq_mul] using this
    have hs : 5000 ≤ s := sqrt_ge (by norm_num) (by norm_num; linarith)
    have hm : 5000 * s ≤ N := by nlinarith
    have hkey : (N : ℝ) * (1500.5 + 8 / 5 * s) < N * (0.0004 * N) :=
      mul_lt_mul_of_pos_left (by linarith) hN0
    have hψN : (N : ℝ) * Chebyshev.psi N ≤ N * (N + 4 / 5 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0.le
    linarith
  · -- `N > 10¹⁰`: PsiCert to `10¹⁰`, the RS75 row beyond
    have hψ := (abs_lt.1 (RosserSchoenfeld1975.psi_error_b23 hRH N (exp_23_le.trans h.le))).2
    have hgap : ∑ n ∈ range N, ((n : ℝ) - Chebyshev.psi n) ≤
        N * (1500 + 4 / 5 * s) + 0.00020211 * (N * (N - 1) / 2) := by
      calc ∑ n ∈ range N, ((n : ℝ) - Chebyshev.psi n)
          ≤ ∑ n ∈ range N, ((1500 + 4 / 5 * s) + 0.00020211 * (n : ℝ)) :=
            Finset.sum_le_sum fun n hn => gap_le hcert hRH (Finset.mem_range.1 hn).le
        _ = N * (1500 + 4 / 5 * s) + 0.00020211 * (N * (N - 1) / 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_cast, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
    have hs : 100000 ≤ s := sqrt_ge (by norm_num) (by linarith)
    have hm : 100000 * s ≤ N := by nlinarith
    have hkey : (N : ℝ) * (1500.5 + 4 / 5 * s) < N * (0.000096835 * N) :=
      mul_lt_mul_of_pos_left (by linarith) hN0
    have hψN : (N : ℝ) * Chebyshev.psi N ≤ N * (N + 0.00020211 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0.le
    linarith

end TernaryGoldbach.RSBounds.HelfgottPsiBounds
