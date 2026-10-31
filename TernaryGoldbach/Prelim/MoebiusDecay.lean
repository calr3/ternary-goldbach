import TernaryGoldbach.Prelim.MertensProduct

/-!
# `∑_{n ≤ x} μ(n)/n` from the error term of `∑ Λ(n)/n`

For every constant `c`, `m(x)(log x + c) = −∑_{n ≤ x} μ(n)/n · (E(x/n) − c)` where
`m(x) = ∑_{n≤x} μ(n)/n` and `E(y) = ∑_{n≤y} Λ(n)/n − log y` (`E₁Λ`).  (From `μ log = −Λ ∗ μ`.)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-- `μ · log = −Λ ∗ μ`. -/
theorem pmul_moebius_log :
    pmul (μ : ArithmeticFunction ℝ) log = -(Λ * (μ : ArithmeticFunction ℝ)) := by
  have h1 : pmul (μ : ArithmeticFunction ℝ) log * (ζ : ArithmeticFunction ℝ) = -Λ := by
    ext n
    rw [coe_mul_zeta_apply, ArithmeticFunction.neg_apply]
    simp only [pmul_apply, intCoe_apply, log_apply]
    exact sum_moebius_mul_log_eq
  calc pmul (μ : ArithmeticFunction ℝ) log
      = pmul (μ : ArithmeticFunction ℝ) log * ((ζ : ArithmeticFunction ℝ) * μ) := by
        rw [coe_zeta_mul_coe_moebius, mul_one]
    _ = -(Λ * (μ : ArithmeticFunction ℝ)) := by rw [← mul_assoc, h1, neg_mul]

theorem moebius_conv_vonMangoldt (k : ℕ) :
    ∑ x ∈ k.divisorsAntidiagonal, (μ x.1 : ℝ) * Λ x.2 = -((μ k : ℝ) * Real.log k) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f k) pmul_moebius_log
  simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply] at h
  rw [h, neg_neg, mul_comm Λ, mul_apply]
  simp only [intCoe_apply]

/-- **The identity**: `m(x)(log x + c) = −∑_{n ≤ x} μ(n)/n (E(x/n) − c)`. -/
theorem mlog_identity {x : ℝ} (hx : 1 ≤ x) (c : ℝ) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) * (Real.log x + c) =
      -∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * (E₁Λ (x / n) - c) := by
  set N := ⌊x⌋₊ with hN
  have hx0 : 0 < x := by linarith
  -- `∑ μ(n)/n ψ̃(x/n) = −∑ μ(k) log k / k`
  let f : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (Λ n : ℝ) / n, by simp⟩
  have hconv := sum_Ioc_mul_eq_sum_sum f g N
  have hfg : ∀ k ∈ Ioc 0 N, (f * g) k = -((μ k : ℝ) * Real.log k) / k := by
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Ioc.1 hk).1; omega
    rw [mul_apply, ← moebius_conv_vonMangoldt, sum_div]
    refine sum_congr rfl fun y hy => ?_
    have hy' := Nat.mem_divisorsAntidiagonal.1 hy
    have h1 : (y.1 : ℝ) ≠ 0 := by
      have : y.1 ≠ 0 := fun h => hk0 (by rw [← hy'.1, h, zero_mul])
      exact_mod_cast this
    have h2 : (y.2 : ℝ) ≠ 0 := by
      have : y.2 ≠ 0 := fun h => hk0 (by rw [← hy'.1, h, mul_zero])
      exact_mod_cast this
    have hk : (k : ℝ) = y.1 * y.2 := by exact_mod_cast hy'.1.symm
    show (μ y.1 : ℝ) / y.1 * ((Λ y.2 : ℝ) / y.2) = (μ y.1 : ℝ) * Λ y.2 / k
    rw [hk]; field_simp
  have hpsi : ∑ n ∈ Ioc 0 N, (μ n : ℝ) / n * ∑ d ∈ Ioc 0 (N / n), (Λ d : ℝ) / d =
      -∑ k ∈ Ioc 0 N, (μ k : ℝ) * Real.log k / k := by
    rw [← sum_neg_distrib]
    have := hconv
    simp only [f, g, coe_mk] at this
    rw [← this]
    refine sum_congr rfl fun k hk => ?_
    rw [hfg k hk, neg_div]
  -- expand `E(x/n)`
  have hE : ∀ n ∈ Icc 1 N, E₁Λ (x / n) =
      ∑ d ∈ Ioc 0 (N / n), (Λ d : ℝ) / d - (Real.log x - Real.log n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    simp only [E₁Λ]
    rw [Nat.floor_div_natCast, Real.log_div hx0.ne' hn0.ne']
  have hsplit : ∑ n ∈ Icc 1 N, (μ n : ℝ) / n * (E₁Λ (x / n) - c) =
      ∑ n ∈ Ioc 0 N, (μ n : ℝ) / n * ∑ d ∈ Ioc 0 (N / n), (Λ d : ℝ) / d -
        (Real.log x + c) * ∑ n ∈ Icc 1 N, (μ n : ℝ) / n +
        ∑ k ∈ Ioc 0 N, (μ k : ℝ) * Real.log k / k := by
    rw [mul_sum, show Icc 1 N = Ioc 0 N from rfl, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [hE n hn]; ring
  rw [hsplit, hpsi]; ring

end TernaryGoldbach.Prelim
