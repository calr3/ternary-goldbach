import TernaryGoldbach.Helfgott.Inputs
import TernaryGoldbach.Helfgott.Numerics
import TernaryGoldbach.Helfgott.SmallCases

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Assembling Helfgott's proof

This file derives the ternary Goldbach conjecture from the inputs in
`TernaryGoldbach.Helfgott.Inputs` and `SmallCases.lean`. There is no `sorry`; `#print axioms ternary_goldbach`
lists only Lean's three standard axioms. The hypotheses (`Fact` instances) are checked against their
sources in `HYPOTHESES.md`.

The argument follows [H13, §7.4]:

1. the weighted count equals `∫ = ∫_𝔐 + ∫_𝔪`;
2. `Re ∫_𝔐 ≥ 1.049 x²/κ` and `|∫_𝔪| ≤ ∫_𝔪 |S_{η_*}||S_{η₊}|² ≤ 1.0376 x²/κ`;
3. so the count restricted to odd primes is `≥ 0.0114 x²/κ - 6.7·10⁶ N^{3/2} log N > 0`;
4. a positive count over primes gives a representation;
5. the cases `N < 10²⁷` follow from binary Goldbach up to `4·10¹⁸` and the bounds for `θ`
   (`ternaryGoldbachUpTo_1e27`, `SmallCases.lean`).
-/

open Complex MeasureTheory ArithmeticFunction

namespace TernaryGoldbach.Helfgott

/-- Steps 1–2: the full weighted count is at least `(1.049 - 1.0376) x²/κ`. -/
theorem repSum_lower_bound (N : ℕ) (hN : Odd N) (hN27 : 10 ^ 27 ≤ N) :
    (1.049 - 1.0376) * xOf N ^ 2 / κ ≤ repSum (fun _ => True) N := by
  set M := majorArcs 8 r₀ (xOf N)
  obtain ⟨hint, hid⟩ := circle_identity_input N (by omega)
  have hsplit := integral_inter_add_sdiff (measurableSet_majorArcs 8 r₀ (xOf N)) hint
  have hmaj := major_arcs_input N hN hN27
  have hmin := minor_arcs_input N hN27
  -- The minor arc contribution is bounded by the integral of the norm.
  have hnorm : ‖∫ α in Set.Ioc (0:ℝ) 1 \ M, integrand N α‖ ≤ 1.0376 * xOf N ^ 2 / κ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ hmin)
    refine setIntegral_congr_fun (measurableSet_Ioc.diff (measurableSet_majorArcs _ _ _)) ?_
    intro α _
    simp only [integrand, norm_mul, norm_pow, norm_e, mul_one]
    ring
  have hre : repSum (fun _ => True) N =
      (∫ α in Set.Ioc (0:ℝ) 1 ∩ M, integrand N α).re +
        (∫ α in Set.Ioc (0:ℝ) 1 \ M, integrand N α).re := by
    rw [← Complex.add_re, hsplit, hid, ofReal_re]
  have := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hnorm)
  rw [hre]
  simp only [κ, M] at hmaj this ⊢
  linarith

open Classical in
/-- Step 4: a nonzero count over a set of primes gives a representation. -/
theorem isSumOfThreePrimes_of_repSum_ne_zero {P : ℕ → Prop} (hP : ∀ n, P n → n.Prime)
    (N : ℕ) (h : repSum P N ≠ 0) : IsSumOfThreePrimes N := by
  unfold repSum at h
  obtain ⟨n₁, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨n₂, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨n₃, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  · exact ⟨n₁, n₂, n₃, hP _ hc.2.1, hP _ hc.2.2.1, hP _ hc.2.2.2, hc.1⟩
  · exact absurd rfl h

/-- **Helfgott's theorem for large `N`**: every odd `N ≥ 10²⁷` is a sum of three primes
(in fact of three odd primes). -/
theorem ternaryGoldbachFrom : TernaryGoldbachFrom (10 ^ 27) := by
  intro N hN hN27
  have h1 := repSum_lower_bound N hN hN27
  have h2 := nonprime_input N hN27
  have h3 := final_inequality_crude N hN27
  apply isSumOfThreePrimes_of_repSum_ne_zero (P := fun n => n.Prime ∧ Odd n) (fun n h => h.1)
  intro h0
  linarith

omit [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.RamareMoebius] in
/-- The small cases: ternary Goldbach for odd `5 < N ≤ 10²⁷` (`SmallCases.lean`). -/
theorem ternaryGoldbachUpTo [Fact TernaryGoldbach.BinaryGoldbachInput] :
    TernaryGoldbachUpTo (10 ^ 27) := ternaryGoldbachUpTo_1e27

end TernaryGoldbach.Helfgott

namespace TernaryGoldbach

variable [Fact BinaryGoldbachInput]

/-- **The ternary Goldbach conjecture** (Helfgott, 2013): every odd integer greater than `5`
is a sum of three primes.

It depends on the four hypotheses of `Statement.lean`, passed as `Fact` instances (see
`MainTheorems.lean` for the version with explicit hypotheses). -/
theorem ternary_goldbach : Statement :=
  statement_of_upTo_of_from Helfgott.ternaryGoldbachUpTo Helfgott.ternaryGoldbachFrom

end TernaryGoldbach
