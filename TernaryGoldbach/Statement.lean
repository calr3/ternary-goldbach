import Mathlib

/-!
# Statements

The ternary Goldbach conjecture (Helfgott's theorem): every odd integer `n > 5` is a sum of
three primes.  We also define the finite-range versions of the binary and ternary statements
that appear in the reduction of the small cases to numerical verification.
-/

namespace TernaryGoldbach

/-- `n` is a sum of three primes. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- `n` is a sum of two primes. -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- The ternary Goldbach conjecture: every odd `n > 5` is a sum of three primes. -/
def Statement : Prop :=
  ∀ n : ℕ, Odd n → 5 < n → IsSumOfThreePrimes n

/-- Binary Goldbach verified up to `N`: every even `n` with `4 ≤ n ≤ N` is a sum of two primes. -/
def BinaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → n ≤ N → IsSumOfTwoPrimes n

/-- Ternary Goldbach for odd `n` with `5 < n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, Odd n → 5 < n → n ≤ N → IsSumOfThreePrimes n

/-- Ternary Goldbach for odd `n ≥ C`. -/
def TernaryGoldbachFrom (C : ℕ) : Prop :=
  ∀ n : ℕ, Odd n → C ≤ n → IsSumOfThreePrimes n

/-- A finite verification and an asymptotic result with matching ranges give the full
statement. -/
theorem statement_of_upTo_of_from {C : ℕ} (h₁ : TernaryGoldbachUpTo C)
    (h₂ : TernaryGoldbachFrom C) : Statement := by
  intro n hn h5
  rcases le_or_gt C n with h | h
  · exact h₂ n hn h
  · exact h₁ n hn h5 h.le

/-! ## Hypotheses

The proof rests on two published numerical results, stated here as `Prop`s and passed to the
theorems that need them as `Fact` instances. Each is a large computation, and neither
is formalized. -/

/-- D. Platt [Plab, Thm 7.1], [H, §9.6]: for every primitive character `χ` of conductor `q`, GRH
holds for `L(s, χ)` up to height `10⁸/q` if `q ≤ 3·10⁵` is odd, and up to height
`max(10⁸/q, 200 + 7.5·10⁷/q)` if `q ≤ 4·10⁵` is even. -/
def PlattGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    (Odd q → q ≤ 300000 → ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1e8 / q → ρ.re = 1 / 2) ∧
    (Even q → q ≤ 400000 → ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ max (1e8 / q : ℝ) (200 + 7.5e7 / q) → ρ.re = 1 / 2)

/-- [OeSHP] Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014): every even `4 ≤ n ≤ 4·10¹⁸` is
a sum of two primes. -/
def BinaryGoldbachInput : Prop := BinaryGoldbachUpTo (4 * 10 ^ 18)

/-! ## Proved inputs

`RamareMoebius` is not a hypothesis: `Prelim.ramareMoebius_of_plattGRH` (`Prelim/RamareMoebius.lean`)
proves it from `PlattGRH`, by Helfgott's formalization of `mobius003.tex` (vendored from
Garald1/RSBounds). Inside the development it is still passed as a `Fact` instance, which
`Prelim/RamareMoebius.lean` provides from `Fact PlattGRH`. -/

/-- O. Ramaré, Acta Arith. 157 (2013), Cor. 1.4, as cited in [H, (2.21)]:
`|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`. Proved from `PlattGRH`
(`Prelim.ramareMoebius_of_plattGRH`). -/
def RamareMoebius : Prop :=
  ∀ x : ℝ, 11815 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| ≤ 0.03 / Real.log x

end TernaryGoldbach
