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
  rcases le_or_lt C n with h | h
  · exact h₂ n hn h
  · exact h₁ n hn h5 h.le

end TernaryGoldbach
