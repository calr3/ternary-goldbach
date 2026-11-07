import TernaryGoldbach.Ladder.Spec
import TernaryGoldbach.Ladder.Data

/-!
# A prime ladder up to `10²⁷`

`ladder_prime`: for `1 ≤ i ≤ 254638308` there is a prime in `[(S·i − 2047)·2⁴⁵ + 1, S·i·2⁴⁵ + 1]`,
`S = 111616`. The primes are Proth primes `(S·i − t)·2⁴⁵ + 1` with `0 ≤ t < 2048`, certified by
`3^((c−1)/2) ≡ −1 (mod c)`; the Lean kernel checks all of them (`Ladder/Check.lean`,
`Ladder/Data/`). Consecutive windows give primes less than `(S + 2047)·2⁴⁵ < 4·10¹⁸ − 4` apart, and
rung `254638308` lies above `10²⁷`. This is the prime ladder of [H, §1.6] (there [HP13], up to
`8.875·10³⁰`) for the range `n ≤ 10²⁷` that the small cases need.
-/

namespace TernaryGoldbach.Ladder

/-- **The prime ladder**: a prime in `[(111616 i − 2047)·2⁴⁵ + 1, 111616 i·2⁴⁵ + 1]` for
`1 ≤ i ≤ 254638308`. -/
theorem ladder_prime {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 254638308) :
    ∃ p, p.Prime ∧ (111616 * i - 2047) * 35184372088832 + 1 ≤ p ∧
      p ≤ 111616 * i * 35184372088832 + 1 := by
  obtain ⟨p, hp, h3, h4⟩ :=
    prime_of_runsOK runsOK_all (le_refl 1) (by norm_num) (by norm_num) h1 (by omega)
  rw [show (2 : ℕ) ^ 45 = 35184372088832 by norm_num] at h3 h4
  exact ⟨p, hp, h3, h4⟩

end TernaryGoldbach.Ladder
