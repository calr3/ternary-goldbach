import TernaryGoldbach.Helfgott.Inputs
import TernaryGoldbach.Ladder.Main

/-!
# The small cases `5 < n ≤ 10²⁷` from binary Goldbach and a prime ladder

For odd `n ≤ 4·10¹⁸ + 3`, `n = 3 + (n − 3)` and binary Goldbach up to `4·10¹⁸` (`binary_goldbach_input`,
[OeSHP14]) applies. For odd `4·10¹⁸ + 3 < n ≤ 10²⁷` the prime ladder (`Ladder.ladder_prime`,
`TernaryGoldbach/Ladder/`) gives a prime `p` with `n − 4·10¹⁸ ≤ p ≤ n − 4`: rung
`i = ⌊(n − 5)/(111616·2⁴⁵)⌋` has a prime in `[(111616 i − 2047)·2⁴⁵ + 1, 111616 i·2⁴⁵ + 1]`. Then
`n − p` is even, at least `4` and at most `4·10¹⁸`.

This is the argument of [H, §1.6], with a ladder of Proth primes up to `10²⁷` that the Lean kernel
checks in place of the Helfgott–Platt ladder [HP13].
-/

namespace TernaryGoldbach.Helfgott

variable [Fact TernaryGoldbach.BinaryGoldbachInput] in
/-- **Ternary Goldbach for odd `5 < n ≤ 10²⁷`**. -/
theorem ternaryGoldbachUpTo_1e27 : TernaryGoldbachUpTo (10 ^ 27) := by
  intro n hn h5 hle
  have hBG := binary_goldbach_input
  by_cases hsmall : n ≤ 4 * 10 ^ 18 + 3
  · -- `n = 3 + (n − 3)`
    have hev : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
    obtain ⟨p, q, hp, hq, hpq⟩ := hBG (n - 3) hev (by obtain ⟨k, hk⟩ := hn; omega) (by omega)
    exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩
  · -- a prime `p ∈ [n − 4·10¹⁸, n − 4]` from rung `i` of the ladder
    push Not at hsmall
    have hi1 : 1 ≤ (n - 5) / 3927138875067072512 := by omega
    have hi2 : (n - 5) / 3927138875067072512 ≤ 254638308 := by omega
    obtain ⟨p, hp, hp1, hp2⟩ := Ladder.ladder_prime hi1 hi2
    have hpb : p ≤ n - 4 := by omega
    have hpa : n - 4 * 10 ^ 18 ≤ p := by omega
    have hp2' : p ≠ 2 := by omega
    have hpo : Odd p := hp.odd_of_ne_two hp2'
    have hev : Even (n - p) := Nat.Odd.sub_odd hn hpo
    obtain ⟨q, r, hq, hr, hqr⟩ := hBG (n - p) hev (by omega) (by omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

end TernaryGoldbach.Helfgott
