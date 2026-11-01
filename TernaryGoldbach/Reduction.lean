import TernaryGoldbach.Statement

/-!
# Reducing the small cases of ternary Goldbach to binary Goldbach and a prime ladder

Helfgott's analytic argument proves ternary Goldbach for odd `n ≥ C` with `C ≈ 10²⁷`.
Below `C` he uses the classical reduction: if binary Goldbach is known for even numbers up
to `N`, and there is a "ladder" of primes `3 = p₀ < p₁ < ⋯ < p_k` with consecutive gaps at
most `N - 4`, then every odd `n` with `7 ≤ n ≤ p_k + 4` is a sum of three primes.  (Pick the
largest `pᵢ ≤ n - 4`; then `n - pᵢ` is even and lies in `[4, N]`.)

Helfgott–Platt used `N = 4 · 10¹⁸` (Oliveira e Silva–Herzog–Pardi) and a ladder of
certified primes reaching beyond `8.8 · 10³⁰`.

Everything in this file is proved, with no `sorry`.
-/

namespace TernaryGoldbach

/-- If every `m ∈ [3, M]` is within `N - 4` above some odd prime `p ≤ m`, and binary Goldbach
holds up to `N ≥ 4`, then ternary Goldbach holds up to `M + 4`. -/
theorem ternaryUpTo_of_primeCover {N M : ℕ} (hN4 : 4 ≤ N) (hN : BinaryGoldbachUpTo N)
    (hcover : ∀ m, 3 ≤ m → m ≤ M → ∃ p, p.Prime ∧ Odd p ∧ p ≤ m ∧ m ≤ p + (N - 4)) :
    TernaryGoldbachUpTo (M + 4) := by
  intro n hn h5 hnM
  have h7 : 7 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  obtain ⟨p, hp, hpodd, hpm, hmp⟩ := hcover (n - 4) (by omega) (by omega)
  have hev : Even (n - p) := Nat.Odd.sub_odd hn hpodd
  obtain ⟨q, r, hq, hr, hqr⟩ := hN (n - p) hev (by omega) (by omega)
  exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-- The step relation of a prime ladder with maximum gap `g`. -/
def LadderStep (g : ℕ) (a b : ℕ) : Prop := a ≤ b ∧ b ≤ a + g

/-- Every `m` between the bottom and top rungs of a ladder with gaps `≤ g` is at most `g`
above some rung that is `≤ m`. -/
theorem exists_rung_of_chain {g : ℕ} :
    ∀ (a : ℕ) (l : List ℕ), List.IsChain (LadderStep g) (a :: l) →
      ∀ m, a ≤ m → m ≤ (a :: l).getLast (List.cons_ne_nil _ _) →
        ∃ p ∈ a :: l, p ≤ m ∧ m ≤ p + g := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ m ham hmL
    simp only [List.getLast_singleton] at hmL
    exact ⟨a, List.mem_singleton_self a, ham, by omega⟩
  | cons b l ih =>
    intro hc m ham hmL
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨hab, hba⟩, hc⟩ := hc
    rcases lt_or_ge m b with hmb | hbm
    · exact ⟨a, List.mem_cons_self, ham, by omega⟩
    · rw [List.getLast_cons (List.cons_ne_nil _ _)] at hmL
      obtain ⟨p, hp, hpm, hmp⟩ := ih b hc m hbm hmL
      exact ⟨p, List.mem_cons_of_mem _ hp, hpm, hmp⟩

/-- **Small-case reduction.**  Binary Goldbach up to `N ≥ 4` together with a ladder of odd
primes `3 = p₀ ≤ p₁ ≤ ⋯ ≤ p_k` with consecutive gaps `≤ N - 4` gives ternary Goldbach for all
odd `n` with `5 < n ≤ p_k + 4`. -/
theorem ternaryUpTo_of_ladder {N : ℕ} (hN4 : 4 ≤ N) (hN : BinaryGoldbachUpTo N)
    (l : List ℕ) (hprime : ∀ p ∈ 3 :: l, p.Prime ∧ Odd p)
    (hchain : List.IsChain (LadderStep (N - 4)) (3 :: l)) :
    TernaryGoldbachUpTo ((3 :: l).getLast (List.cons_ne_nil _ _) + 4) := by
  apply ternaryUpTo_of_primeCover hN4 hN
  intro m h3m hmM
  obtain ⟨p, hpL, hpm, hmp⟩ := exists_rung_of_chain 3 l hchain m h3m hmM
  exact ⟨p, (hprime p hpL).1, (hprime p hpL).2, hpm, hmp⟩

/-- With gaps `≤ g` and `g ≥ 1`: every `m` between the bottom and top rungs is less than `g` above
some rung that is `≤ m`. -/
theorem exists_rung_of_chain_lt {g : ℕ} (hg : 1 ≤ g) :
    ∀ (a : ℕ) (l : List ℕ), List.IsChain (LadderStep g) (a :: l) →
      ∀ m, a ≤ m → m ≤ (a :: l).getLast (List.cons_ne_nil _ _) →
        ∃ p ∈ a :: l, p ≤ m ∧ m < p + g := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ m ham hmL
    simp only [List.getLast_singleton] at hmL
    exact ⟨a, List.mem_singleton_self a, ham, by omega⟩
  | cons b l ih =>
    intro hc m ham hmL
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨hab, hba⟩, hc⟩ := hc
    rcases lt_or_ge m b with hmb | hbm
    · exact ⟨a, List.mem_cons_self, ham, by omega⟩
    · rw [List.getLast_cons (List.cons_ne_nil _ _)] at hmL
      obtain ⟨p, hp, hpm, hmp⟩ := ih b hc m hbm hmL
      exact ⟨p, List.mem_cons_of_mem _ hp, hpm, hmp⟩

/-- **Small-case reduction, as in [B, §1.6].**  Binary Goldbach up to an even `N ≥ 4`, a
decomposition of `N + 2` into two primes, and a ladder of odd primes `3 = p₀ ≤ p₁ ≤ ⋯ ≤ p_k`
with consecutive gaps `≤ N` give ternary Goldbach for all odd `n` with `5 < n ≤ p_k + 4`.
(For the largest rung `p ≤ n − 4`, `n − p` is even and lies in `[4, N + 2]`.) -/
theorem ternaryUpTo_of_ladder_two {N : ℕ} (hN4 : 4 ≤ N) (hNe : Even N)
    (hN : BinaryGoldbachUpTo N) (hN2 : IsSumOfTwoPrimes (N + 2))
    (l : List ℕ) (hprime : ∀ p ∈ 3 :: l, p.Prime ∧ Odd p)
    (hchain : List.IsChain (LadderStep N) (3 :: l)) :
    TernaryGoldbachUpTo ((3 :: l).getLast (List.cons_ne_nil _ _) + 4) := by
  intro n hn h5 hnM
  have h7 : 7 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  obtain ⟨p, hpL, hpm, hmp⟩ :=
    exists_rung_of_chain_lt (by omega) 3 l hchain (n - 4) (by omega) (by omega)
  obtain ⟨hp, hpodd⟩ := hprime p hpL
  have hev : Even (n - p) := Nat.Odd.sub_odd hn hpodd
  have hcases : n - p ≤ N ∨ n - p = N + 2 := by
    obtain ⟨a, ha⟩ := hev
    obtain ⟨b, hb⟩ := hNe
    omega
  rcases hcases with h | h
  · obtain ⟨q, r, hq, hr, hqr⟩ := hN (n - p) hev (by omega) h
    exact ⟨p, q, r, hp, hq, hr, by omega⟩
  · obtain ⟨q, r, hq, hr, hqr⟩ := hN2
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

end TernaryGoldbach
