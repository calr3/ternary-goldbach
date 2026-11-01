import TernaryGoldbach.Statement

/-!
# Primality certificates checked by the kernel

`4·10¹⁸ + 2 = 2000000000000001301 + 1999999999999998701` with both summands prime ([B, §1.6]).
This covers the one even number the prime ladder of [HP13] needs beyond the binary Goldbach
verification of [OeSHP14] (ladder gaps `≤ 4·10¹⁸` leave `n − p ≤ 4·10¹⁸ + 2`).

Primality is proved with Lucas's test (`lucas_primality`, i.e. Pratt certificates): modular
exponentiation by repeated squaring (`powModAux`, proved correct in `ZMod m`) is evaluated by
`decide +kernel` (the kernel's GMP arithmetic), so no extra axioms (no `native_decide`) are used.
-/

namespace TernaryGoldbach

/-- Modular exponentiation by repeated squaring: `acc · b^e mod m`, using at most `fuel` bits of `e`. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | fuel + 1, b, e, m, acc =>
    if e = 0 then acc
    else powModAux fuel (b * b % m) (e / 2) m (if e % 2 = 1 then acc * b % m else acc)

theorem powModAux_cast (m : ℕ) : ∀ (fuel b e acc : ℕ), e < 2 ^ fuel →
    ((powModAux fuel b e m acc : ℕ) : ZMod m) = (acc : ZMod m) * (b : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this; simp [powModAux]
  | succ fuel ih =>
    intro b e acc he
    rw [powModAux]
    split_ifs with h0 h1
    · subst h0; simp
    · rw [ih _ _ _ (by rw [pow_succ] at he; omega)]
      push_cast [ZMod.natCast_mod]
      conv_rhs => rw [← Nat.mod_add_div e 2, h1, pow_add, pow_mul]
      ring
    · rw [ih _ _ _ (by rw [pow_succ] at he; omega)]
      push_cast [ZMod.natCast_mod]
      have h2 : e % 2 = 0 := by omega
      conv_rhs => rw [← Nat.mod_add_div e 2, h2, pow_add, pow_mul]
      ring

theorem powModAux_lt {m : ℕ} (hm : 0 < m) : ∀ (fuel b e acc : ℕ), acc < m →
    powModAux fuel b e m acc < m := by
  intro fuel
  induction fuel with
  | zero => intro b e acc h; simpa [powModAux] using h
  | succ fuel ih =>
    intro b e acc h
    rw [powModAux]
    split_ifs with h0 h1
    · exact h
    · exact ih _ _ _ (Nat.mod_lt _ hm)
    · exact ih _ _ _ h

/-- **Lucas's primality test** with an explicit factorization `fs` of `p − 1` (a Pratt certificate). -/
theorem prime_of_lucas_cert (p a : ℕ) (fs : List ℕ) (hp : 1 < p) (hlt : p - 1 < 2 ^ 64)
    (hfs : ∀ q ∈ fs, q.Prime) (hprod : fs.prod = p - 1)
    (ha : powModAux 64 a (p - 1) p 1 = 1)
    (hd : ∀ q ∈ fs, powModAux 64 a ((p - 1) / q) p 1 ≠ 1) : p.Prime := by
  have hp0 : 0 < p := by omega
  have hcast : ∀ e, e < 2 ^ 64 → ((a : ZMod p) ^ e = 1 ↔ powModAux 64 a e p 1 = 1) := by
    intro e he
    rw [← one_mul ((a : ZMod p) ^ e), ← Nat.cast_one (R := ZMod p), ← powModAux_cast p 64 a e 1 he]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (powModAux_lt hp0 _ _ _ _ hp),
        Nat.mod_eq_of_lt hp] at hv
      exact hv
    · intro h; rw [h]
  refine lucas_primality p (a : ZMod p) ((hcast _ hlt).2 ha) ?_
  intro q hq hqd
  rw [← hprod] at hqd
  obtain ⟨f, hf, hqf⟩ := (Prime.dvd_prod_iff hq.prime).1 hqd
  have : q = f := (Nat.prime_dvd_prime_iff_eq hq (hfs f hf)).1 hqf
  subst this
  intro h
  exact hd q hf ((hcast _ (lt_of_le_of_lt (Nat.div_le_self _ _) hlt)).1 h)

theorem prime_25852339 : Nat.Prime 25852339 :=
  prime_of_lucas_cert 25852339 3 [2, 3, 3, 3, 478747] (by norm_num) (by norm_num)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem prime_1809663731 : Nat.Prime 1809663731 :=
  prime_of_lucas_cert 1809663731 6 [2, 5, 7, 25852339] (by norm_num) (by norm_num)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · exact prime_25852339)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem prime_952380952380953 : Nat.Prime 952380952380953 :=
  prime_of_lucas_cert 952380952380953 3 [2, 2, 2, 19, 23, 739, 1187, 310559] (by norm_num)
    (by norm_num)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem prime_2000000000000001301 : Nat.Prime 2000000000000001301 :=
  prime_of_lucas_cert 2000000000000001301 2 [2, 2, 3, 5, 5, 7, 952380952380953] (by norm_num)
    (by norm_num)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact prime_952380952380953 | norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem prime_1999999999999998701 : Nat.Prime 1999999999999998701 :=
  prime_of_lucas_cert 1999999999999998701 2 [2, 2, 5, 5, 11, 11, 149, 613, 1809663731]
    (by norm_num) (by norm_num)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact prime_1809663731 | norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

/-- `4·10¹⁸ + 2 = 2000000000000001301 + 1999999999999998701` ([B, §1.6]). -/
theorem isSumOfTwoPrimes_4e18_add_two : IsSumOfTwoPrimes (4 * 10 ^ 18 + 2) :=
  ⟨2000000000000001301, 1999999999999998701, prime_2000000000000001301,
    prime_1999999999999998701, by norm_num⟩

end TernaryGoldbach
