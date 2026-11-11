/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RSBounds.LambdaCert.Tables

/-!
# The sieve masks

For a segment `[L, L + B)`, bit `i` of `compMask L B` is set iff `L + i` is a multiple `m ≥ 2p` of
some `p ∈ smallPrimes`; every `q` of `hpList` in the segment has its bit set in `hpMask L B`.
Consequently (for `2 ≤ L + i ≤ 2^20`): an unset sieve bit means `L + i` is prime, and a set sieve
bit together with an unset `hpList` bit means `L + i` is not a prime power.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

/-- `∑_{t < c} 2^(t p)`, recursively. -/
def geomR (p : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => 2 ^ p * geomR p c + 1

theorem geomR_mul (p : Nat) : ∀ c, (2 ^ p - 1) * geomR p c + 1 = 2 ^ (c * p)
  | 0 => by simp [geomR]
  | c + 1 => by
    have ih := geomR_mul p c
    have hu : 2 ^ p = (2 ^ p - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    calc (2 ^ p - 1) * geomR p (c + 1) + 1 = (2 ^ p - 1) * (2 ^ p * geomR p c + 1) + 1 := rfl
      _ = 2 ^ p * ((2 ^ p - 1) * geomR p c + 1) := by
          generalize 2 ^ p - 1 = v at hu ⊢
          rw [hu]; ring
      _ = 2 ^ p * 2 ^ (c * p) := by rw [ih]
      _ = 2 ^ ((c + 1) * p) := by rw [← pow_add]; ring_nf

theorem geom_eq (p c : Nat) (hp : 1 ≤ p) : geom p c = geomR p c := by
  have h := geomR_mul p c
  have hpos : 0 < 2 ^ p - 1 := by
    have : 2 ≤ 2 ^ p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  unfold geom
  rw [show 2 ^ (c * p) - 1 = (2 ^ p - 1) * geomR p c by omega]
  exact Nat.mul_div_cancel_left _ hpos

theorem testBit_geomR (p : Nat) (hp : 1 ≤ p) :
    ∀ c i, (geomR p c).testBit i = true ↔ p ∣ i ∧ i / p < c
  | 0, i => by simp [geomR]
  | c + 1, i => by
    have ih := testBit_geomR p hp c
    have h1 : 1 < 2 ^ p := Nat.one_lt_two_pow (by omega)
    show (2 ^ p * geomR p c + 1).testBit i = true ↔ _
    rw [Nat.testBit_two_pow_mul_add _ h1]
    by_cases hi : i < p
    · simp only [hi, ↓reduceIte, Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · rintro rfl; simp
      · rintro ⟨hd, _⟩
        exact Nat.eq_zero_of_dvd_of_lt hd hi
    · simp only [hi, ↓reduceIte]
      rw [ih]
      have hpi : p ≤ i := by omega
      have e : i = (i - p) + p := by omega
      have hdiv : i / p = (i - p) / p + 1 := by
        conv_lhs => rw [e]
        exact Nat.add_div_right _ (by omega)
      constructor
      · rintro ⟨hd, hlt⟩
        refine ⟨?_, by omega⟩
        rw [e]; exact Nat.dvd_add hd (dvd_refl p)
      · rintro ⟨hd, hlt⟩
        refine ⟨?_, by omega⟩
        rw [e] at hd
        exact (Nat.dvd_add_right (dvd_refl p)).1 (by simpa [add_comm] using hd)

theorem firstMult_ge (p L : Nat) (hp : 1 ≤ p) : L ≤ firstMult p L := by
  unfold firstMult
  have h1 := Nat.div_add_mod (L + p - 1) p
  have h2 := Nat.mod_lt (L + p - 1) (show 0 < p by omega)
  have h3 : p * ((L + p - 1) / p) ≤ p * max 2 ((L + p - 1) / p) :=
    Nat.mul_le_mul_left _ (le_max_right _ _)
  generalize (L + p - 1) / p = Q at h1 h2 h3
  generalize p * Q = M at h1 h2 h3
  omega

theorem two_mul_le_firstMult (p L : Nat) : 2 * p ≤ firstMult p L := by
  unfold firstMult
  calc 2 * p = p * 2 := by ring
    _ ≤ p * max 2 ((L + p - 1) / p) := Nat.mul_le_mul_left _ (le_max_left _ _)

theorem dvd_firstMult (p L : Nat) : p ∣ firstMult p L := Dvd.intro _ rfl

theorem firstMult_le (p L k : Nat) (hp : 1 ≤ p) (hdvd : p ∣ k) (h2 : 2 * p ≤ k) (hL : L ≤ k) :
    firstMult p L ≤ k := by
  obtain ⟨m, rfl⟩ := hdvd
  unfold firstMult
  apply Nat.mul_le_mul_left
  apply max_le
  · by_contra hc
    have : m ≤ 1 := by omega
    have : p * m ≤ p * 1 := Nat.mul_le_mul_left _ this
    omega
  · apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : p * m + p = (m + 1) * p := by ring
    show L + p - 1 < (m + 1) * p
    omega

theorem testBit_pat (p L B i : Nat) (hp : 1 ≤ p) :
    (pat p L B).testBit i = true ↔
      firstMult p L < L + B ∧ firstMult p L - L ≤ i ∧ p ∣ (i - (firstMult p L - L)) ∧
        (i - (firstMult p L - L)) / p < (L + B - firstMult p L + p - 1) / p := by
  unfold pat
  by_cases hf : firstMult p L < L + B
  · simp only [hf, ↓reduceIte, true_and]
    rw [Nat.testBit_two_pow_mul, geom_eq p _ hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_geomR p hp]
  · simp [hf]

theorem testBit_foldr_or {α : Type} (l : List α) (f : α → Nat) (i : Nat) :
    (l.foldr (fun a acc => f a ||| acc) 0).testBit i = true ↔ ∃ a ∈ l, (f a).testBit i = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, ih]
    simp

theorem testBit_compMask (L B i : Nat) :
    (compMask L B).testBit i = true ↔ ∃ p ∈ smallPrimes, (pat p L B).testBit i = true :=
  testBit_foldr_or smallPrimes (fun p => pat p L B) i

/-- Direction A: multiples `k ≥ 2p` of a small prime in the segment are marked. -/
theorem compMask_bit_of_dvd {L B p k : Nat} (hp : p ∈ smallPrimes) (hdvd : p ∣ k)
    (h2 : 2 * p ≤ k) (hL : L ≤ k) (hB : k < L + B) : (compMask L B).testBit (k - L) = true := by
  rw [testBit_compMask]
  refine ⟨p, hp, ?_⟩
  have hp1 : 1 ≤ p := (prime_of_mem_smallPrimes hp).one_lt.le
  have hf := firstMult_le p L k hp1 hdvd h2 hL
  have hfL := firstMult_ge p L hp1
  rw [testBit_pat p L B _ hp1]
  have e : k - L - (firstMult p L - L) = k - firstMult p L := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [e]; exact Nat.dvd_sub hdvd (dvd_firstMult p L)
  · rw [e, Nat.div_lt_iff_lt_mul (by omega)]
    have h1 := Nat.div_add_mod (L + B - firstMult p L + p - 1) p
    have h2 := Nat.mod_lt (L + B - firstMult p L + p - 1) (show 0 < p by omega)
    have hm : (L + B - firstMult p L + p - 1) / p * p = p * ((L + B - firstMult p L + p - 1) / p) :=
      by ring
    rw [hm]
    generalize (L + B - firstMult p L + p - 1) / p = Q at h1 h2 ⊢
    generalize p * Q = M at h1 h2 ⊢
    omega

/-- Direction B: a marked position is a multiple `m ≥ 2p` of some small prime `p`. -/
theorem dvd_of_compMask_bit {L B i : Nat} (h : (compMask L B).testBit i = true) :
    ∃ p ∈ smallPrimes, p ∣ L + i ∧ 2 * p ≤ L + i := by
  rw [testBit_compMask] at h
  obtain ⟨p, hp, hb⟩ := h
  have hp1 : 1 ≤ p := (prime_of_mem_smallPrimes hp).one_lt.le
  rw [testBit_pat p L B _ hp1] at hb
  obtain ⟨_, h1, h2, _⟩ := hb
  have hfL := firstMult_ge p L hp1
  have h2p := two_mul_le_firstMult p L
  refine ⟨p, hp, ?_, by omega⟩
  have e : L + i = firstMult p L + (i - (firstMult p L - L)) := by omega
  rw [e]
  exact Nat.dvd_add (dvd_firstMult p L) h2

theorem hpMask_bit {L B : Nat} {e : Nat × Nat × Nat} (he : e ∈ hpList) (hL : L ≤ e.1)
    (hB : e.1 < L + B) : (hpMask L B).testBit (e.1 - L) = true := by
  unfold hpMask
  rw [testBit_foldr_or hpList (fun e => if L ≤ e.1 ∧ e.1 < L + B then 2 ^ (e.1 - L) else 0)]
  refine ⟨e, he, ?_⟩
  simp only [hL, hB, and_self, ↓reduceIte, Nat.testBit_two_pow, decide_true]

theorem prime_of_compMask_bit_false {L B i : Nat} (hk2 : 2 ≤ L + i) (hkT : L + i ≤ TOP)
    (hiB : i < B) (h : (compMask L B).testBit i = false) : (L + i).Prime := by
  by_contra hnp
  set k := L + i with hk
  have hk0 : 0 < k := by omega
  have hk1 : k ≠ 1 := by omega
  have hm := Nat.minFac_prime hk1
  have hsq := Nat.minFac_sq_le_self hk0 hnp
  have hm2 := hm.two_le
  have hTOP : TOP = 1048576 := rfl
  have hle : k.minFac ≤ 1024 := by
    rw [hTOP] at hkT
    nlinarith
  have hmem := mem_smallPrimes_of_prime hm hle
  have h2 : 2 * k.minFac ≤ k := by nlinarith
  have hbit := compMask_bit_of_dvd (L := L) (B := B) hmem (Nat.minFac_dvd k) h2 (by omega) (by omega)
  rw [show k - L = i by omega, h] at hbit
  exact absurd hbit (by decide)

theorem not_isPrimePow_of_bits {L B i : Nat} (hiB : i < B) (hkT : L + i ≤ TOP)
    (hc : (compMask L B).testBit i = true) (hh : (hpMask L B).testBit i = false) :
    ¬ IsPrimePow (L + i) := by
  obtain ⟨p, hp, hdvd, h2⟩ := dvd_of_compMask_bit hc
  have hpp := prime_of_mem_smallPrimes hp
  rw [isPrimePow_nat_iff]
  rintro ⟨r, j, hr, hj, hrj⟩
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hpp hr).1 (hpp.dvd_of_dvd_pow (hrj ▸ hdvd))
  subst hpr
  rcases Nat.lt_or_ge j 2 with hj1 | hj2
  · have : j = 1 := by omega
    subst this
    have := hpp.two_le
    simp at hrj
    omega
  · obtain ⟨e, he, he1⟩ := hpList_complete hr hj2 (hrj ▸ hkT)
    have hbit := hpMask_bit (L := L) (B := B) he (by omega) (by omega)
    rw [he1, hrj, show L + i - L = i by omega, hh] at hbit
    exact absurd hbit (by decide)

/-- What the step uses about the current mask bits `cm % 2`, `hm % 2` of `k`. -/
def MaskFacts (cm hm k : Nat) : Prop :=
  k ≤ TOP → (cm % 2 = 0 → k.Prime) ∧ (cm % 2 ≠ 0 → hm % 2 ≠ 1 → ¬ IsPrimePow k)

theorem maskFacts_seg (L B i : Nat) (hL : 2 ≤ L) (hi : i < B) :
    MaskFacts (compMask L B / 2 ^ i) (hpMask L B / 2 ^ i) (L + i) := by
  intro hkT
  constructor
  · intro h0
    apply prime_of_compMask_bit_false (by omega) hkT hi
    rw [Nat.testBit_eq_decide_div_mod_eq, h0]; decide
  · intro hc hh
    apply not_isPrimePow_of_bits hi hkT
    · rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      omega
    · rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_false_iff_not]
      exact hh

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
