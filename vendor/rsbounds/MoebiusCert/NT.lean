/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

/-!
# Reading `μ(n)` off the sieve data

For `n ≤ 1000014128 < 31623²`, write `s` for the product of the primes `p < 1000` dividing `n` and
`v = ∑ (2ℓ_p + 1)` for their weights, where `2^ℓ_p ≤ p² < 2^(ℓ_p+1)`. Let `c` be the number of
primes `1000 < p ≤ 31622` dividing `n`. If `n` is squarefree, the number `b` of prime factors
`> 31622` is `0` or `1`, and it is determined by comparing `v` with a threshold: `b = 1` iff
`v < θ_c`, where `θ_0 = 5λ - 69`, `θ_1 = 5λ - 119`, `λ = ⌊log₂ n⌋`. This is what the decode step
of the kernel checker computes.
-/

namespace MoebiusCert

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega ArithmeticFunction.Omega

section bounds

variable {s A k v n lam K e : ℕ}

/-- Lower bound on the weight sum when the unsieved part is small. -/
lemma weight_low (hv : v = 2 * A + k) (hAk : 2 * k ≤ A) (hs2 : s ^ 2 ≤ 2 ^ (A + k))
    (hns : n ≤ s * K) (hK : K * K ≤ 2 ^ e) (hl1 : 2 ^ lam ≤ n) : 10 * lam ≤ 3 * v + 5 * e := by
  have h1 : 2 ^ (2 * lam) ≤ 2 ^ (A + k + e) := by
    calc 2 ^ (2 * lam) = (2 ^ lam) ^ 2 := by ring
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hl1 2
      _ ≤ (s * K) ^ 2 := Nat.pow_le_pow_left hns 2
      _ = s ^ 2 * (K * K) := by ring
      _ ≤ 2 ^ (A + k) * 2 ^ e := Nat.mul_le_mul hs2 hK
      _ = 2 ^ (A + k + e) := by rw [← pow_add]
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  omega

/-- Upper bound on the weight sum when the unsieved part is large. -/
lemma weight_high (hv : v = 2 * A + k) (hAk : 2 * k ≤ A) (hs1 : 2 ^ A ≤ s ^ 2)
    (hns : s * K ≤ n) (hK : 2 ^ e ≤ K * K) (hl2 : n < 2 ^ (lam + 1)) : 2 * v + 5 * e ≤ 10 * lam + 5 := by
  have h1 : 2 ^ (A + e) < 2 ^ (2 * lam + 2) := by
    calc 2 ^ (A + e) = 2 ^ A * 2 ^ e := by rw [pow_add]
      _ ≤ s ^ 2 * (K * K) := Nat.mul_le_mul hs1 hK
      _ = (s * K) ^ 2 := by ring
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hns 2
      _ < (2 ^ (lam + 1)) ^ 2 := Nat.pow_lt_pow_left hl2 (by norm_num)
      _ = 2 ^ (2 * lam + 2) := by ring
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h1
  omega

end bounds

/-- `ω n` is the number of prime factors. -/
lemma cardDistinctFactors_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset]; rfl

lemma moebius_of_squarefree' {n : ℕ} (hn : Squarefree n) (h0 : n ≠ 0) :
    μ n = (-1) ^ n.primeFactors.card := by
  rw [moebius_apply_of_squarefree hn, ← cardDistinctFactors_eq_card,
    (cardDistinctFactors_eq_cardFactors_iff_squarefree h0).2 hn]

/-- The decoding lemma. `W p = 2ℓ_p + 1` are the weights of the small primes. -/
theorem mu_core (n lam : ℕ) (W : ℕ → ℕ)
    (hW : ∀ p, p.Prime → p < 1000 → W p % 2 = 1 ∧ 2 ^ (W p / 2) ≤ p ^ 2 ∧ p ^ 2 < 2 ^ (W p / 2 + 1))
    (hn1 : 1 ≤ n) (hn : n ≤ 1000014128) (hl1 : 2 ^ lam ≤ n) (hl2 : n < 2 ^ (lam + 1)) (hlam : lam ≤ 29) :
    let v := ∑ p ∈ Finset.filter (fun p => p < 1000) n.primeFactors, W p
    let c := (n.primeFactors.filter (fun p => 1000 < p ∧ p ≤ 31622)).card
    let a := if 1 ≤ c then 1 else 0
    let b := if 2 ≤ c then 1 else 0
    v + (128 - (5 * lam - 69)) < 2 ^ 8 ∧ v + (128 - (5 * lam - 119)) < 2 ^ 8 ∧
    ((if (∃ p < 31623, p.Prime ∧ p * p ∣ n) then 1 else
        if (v + a + b + (if b = 0 ∧ ((a = 0 ∧ v < 5 * lam - 69) ∨ (a = 1 ∧ v < 5 * lam - 119)) then 1 else 0))
          % 2 = 0 then 2 else 0 : ℕ) : ℤ) = μ n + 1 := by
  intro v c a b
  have hn0 : n ≠ 0 := by omega
  set PF := n.primeFactors with hPF
  set SPF := PF.filter (fun p => p < 1000) with hSPF
  set s := ∏ p ∈ SPF, p with hs
  set A := ∑ p ∈ SPF, W p / 2 with hA
  set k := SPF.card with hk
  have hprime : ∀ p ∈ SPF, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (mem_filter.1 hp).1).1
  have hW' : ∀ p ∈ SPF, W p % 2 = 1 ∧ 2 ^ (W p / 2) ≤ p ^ 2 ∧ p ^ 2 < 2 ^ (W p / 2 + 1) :=
    fun p hp => hW p (hprime p hp) (mem_filter.1 hp).2
  have hv : v = 2 * A + k := by
    show ∑ p ∈ SPF, W p = _
    rw [hA, hk, mul_sum, card_eq_sum_ones, ← sum_add_distrib]
    exact sum_congr rfl fun p hp => by have := (hW' p hp).1; omega
  have hAk : 2 * k ≤ A := by
    rw [hk, card_eq_sum_ones, mul_sum, hA]
    refine sum_le_sum fun p hp => ?_
    have h2 := (hprime p hp).two_le
    have := (hW' p hp).2.2
    by_contra hlt
    have : W p / 2 + 1 ≤ 2 := by omega
    have : p ^ 2 < 2 ^ 2 := lt_of_lt_of_le ‹_› (Nat.pow_le_pow_right (by norm_num) this)
    nlinarith
  have hs1 : 2 ^ A ≤ s ^ 2 := by
    rw [hs, ← prod_pow, hA, ← prod_pow_eq_pow_sum]
    exact prod_le_prod' fun p hp => (hW' p hp).2.1
  have hs2 : s ^ 2 ≤ 2 ^ (A + k) := by
    rw [hs, ← prod_pow, hA, hk, card_eq_sum_ones, ← sum_add_distrib, ← prod_pow_eq_pow_sum]
    exact prod_le_prod' fun p hp => (hW' p hp).2.2.le
  have hsdvd : s ∣ n := by
    rw [hs]
    exact Finset.prod_primes_dvd n (fun p hp => (hprime p hp).prime)
      (fun p hp => (Nat.mem_primeFactors.1 (mem_filter.1 hp).1).2.1)
  have hspos : 0 < s := Nat.pos_of_ne_zero (fun h => by rw [h] at hsdvd; simp at hsdvd; omega)
  have hsn : s ≤ n := Nat.le_of_dvd (by omega) hsdvd
  -- the weight bound used by the decoder
  have hvb : 2 * v ≤ 10 * lam + 5 := by
    have := weight_high (K := 1) (e := 0) hv hAk hs1 (by simpa using hsn) (by norm_num) hl2
    omega
  refine ⟨by omega, by omega, ?_⟩
  by_cases hsq : ∃ p < 31623, p.Prime ∧ p * p ∣ n
  · -- not squarefree
    have hnsq : ¬ Squarefree n := by
      obtain ⟨p, -, hp, hpp⟩ := hsq
      rw [Nat.squarefree_iff_prime_squarefree]; push Not; exact ⟨p, hp, hpp⟩
    rw [if_pos hsq, moebius_eq_zero_of_not_squarefree hnsq]; simp
  rw [if_neg hsq]
  have hsqf : Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    apply hsq
    refine ⟨p, ?_, hp, hpp⟩
    by_contra hbig; push Not at hbig
    have : 31623 * 31623 ≤ p * p := Nat.mul_le_mul hbig hbig
    have := Nat.le_of_dvd (by omega) hpp
    omega
  rw [moebius_of_squarefree' hsqf hn0]
  -- split the prime factors
  set MPF := PF.filter (fun p => 1000 < p ∧ p ≤ 31622) with hMPF
  set BPF := PF.filter (fun p => 31622 < p) with hBPF
  set m := ∏ p ∈ MPF, p with hm
  set q := ∏ p ∈ BPF, p with hq
  have hc : c = MPF.card := rfl
  have hne : ∀ p ∈ PF, p ≠ 1000 := fun p hp h => by
    have := (Nat.mem_primeFactors.1 hp).1; rw [h] at this
    rcases this.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> omega
  have hM : (PF.filter (fun p => ¬ p < 1000)).filter (fun p => p ≤ 31622) = MPF := by
    rw [filter_filter]; exact filter_congr fun p hp => by have := hne p hp; omega
  have hB : (PF.filter (fun p => ¬ p < 1000)).filter (fun p => ¬ p ≤ 31622) = BPF := by
    rw [filter_filter]; exact filter_congr fun p hp => by have := hne p hp; omega
  have hprod : n = s * (m * q) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsqf]
    rw [← prod_filter_mul_prod_filter_not PF (fun p => p < 1000),
      ← prod_filter_mul_prod_filter_not (PF.filter (fun p => ¬ p < 1000)) (fun p => p ≤ 31622), hM, hB]
  have hcard : PF.card = k + (c + BPF.card) := by
    rw [← card_filter_add_card_filter_not (s := PF) (fun p => p < 1000),
      ← card_filter_add_card_filter_not (s := PF.filter (fun p => ¬ p < 1000)) (fun p => p ≤ 31622),
      hM, hB]
  rw [hcard]
  set bb := BPF.card with hbb
  have hm1 : 1001 ^ c ≤ m := by
    rw [hc, hm]; exact pow_card_le_prod _ _ _ fun p hp => (mem_filter.1 hp).2.1
  have hm2 : m ≤ 31622 ^ c := by
    rw [hc, hm]; exact prod_le_pow_card _ _ _ fun p hp => (mem_filter.1 hp).2.2
  have hq1 : 31623 ^ bb ≤ q := by
    rw [hbb, hq]; exact pow_card_le_prod _ _ _ fun p hp => (mem_filter.1 hp).2
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hqn : q ≤ n := by
    rw [hprod]; calc q = 1 * (1 * q) := by ring
      _ ≤ s * (m * q) := Nat.mul_le_mul hspos (Nat.mul_le_mul hmpos le_rfl)
  have hmn : m ≤ n := by
    rw [hprod]; calc m = 1 * (m * 1) := by ring
      _ ≤ s * (m * q) := Nat.mul_le_mul hspos (Nat.mul_le_mul le_rfl hqpos)
  have hb1 : bb ≤ 1 := by
    by_contra h; push Not at h
    have : 31623 ^ 2 ≤ 31623 ^ bb := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hc2 : c ≤ 2 := by
    by_contra h; push Not at h
    have : 1001 ^ 3 ≤ 1001 ^ c := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hneg : ∀ t : ℕ, ((-1 : ℤ) ^ t + 1) = if t % 2 = 0 then 2 else 0 := by
    intro t
    rcases Nat.even_or_odd t with ht | ht
    · rw [ht.neg_one_pow, if_pos (Nat.even_iff.1 ht)]; norm_num
    · rw [ht.neg_one_pow, if_neg (by rw [Nat.odd_iff] at ht; omega)]; norm_num
  rw [hneg]
  push_cast
  have hpar : ∀ X Y : ℕ, X % 2 = Y % 2 →
      (if X % 2 = 0 then (2 : ℤ) else 0) = (if Y % 2 = 0 then 2 else 0 : ℤ) := by
    intro X Y h; rw [h]
  apply hpar
  have hvk : v % 2 = k % 2 := by omega
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with hc0 | hc0 | hc0
  · have ha : a = 0 := by simp [a, hc0]
    have hb' : b = 0 := by simp [b, hc0]
    have hm1' : m = 1 := by
      rw [hm, show MPF = ∅ from card_eq_zero.1 (by rw [← hc]; exact hc0)]; simp
    rcases (by omega : bb = 0 ∨ bb = 1) with hbb0 | hbb0
    · have hq1' : q = 1 := by
        rw [hq, show BPF = ∅ from card_eq_zero.1 hbb0]; simp
      have hns : n ≤ s * 1 := by rw [hprod, hm1', hq1']
      have := weight_low hv hAk hs2 hns (by norm_num : 1 * 1 ≤ 2 ^ 0) hl1
      rw [ha, hb', hc0, hbb0]
      rw [if_neg (by omega)]; omega
    · have hns : s * 31623 ≤ n := by
        rw [hprod, hm1', one_mul]; exact Nat.mul_le_mul_left _ (by simpa [hbb0] using hq1)
      have := weight_high hv hAk hs1 hns (by norm_num : 2 ^ 29 ≤ 31623 * 31623) hl2
      rw [ha, hb', hc0, hbb0]
      rw [if_pos (by omega)]; omega
  · have ha : a = 1 := by simp [a, hc0]
    have hb' : b = 0 := by simp [b, hc0]
    rcases (by omega : bb = 0 ∨ bb = 1) with hbb0 | hbb0
    · have hq1' : q = 1 := by
        rw [hq, show BPF = ∅ from card_eq_zero.1 hbb0]; simp
      have hns : n ≤ s * 31622 := by
        rw [hprod, hq1', mul_one]; exact Nat.mul_le_mul_left _ (by simpa [hc0] using hm2)
      have := weight_low hv hAk hs2 hns (by norm_num : 31622 * 31622 ≤ 2 ^ 30) hl1
      rw [ha, hb', hc0, hbb0]
      rw [if_neg (by omega)]; omega
    · have hns : s * (1001 * 31623) ≤ n := by
        rw [hprod]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by simpa [hc0] using hm1)
          (by simpa [hbb0] using hq1))
      have := weight_high hv hAk hs1 hns (by norm_num : 2 ^ 49 ≤ 1001 * 31623 * (1001 * 31623)) hl2
      rw [ha, hb', hc0, hbb0]
      rw [if_pos (by omega)]; omega
  · have ha : a = 1 := by simp [a, hc0]
    have hb' : b = 1 := by simp [b, hc0]
    have hbb0 : bb = 0 := by
      by_contra h
      have : 1 ≤ bb := by omega
      have h1 : 31623 ≤ q := le_trans (by simpa using Nat.pow_le_pow_right (show 0 < 31623 by norm_num) this) hq1
      have h2 : 1001 ^ 2 ≤ m := by simpa [hc0] using hm1
      have : 1001 ^ 2 * 31623 ≤ m * q := Nat.mul_le_mul h2 h1
      have : m * q ≤ n := by rw [hprod]; exact Nat.le_mul_of_pos_left _ hspos
      omega
    rw [ha, hb', hc0, hbb0]
    rw [if_neg (by omega)]; omega

end MoebiusCert
