/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import RSBounds.LambdaCert.Defs

/-!
# The tables `smallPrimes` and `hpList`, checked in the kernel

* `smallPrimes` is exactly the set of primes `≤ 1024`;
* every `(q, p, j) ∈ hpList` has `p` prime, `p ^ j = q`, `j ≥ 1`;
* every `p ^ j ≤ 2^20` with `p` prime and `j ≥ 2` occurs in `hpList`.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

/-- `true` iff no `m ≥ d` with `m * m ≤ n` divides `n` (trying at most `fuel` values of `m`). -/
def noDiv (n fuel : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun d => decide (n < d * d))
    (fun _ ih d => if n < d * d then true else (n % d != 0) && ih (d + 1)) fuel

theorem noDiv_sound (n : Nat) :
    ∀ fuel d, noDiv n fuel d = true → ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro d h m hdm hmn _
    have h' : n < d * d := by simpa [noDiv] using h
    have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
    omega
  | succ f ih =>
    intro d h m hdm hmn hmd
    have hstep : noDiv n (f + 1) d =
        (if n < d * d then true else (n % d != 0) && noDiv n f (d + 1)) := rfl
    rw [hstep] at h
    by_cases hlt : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · simp only [hlt, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt'
      · exact h.1 (Nat.mod_eq_zero_of_dvd hmd)
      · exact ih (d + 1) h.2 m hlt' hmn hmd

theorem noDiv_complete (n : Nat) (hn : n.Prime) :
    ∀ fuel d, 2 ≤ d → n < (d + fuel) * (d + fuel) → noDiv n fuel d = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ h
    simpa [noDiv] using h
  | succ f ih =>
    intro d hd h
    have hstep : noDiv n (f + 1) d =
        (if n < d * d then true else (n % d != 0) && noDiv n f (d + 1)) := rfl
    rw [hstep]
    by_cases hlt : n < d * d
    · simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq]
      refine ⟨?_, ih (d + 1) (by omega) (by rw [show d + 1 + f = d + (f + 1) by omega]; exact h)⟩
      intro hmod
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
      rcases (Nat.dvd_prime hn).1 hdvd with h1 | h1
      · omega
      · subst h1
        have : d < d * d := by nlinarith
        omega

/-- Primality by trial division up to `41`; correct for `n < 42 ^ 2`. -/
def isPrimeTD (n : Nat) : Bool := decide (2 ≤ n) && noDiv n 40 2

theorem isPrimeTD_iff (n : Nat) (hn : n < 42 * 42) : isPrimeTD n = true ↔ n.Prime := by
  constructor
  · intro h
    simp only [isPrimeTD, Bool.and_eq_true, decide_eq_true_eq] at h
    by_contra hp
    have hn0 : 0 < n := by omega
    have hn1 : n ≠ 1 := by omega
    have hm := Nat.minFac_prime hn1
    have hsq := Nat.minFac_sq_le_self hn0 hp
    exact noDiv_sound n 40 2 h.2 n.minFac hm.two_le (by nlinarith) (Nat.minFac_dvd n)
  · intro hp
    simp only [isPrimeTD, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hp.two_le, noDiv_complete n hp 40 2 le_rfl (by omega)⟩

/-- Every element of `smallPrimes` is prime (trial division). -/
def smallPrimesSound : Bool := smallPrimes.all isPrimeTD

/-- Every prime `≤ 1024` is in `smallPrimes`. -/
def smallPrimesComplete : Bool :=
  (List.range 1025).all (fun n => !isPrimeTD n || smallPrimes.contains n)

theorem smallPrimesSound_eq : smallPrimesSound = true := by decide +kernel

theorem smallPrimesComplete_eq : smallPrimesComplete = true := by decide +kernel

theorem prime_of_mem_smallPrimes {p : Nat} (hp : p ∈ smallPrimes) : p.Prime := by
  have h := smallPrimesSound_eq
  simp only [smallPrimesSound, List.all_eq_true] at h
  have hle : p ≤ 1021 := by
    have : ∀ x ∈ smallPrimes, x ≤ 1021 := by decide +kernel
    exact this p hp
  exact (isPrimeTD_iff p (by omega)).1 (h p hp)

theorem mem_smallPrimes_of_prime {p : Nat} (hp : p.Prime) (hle : p ≤ 1024) : p ∈ smallPrimes := by
  have h := smallPrimesComplete_eq
  simp only [smallPrimesComplete, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_iff_mem] at h
  rcases h p (by omega) with h1 | h1
  · rw [(isPrimeTD_iff p (by omega)).2 hp] at h1
    exact absurd h1 (by decide)
  · exact h1

/-- Each `(q, p, j) ∈ hpList` has `p ∈ smallPrimes`, `p ^ j = q` and `1 ≤ j`. -/
def hpListSound : Bool :=
  hpList.all (fun e => smallPrimes.contains e.2.1 && Nat.beq (e.2.1 ^ e.2.2) e.1 && Nat.ble 1 e.2.2)

/-- Every `p ^ j ≤ 2^20` with `p ∈ smallPrimes` and `2 ≤ j ≤ 20` occurs in `hpList`. -/
def hpListComplete : Bool :=
  smallPrimes.all (fun p => (List.range 21).all (fun j =>
    decide (j < 2) || decide (TOP < p ^ j) || hpList.any (fun e => Nat.beq e.1 (p ^ j))))

theorem hpListSound_eq : hpListSound = true := by decide +kernel

theorem hpListComplete_eq : hpListComplete = true := by decide +kernel

theorem hpList_sound {e : Nat × Nat × Nat} (he : e ∈ hpList) :
    e.2.1.Prime ∧ e.2.1 ^ e.2.2 = e.1 ∧ 1 ≤ e.2.2 := by
  have h := hpListSound_eq
  simp only [hpListSound, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h e he
  exact ⟨prime_of_mem_smallPrimes h1, h2, h3⟩

theorem hpList_complete {p j : Nat} (hp : p.Prime) (hj : 2 ≤ j) (hle : p ^ j ≤ TOP) :
    ∃ e ∈ hpList, e.1 = p ^ j := by
  have hTOP : TOP = 2 ^ 20 := rfl
  have hp2 := hp.two_le
  have hj20 : j < 21 := by
    by_contra hc
    have : 2 ^ 21 ≤ p ^ j :=
      (Nat.pow_le_pow_left hp2 21).trans (Nat.pow_le_pow_right (by omega) (by omega))
    rw [hTOP] at hle
    omega
  have hp1024 : p ≤ 1024 := by
    have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj
    rw [hTOP] at hle
    nlinarith
  have hmem := mem_smallPrimes_of_prime hp hp1024
  have h := hpListComplete_eq
  simp only [hpListComplete, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, Nat.beq_eq] at h
  rcases h p hmem j hj20 with (h1 | h1) | ⟨e, he, h1⟩
  · omega
  · omega
  · exact ⟨e, he, h1⟩

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
