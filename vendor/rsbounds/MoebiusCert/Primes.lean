/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.PrimeData
import MoebiusCert.Raw
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith

/-!
# Certification of the prime data

`spData` lists exactly the primes below `1000` (with valid weights) and `mpData` exactly the primes
in `(1000, 31622]`, each without repetition. Checked once by the kernel, by trial division.
-/

namespace MoebiusCert

/-- `tdAux n fuel d`: no `e ∈ [d, d + fuel)` with `e² ≤ n` divides `n`. -/
def tdAux (n : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih d => (Nat.blt n (Nat.mul d d) || !Nat.beq (Nat.mod n d) 0) && ih (Nat.add d 1))

/-- Trial division primality test, valid for `n < 178²`. -/
def isPrimeTD (n : ℕ) : Bool := Nat.ble 2 n && tdAux n 176 2

lemma tdAux_succ_raw (n fuel d : ℕ) :
    tdAux n (fuel + 1) d = ((Nat.blt n (Nat.mul d d) || !Nat.beq (Nat.mod n d) 0) && tdAux n fuel (Nat.add d 1)) :=
  rfl

lemma tdAux_succ (n fuel d : ℕ) :
    tdAux n (fuel + 1) d = ((decide (n < d * d) || !decide (n % d = 0)) && tdAux n fuel (d + 1)) := by
  rw [tdAux_succ_raw]; raw_norm

lemma tdAux_spec (n : ℕ) : ∀ fuel d, tdAux n fuel d = true ↔
    ∀ e, d ≤ e → e < d + fuel → e * e ≤ n → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d; simp [tdAux]; intro e h1 h2; omega
  | succ fuel ih =>
    intro d
    rw [tdAux_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ e he1 he2 he3
      rcases Nat.eq_or_lt_of_le he1 with rfl | hlt
      · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h1
        rcases h1 with h | h
        · omega
        · exact fun hd => h (Nat.mod_eq_zero_of_dvd hd)
      · exact h2 e (by omega) (by omega) he3
    · intro h
      refine ⟨?_, fun e he1 he2 he3 => h e (by omega) (by omega) he3⟩
      by_cases hdd : n < d * d
      · simp [hdd]
      · have := h d le_rfl (by omega) (by omega)
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        right; intro hm; exact this (Nat.dvd_of_mod_eq_zero hm)

theorem isPrimeTD_iff {n : ℕ} (hn : n < 178 * 178) : isPrimeTD n = true ↔ n.Prime := by
  unfold isPrimeTD
  rw [Bool.and_eq_true, tdAux_spec, raw_ble, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hp
    have hmf := Nat.minFac_sq_le_self (by omega) hp
    have hmd := Nat.minFac_dvd n
    have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    exact h n.minFac hm2 (by nlinarith) (by nlinarith) hmd
  · intro hp
    refine ⟨hp.two_le, fun e he1 _ he3 hd => ?_⟩
    rcases hp.eq_one_or_self_of_dvd e hd with h | h
    · omega
    · subst h; nlinarith [hp.two_le]


/-! ### Kernel certificates -/

set_option maxRecDepth 100000 in
theorem spData_keys : spData.map Prod.fst = (List.range 1000).filter isPrimeTD := by decide +kernel

set_option maxRecDepth 100000 in
theorem mpData_eq : mpData = (List.range 31623).filter (fun n => Nat.blt 1000 n && isPrimeTD n) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spData_weights : spData.all (fun pa => Nat.beq (pa.2 % 2) 1 && Nat.ble (2 ^ (pa.2 / 2)) (pa.1 ^ 2) &&
    Nat.blt (pa.1 ^ 2) (2 ^ (pa.2 / 2 + 1))) = true := by decide +kernel

/-! ### Consequences -/

theorem mem_sp_keys {p : ℕ} : p ∈ spData.map Prod.fst ↔ p.Prime ∧ p < 1000 := by
  rw [spData_keys, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(isPrimeTD_iff (by omega)).1 h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, (isPrimeTD_iff (by omega)).2 h1⟩

theorem sp_keys_nodup : (spData.map Prod.fst).Nodup := by
  rw [spData_keys]; exact (List.nodup_range).filter _

theorem mem_mp {p : ℕ} : p ∈ mpData ↔ p.Prime ∧ 1000 < p ∧ p ≤ 31622 := by
  rw [mpData_eq, List.mem_filter, List.mem_range, Bool.and_eq_true, raw_blt, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨(isPrimeTD_iff (by omega)).1 h3, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, (isPrimeTD_iff (by omega)).2 h1⟩

theorem mp_nodup : mpData.Nodup := by
  rw [mpData_eq]; exact (List.nodup_range).filter _

theorem sp_weight {pa : ℕ × ℕ} (h : pa ∈ spData) :
    pa.2 % 2 = 1 ∧ 2 ^ (pa.2 / 2) ≤ pa.1 ^ 2 ∧ pa.1 ^ 2 < 2 ^ (pa.2 / 2 + 1) := by
  have := List.all_eq_true.1 spData_weights pa h
  simp only [Bool.and_eq_true, raw_beq, raw_ble, raw_blt, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem sp_pos {pa : ℕ × ℕ} (h : pa ∈ spData) : 0 < pa.1 :=
  (mem_sp_keys.1 (List.mem_map_of_mem h)).1.pos

theorem mp_pos {p : ℕ} (h : p ∈ mpData) : 0 < p := (mem_mp.1 h).1.pos

end MoebiusCert
