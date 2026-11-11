/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Data.Nat.Bitwise

/-!
# Normalizing the kernel primitives

The kernel-evaluated definitions use raw primitives (`Nat.div`, `Nat.shiftLeft`, `Nat.beq`, …).
These `simp` lemmas rewrite them to the usual notation.
-/

namespace MoebiusCert

lemma raw_div (a b : ℕ) : Nat.div a b = a / b := rfl
lemma raw_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
lemma raw_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
lemma raw_shiftRight (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma raw_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma raw_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma raw_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma raw_beq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; intro e; subst e; simp [Nat.beq_refl] at h
  · simp only [Nat.beq_eq] at h; simp [h]
lemma raw_ble (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; intro e; simp [Nat.ble_eq_true_of_le e] at h
  · simp only [Nat.ble_eq] at h; simp [h]
lemma raw_blt (a b : ℕ) : Nat.blt a b = decide (a < b) := raw_ble _ _

/-- `simp only [raw]` turns kernel primitives into notation. -/
lemma raw_max (a b : ℕ) : Nat.max a b = max a b := rfl

end MoebiusCert

namespace MoebiusCert

/-- Rewrite kernel primitives into notation in the goal. -/
macro "raw_norm" : tactic => `(tactic| simp only [MoebiusCert.raw_div, MoebiusCert.raw_mod,
  MoebiusCert.raw_shiftLeft, MoebiusCert.raw_shiftRight, MoebiusCert.raw_land, MoebiusCert.raw_lor,
  MoebiusCert.raw_xor, MoebiusCert.raw_beq, MoebiusCert.raw_ble, MoebiusCert.raw_blt,
  MoebiusCert.raw_max, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Bool.cond_decide])

end MoebiusCert
