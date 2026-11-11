/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.Segments
import MoebiusCert.DefsSmall

/-!
# Soundness of the per-element checks (`n < 2^18` for `(M)`)
-/

namespace MoebiusCert

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma smallLoop_zero (X n : ℕ) (M : ℤ) : smallLoop 0 X n M = (true, M) := rfl

lemma smallLoop_succ_raw (c X n : ℕ) (M : ℤ) : smallLoop (c + 1) X n M =
    cond (Nat.blt n 33 || Nat.ble (Nat.mul 1000000 (Nat.mul (Int.natAbs (M + (Int.ofNat (Nat.mod X 256) - 1)))
        (Int.natAbs (M + (Int.ofNat (Nat.mod X 256) - 1))))) (Nat.mul 326041 n))
      (smallLoop c (Nat.shiftRight X 8) (Nat.add n 1) (M + (Int.ofNat (Nat.mod X 256) - 1)))
      (false, M + (Int.ofNat (Nat.mod X 256) - 1)) := rfl

lemma smallLoop_succ (c X n : ℕ) (M : ℤ) : smallLoop (c + 1) X n M =
    cond (decide (n < 33) || decide (1000000 * ((M + ((X % 256 : ℕ) - 1)).natAbs *
        (M + ((X % 256 : ℕ) - 1)).natAbs) ≤ 326041 * n))
      (smallLoop c (X >>> 8) (n + 1) (M + ((X % 256 : ℕ) - 1))) (false, M + ((X % 256 : ℕ) - 1)) := by
  rw [smallLoop_succ_raw]
  simp only [raw_blt, raw_ble, raw_mod, raw_shiftRight, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_coe]

theorem smallLoop_spec : ∀ (c X n : ℕ) (M : ℤ) (f : ℕ → ℕ), (∀ i < c, f i < 256) → X = pk 8 f c →
    (smallLoop c X n M).1 = true →
      (∀ i < c, n + i < 33 ∨
        10 ^ 6 * (M + ∑ e ∈ range (i + 1), ((f e : ℤ) - 1)) ^ 2 ≤ 326041 * ((n + i : ℕ) : ℤ)) ∧
      (smallLoop c X n M).2 = M + ∑ e ∈ range c, ((f e : ℤ) - 1) := by
  intro c
  induction c with
  | zero => intro X n M f _ _ _; simp [smallLoop_zero]
  | succ c ih =>
    intro X n M f hf hX hok
    have hlow : X % 256 = f 0 := by rw [hX]; exact pk_low (w := 8) (by simpa using hf)
    have hhigh : X >>> 8 = pk 8 (fun i => f (i + 1)) c := by rw [hX]; exact pk_high 8 (by simpa using hf)
    rw [smallLoop_succ, hlow, hhigh] at hok ⊢
    by_cases hcond : (decide (n < 33) || decide (1000000 * ((M + ((f 0 : ℕ) - 1)).natAbs *
        (M + ((f 0 : ℕ) - 1)).natAbs) ≤ 326041 * n)) = true
    · rw [hcond, Bool.cond_true] at hok ⊢
      obtain ⟨h1, h2⟩ := ih _ (n + 1) _ (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega)) rfl hok
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond
          rcases hcond with h | h
          · left; omega
          · right
            simp only [zero_add, sum_range_one, add_zero]
            have : ((M + ((f 0 : ℕ) - 1)) ^ 2 : ℤ) = ((M + ((f 0 : ℕ) - 1)).natAbs : ℤ) ^ 2 := by
              rw [Int.natAbs_sq]
            rw [this]; exact_mod_cast (by nlinarith : 10 ^ 6 * (M + ((f 0 : ℕ) - 1)).natAbs ^ 2 ≤ 326041 * n)
        · rcases h1 (i - 1) (by omega) with h | h
          · left; omega
          · right
            have key : M + ∑ e ∈ range (i + 1), ((f e : ℤ) - 1) =
                (M + ((f 0 : ℕ) - 1)) + ∑ e ∈ range (i - 1 + 1), ((f (e + 1) : ℤ) - 1) := by
              rw [sum_range_succ', show i - 1 + 1 = i by omega]; ring
            rw [key, show n + i = n + 1 + (i - 1) by omega]; exact h
      · rw [h2, sum_range_succ']; ring
    · rw [Bool.not_eq_true] at hcond
      rw [hcond, Bool.cond_false] at hok
      exact absurd hok (by simp)

theorem smallCheck_sound (L K lam : ℕ) (M0 Mend : ℤ) (h : smallCheck L K lam M0 Mend = true) :
    SegGood L (2 ^ K) M0 Mend := by
  unfold smallCheck at h
  simp only [Bool.and_eq_true, raw_ble, raw_shiftLeft, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
    decide_eq_true_eq, int_beq'_iff, Nat.shiftLeft_eq, one_mul] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hK, hL1⟩, hl1⟩, hl2⟩, hlam⟩, hmax⟩, hok⟩, hend⟩ := h
  rw [segMu1_eq L K lam hK hL1 hl1 hl2 hmax hlam] at hok hend
  generalize hS : 2 ^ K = S at *
  obtain ⟨hb, he⟩ := smallLoop_spec S _ L M0 (fun i => (μ (L + i) + 1).toNat)
    (fun i _ => by have := moebius_add_one_toNat_le (L + i); omega) rfl hok
  have hsum : ∀ m, ∑ e ∈ range m, (((μ (L + e) + 1).toNat : ℕ) - 1 : ℤ) = ∑ e ∈ range m, μ (L + e) :=
    fun m => sum_congr rfl fun e _ => by rw [moebius_add_one_toNat]; ring
  have hmert : ∀ m, mert (L - 1 + m) = mert (L - 1) + ∑ e ∈ range m, μ (L + e) := by
    intro m; rw [mert_add]; congr 1
    exact sum_congr rfl fun e _ => by rw [show L - 1 + 1 + e = L + e by omega]
  intro hM
  refine ⟨fun n hn1 hn2 hn3 => ?_, ?_⟩
  · rcases hb (n - L) (by omega) with h | h
    · omega
    · rw [hsum, show L + (n - L) = n by omega] at h
      have := hmert (n - L + 1)
      rw [show L - 1 + (n - L + 1) = n by omega, hM] at this
      rw [this]; exact h
  · rw [hend, he, hsum]
    have := hmert S
    rw [show L - 1 + S = L + S - 1 by omega, hM] at this
    exact this

end MoebiusCert
