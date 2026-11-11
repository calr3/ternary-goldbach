/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.Bridge

/-!
# Soundness of the segment checks for `(M)`

`SegGood L S M0 M1`: if `M(L-1) = M0` then `10^6 M(n)^2 ≤ 326041 n` for every `n ∈ [L, L+S)` with
`n ≥ 33`, and `M(L+S-1) = M1`. Both `largeCheck` and `smallCheck` imply it.
-/

namespace MoebiusCert

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The Mertens function. -/
def mert (n : ℕ) : ℤ := ∑ k ∈ Icc 1 n, μ k

lemma mert_zero : mert 0 = 0 := by simp [mert]

lemma mert_succ (n : ℕ) : mert (n + 1) = mert n + μ (n + 1) := by
  unfold mert; rw [sum_Icc_succ_top (by omega)]

lemma mert_add (a m : ℕ) : mert (a + m) = mert a + ∑ e ∈ range m, μ (a + 1 + e) := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, mert_succ, ih, sum_range_succ]; ring_nf

lemma abs_mert_sub (a m : ℕ) : |mert (a + m) - mert a| ≤ m := by
  rw [mert_add, add_sub_cancel_left]
  calc |∑ e ∈ range m, μ (a + 1 + e)| ≤ ∑ e ∈ range m, |μ (a + 1 + e)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ range m, (1 : ℤ) := sum_le_sum fun e _ => abs_moebius_le_one
    _ = m := by simp

lemma int_beq'_iff (a b : ℤ) : Int.beq' a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [Int.beq', raw_beq] <;> omega

/-- The segment predicate for `(M)`. -/
def SegGood (L S : ℕ) (M0 M1 : ℤ) : Prop :=
  mert (L - 1) = M0 →
    (∀ n, L ≤ n → n < L + S → 33 ≤ n → 10 ^ 6 * mert n ^ 2 ≤ 326041 * (n : ℤ)) ∧ mert (L + S - 1) = M1

lemma SegGood.trans {L S S' : ℕ} {M0 M1 M2 : ℤ} (h1 : SegGood L S M0 M1)
    (h2 : SegGood (L + S) S' M1 M2) : SegGood L (S + S') M0 M2 := by
  intro h0
  obtain ⟨b1, e1⟩ := h1 h0
  obtain ⟨b2, e2⟩ := h2 (by simpa using e1)
  refine ⟨fun n hn1 hn2 hn3 => ?_, by rw [← add_assoc]; exact e2⟩
  by_cases h : n < L + S
  · exact b1 n hn1 h hn3
  · exact b2 n (by omega) (by omega) hn3

/-- Chaining with explicit arithmetic side conditions (used by the generated modules). -/
lemma SegGood.trans_eq {L S L' S' T : ℕ} {M0 M1 M2 : ℤ} (h1 : SegGood L S M0 M1)
    (h2 : SegGood L' S' M1 M2) (hL : L + S = L') (hT : S + S' = T) : SegGood L T M0 M2 := by
  subst hL hT; exact h1.trans h2

lemma moebius_add_one_toNat (k : ℕ) : (((μ k + 1).toNat : ℕ) : ℤ) = μ k + 1 := by
  have := abs_moebius_le_one (n := k)
  rw [Int.toNat_of_nonneg (by rw [abs_le] at this; omega)]

lemma moebius_add_one_toNat_le (k : ℕ) : (μ k + 1).toNat ≤ 2 := by
  have := abs_moebius_le_one (n := k)
  rw [abs_le] at this; omega

/-! ### Large mode -/

lemma sum_groups (x : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ range m, (x (4 * j) + x (4 * j + 1) + x (4 * j + 2) + x (4 * j + 3)) = ∑ e ∈ range (4 * m), x e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ]
    ring

theorem largeCheck_sound (L K lam B : ℕ) (M0 Mend : ℤ) (h : largeCheck L K lam B M0 Mend = true) :
    SegGood L (2 ^ K) M0 Mend := by
  unfold largeCheck at h
  simp only [Bool.and_eq_true, raw_ble, raw_shiftLeft, Nat.add_eq, Nat.sub_eq,
    Nat.mul_eq, decide_eq_true_eq, int_beq'_iff, Nat.shiftLeft_eq, one_mul] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK2, hK24⟩, hL1⟩, hl1⟩, hl2⟩, hlam⟩, hmax⟩, hB⟩, hM0⟩, hok⟩, hend⟩ := h
  set S := 2 ^ K with hS
  set n4 := 2 ^ (K - 2) with hn4
  have hSn : S = 4 * n4 := by
    rw [hS, hn4, show K = K - 2 + 2 by omega, pow_add]; norm_num; ring
  have hn4pos : 1 ≤ n4 := Nat.one_le_two_pow
  have hn426 : n4 < 2 ^ 26 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [segMu1_eq L K lam (by omega) hL1 hl1 hl2 hmax hlam, ← hS, hSn,
    group4_eq n4 (fun i => (μ (L + i) + 1).toNat) (by omega)
      (fun i _ => by have := moebius_add_one_toNat_le (L + i); omega)] at hok hend
  simp only [Int.ofNat_eq_coe] at hok hend
  set x : ℕ → ℕ := fun i => (μ (L + i) + 1).toNat with hx
  set g : ℕ → ℕ := fun j => x (4 * j) + x (4 * j + 1) + x (4 * j + 2) + x (4 * j + 3) with hg
  have hg8 : ∀ j, g j ≤ 8 := fun j => by
    simp only [hg, hx]
    have := moebius_add_one_toNat_le (L + 4 * j); have := moebius_add_one_toNat_le (L + (4 * j + 1))
    have := moebius_add_one_toNat_le (L + (4 * j + 2)); have := moebius_add_one_toNat_le (L + (4 * j + 3))
    omega
  have hBle : B ≤ 20000 := by
    by_contra hc; push Not at hc
    have : 20001 * 20001 ≤ B * B := Nat.mul_le_mul hc hc
    omega
  have hK1 : (↑B - 2 + M0).toNat < 2 ^ 29 := by omega
  have hK2' : (↑B - 2 - M0).toNat < 2 ^ 29 := by omega
  obtain ⟨hlast, hband⟩ := bandCheck_spec n4 (K - 2) _ _ g hg8 hn4pos hn426 le_rfl hK1 hK2'
  -- Mertens values at the group ends
  intro hM
  have hmert : ∀ m, mert (L - 1 + m) = mert (L - 1) + ∑ e ∈ range m, ((x e : ℤ) - 1) := by
    intro m
    rw [mert_add]
    congr 1
    exact sum_congr rfl fun e _ => by
      simp only [hx]; rw [moebius_add_one_toNat, show L - 1 + 1 + e = L + e by omega]; ring
  have hP : ∀ j, ((∑ i ∈ range (j + 1), g i : ℕ) : ℤ) = mert (L - 1 + 4 * (j + 1)) - M0 + 4 * (j + 1) := by
    intro j
    rw [hmert, hM, sum_groups x (j + 1)]
    push_cast
    rw [sum_sub_distrib]
    simp
  have hbandZ : ∀ j < n4, |mert (L - 1 + 4 * (j + 1))| ≤ (B : ℤ) - 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hband hok j hj
    have e := hP j
    rw [abs_le]
    have h1' : (4 * (j + 1) : ℤ) ≤ ((∑ i ∈ range (j + 1), g i : ℕ) : ℤ) + ((↑B - 2 + M0).toNat : ℤ) := by
      exact_mod_cast h1
    have h2' : ((∑ i ∈ range (j + 1), g i : ℕ) : ℤ) ≤ 4 * (j + 1) + ((↑B - 2 - M0).toNat : ℤ) := by
      exact_mod_cast h2
    rw [Int.toNat_of_nonneg (by omega)] at h1' h2'
    constructor <;> omega
  have hM0' : |mert (L - 1)| ≤ (B : ℤ) - 2 := by rw [hM, abs_le]; omega
  refine ⟨fun n hn1 hn2 _ => ?_, ?_⟩
  · -- every `n` in the segment is within 2 of a checked value
    have hBn : |mert n| ≤ (B : ℤ) := by
      set t := n - L with ht
      set j := t / 4 with hj
      have hj4 : j < n4 := by omega
      have hlo : |mert (L - 1 + 4 * j)| ≤ (B : ℤ) - 2 := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, mul_zero, add_zero]; exact hM0'
        · have := hbandZ (j - 1) (by omega); rwa [show 4 * (j - 1 + 1) = 4 * j by omega] at this
      have hhi := hbandZ j hj4
      have d1 := abs_mert_sub (L - 1 + 4 * j) (n - (L - 1 + 4 * j))
      have d2 := abs_mert_sub n (L - 1 + 4 * (j + 1) - n)
      rw [show L - 1 + 4 * j + (n - (L - 1 + 4 * j)) = n by omega] at d1
      rw [show n + (L - 1 + 4 * (j + 1) - n) = L - 1 + 4 * (j + 1) by omega] at d2
      rw [abs_le] at *
      have : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have : t = 4 * j + t % 4 := by omega
      push_cast at d1 d2
      constructor <;> omega
    have hsq : mert n ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq' (by rw [abs_le] at hBn; linarith)
      (by rw [abs_le] at hBn; linarith)
    have : (10 ^ 6 : ℤ) * (B : ℤ) ^ 2 ≤ 326041 * (L : ℤ) := by exact_mod_cast (by nlinarith : 10 ^ 6 * B ^ 2 ≤ 326041 * L)
    nlinarith
  · rw [hend, hlast]
    have := hmert S
    rw [show L - 1 + S = L + S - 1 by omega, hM] at this
    rw [this, hSn, show (∑ i ∈ range n4, g i) = ∑ e ∈ range (4 * n4), x e from sum_groups x n4]
    push_cast
    rw [sum_sub_distrib]
    simp
    ring

end MoebiusCert
