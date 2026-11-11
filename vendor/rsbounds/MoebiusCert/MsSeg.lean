/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.SmallSeg
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Soundness of the `(m)` checks

`D·m(k)` is enclosed in `[lo, hi]` with `D = 10^20`, rounding `D/k` down and up. When
`(k+1)^16 ≤ 2^e`, `log(k+1) ≤ (e/16) log 2 < (e/16)·0.6931471808`.
-/

namespace MoebiusCert

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `m(n) = ∑_{k ≤ n} μ(k)/k`. -/
def msum (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (μ k : ℚ) / k

/-- The scale. -/
def Dsc : ℕ := 100000000000000000000

lemma msum_succ (n : ℕ) : msum (n + 1) = msum n + (μ (n + 1) : ℚ) / (n + 1 : ℕ) := by
  unfold msum; rw [sum_Icc_succ_top (by omega)]

/-- The enclosure invariant at the start of `k`. -/
def MsInv (k : ℕ) (lo hi : ℤ) : Prop :=
  (lo : ℚ) ≤ Dsc * msum (k - 1) ∧ (Dsc : ℚ) * msum (k - 1) ≤ hi

/-- The target inequality at `n`. -/
def MBound (n : ℕ) : Prop :=
  |∑ k ∈ Icc 1 n, (μ k : ℝ) / k| * Real.log ((n : ℝ) + 1) ≤ 0.03

/-- The segment predicate for `(m)`. -/
def MsGood (L S : ℕ) (lo0 hi0 lo1 hi1 : ℤ) : Prop :=
  MsInv L lo0 hi0 → (∀ n, L ≤ n → n < L + S → 11815 ≤ n → MBound n) ∧ MsInv (L + S) lo1 hi1

/-- Chaining with explicit arithmetic side conditions (used by the generated modules). -/
lemma MsGood.trans_eq {L S L' S' T : ℕ} {a b c d e f : ℤ} (h1 : MsGood L S a b c d)
    (h2 : MsGood L' S' c d e f) (hL : L + S = L') (hT : S + S' = T) : MsGood L T a b e f := by
  subst hL hT
  intro h0
  obtain ⟨b1, i1⟩ := h1 h0
  obtain ⟨b2, i2⟩ := h2 i1
  refine ⟨fun n hn1 hn2 hn3 => ?_, by rw [← add_assoc]; exact i2⟩
  by_cases h : n < L + S
  · exact b1 n hn1 h hn3
  · exact b2 n (by omega) (by omega) hn3

lemma MsGood.trans {L S S' : ℕ} {a b c d e f : ℤ} (h1 : MsGood L S a b c d)
    (h2 : MsGood (L + S) S' c d e f) : MsGood L (S + S') a b e f := by
  intro h0
  obtain ⟨b1, i1⟩ := h1 h0
  obtain ⟨b2, i2⟩ := h2 i1
  refine ⟨fun n hn1 hn2 hn3 => ?_, by rw [← add_assoc]; exact i2⟩
  by_cases h : n < L + S
  · exact b1 n hn1 h hn3
  · exact b2 n (by omega) (by omega) hn3

lemma floor_le (k : ℕ) (hk : 1 ≤ k) : ((Dsc / k : ℕ) : ℚ) ≤ (Dsc : ℚ) / k := Nat.cast_div_le

lemma le_ceil (k : ℕ) (hk : 1 ≤ k) : (Dsc : ℚ) / k ≤ (((Dsc + (k - 1)) / k : ℕ) : ℚ) := by
  rw [div_le_iff₀ (by exact_mod_cast hk)]
  have h1 := Nat.div_add_mod (Dsc + (k - 1)) k
  have h2 := Nat.mod_lt (Dsc + (k - 1)) (show 0 < k by omega)
  have : Dsc ≤ (Dsc + (k - 1)) / k * k := by
    rw [mul_comm]
    generalize k * ((Dsc + (k - 1)) / k) = X at h1 ⊢
    omega
  exact_mod_cast this

/-- One step of the enclosure. -/
lemma msInv_step (k : ℕ) (hk : 1 ≤ k) (lo hi : ℤ) (h : MsInv k lo hi) :
    MsInv (k + 1)
      (lo + if (μ k + 1).toNat = 2 then ((Dsc / k : ℕ) : ℤ)
        else if (μ k + 1).toNat = 0 then -(((Dsc + (k - 1)) / k : ℕ) : ℤ) else 0)
      (hi + if (μ k + 1).toNat = 2 then (((Dsc + (k - 1)) / k : ℕ) : ℤ)
        else if (μ k + 1).toNat = 0 then -((Dsc / k : ℕ) : ℤ) else 0) := by
  obtain ⟨h1, h2⟩ := h
  unfold MsInv
  rw [show k + 1 - 1 = (k - 1) + 1 by omega, msum_succ, show k - 1 + 1 = k by omega]
  have hfl := floor_le k hk
  have hce := le_ceil k hk
  have hm := abs_moebius_le_one (n := k)
  rw [abs_le] at hm
  rcases (by omega : μ k = -1 ∨ μ k = 0 ∨ μ k = 1) with hμ | hμ | hμ
  · simp only [hμ, show ((-1 : ℤ) + 1).toNat = 0 by rfl, show (0 : ℕ) ≠ 2 by norm_num, if_false, if_true]
    simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    have : (Dsc : ℚ) * (-1 / k) = -((Dsc : ℚ) / k) := by ring
    rw [mul_add, this]
    constructor <;> linarith
  · simp only [hμ, show ((0 : ℤ) + 1).toNat = 1 by rfl, show (1 : ℕ) ≠ 2 by norm_num,
      show (1 : ℕ) ≠ 0 by norm_num, if_false]
    simp only [Int.cast_add, Int.cast_zero, Int.cast_natCast, add_zero, zero_div]; exact ⟨h1, h2⟩
  · simp only [hμ, show ((1 : ℤ) + 1).toNat = 2 by rfl, if_true]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [mul_add, one_div, ← div_eq_mul_inv]
    constructor <;> linarith

/-- The check implies the bound. -/
lemma mbound_of_check (k : ℕ) (hk : 1 ≤ k) (lo hi : ℤ) (e : ℕ) (h : MsInv (k + 1) lo hi)
    (he : (k + 1) ^ 16 ≤ 2 ^ e)
    (hA : max lo.natAbs hi.natAbs * e * 6931471808 ≤ 48 * (Dsc * 100000000)) : MBound k := by
  obtain ⟨h1, h2⟩ := h
  rw [show k + 1 - 1 = k by omega] at h1 h2
  unfold MBound
  have hcast : (∑ i ∈ Icc 1 k, (μ i : ℝ) / i) = ((msum k : ℚ) : ℝ) := by
    unfold msum; push_cast; rfl
  rw [hcast]
  set m : ℝ := ((msum k : ℚ) : ℝ)
  set A : ℝ := ((max lo.natAbs hi.natAbs : ℕ) : ℝ)
  have hD : (0 : ℝ) < Dsc := by unfold Dsc; norm_num
  -- |D m| ≤ A
  have h1' : (lo : ℝ) ≤ Dsc * m := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2' : (Dsc : ℝ) * m ≤ hi := by
    have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; exact this
  have hlo : |(lo : ℝ)| ≤ A := by
    simp only [A]; rw [Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]; exact le_max_left _ _
  have hhi : |(hi : ℝ)| ≤ A := by
    simp only [A]; rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact le_max_right _ _
  have hDm : |Dsc * m| ≤ A := by
    rw [abs_le] at hlo hhi ⊢; constructor <;> linarith
  have hm : |m| ≤ A / Dsc := by
    rw [abs_mul, abs_of_pos hD] at hDm
    rw [le_div_iff₀ hD]; linarith
  -- log bound
  have hlog : Real.log ((k : ℝ) + 1) ≤ e * Real.log 2 / 16 := by
    have : ((k : ℝ) + 1) ^ 16 ≤ (2 : ℝ) ^ e := by exact_mod_cast he
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogpos : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith)
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have he0 : (0 : ℝ) ≤ e := by positivity
  have hAe : A * e * 6931471808 ≤ 48 * (Dsc * 100000000) := by simp only [A]; exact_mod_cast hA
  calc |m| * Real.log ((k : ℝ) + 1) ≤ (A / Dsc) * (e * Real.log 2 / 16) :=
        mul_le_mul hm hlog hlogpos (by positivity)
    _ ≤ (A / Dsc) * (e * 0.6931471808 / 16) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hlog2.le he0
    _ = (A * e * 6931471808) / (Dsc * 160000000000) := by field_simp; ring
    _ ≤ (48 * (Dsc * 100000000)) / (Dsc * 160000000000) := by
        apply div_le_div_of_nonneg_right hAe (by positivity)
    _ = 0.03 := by field_simp; norm_num


lemma msLoop_zero (X k : ℕ) (lo hi : ℤ) (e : ℕ) : msLoop 0 X k lo hi e = (true, (lo, hi, e)) := rfl

/-- Lower end after one step (kernel form). -/
def stLoR (f k : ℕ) (lo : ℤ) : ℤ :=
  lo + cond (Nat.beq f 2) (Int.ofNat (Nat.div 100000000000000000000 k))
    (cond (Nat.beq f 0) (-(Int.ofNat (Nat.div (Nat.add 100000000000000000000 (Nat.sub k 1)) k))) 0)
/-- Upper end after one step (kernel form). -/
def stHiR (f k : ℕ) (hi : ℤ) : ℤ :=
  hi + cond (Nat.beq f 2) (Int.ofNat (Nat.div (Nat.add 100000000000000000000 (Nat.sub k 1)) k))
    (cond (Nat.beq f 0) (-(Int.ofNat (Nat.div 100000000000000000000 k))) 0)
/-- Exponent after one step (kernel form). -/
def stER (k e : ℕ) : ℕ :=
  Nat.add e (cond (Nat.ble 11815 k && !Nat.ble (Nat.pow (Nat.add k 1) 16) (Nat.pow 2 e)) 1 0)
/-- The per-step check (kernel form). -/
def stOK (k : ℕ) (lo hi : ℤ) (e : ℕ) : Bool :=
  !Nat.ble 11815 k || (Nat.ble (Nat.pow (Nat.add k 1) 16) (Nat.pow 2 e) &&
    Nat.ble (Nat.mul (Nat.mul (Nat.max (Int.natAbs lo) (Int.natAbs hi)) e) 6931471808)
      (Nat.mul 48 (Nat.mul 100000000000000000000 100000000)))

lemma msLoop_succ (c X k : ℕ) (lo hi : ℤ) (e : ℕ) : msLoop (c + 1) X k lo hi e =
    cond (stOK k (stLoR (Nat.mod X 256) k lo) (stHiR (Nat.mod X 256) k hi) (stER k e))
      (msLoop c (Nat.shiftRight X 8) (Nat.add k 1) (stLoR (Nat.mod X 256) k lo) (stHiR (Nat.mod X 256) k hi)
        (stER k e))
      (false, (stLoR (Nat.mod X 256) k lo, stHiR (Nat.mod X 256) k hi, stER k e)) := rfl

lemma stLoR_eq (f k : ℕ) (lo : ℤ) : stLoR f k lo =
    lo + if f = 2 then ((Dsc / k : ℕ) : ℤ) else if f = 0 then -(((Dsc + (k - 1)) / k : ℕ) : ℤ) else 0 := by
  unfold stLoR Dsc; simp only [raw_beq, raw_div, Nat.add_eq, Nat.sub_eq, Bool.cond_decide, Int.ofNat_eq_coe]

lemma stHiR_eq (f k : ℕ) (hi : ℤ) : stHiR f k hi =
    hi + if f = 2 then (((Dsc + (k - 1)) / k : ℕ) : ℤ) else if f = 0 then -((Dsc / k : ℕ) : ℤ) else 0 := by
  unfold stHiR Dsc; simp only [raw_beq, raw_div, Nat.add_eq, Nat.sub_eq, Bool.cond_decide, Int.ofNat_eq_coe]

lemma stOK_iff (k : ℕ) (lo hi : ℤ) (e : ℕ) : stOK k lo hi e = true ↔
    (¬ 11815 ≤ k ∨ ((k + 1) ^ 16 ≤ 2 ^ e ∧
      max lo.natAbs hi.natAbs * e * 6931471808 ≤ 48 * (Dsc * 100000000))) := by
  unfold stOK Dsc
  simp only [raw_ble, raw_max, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]

theorem msLoop_spec : ∀ (c X k : ℕ) (lo hi : ℤ) (e : ℕ) (f : ℕ → ℕ),
    (∀ i < c, f i = (μ (k + i) + 1).toNat) → X = pk 8 f c → 1 ≤ k → MsInv k lo hi →
    (msLoop c X k lo hi e).1 = true →
      (∀ i < c, 11815 ≤ k + i → MBound (k + i)) ∧
      MsInv (k + c) (msLoop c X k lo hi e).2.1 (msLoop c X k lo hi e).2.2.1 := by
  intro c
  induction c with
  | zero => intro X k lo hi e f _ _ _ hinv _; simpa [msLoop_zero] using hinv
  | succ c ih =>
    intro X k lo hi e f hf hX hk hinv hok
    have hf256 : ∀ i < c + 1, f i < 256 := fun i hi => by
      rw [hf i hi]; have := moebius_add_one_toNat_le (k + i); omega
    have hlow : Nat.mod X 256 = (μ k + 1).toNat := by
      rw [raw_mod, hX, show (256 : ℕ) = 2 ^ 8 by norm_num, pk_low hf256, hf 0 (by omega), add_zero]
    have hhigh : Nat.shiftRight X 8 = pk 8 (fun i => f (i + 1)) c := by
      rw [raw_shiftRight, hX]; exact pk_high 8 hf256
    have hstep := msInv_step k hk lo hi hinv
    rw [← stLoR_eq, ← stHiR_eq] at hstep
    rw [msLoop_succ, hlow, hhigh] at hok ⊢
    cases hc : stOK k (stLoR (μ k + 1).toNat k lo) (stHiR (μ k + 1).toNat k hi) (stER k e)
    · simp only [hc, Bool.cond_false] at hok; exact absurd hok (by simp)
    simp only [hc, Bool.cond_true, Nat.add_eq] at hok ⊢
    obtain ⟨h1, h2⟩ := ih _ (k + 1) _ _ _ (fun i => f (i + 1))
      (fun i hi => by rw [hf (i + 1) (by omega)]; ring_nf) rfl (by omega) hstep hok
    refine ⟨fun i hi hbig => ?_, by rw [show k + (c + 1) = k + 1 + c by ring]; exact h2⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [add_zero] at hbig ⊢
      rcases (stOK_iff _ _ _ _).1 hc with h | ⟨he, hA⟩
      · exact absurd hbig h
      · exact mbound_of_check k hk _ _ _ hstep he hA
    · have := h1 (i - 1) (by omega) (by omega)
      rwa [show k + 1 + (i - 1) = k + i by omega] at this


theorem msCheck_sound (L K lam : ℕ) (lo0 hi0 : ℤ) (e0 : ℕ) (lo1 hi1 : ℤ) (e1 : ℕ)
    (h : msCheck L K lam lo0 hi0 e0 lo1 hi1 e1 = true) : MsGood L (2 ^ K) lo0 hi0 lo1 hi1 := by
  unfold msCheck at h
  simp only [Bool.and_eq_true, raw_ble, raw_beq, raw_shiftLeft, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
    decide_eq_true_eq, int_beq'_iff, Nat.shiftLeft_eq, one_mul] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hK, hL1⟩, hl1⟩, hl2⟩, hlam⟩, hmax⟩, hok⟩, hlo⟩, hhi⟩, -⟩ := h
  rw [segMu1_eq L K lam hK hL1 hl1 hl2 hmax hlam] at hok hlo hhi
  intro hinv
  obtain ⟨hb, hi⟩ := msLoop_spec (2 ^ K) _ L lo0 hi0 e0 (fun i => (μ (L + i) + 1).toNat)
    (fun i _ => rfl) rfl hL1 hinv hok
  refine ⟨fun n hn1 hn2 hn3 => ?_, by rw [hlo, hhi]; exact hi⟩
  have := hb (n - L) (by omega) (by omega)
  rwa [show L + (n - L) = n by omega] at this


end MoebiusCert
