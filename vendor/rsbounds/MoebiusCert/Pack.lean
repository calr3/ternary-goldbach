/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Bitwise

/-!
# Packed natural numbers

`pk w f n = ∑_{i<n} f i * 2^(w*i)`: the natural number whose `w`-bit fields are `f 0, …, f (n-1)`.
All the bit-parallel ("SWAR") computations of the kernel checkers are reduced to identities about
`pk`.
-/

namespace MoebiusCert

open Finset

/-- The packed number with `w`-bit fields `f 0, …, f (n-1)`. -/
def pk (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, f i * 2 ^ (w * i)

@[simp] lemma pk_zero (w : ℕ) (f : ℕ → ℕ) : pk w f 0 = 0 := by simp [pk]

lemma pk_succ (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : pk w f (n + 1) = pk w f n + f n * 2 ^ (w * n) := by
  simp [pk, sum_range_succ]

/-- Peel off the lowest field. -/
lemma pk_succ' (w : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    pk w f (n + 1) = f 0 + 2 ^ w * pk w (fun i => f (i + 1)) n := by
  rw [pk, sum_range_succ', pk, mul_sum]
  simp only [mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [mul_add, pow_add, mul_one]; ring

lemma pk_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : pk w f n = pk w g n :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

lemma pk_add (w : ℕ) (f g : ℕ → ℕ) (n : ℕ) : pk w f n + pk w g n = pk w (fun i => f i + g i) n := by
  simp [pk, ← sum_add_distrib, add_mul]

lemma pk_mul (w : ℕ) (c : ℕ) (f : ℕ → ℕ) (n : ℕ) : c * pk w f n = pk w (fun i => c * f i) n := by
  simp [pk, mul_sum, mul_assoc]

lemma pk_sub (w : ℕ) {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, g i ≤ f i) :
    pk w f n - pk w g n = pk w (fun i => f i - g i) n := by
  have : pk w f n = pk w (fun i => f i - g i) n + pk w g n := by
    rw [pk_add]; exact pk_congr fun i hi => by have := h i hi; omega
  omega

lemma pk_lt {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) : pk w f n < 2 ^ (w * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pk_succ]
    have h1 := ih fun i hi => hf i (by omega)
    have h2 : f n + 1 ≤ 2 ^ w := hf n (by omega)
    calc pk w f n + f n * 2 ^ (w * n) < 2 ^ (w * n) + f n * 2 ^ (w * n) := by omega
      _ = (f n + 1) * 2 ^ (w * n) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w * (n + 1)) := by rw [← pow_add]; ring_nf

lemma testBit_pk {w n : ℕ} (hw : 0 < w) {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) (t : ℕ) :
    (pk w f n).testBit t = (decide (t < w * n) && (f (t / w)).testBit (t % w)) := by
  induction n generalizing f t with
  | zero => simp
  | succ n ih =>
    rw [pk_succ', Nat.add_comm, Nat.testBit_two_pow_mul_add _ (hf 0 (by omega))]
    by_cases ht : t < w
    · simp [ht, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, show t < w * (n + 1) by nlinarith]
    · rw [if_neg ht, ih (fun i hi => hf (i + 1) (by omega))]
      obtain ⟨u, rfl⟩ : ∃ u, t = w + u := ⟨t - w, by omega⟩
      have h1 : (w + u) / w = u / w + 1 := by
        rw [Nat.add_comm, Nat.add_div_right _ hw]
      have h2 : (w + u) % w = u % w := by rw [Nat.add_comm, Nat.add_mod_right]
      simp only [Nat.add_sub_cancel_left, h1, h2]
      congr 1
      simp only [decide_eq_decide]
      constructor <;> intro h <;> nlinarith

lemma testBit_pk_of_lt {w n : ℕ} (hw : 0 < w) {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    {i b : ℕ} (hi : i < n) (hb : b < w) : (pk w f n).testBit (w * i + b) = (f i).testBit b := by
  rw [testBit_pk hw hf]
  have h1 : (w * i + b) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hb, zero_add]
  have h2 : (w * i + b) % w = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  rw [h1, h2]
  have : w * i + b < w * n := by nlinarith
  simp [this]

/-- The field decomposition of a bit position. -/
lemma testBit_pk_ge {w n : ℕ} (hw : 0 < w) {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    {t : ℕ} (ht : w * n ≤ t) : (pk w f n).testBit t = false := by
  rw [testBit_pk hw hf]; simp; omega

/-- Generic bitwise lemma: an operation that is bitwise on fields commutes with packing. -/
lemma pk_bitwise_eq {w n : ℕ} (hw : 0 < w) {f g h : ℕ → ℕ} {X Y : ℕ}
    (hf : ∀ i < n, f i < 2 ^ w) (hh : ∀ i < n, h i < 2 ^ w)
    (hX : ∀ t, X.testBit t = (decide (t < w * n) && (h (t / w)).testBit (t % w))) :
    X = pk w h n := by
  apply Nat.eq_of_testBit_eq; intro t; rw [hX, testBit_pk hw hh]

lemma pk_land {w n : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    (hg : ∀ i < n, g i < 2 ^ w) : pk w f n &&& pk w g n = pk w (fun i => f i &&& g i) n := by
  have hfg : ∀ i < n, (f i &&& g i) < 2 ^ w := fun i hi => Nat.and_lt_two_pow _ (hg i hi)
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_and, testBit_pk hw hf, testBit_pk hw hg, testBit_pk hw hfg, Nat.testBit_and]
  cases decide (t < w * n) <;> simp

lemma pk_lor {w n : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    (hg : ∀ i < n, g i < 2 ^ w) : pk w f n ||| pk w g n = pk w (fun i => f i ||| g i) n := by
  have hfg : ∀ i < n, (f i ||| g i) < 2 ^ w := fun i hi => Nat.or_lt_two_pow (hf i hi) (hg i hi)
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_or, testBit_pk hw hf, testBit_pk hw hg, testBit_pk hw hfg, Nat.testBit_or]
  cases decide (t < w * n) <;> simp

lemma pk_xor {w n : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    (hg : ∀ i < n, g i < 2 ^ w) : pk w f n ^^^ pk w g n = pk w (fun i => f i ^^^ g i) n := by
  have hfg : ∀ i < n, (f i ^^^ g i) < 2 ^ w := fun i hi => Nat.xor_lt_two_pow (hf i hi) (hg i hi)
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_xor, testBit_pk hw hf, testBit_pk hw hg, testBit_pk hw hfg, Nat.testBit_xor]
  cases decide (t < w * n) <;> simp

/-- Extract bits `b, b+1, …` of each field, masked by `m`. -/
lemma pk_shiftRight_land {w n : ℕ} (hw : 0 < w) {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    {b c m : ℕ} (hm : m < 2 ^ c) (hbc : b + c ≤ w) :
    (pk w f n >>> b) &&& pk w (fun _ => m) n = pk w (fun i => (f i >>> b) &&& m) n := by
  have hmw : m < 2 ^ w := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hr : ∀ i < n, ((f i >>> b) &&& m) < 2 ^ w := fun i _ => Nat.and_lt_two_pow _ hmw
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pk hw (fun i _ => hmw), testBit_pk hw hr,
    Nat.testBit_and, Nat.testBit_shiftRight]
  obtain ⟨j, u, hu, rfl⟩ : ∃ j u, u < w ∧ t = w * j + u :=
    ⟨t / w, t % w, Nat.mod_lt _ hw, (Nat.div_add_mod t w).symm⟩
  have e1 : (w * j + u) / w = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hu, zero_add]
  have e2 : (w * j + u) % w = u := by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  rw [e1, e2]
  by_cases hmu : m.testBit u
  · -- then u < c, so b + u < w
    have huc : u < c := by
      by_contra h; push Not at h
      exact absurd hmu (by rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h))]; simp)
    have hbu : b + u < w := by omega
    rw [show b + (w * j + u) = w * j + (b + u) by ring, testBit_pk hw hf]
    have e3 : (w * j + (b + u)) / w = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hbu, zero_add]
    have e4 : (w * j + (b + u)) % w = b + u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbu]
    rw [e3, e4, hmu]
    by_cases hj : j < n
    · have h1 : w * j + (b + u) < w * n := by nlinarith
      have h2 : w * j + u < w * n := by nlinarith
      simp [h1, h2]
    · have h1 : ¬ w * j + (b + u) < w * n := by intro h; apply hj; nlinarith
      have h2 : ¬ w * j + u < w * n := by intro h; apply hj; nlinarith
      simp [h1, h2]
  · simp [hmu]

/-! ### Shifting by whole fields -/

lemma pk_shift_one (w : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    pk w f n * 2 ^ w = pk w (fun i => if i = 0 then 0 else f (i - 1)) (n + 1) := by
  rw [pk_succ']
  have : (fun i => if i + 1 = 0 then 0 else f (i + 1 - 1)) = f := by
    funext i; simp
  rw [this]; simp; ring

lemma pk_shift (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) :
    pk w f n * 2 ^ (w * k) = pk w (fun i => if i < k then 0 else f (i - k)) (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, pow_add, ← mul_assoc, ih, pk_shift_one, ← add_assoc]
    apply pk_congr; intro i _
    by_cases h0 : i = 0
    · simp [h0]
    · simp only [h0, ite_false]
      by_cases h : i < k + 1
      · have : i - 1 < k := by omega
        simp [h, this]
      · have : ¬ i - 1 < k := by omega
        simp only [h, this, ite_false]; congr 1; omega

lemma pk_shiftLeft (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) :
    pk w f n <<< (w * k) = pk w (fun i => if i < k then 0 else f (i - k)) (n + k) := by
  rw [Nat.shiftLeft_eq, pk_shift]

/-- Splitting a packed number. -/
lemma pk_split (w : ℕ) (f : ℕ → ℕ) (m k : ℕ) :
    pk w f (m + k) = pk w f m + pk w (fun i => f (i + m)) k * 2 ^ (w * m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pk_succ, ih, pk_succ]
    rw [show w * (m + k) = w * k + w * m by ring, pow_add, add_comm k m]
    ring

lemma pk_mod {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) {m : ℕ} (hm : m ≤ n) :
    pk w f n % 2 ^ (w * m) = pk w f m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [pk_split, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (pk_lt fun i hi => hf i (by omega))]

lemma pk_shiftRight_top {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n + 1, f i < 2 ^ w) :
    pk w f (n + 1) >>> (w * n) = f n := by
  rw [Nat.shiftRight_eq_div_pow, pk_succ, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (pk_lt fun i hi => hf i (by omega)), zero_add]

lemma pk_low {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n + 1, f i < 2 ^ w) :
    pk w f (n + 1) % 2 ^ w = f 0 := by
  rw [pk_succ', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0 (by omega))]

lemma pk_high (w : ℕ) {n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n + 1, f i < 2 ^ w) :
    pk w f (n + 1) >>> w = pk w (fun i => f (i + 1)) n := by
  rw [Nat.shiftRight_eq_div_pow, pk_succ', Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (hf 0 (by omega)), zero_add]

/-! ### Sums of constant fields -/

lemma pk_const_lt {w n m : ℕ} (hm : m < 2 ^ w) : ∀ i < n, (fun _ => m) i < 2 ^ w := fun _ _ => hm

end MoebiusCert

namespace MoebiusCert

open Finset

/-- Interleaving: `2c`-bit fields `u b + 2^c v b` are pairs of `c`-bit fields. -/
lemma pk_refine (c : ℕ) (u v : ℕ → ℕ) (n : ℕ) :
    pk (2 * c) (fun b => u b + 2 ^ c * v b) n =
      pk c (fun i => if i % 2 = 0 then u (i / 2) else v (i / 2)) (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pk_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pk_succ, pk_succ]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    have h3 : (2 * n) / 2 = n := by omega
    have h4 : (2 * n + 1) / 2 = n := by omega
    simp only [h1, h2, h3, h4, if_true, show (1 : ℕ) ≠ 0 from one_ne_zero, if_false]
    rw [show c * (2 * n + 1) = c + 2 * c * n by ring, show c * (2 * n) = 2 * c * n by ring, pow_add]
    ring

/-- Extending a packed number with zero fields. -/
lemma pk_extend (w : ℕ) (g : ℕ → ℕ) (m j : ℕ) :
    pk w g m = pk w (fun i => if i < m then g i else 0) (m + j) := by
  rw [pk_split]
  have : pk w (fun i => if i + m < m then g (i + m) else 0) j = 0 := by
    rw [show (fun i => if i + m < m then g (i + m) else 0) = fun _ => 0 by funext i; simp]
    simp [pk]
  rw [this, zero_mul, add_zero]
  exact pk_congr fun i hi => by simp [hi]

/-- Shifting right by whole fields. -/
lemma pk_shiftRight_fields {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) {k : ℕ} (hk : k ≤ n) :
    pk w f n >>> (w * k) = pk w (fun i => if i + k < n then f (i + k) else 0) n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [Nat.shiftRight_eq_div_pow, pk_split, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (pk_lt fun i hi => hf i (by omega)), zero_add, pk_extend w _ j k]
  rw [add_comm j k]
  exact pk_congr fun i _ => by
    by_cases h : i < j
    · simp [h, show i + k < k + j by omega]
    · simp [h, show ¬ i + k < k + j by omega]

/-- Fields are determined by the packed number. -/
lemma pk_inj {w n : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ w)
    (h : pk w f n = pk w g n) : ∀ j < n, f j = g j := by
  intro j hj
  apply Nat.eq_of_testBit_eq; intro b
  by_cases hb : b < w
  · have h1 := testBit_pk_of_lt hw hf hj hb
    have h2 := testBit_pk_of_lt hw hg hj hb
    rw [← h1, ← h2, h]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end MoebiusCert
