/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.Pack
import MoebiusCert.Defs
import MoebiusCert.Raw
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Soundness of the sieve passes

Each kernel function of `MoebiusCert.Defs` is identified with a packed number `pk w f n`.
-/

namespace MoebiusCert

open Finset

/-! ### Repunits -/

lemma repB_zero (base d m : ℕ) : repB base d 0 m = 0 := rfl

lemma repB_succ_raw (base d fuel m : ℕ) : repB base d (fuel + 1) m =
    cond (Nat.beq m 0) 0
      (cond (Nat.beq (Nat.mod m 2) 0)
        (Nat.add (repB base d fuel (Nat.div m 2))
          (Nat.shiftLeft (repB base d fuel (Nat.div m 2)) (Nat.mul d (Nat.div m 2))))
        (Nat.add (Nat.add (repB base d fuel (Nat.div m 2))
          (Nat.shiftLeft (repB base d fuel (Nat.div m 2)) (Nat.mul d (Nat.div m 2))))
          (Nat.shiftLeft base (Nat.mul d (Nat.mul 2 (Nat.div m 2)))))) := rfl

lemma repB_succ (base d fuel m : ℕ) : repB base d (fuel + 1) m =
    if m = 0 then 0 else
      if m % 2 = 0 then repB base d fuel (m / 2) + (repB base d fuel (m / 2) <<< (d * (m / 2)))
      else repB base d fuel (m / 2) + (repB base d fuel (m / 2) <<< (d * (m / 2))) +
          (base <<< (d * (2 * (m / 2)))) := by
  rw [repB_succ_raw]; raw_norm

lemma pk_const_add (w c a b : ℕ) :
    pk w (fun _ => c) (a + b) = pk w (fun _ => c) a + pk w (fun _ => c) b * 2 ^ (w * a) :=
  pk_split w _ a b

theorem repB_eq (base d : ℕ) : ∀ (fuel m : ℕ), m < 2 ^ fuel → repB base d fuel m = pk d (fun _ => base) m := by
  intro fuel
  induction fuel with
  | zero => intro m hm; simp at hm; subst hm; simp [repB_zero]
  | succ fuel ih =>
    intro m hm
    rw [repB_succ]
    by_cases h0 : m = 0
    · subst h0; simp
    rw [if_neg h0]
    have hh : m / 2 < 2 ^ fuel := by rw [pow_succ] at hm; omega
    rw [ih _ hh, Nat.shiftLeft_eq, ← pk_const_add]
    by_cases hm2 : m % 2 = 0
    · rw [if_pos hm2]; congr 1; omega
    · rw [if_neg hm2, Nat.shiftLeft_eq, show 2 * (m / 2) = m / 2 + m / 2 by ring, ← pk_succ]
      congr 1; omega

lemma ones_eq (d n : ℕ) (hn : n < 2 ^ 32) : ones d n = pk d (fun _ => 1) n := repB_eq 1 d 32 n hn

/-! ### Arithmetic progressions -/

lemma firstOff_eq (L q : ℕ) : firstOff L q = (q - L % q) % q := rfl

lemma firstOff_lt {L q : ℕ} (hq : 0 < q) : firstOff L q < q := by
  rw [firstOff_eq]; exact Nat.mod_lt _ hq

lemma dvd_add_firstOff {L q : ℕ} (hq : 0 < q) : q ∣ L + firstOff L q := by
  rw [firstOff_eq, Nat.dvd_iff_mod_eq_zero]
  have hb := Nat.mod_lt L hq
  by_cases hb0 : L % q = 0
  · rw [hb0, Nat.sub_zero, Nat.mod_self, add_zero, hb0]
  · rw [Nat.mod_eq_of_lt (by omega : q - L % q < q), Nat.add_mod, Nat.mod_eq_of_lt (by omega : q - L % q < q)]
    rw [show L % q + (q - L % q) = q by omega, Nat.mod_self]

lemma dvd_iff_firstOff {L q : ℕ} (hq : 0 < q) (i : ℕ) :
    q ∣ L + i ↔ firstOff L q ≤ i ∧ q ∣ i - firstOff L q := by
  have hr := firstOff_lt (L := L) hq
  have hd := dvd_add_firstOff (L := L) hq
  constructor
  · intro h
    by_cases hi : firstOff L q ≤ i
    · refine ⟨hi, ?_⟩
      have := Nat.dvd_sub h hd
      rwa [show L + i - (L + firstOff L q) = i - firstOff L q by omega] at this
    · exfalso
      have := Nat.dvd_sub hd h
      rw [show L + firstOff L q - (L + i) = firstOff L q - i by omega] at this
      have := Nat.le_of_dvd (by omega) this
      omega
  · rintro ⟨hi, h⟩
    have := Nat.dvd_add hd h
    rwa [show L + firstOff L q + (i - firstOff L q) = L + i by omega] at this

/-- The closed form of the progression pattern equals the packed indicator. -/
theorem prog_eq (w c : ℕ) {L q : ℕ} (hq : 0 < q) (S : ℕ) :
    (if firstOff L q < S then pk (w * q) (fun _ => c * 2 ^ (w * firstOff L q)) ((S - 1 - firstOff L q) / q + 1)
      else 0) = pk w (fun i => if q ∣ L + i then c else 0) S := by
  set r := firstOff L q with hr_def
  have hr : r < q := firstOff_lt hq
  induction S with
  | zero => simp
  | succ S ih =>
    conv_rhs => rw [pk_succ]
    rw [← ih]
    rcases lt_trichotomy S r with h | h | h
    · have h1 : ¬ r < S + 1 := by omega
      have h2 : ¬ r < S := by omega
      have h3 : ¬ q ∣ L + S := by rw [dvd_iff_firstOff hq]; omega
      simp [h1, h2, h3]
    · subst h
      have h3 : q ∣ L + r := dvd_add_firstOff hq
      simp [h3, pk_succ]
    · have h1 : r < S + 1 := by omega
      simp only [h1, h, if_true]
      have ht : S + 1 - 1 - r = (S - 1 - r) + 1 := by omega
      rw [ht, Nat.succ_div]
      by_cases hdq : q ∣ S - 1 - r + 1
      · have hd2 : q ∣ L + S := by
          rw [dvd_iff_firstOff hq]; refine ⟨by omega, ?_⟩; rwa [show S - r = S - 1 - r + 1 by omega]
        rw [if_pos hdq, if_pos hd2, pk_succ]
        congr 1
        rw [mul_assoc, ← pow_add]
        congr 2
        rw [show (S - 1 - r) / q + 1 = (S - 1 - r + 1) / q by rw [Nat.succ_div, if_pos hdq]]
        rw [mul_assoc, Nat.mul_div_cancel' hdq, ← mul_add]
        congr 1; omega
      · have hd2 : ¬ q ∣ L + S := by
          rw [dvd_iff_firstOff hq]; rintro ⟨_, h'⟩; apply hdq; rwa [show S - r = S - 1 - r + 1 by omega] at h'
        rw [if_neg hdq, if_neg hd2]; simp

theorem patt_eq (w L S q c : ℕ) (hq : 0 < q) (hS : S < 2 ^ 32) :
    patt w L S q c = pk w (fun i => if q ∣ L + i then c else 0) S := by
  rw [← prog_eq w c hq S]
  unfold patt
  raw_norm
  by_cases h : firstOff L q < S
  · rw [if_pos h, if_pos h, repB_eq _ _ _ _ (by
      have : (S - 1 - firstOff L q) / q + 1 ≤ S := by
        have := Nat.div_le_self (S - 1 - firstOff L q) q; omega
      omega)]
    congr 1
    funext _; rw [Nat.shiftLeft_eq]
  · rw [if_neg h, if_neg h]

theorem addPatt_eq (w L S q c acc : ℕ) : addPatt w L S q c acc = acc + patt w L S q c := by
  unfold addPatt patt
  raw_norm
  split_ifs <;> simp

theorem orPatt_eq (L S q acc : ℕ) : orPatt L S q acc = acc ||| patt 1 L S q 1 := by
  unfold orPatt patt
  raw_norm
  split_ifs <;> simp

/-- Bits of a 1-bit-layout pattern. -/
lemma testBit_patt1 (L S q : ℕ) (hq : 0 < q) (hS : S < 2 ^ 32) (t : ℕ) :
    (patt 1 L S q 1).testBit t = (decide (t < S) && decide (q ∣ L + t)) := by
  rw [patt_eq 1 L S q 1 hq hS, testBit_pk (by norm_num) (fun i _ => by split_ifs <;> norm_num)]
  simp only [Nat.div_one, Nat.mod_one, one_mul]
  by_cases h : q ∣ L + t <;> simp [h]

/-! ### The three passes -/

lemma pk_zero_fun (w n : ℕ) : pk w (fun _ => 0) n = 0 := by simp [pk]

lemma vPass_nil (L S acc : ℕ) : vPass L S [] acc = acc := rfl
lemma vPass_cons (L S : ℕ) (pa : ℕ × ℕ) (l : List (ℕ × ℕ)) (acc : ℕ) :
    vPass L S (pa :: l) acc = vPass L S l (addPatt 8 L S pa.1 pa.2 acc) := rfl

theorem vPass_eq (L S : ℕ) (hS : S < 2 ^ 32) :
    ∀ (l : List (ℕ × ℕ)) (acc : ℕ), (∀ pa ∈ l, 0 < pa.1) →
      vPass L S l acc = acc + pk 8 (fun i => (l.map fun pa => if pa.1 ∣ L + i then pa.2 else 0).sum) S := by
  intro l
  induction l with
  | nil => intro acc _; simp [vPass_nil, pk_zero_fun]
  | cons pa l ih =>
    intro acc hl
    rw [vPass_cons, ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)), addPatt_eq,
      patt_eq _ _ _ _ _ (hl pa List.mem_cons_self) hS, add_assoc, pk_add]
    simp [List.map_cons, List.sum_cons]

lemma mPass_nil (L S c0 c1 : ℕ) : mPass L S [] c0 c1 = (c0, c1) := rfl
lemma mPass_cons (L S p : ℕ) (l : List ℕ) (c0 c1 : ℕ) :
    mPass L S (p :: l) c0 c1 =
      mPass L S l (c0 ||| patt 1 L S p 1) (c1 ||| (c0 &&& patt 1 L S p 1)) := rfl

/-- The medium pass keeps a saturating count (≥ 1, ≥ 2) of the primes dividing `L + t`. -/
theorem mPass_spec (L S : ℕ) (hS : S < 2 ^ 32) :
    ∀ (l : List ℕ) (c0 c1 : ℕ) (g : ℕ → ℕ), (∀ p ∈ l, 0 < p) →
      (∀ t, c0.testBit t = (decide (t < S) && decide (1 ≤ g t))) →
      (∀ t, c1.testBit t = (decide (t < S) && decide (2 ≤ g t))) →
      (∀ t, (mPass L S l c0 c1).1.testBit t =
          (decide (t < S) && decide (1 ≤ g t + l.countP (fun p => p ∣ L + t)))) ∧
      (∀ t, (mPass L S l c0 c1).2.testBit t =
          (decide (t < S) && decide (2 ≤ g t + l.countP (fun p => p ∣ L + t)))) := by
  intro l
  induction l with
  | nil => intro c0 c1 g _ h0 h1; simpa [mPass_nil] using ⟨h0, h1⟩
  | cons p l ih =>
    intro c0 c1 g hl h0 h1
    have hp : 0 < p := hl p List.mem_cons_self
    rw [mPass_cons]
    have := ih (c0 ||| patt 1 L S p 1) (c1 ||| (c0 &&& patt 1 L S p 1))
      (fun t => g t + if p ∣ L + t then 1 else 0) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun t => by
        rw [Nat.testBit_or, h0, testBit_patt1 L S p hp hS]
        by_cases ht : t < S <;> by_cases hd : p ∣ L + t <;> simp [ht, hd])
      (fun t => by
        rw [Nat.testBit_or, Nat.testBit_and, h0, h1, testBit_patt1 L S p hp hS]
        by_cases ht : t < S <;> by_cases hd : p ∣ L + t <;> simp [ht, hd] <;> omega)
    simp only [List.countP_cons] at this ⊢
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [this.1 t]; by_cases hd : p ∣ L + t <;> simp [hd]; ring_nf
    · rw [this.2 t]; by_cases hd : p ∣ L + t <;> simp [hd]; ring_nf

lemma fPass_nil (L S F : ℕ) : fPass L S [] F = F := rfl
lemma fPass_cons (L S p : ℕ) (l : List ℕ) (F : ℕ) :
    fPass L S (p :: l) F = fPass L S l (orPatt L S (p * p) F) := rfl

theorem fPass_spec (L S : ℕ) (hS : S < 2 ^ 32) :
    ∀ (l : List ℕ) (F : ℕ), (∀ p ∈ l, 0 < p) → ∀ t,
      (fPass L S l F).testBit t = (F.testBit t || (decide (t < S) && decide (∃ p ∈ l, p * p ∣ L + t))) := by
  intro l
  induction l with
  | nil => intro F _ t; simp [fPass_nil]
  | cons p l ih =>
    intro F hl t
    have hp : 0 < p := hl p List.mem_cons_self
    rw [fPass_cons, ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)), orPatt_eq, Nat.testBit_or,
      testBit_patt1 L S (p * p) (Nat.mul_pos hp hp) hS]
    by_cases ht : t < S
    · by_cases hd : p * p ∣ L + t
      · simp [ht, hd]
      · simp only [ht, hd, decide_true, decide_false, Bool.and_false, Bool.or_false, Bool.true_and,
          List.mem_cons, exists_eq_or_imp, false_or]
    · simp [ht]


/-! ### Morton spread -/

/-- The `j`-th `k`-bit chunk of `X`. -/
def blk (X k j : ℕ) : ℕ := (X >>> (k * j)) % 2 ^ k

lemma blk_lt (X k j : ℕ) : blk X k j < 2 ^ k := Nat.mod_lt _ (by positivity)

lemma blk_low (X h b : ℕ) : blk X (2 * h) b &&& (2 ^ h - 1) = blk X h (2 * b) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [blk, Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < h
  · simp [hi, show i < 2 * h by omega, show 2 * h * b = h * (2 * b) by ring]
  · simp [hi]

lemma blk_high (X h b : ℕ) :
    blk X (2 * h) b &&& ((2 ^ h - 1) * 2 ^ h) = blk X h (2 * b + 1) * 2 ^ h := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [blk, Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : h ≤ i
  · by_cases hi2 : i < 2 * h
    · simp [hi, hi2, show i - h < h by omega, show h * (2 * b + 1) + (i - h) = 2 * h * b + i by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm h 2]; omega]
    · simp [hi2, show ¬ i - h < h by omega]
  · simp [hi]

lemma spStep_eq' (S h X : ℕ) : spStep S h X =
    (X &&& repB (2 ^ h - 1) (16 * h) 32 (S / (2 * h))) |||
      ((X &&& (repB (2 ^ h - 1) (16 * h) 32 (S / (2 * h)) <<< h)) <<< (7 * h)) := by
  show Nat.lor (Nat.land X _) _ = _
  raw_norm
  rw [Nat.shiftLeft_eq, one_mul]

/-- One Morton level. -/
theorem spStep_eq (X h n S : ℕ) (hh : 0 < h) (hn : S / (2 * h) = n) (hn32 : n < 2 ^ 32) :
    spStep S h (pk (16 * h) (fun b => blk X (2 * h) b) n) = pk (8 * h) (fun c => blk X h c) (2 * n) := by
  have hw : 0 < 16 * h := by omega
  have hpow : ∀ a, a ≤ 16 * h → 2 ^ a ≤ 2 ^ (16 * h) := fun a ha => Nat.pow_le_pow_right (by norm_num) ha
  have hB : ∀ i < n, blk X (2 * h) i < 2 ^ (16 * h) := fun i _ =>
    lt_of_lt_of_le (blk_lt _ _ _) (hpow _ (by omega))
  have hLO : (2 ^ h - 1) < 2 ^ (16 * h) := lt_of_lt_of_le (by have := Nat.one_le_two_pow (n := h); omega) (hpow h (by omega))
  have hHI : (2 ^ h - 1) * 2 ^ h < 2 ^ (16 * h) := by
    calc (2 ^ h - 1) * 2 ^ h < 2 ^ h * 2 ^ h := by
          apply Nat.mul_lt_mul_of_pos_right _ (by positivity); have := Nat.one_le_two_pow (n := h); omega
      _ = 2 ^ (2 * h) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (16 * h) := hpow _ (by omega)
  have eLO : repB (2 ^ h - 1) (16 * h) 32 n = pk (16 * h) (fun _ => 2 ^ h - 1) n := repB_eq _ _ _ _ hn32
  have eLOsh : pk (16 * h) (fun _ => 2 ^ h - 1) n <<< h = pk (16 * h) (fun _ => 2 ^ h * (2 ^ h - 1)) n := by
    rw [Nat.shiftLeft_eq, mul_comm, pk_mul]
  have eA : pk (16 * h) (fun b => blk X (2 * h) b) n &&& pk (16 * h) (fun _ => 2 ^ h - 1) n =
      pk (16 * h) (fun b => blk X h (2 * b)) n := by
    rw [pk_land hw hB (fun _ _ => hLO)]; simp only [blk_low]
  have eB : pk (16 * h) (fun b => blk X (2 * h) b) n &&& pk (16 * h) (fun _ => 2 ^ h * (2 ^ h - 1)) n =
      pk (16 * h) (fun b => blk X h (2 * b + 1) * 2 ^ h) n := by
    rw [pk_land hw hB (fun _ _ => by rw [mul_comm]; exact hHI)]
    apply pk_congr; intro b _; rw [mul_comm (2 ^ h), blk_high]
  have eC : pk (16 * h) (fun b => blk X h (2 * b + 1) * 2 ^ h) n <<< (7 * h) =
      pk (16 * h) (fun b => 2 ^ (8 * h) * blk X h (2 * b + 1)) n := by
    rw [Nat.shiftLeft_eq, mul_comm, pk_mul]
    apply pk_congr; intro b _
    rw [show 8 * h = 7 * h + h by ring, pow_add]; ring
  have hlo : ∀ i < n, blk X h (2 * i) < 2 ^ (16 * h) := fun i _ =>
    lt_of_lt_of_le (blk_lt _ _ _) (hpow _ (by omega))
  have hhi : ∀ i < n, 2 ^ (8 * h) * blk X h (2 * i + 1) < 2 ^ (16 * h) := by
    intro i _
    calc 2 ^ (8 * h) * blk X h (2 * i + 1) < 2 ^ (8 * h) * 2 ^ h :=
          Nat.mul_lt_mul_of_pos_left (blk_lt _ _ _) (by positivity)
      _ = 2 ^ (9 * h) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (16 * h) := hpow _ (by omega)
  rw [spStep_eq', hn, eLO, eLOsh, eA, eB, eC, pk_lor hw hlo hhi]
  have eor : ∀ i, (blk X h (2 * i) ||| 2 ^ (8 * h) * blk X h (2 * i + 1)) =
      blk X h (2 * i) + 2 ^ (8 * h) * blk X h (2 * i + 1) := by
    intro i
    rw [Nat.lor_comm, ← Nat.two_pow_add_eq_or_of_lt (blk_lt X h (2 * i) |>.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))), add_comm]
  simp only [eor]
  rw [show 16 * h = 2 * (8 * h) by ring, pk_refine]
  apply pk_congr; intro i _
  split_ifs with h2
  · congr 1; omega
  · congr 1; omega



lemma spreadAux_zero (S X : ℕ) : spreadAux S 0 X = X := rfl
lemma spreadAux_succ (S t X : ℕ) : spreadAux S (t + 1) X = spreadAux S t (spStep S (Nat.shiftLeft 1 t) X) := rfl

theorem spreadAux_eq (X K : ℕ) (hK : K ≤ 32) : ∀ t ≤ K,
    spreadAux (2 ^ K) t (pk (8 * 2 ^ t) (fun b => blk X (2 ^ t) b) (2 ^ K / 2 ^ t)) =
      pk 8 (fun i => blk X 1 i) (2 ^ K) := by
  intro t
  induction t with
  | zero => intro _; simp [spreadAux_zero]
  | succ t ih =>
    intro ht
    rw [spreadAux_succ, show Nat.shiftLeft 1 t = 2 ^ t by rw [raw_shiftLeft, Nat.shiftLeft_eq, one_mul]]
    have hdiv : 2 ^ K / 2 ^ (t + 1) * 2 = 2 ^ K / 2 ^ t := by
      rw [Nat.pow_div (by omega) (by norm_num), Nat.pow_div (by omega) (by norm_num), ← pow_succ]
      congr 1; omega
    rw [show 8 * 2 ^ (t + 1) = 16 * 2 ^ t by ring, show 2 ^ (t + 1) = 2 * 2 ^ t by ring]
    rw [spStep_eq X (2 ^ t) (2 ^ K / (2 * 2 ^ t)) (2 ^ K) (by positivity) rfl (by
      rw [← show 2 ^ (t + 1) = 2 * 2 ^ t by ring, Nat.pow_div (by omega) (by norm_num)]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega))]
    rw [show 2 * (2 ^ K / (2 * 2 ^ t)) = 2 ^ K / 2 ^ t by
      rw [← show 2 ^ (t + 1) = 2 * 2 ^ t by ring, mul_comm, hdiv]]
    exact ih (by omega)

lemma blk_one (X i : ℕ) : blk X 1 i = if X.testBit i then 1 else 0 := by
  unfold blk
  rw [one_mul, pow_one]
  have := Nat.mod_two_eq_zero_or_one (X >>> i)
  rcases this with h | h
  · have : X.testBit i = false := by
      rw [show X.testBit i = (X >>> i).testBit 0 by rw [Nat.testBit_shiftRight, add_zero],
        ← Nat.mod_two_eq_zero_iff_testBit_zero]; exact h
    simp [h, this]
  · have : X.testBit i = true := by
      rw [show X.testBit i = (X >>> i).testBit 0 by rw [Nat.testBit_shiftRight, add_zero],
        ← Nat.mod_two_eq_one_iff_testBit_zero]; exact h
    simp [h, this]

/-- The Morton spread puts bit `i` of `X` into the `i`-th 8-bit field. -/
theorem spread8_eq (K X : ℕ) (hK : K ≤ 32) (hX : X < 2 ^ (2 ^ K)) :
    spread8 K X = pk 8 (fun i => if X.testBit i then 1 else 0) (2 ^ K) := by
  have h0 : spread8 K X = spreadAux (2 ^ K) K X := by
    show spreadAux (Nat.shiftLeft 1 K) K X = _
    rw [raw_shiftLeft, Nat.shiftLeft_eq, one_mul]
  have h1 : X = pk (8 * 2 ^ K) (fun b => blk X (2 ^ K) b) (2 ^ K / 2 ^ K) := by
    rw [Nat.div_self (by positivity)]
    simp [pk, blk, Nat.mod_eq_of_lt hX]
  rw [h0]
  conv_lhs => rw [h1]
  rw [spreadAux_eq X K hK K le_rfl]
  apply pk_congr; intro i _; rw [blk_one]


/-! ### Decode -/

/-- Field-level "`v ≥ θ`" bit. -/
def nbf (θ v : ℕ) : ℕ := ((v + (128 - θ)) >>> 7) &&& 1

/-- Field-level decode, mirroring `decode`. -/
def decf (θ0 θ1 v a b f : ℕ) : ℕ :=
  f + (((f ^^^ 1) &&& (((((v &&& 1) ^^^ a) ^^^ b) ^^^ ((b ^^^ 1) &&&
    (((a ^^^ 1) &&& (nbf θ0 v ^^^ 1)) ||| (a &&& (nbf θ1 v ^^^ 1))))) ^^^ 1)) <<< 1)

lemma lt256_and {x y : ℕ} (hy : y < 2 ^ 8) : x &&& y < 2 ^ 8 := Nat.and_lt_two_pow _ hy
lemma lt256_or {x y : ℕ} (hx : x < 2 ^ 8) (hy : y < 2 ^ 8) : x ||| y < 2 ^ 8 := Nat.or_lt_two_pow hx hy
lemma lt256_xor {x y : ℕ} (hx : x < 2 ^ 8) (hy : y < 2 ^ 8) : x ^^^ y < 2 ^ 8 := Nat.xor_lt_two_pow hx hy

theorem decode_eq (S θ0 θ1 : ℕ) (v a b f : ℕ → ℕ) (hS : S < 2 ^ 32)
    (hv0 : ∀ i < S, v i + (128 - θ0) < 2 ^ 8) (hv1 : ∀ i < S, v i + (128 - θ1) < 2 ^ 8)
    (ha : ∀ i < S, a i < 2) (hb : ∀ i < S, b i < 2) (hf : ∀ i < S, f i < 2) :
    decode S θ0 θ1 (pk 8 v S) (pk 8 a S) (pk 8 b S) (pk 8 f S) =
      pk 8 (fun i => decf θ0 θ1 (v i) (a i) (b i) (f i)) S := by
  have h8 : (0 : ℕ) < 8 := by norm_num
  have one8 : (1 : ℕ) < 2 ^ 8 := by norm_num
  have hv : ∀ i < S, v i < 2 ^ 8 := fun i hi => by have := hv0 i hi; omega
  have ha8 : ∀ i < S, a i < 2 ^ 8 := fun i hi => by have := ha i hi; omega
  have hb8 : ∀ i < S, b i < 2 ^ 8 := fun i hi => by have := hb i hi; omega
  have hf8 : ∀ i < S, f i < 2 ^ 8 := fun i hi => by have := hf i hi; omega
  have hO : ∀ i < S, (fun _ => (1 : ℕ)) i < 2 ^ 8 := fun _ _ => one8
  -- the two comparison bits
  have hT : ∀ θ, (∀ i < S, v i + (128 - θ) < 2 ^ 8) →
      ((pk 8 v S + (128 - θ) * pk 8 (fun _ => 1) S) >>> 7) &&& pk 8 (fun _ => 1) S =
        pk 8 (fun i => nbf θ (v i)) S := by
    intro θ hθ
    rw [pk_mul, pk_add, pk_shiftRight_land h8 (fun i hi => by simpa using hθ i hi) (c := 1) (by norm_num)
      (by norm_num)]
    simp [nbf]
  have hnb : ∀ θ, ∀ i < S, nbf θ (v i) < 2 ^ 8 := fun θ i _ => lt256_and one8
  unfold decode
  raw_norm
  rw [ones_eq 8 S hS, hT θ0 hv0, hT θ1 hv1, pk_land h8 hv hO, pk_xor h8 hb8 hO, pk_xor h8 ha8 hO,
    pk_xor h8 (hnb θ0) hO, pk_xor h8 (hnb θ1) hO,
    pk_land h8 (fun i _ => lt256_xor (ha8 i ‹_›) one8) (fun i _ => lt256_xor (hnb θ0 i ‹_›) one8),
    pk_land h8 ha8 (fun i _ => lt256_xor (hnb θ1 i ‹_›) one8),
    pk_lor h8 (fun i _ => lt256_and (lt256_xor (hnb θ0 i ‹_›) one8))
      (fun i _ => lt256_and (lt256_xor (hnb θ1 i ‹_›) one8)),
    pk_land h8 (fun i _ => lt256_xor (hb8 i ‹_›) one8)
      (fun i _ => lt256_or (lt256_and (lt256_xor (hnb θ0 i ‹_›) one8)) (lt256_and (lt256_xor (hnb θ1 i ‹_›) one8))),
    pk_xor h8 (fun i _ => lt256_and one8) ha8,
    pk_xor h8 (fun i _ => lt256_xor (lt256_and one8) (ha8 i ‹_›)) hb8,
    pk_xor h8 (fun i _ => lt256_xor (lt256_xor (lt256_and one8) (ha8 i ‹_›)) (hb8 i ‹_›))
      (fun i _ => lt256_and (lt256_or (lt256_and (lt256_xor (hnb θ0 i ‹_›) one8))
        (lt256_and (lt256_xor (hnb θ1 i ‹_›) one8)))),
    pk_xor h8 hf8 hO]
  rw [pk_xor h8 (fun i _ => lt256_xor (lt256_xor (lt256_xor (lt256_and one8) (ha8 i ‹_›)) (hb8 i ‹_›))
      (lt256_and (lt256_or (lt256_and (lt256_xor (hnb θ0 i ‹_›) one8))
        (lt256_and (lt256_xor (hnb θ1 i ‹_›) one8))))) hO,
    pk_land h8 (fun i _ => lt256_xor (hf8 i ‹_›) one8) (fun i _ => lt256_xor (lt256_xor (lt256_xor
      (lt256_xor (lt256_and one8) (ha8 i ‹_›)) (hb8 i ‹_›)) (lt256_and (lt256_or (lt256_and
        (lt256_xor (hnb θ0 i ‹_›) one8)) (lt256_and (lt256_xor (hnb θ1 i ‹_›) one8))))) one8),
    Nat.shiftLeft_eq, pow_one, mul_comm, pk_mul, pk_add]
  apply pk_congr; intro i _
  simp only [decf, Nat.shiftLeft_eq, pow_one]
  ring

/-- Arithmetic meaning of `nbf`. -/
lemma nbf_eq {θ v : ℕ} (hθ : θ ≤ 128) (hv : v + (128 - θ) < 2 ^ 8) : nbf θ v = if θ ≤ v then 1 else 0 := by
  unfold nbf
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  split_ifs with h
  · have : (v + (128 - θ)) / 2 ^ 7 = 1 := by
      rw [Nat.div_eq_iff (by norm_num)]; norm_num at hv ⊢; omega
    rw [this]
  · have : (v + (128 - θ)) / 2 ^ 7 = 0 := by
      rw [Nat.div_eq_iff (by norm_num)]; norm_num at hv ⊢; omega
    rw [this]

/-- Arithmetic meaning of `decf`. -/
lemma decf_eq {θ0 θ1 v a b f : ℕ} (h0 : θ0 ≤ 128) (h1 : θ1 ≤ 128) (hv0 : v + (128 - θ0) < 2 ^ 8)
    (hv1 : v + (128 - θ1) < 2 ^ 8) (ha : a < 2) (hb : b < 2) (hf : f < 2) :
    decf θ0 θ1 v a b f =
      if f = 1 then 1 else
        if (v + a + b + (if b = 0 ∧ ((a = 0 ∧ v < θ0) ∨ (a = 1 ∧ v < θ1)) then 1 else 0)) % 2 = 0
        then 2 else 0 := by
  unfold decf
  rw [nbf_eq h0 hv0, nbf_eq h1 hv1, Nat.and_one_is_mod]
  have hv2 : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have key : (v + a + b + (if b = 0 ∧ ((a = 0 ∧ v < θ0) ∨ (a = 1 ∧ v < θ1)) then 1 else 0)) % 2 =
      (v % 2 + a + b + (if b = 0 ∧ ((a = 0 ∧ v < θ0) ∨ (a = 1 ∧ v < θ1)) then 1 else 0)) % 2 := by
    omega
  rw [key]
  have hc0 : (if θ0 ≤ v then 1 else 0) = (if v < θ0 then 0 else 1 : ℕ) := by split_ifs <;> omega
  have hc1 : (if θ1 ≤ v then 1 else 0) = (if v < θ1 then 0 else 1 : ℕ) := by split_ifs <;> omega
  rw [hc0, hc1]
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;>
  rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl <;>
  rcases Nat.mod_two_eq_zero_or_one v with hm | hm <;>
  by_cases c0 : v < θ0 <;> by_cases c1 : v < θ1 <;> simp [hm, c0, c1, Nat.shiftLeft_eq]


/-! ### Groups of four, prefix sums, band check -/

lemma group4_raw (S X : ℕ) : group4 S X =
    ((X + (X >>> 8)) + ((X >>> 16) + (X >>> 24))) &&& (255 * ones 32 (S / 4)) := by
  show Nat.land _ _ = _
  raw_norm

/-- Regrouping four 8-bit fields into a 32-bit field. -/
lemma pk_regroup (y : ℕ → ℕ) (n : ℕ) :
    pk 8 y (4 * n) = pk 32 (fun j => y (4 * j) + 2 ^ 8 * y (4 * j + 1) + 2 ^ 16 * y (4 * j + 2) +
      2 ^ 24 * y (4 * j + 3)) n := by
  have e1 : pk 8 y (4 * n) = pk 16 (fun b => y (2 * b) + 2 ^ 8 * y (2 * b + 1)) (2 * n) := by
    rw [show 16 = 2 * 8 by norm_num, pk_refine, show 2 * (2 * n) = 4 * n by ring]
    apply pk_congr; intro i _; split_ifs <;> congr 1 <;> omega
  have e2 : pk 16 (fun b => y (2 * b) + 2 ^ 8 * y (2 * b + 1)) (2 * n) =
      pk 32 (fun j => (y (4 * j) + 2 ^ 8 * y (4 * j + 1)) + 2 ^ 16 * (y (4 * j + 2) + 2 ^ 8 * y (4 * j + 3))) n := by
    rw [show 32 = 2 * 16 by norm_num, pk_refine]
    apply pk_congr; intro i _
    split_ifs with h
    · rw [show 2 * i = 4 * (i / 2) by omega, show 4 * (i / 2) + 1 = 4 * (i / 2) + 1 from rfl]
    · rw [show 2 * i = 4 * (i / 2) + 2 by omega, show 4 * (i / 2) + 2 + 1 = 4 * (i / 2) + 3 by ring]
  rw [e1, e2]
  apply pk_congr; intro j _; ring



theorem group4_eq (n : ℕ) (x : ℕ → ℕ) (hn : 4 * n < 2 ^ 32) (hx : ∀ i < 4 * n, x i < 64) :
    group4 (4 * n) (pk 8 x (4 * n)) =
      pk 32 (fun j => x (4 * j) + x (4 * j + 1) + x (4 * j + 2) + x (4 * j + 3)) n := by
  have h8 : (0 : ℕ) < 8 := by norm_num
  have hx8 : ∀ i < 4 * n, x i < 2 ^ 8 := fun i hi => by have := hx i hi; omega
  set y : ℕ → ℕ := fun i => (if i < 4 * n then x i else 0) + (if i + 1 < 4 * n then x (i + 1) else 0) +
    ((if i + 2 < 4 * n then x (i + 2) else 0) + (if i + 3 < 4 * n then x (i + 3) else 0)) with hy
  have hsum : (pk 8 x (4 * n) + (pk 8 x (4 * n) >>> 8)) + ((pk 8 x (4 * n) >>> 16) + (pk 8 x (4 * n) >>> 24)) =
      pk 8 y (4 * n) := by
    by_cases hn0 : n = 0
    · subst hn0; simp
    rw [show (8 : ℕ) = 8 * 1 by rfl, pk_shiftRight_fields hx8 (by omega),
      show (16 : ℕ) = 8 * 2 by rfl, pk_shiftRight_fields hx8 (by omega),
      show (24 : ℕ) = 8 * 3 by rfl, pk_shiftRight_fields hx8 (by omega), pk_add, pk_add, pk_add]
    apply pk_congr; intro i hi; simp [hy, hi]
  have hy64 : ∀ i, y i < 2 ^ 8 := by
    intro i; simp only [hy]
    have : ∀ k, (if i + k < 4 * n then x (i + k) else 0) < 64 := by
      intro k; split_ifs with h
      · exact hx _ h
      · norm_num
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3
    simp only [add_zero] at h0
    norm_num; omega
  rw [group4_raw, hsum, show 4 * n / 4 = n by omega, ones_eq 32 n (by omega), pk_mul, pk_regroup,
    pk_land (by norm_num) (fun j _ => by
      have := hy64 (4 * j); have := hy64 (4 * j + 1); have := hy64 (4 * j + 2); have := hy64 (4 * j + 3)
      norm_num at *; omega) (fun _ _ => by norm_num)]
  apply pk_congr; intro j hj
  rw [show (255 * 1 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have := hy64 (4 * j + 1); have := hy64 (4 * j + 2); have := hy64 (4 * j + 3)
  rw [show y (4 * j) + 2 ^ 8 * y (4 * j + 1) + 2 ^ 16 * y (4 * j + 2) + 2 ^ 24 * y (4 * j + 3) =
      y (4 * j) + 2 ^ 8 * (y (4 * j + 1) + 2 ^ 8 * y (4 * j + 2) + 2 ^ 16 * y (4 * j + 3)) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hy64 _)]
  simp only [hy, show 4 * j < 4 * n by omega, show 4 * j + 1 < 4 * n by omega,
    show 4 * j + 2 < 4 * n by omega, show 4 * j + 3 < 4 * n by omega, if_true]
  ring

/-- Window sums. -/
def win (g : ℕ → ℕ) (s j : ℕ) : ℕ := ∑ i ∈ range (2 ^ s), if i ≤ j then g (j - i) else 0

lemma win_zero (g : ℕ → ℕ) (j : ℕ) : win g 0 j = g j := by simp [win]

lemma win_succ (g : ℕ → ℕ) (s j : ℕ) :
    win g (s + 1) j = win g s j + if j < 2 ^ s then 0 else win g s (j - 2 ^ s) := by
  unfold win
  rw [pow_succ, mul_two, sum_range_add]
  congr 1
  split_ifs with h
  · exact sum_eq_zero fun i _ => by rw [if_neg (by omega)]
  · exact sum_congr rfl fun i _ => by
      by_cases hi : i ≤ j - 2 ^ s
      · rw [if_pos (by omega), if_pos hi]; congr 1; omega
      · rw [if_neg (by omega), if_neg hi]

lemma win_le (g : ℕ → ℕ) (hg : ∀ i, g i ≤ 8) (s j : ℕ) : win g s j ≤ 8 * (j + 1) := by
  unfold win
  calc ∑ i ∈ range (2 ^ s), (if i ≤ j then g (j - i) else 0)
      ≤ ∑ i ∈ range (2 ^ s), (if i ≤ j then 8 else 0) := sum_le_sum fun i _ => by
        split_ifs; exact hg _; exact le_rfl
    _ = 8 * ((range (2 ^ s)).filter (· ≤ j)).card := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const]; simp [mul_comm]
    _ ≤ 8 * (j + 1) := by
        apply Nat.mul_le_mul_left
        calc ((range (2 ^ s)).filter (· ≤ j)).card ≤ (range (j + 1)).card :=
              card_le_card fun i hi => by simp at hi ⊢; omega
          _ = j + 1 := card_range _

lemma win_full (g : ℕ → ℕ) {s j : ℕ} (hj : j < 2 ^ s) : win g s j = ∑ i ∈ range (j + 1), g i := by
  unfold win
  rw [← sum_subset (s₁ := range (j + 1)) (fun i hi => by simp at hi ⊢; omega)
    (fun i _ hi => by simp at hi; rw [if_neg (by omega)])]
  conv_rhs => rw [← sum_range_reflect]
  exact sum_congr rfl fun i hi => by
    simp at hi; rw [if_pos (by omega), show j + 1 - 1 - i = j - i by omega]


lemma scan_zero (n X : ℕ) : scan n 0 X = X := rfl
lemma scan_succ (n s X : ℕ) :
    scan n (s + 1) X = (scan n s X + (scan n s X <<< (32 * 2 ^ s))) % 2 ^ (32 * n) := by
  show Nat.mod (Nat.add (scan n s X) (Nat.shiftLeft (scan n s X) (Nat.mul 32 (Nat.shiftLeft 1 s))))
    (Nat.shiftLeft 1 (Nat.mul 32 n)) = _
  raw_norm
  rw [Nat.shiftLeft_eq 1 s, Nat.shiftLeft_eq 1 (32 * n), one_mul, one_mul]

theorem scan_eq (n : ℕ) (g : ℕ → ℕ) (hg : ∀ i, g i ≤ 8) (hn : n < 2 ^ 26) :
    ∀ s, scan n s (pk 32 g n) = pk 32 (fun j => win g s j) n := by
  intro s
  induction s with
  | zero => rw [scan_zero]; exact pk_congr fun j _ => (win_zero g j).symm
  | succ s ih =>
    rw [scan_succ, ih, pk_shiftLeft, pk_extend 32 (fun j => win g s j) n (2 ^ s), pk_add]
    rw [pk_mod (m := n) ?_ ?_]
    · exact pk_congr fun j hj => by rw [win_succ, if_pos hj]
    · intro j hj
      have h1 := win_le g hg s j
      have h2 := win_le g hg s (j - 2 ^ s)
      have hp : 0 < 2 ^ s := by positivity
      split_ifs <;> omega
    · exact Nat.le_add_right n (2 ^ s)

/-- Soundness of the band check. With `G` packing the group sums `g j ≤ 8`, `P j = ∑_{i ≤ j} g i`. -/
theorem bandCheck_spec (n T K1 K2 : ℕ) (g : ℕ → ℕ) (hg : ∀ i, g i ≤ 8) (hn1 : 1 ≤ n) (hn : n < 2 ^ 26)
    (hT : n ≤ 2 ^ T) (hK1 : K1 < 2 ^ 29) (hK2 : K2 < 2 ^ 29) :
    (bandCheck n T K1 K2 (pk 32 g n)).2 = ∑ i ∈ range n, g i ∧
    ((bandCheck n T K1 K2 (pk 32 g n)).1 = true →
      ∀ j < n, 4 * (j + 1) ≤ (∑ i ∈ range (j + 1), g i) + K1 ∧
        (∑ i ∈ range (j + 1), g i) ≤ 4 * (j + 1) + K2) := by
  set P : ℕ → ℕ := fun j => ∑ i ∈ range (j + 1), g i with hP
  have hPle : ∀ j, P j ≤ 8 * (j + 1) := fun j => by
    calc P j ≤ ∑ i ∈ range (j + 1), 8 := sum_le_sum fun i _ => hg i
      _ = 8 * (j + 1) := by simp [mul_comm]
  have hscanG : scan n T (pk 32 g n) = pk 32 P n := by
    rw [scan_eq n g hg hn T]; exact pk_congr fun j hj => win_full g (by omega)
  have hscanO : scan n T (pk 32 (fun _ => 1) n) = pk 32 (fun j => j + 1) n := by
    rw [scan_eq n (fun _ => 1) (fun _ => by norm_num) hn T]
    exact pk_congr fun j hj => by rw [win_full _ (by omega)]; simp
  have h32 : (0 : ℕ) < 32 := by norm_num
  have hb32 : ∀ j < n, P j < 2 ^ 32 := fun j hj => by have := hPle j; omega
  unfold bandCheck
  raw_norm
  rw [ones_eq 32 n (by omega), hscanG, hscanO]
  refine ⟨?_, ?_⟩
  · have := pk_shiftRight_top (w := 32) (n := n - 1) (f := P) (fun j hj => hb32 j (by omega))
    rw [show n - 1 + 1 = n by omega] at this
    rw [this]; simp [hP, show n - 1 + 1 = n by omega]
  · intro hok j hj
    simp only [decide_eq_true_eq] at hok
    set H : ℕ := 1 <<< 31 with hH
    have hH' : H = 2 ^ 31 := by rw [hH, Nat.shiftLeft_eq, one_mul]
    have eE1 : pk 32 P n + (H + K1) * pk 32 (fun _ => 1) n - 4 * pk 32 (fun j => j + 1) n =
        pk 32 (fun j => P j + (H + K1) - 4 * (j + 1)) n := by
      rw [pk_mul, pk_mul, pk_add, pk_sub 32 (fun j hj => by omega)]
      exact pk_congr fun j _ => by simp only [mul_one]
    have eE2 : 4 * pk 32 (fun j => j + 1) n + (H + K2) * pk 32 (fun _ => 1) n - pk 32 P n =
        pk 32 (fun j => 4 * (j + 1) + (H + K2) - P j) n := by
      rw [pk_mul, pk_mul, pk_add, pk_sub 32 (fun j hj => by have := hPle j; omega)]
      exact pk_congr fun j _ => by simp only [mul_one]
    have eHM : H * pk 32 (fun _ => 1) n = pk 32 (fun _ => H) n := by rw [pk_mul]; simp
    have he1 : ∀ j < n, P j + (H + K1) - 4 * (j + 1) < 2 ^ 32 := fun j hj => by
      have := hPle j; omega
    have he2 : ∀ j < n, 4 * (j + 1) + (H + K2) - P j < 2 ^ 32 := fun j hj => by
      have := hPle j; omega
    have hH32 : H < 2 ^ 32 := by rw [hH']; norm_num
    rw [eE1, eE2, eHM, pk_land h32 he1 he2,
      pk_land h32 (fun j hj => Nat.and_lt_two_pow _ (he2 j hj)) (fun _ _ => hH32)] at hok
    have hok' := pk_inj h32 (fun j _ => Nat.and_lt_two_pow _ hH32) (fun _ _ => hH32) hok j hj
    have hbit := congrArg (fun x => Nat.testBit x 31) hok'
    simp only [Nat.testBit_and, hH', Nat.testBit_two_pow_self, Bool.and_true] at hbit
    have hb1 := ((Bool.and_eq_true _ _).mp hbit).1
    have hb2 := ((Bool.and_eq_true _ _).mp hbit).2
    have g1 := Nat.ge_two_pow_of_testBit hb1
    have g2 := Nat.ge_two_pow_of_testBit hb2
    have := hPle j
    have hPj : P j = ∑ i ∈ range (j + 1), g i := rfl
    constructor <;> omega

end MoebiusCert
