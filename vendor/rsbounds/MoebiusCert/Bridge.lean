/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.Sieve
import MoebiusCert.NT
import MoebiusCert.Primes

/-!
# The packed `μ + 1` of a segment

`segMu1 spData mpData L K θ0 θ1` (with the thresholds of `MoebiusCert.NT`) is the packed number
whose `i`-th 8-bit field is `μ(L + i) + 1`.
-/

namespace MoebiusCert

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Weight of a key in a list of pairs (sum over matching entries). -/
def wOf (l : List (ℕ × ℕ)) (p : ℕ) : ℕ := (l.map fun pa => if pa.1 = p then pa.2 else 0).sum

lemma wOf_not_mem {l : List (ℕ × ℕ)} {p : ℕ} (h : p ∉ l.map Prod.fst) : wOf l p = 0 := by
  unfold wOf
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨pa, hpa, rfl⟩ := List.mem_map.1 hx
  rw [if_neg]; intro e; exact h (List.mem_map.2 ⟨pa, hpa, e⟩)

lemma wOf_mem {l : List (ℕ × ℕ)} (hl : (l.map Prod.fst).Nodup) {pa : ℕ × ℕ} (h : pa ∈ l) :
    wOf l pa.1 = pa.2 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    unfold wOf at *
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · have h0 := wOf_not_mem hl.1
      unfold wOf at h0
      rw [if_pos rfl, h0, add_zero]
    · have hne : x.1 ≠ pa.1 := fun e => hl.1 (e ▸ List.mem_map_of_mem h')
      rw [if_neg hne, ih hl.2 h', zero_add]

/-- List sum of indicator weights = Finset sum over the keys. -/
lemma list_sum_eq_finset_sum (l : List (ℕ × ℕ)) (hl : (l.map Prod.fst).Nodup) (D : ℕ → Prop) [DecidablePred D] :
    (l.map fun pa => if D pa.1 then pa.2 else 0).sum =
      ∑ p ∈ (l.map Prod.fst).toFinset.filter D, wOf l p := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2, List.map_cons, List.toFinset_cons, filter_insert]
    have hx : x.1 ∉ (l.map Prod.fst).toFinset := by simpa using hl.1
    have hW : ∀ p ∈ (l.map Prod.fst).toFinset.filter D, wOf (x :: l) p = wOf l p := by
      intro p hp
      have hne : x.1 ≠ p := fun e => hx (e ▸ (mem_filter.1 hp).1)
      unfold wOf; rw [List.map_cons, List.sum_cons, if_neg hne, zero_add]
    have hx0 : wOf (x :: l) x.1 = x.2 := by
      unfold wOf; rw [List.map_cons, List.sum_cons, if_pos rfl]
      have := wOf_not_mem (l := l) (by simpa using hl.1); unfold wOf at this; rw [this, add_zero]
    split_ifs with hD
    · rw [sum_insert (fun h => hx (mem_filter.1 h).1), hx0, sum_congr rfl hW]
    · rw [zero_add, sum_congr rfl hW]

/-- The small-prime weight function. -/
def W : ℕ → ℕ := wOf spData

lemma W_spec : ∀ p, p.Prime → p < 1000 → W p % 2 = 1 ∧ 2 ^ (W p / 2) ≤ p ^ 2 ∧ p ^ 2 < 2 ^ (W p / 2 + 1) := by
  intro p hp hp1
  obtain ⟨pa, hpa, rfl⟩ := List.mem_map.1 (mem_sp_keys.2 ⟨hp, hp1⟩)
  rw [W, wOf_mem sp_keys_nodup hpa]
  exact sp_weight hpa

lemma v_bridge {n : ℕ} (hn : n ≠ 0) :
    (spData.map fun pa => if pa.1 ∣ n then pa.2 else 0).sum =
      ∑ p ∈ Finset.filter (fun p => p < 1000) n.primeFactors, W p := by
  rw [list_sum_eq_finset_sum spData sp_keys_nodup (· ∣ n)]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, List.mem_toFinset, mem_sp_keys, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3, hn⟩, h2⟩
  · rintro ⟨⟨h1, h3, -⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩

lemma c_bridge {n : ℕ} (hn : n ≠ 0) :
    mpData.countP (fun p => p ∣ n) = (n.primeFactors.filter (fun p => 1000 < p ∧ p ≤ 31622)).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (mp_nodup.filter _)]
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, mem_mp, decide_eq_true_eq, mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h4, hn⟩, h2, h3⟩
  · rintro ⟨⟨h1, h4, -⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩

lemma sq_bridge (n : ℕ) :
    ((∃ p ∈ spData.map Prod.fst, p * p ∣ n) ∨ (∃ p ∈ mpData, p * p ∣ n)) ↔
      ∃ p < 31623, p.Prime ∧ p * p ∣ n := by
  constructor
  · rintro (⟨p, hp, hd⟩ | ⟨p, hp, hd⟩)
    · obtain ⟨h1, h2⟩ := mem_sp_keys.1 hp; exact ⟨p, by omega, h1, hd⟩
    · obtain ⟨h1, -, h3⟩ := mem_mp.1 hp; exact ⟨p, by omega, h1, hd⟩
  · rintro ⟨p, hp, h1, hd⟩
    by_cases h : p < 1000
    · exact Or.inl ⟨p, mem_sp_keys.2 ⟨h1, h⟩, hd⟩
    · have : p ≠ 1000 := fun e => by
        rw [e] at h1; rcases h1.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> omega
      exact Or.inr ⟨p, mem_mp.2 ⟨h1, by omega, by omega⟩, hd⟩


lemma lt_two_pow_of_bits {x S : ℕ} (h : ∀ t, x.testBit t = true → t < S) : x < 2 ^ S :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    by_contra h'; have := h i (by simpa using h'); omega

lemma segMu1_unfold (L K θ0 θ1 : ℕ) : segMu1 spData mpData L K θ0 θ1 =
    decode (2 ^ K) θ0 θ1 (vPass L (2 ^ K) spData 0) (spread8 K (mPass L (2 ^ K) mpData 0 0).1)
      (spread8 K (mPass L (2 ^ K) mpData 0 0).2)
      (spread8 K (fPass L (2 ^ K) mpData (fPass L (2 ^ K) (spData.map Prod.fst) 0))) := by
  show decode (Nat.shiftLeft 1 K) _ _ _ _ _ _ = _
  rw [raw_shiftLeft, Nat.shiftLeft_eq, one_mul]

/-- **The packed Möbius values of a segment.** -/
theorem segMu1_eq (L K lam : ℕ) (hK : K ≤ 24) (hL1 : 1 ≤ L) (hl1 : 2 ^ lam ≤ L)
    (hl2 : L + 2 ^ K ≤ 2 ^ (lam + 1)) (hmax : L + 2 ^ K ≤ 1000014129) (hlam : lam ≤ 29) :
    segMu1 spData mpData L K (5 * lam - 69) (5 * lam - 119) =
      pk 8 (fun i => (μ (L + i) + 1).toNat) (2 ^ K) := by
  set S := 2 ^ K with hSdef
  have hS : S < 2 ^ 32 := by rw [hSdef]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the three passes
  have hV := vPass_eq L S hS spData 0 (fun pa h => sp_pos h)
  rw [zero_add] at hV
  have hM := mPass_spec L S hS mpData 0 0 (fun _ => 0) (fun p h => mp_pos h) (fun t => by simp)
    (fun t => by simp)
  simp only [zero_add] at hM
  have hF0 := fPass_spec L S hS (spData.map Prod.fst) 0 (fun p h => (mem_sp_keys.1 h).1.pos)
  have hF := fPass_spec L S hS mpData (fPass L S (spData.map Prod.fst) 0) (fun p h => mp_pos h)
  set c0 := (mPass L S mpData 0 0).1
  set c1 := (mPass L S mpData 0 0).2
  set F := fPass L S mpData (fPass L S (spData.map Prod.fst) 0)
  have hc0 : c0 < 2 ^ S := lt_two_pow_of_bits fun t h => by
    rw [hM.1 t] at h; simp at h; exact h.1
  have hc1 : c1 < 2 ^ S := lt_two_pow_of_bits fun t h => by
    rw [hM.2 t] at h; simp at h; exact h.1
  have hFb : ∀ t, F.testBit t = (decide (t < S) &&
      decide ((∃ p ∈ spData.map Prod.fst, p * p ∣ L + t) ∨ (∃ p ∈ mpData, p * p ∣ L + t))) := by
    intro t; rw [hF, hF0]; simp only [Nat.zero_testBit, Bool.false_or]
    by_cases ht : t < S <;> simp [ht]
  have hFl : F < 2 ^ S := lt_two_pow_of_bits fun t h => by
    rw [hFb t] at h; simp at h; exact h.1
  rw [segMu1_unfold, ← hSdef, hV, spread8_eq K c0 (by omega) hc0, spread8_eq K c1 (by omega) hc1,
    spread8_eq K F (by omega) hFl]
  -- the per-integer facts
  have key : ∀ i < S,
      (spData.map fun pa => if pa.1 ∣ L + i then pa.2 else 0).sum + (128 - (5 * lam - 69)) < 2 ^ 8 ∧
      (spData.map fun pa => if pa.1 ∣ L + i then pa.2 else 0).sum + (128 - (5 * lam - 119)) < 2 ^ 8 ∧
      decf (5 * lam - 69) (5 * lam - 119) (spData.map fun pa => if pa.1 ∣ L + i then pa.2 else 0).sum
        (if c0.testBit i then 1 else 0) (if c1.testBit i then 1 else 0) (if F.testBit i then 1 else 0) =
        (μ (L + i) + 1).toNat := by
    intro i hi
    have hn0 : L + i ≠ 0 := by omega
    have hmc := mu_core (L + i) lam W W_spec (by omega) (by omega) (by omega) (by omega) hlam
    simp only at hmc
    rw [v_bridge hn0]
    refine ⟨hmc.1, hmc.2.1, ?_⟩
    have ha : (if c0.testBit i then 1 else 0) =
        (if 1 ≤ ((L + i).primeFactors.filter (fun p => 1000 < p ∧ p ≤ 31622)).card then 1 else 0) := by
      rw [hM.1 i, ← c_bridge hn0]; simp [hi]
    have hb : (if c1.testBit i then 1 else 0) =
        (if 2 ≤ ((L + i).primeFactors.filter (fun p => 1000 < p ∧ p ≤ 31622)).card then 1 else 0) := by
      rw [hM.2 i, ← c_bridge hn0]; simp [hi]
    have hf : (if F.testBit i then 1 else 0) = (if (∃ p < 31623, p.Prime ∧ p * p ∣ L + i) then 1 else 0) := by
      rw [hFb i]
      simp only [hi, decide_true, Bool.true_and, decide_eq_true_eq]
      exact if_congr (sq_bridge (L + i)) rfl rfl
    rw [decf_eq (by omega) (by omega) hmc.1 hmc.2.1 (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
      (by split_ifs <;> norm_num), ha, hb, hf, ← hmc.2.2, Int.toNat_natCast]
    by_cases hsq : ∃ p < 31623, p.Prime ∧ p * p ∣ L + i
    · rw [if_pos hsq, if_pos rfl, if_pos hsq]
    · rw [if_neg hsq, if_neg (by norm_num), if_neg hsq]
  rw [decode_eq S _ _ _ _ _ _ hS (fun i hi => (key i hi).1) (fun i hi => (key i hi).2.1)
    (fun i _ => by split_ifs <;> norm_num) (fun i _ => by split_ifs <;> norm_num)
    (fun i _ => by split_ifs <;> norm_num)]
  exact pk_congr fun i hi => (key i hi).2.2

end MoebiusCert
