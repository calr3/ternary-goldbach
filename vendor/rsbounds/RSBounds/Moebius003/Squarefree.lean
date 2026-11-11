/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Kappa
import RSBounds.Moebius003.Abel
import RSBounds.Moebius003.LogCert
import RSBounds.Moebius003.MofN

/-!
# Lemma 5 of the note: squarefree numbers

* (a) `|Q(x) − κx| ≤ 2√x + 1`.
* (b) `∑_{j ≤ J} μ²(j)/√j ≤ κ(2√J − 1) + 4 + log J` (a discrete variant of the note's (b)).
* (d) For `1 ≤ J < D`, with `L = log D`, `ℓ = log J`, and any `e_lo ≤ e_hi` with
  `e_lo ≥ 0` such that `κ log i + e_lo ≤ Q₁(i) ≤ κ log i + e_hi` for `1 ≤ i ≤ J`:
  `∑_{j ≤ J} μ²(j)/(j log(D/j)) ≤ κ (log(L/(L−ℓ)) + 2/(L−ℓ)²) + (e_hi − e_lo)/(L−ℓ) + e_lo/L`.

Part (c) (the bounds for `Q₁(i) − κ log i`) is in `SquarefreeData`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ### `μ²(n) = ∑_{d² ∣ n} μ(d)` -/

theorem dvd_of_sq_dvd_sq_mul {d b a : ℕ} (ha : Squarefree a) (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at h; rcases h with h | h
    · simp_all
    · subst h; simp at ha
  have hg : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_left _ hd
  obtain ⟨d', hd'⟩ := Nat.gcd_dvd_left d b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right d b
  have hcop : Nat.Coprime d' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := d) (n := b) hg
    have e1 : d / Nat.gcd d b = d' := Nat.div_eq_of_eq_mul_left hg (hd'.trans (mul_comm _ _))
    have e2 : b / Nat.gcd d b = b' := Nat.div_eq_of_eq_mul_left hg (hb'.trans (mul_comm _ _))
    rwa [e1, e2] at this
  generalize hG : Nat.gcd d b = g at hd' hb' hg
  subst hd' hb'
  have h2 : d' ^ 2 ∣ b' ^ 2 * a := by
    rw [mul_pow, mul_pow, mul_assoc] at h
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).1 h
  have h3 : d' ^ 2 ∣ a := (Nat.Coprime.pow 2 2 hcop).dvd_of_dvd_mul_left h2
  have h4 : IsUnit d' := ha d' (by rw [← sq]; exact h3)
  rw [Nat.isUnit_iff] at h4
  rw [h4, mul_one]
  exact Dvd.intro b' rfl

theorem sum_sq_dvd_moebius (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ (Icc 1 n).filter (fun d => d ^ 2 ∣ n), (μ d : ℝ) = (μ n : ℝ) ^ 2 := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
  have hset : (Icc 1 n).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hd⟩
      exact ⟨dvd_of_sq_dvd_sq_mul hsq (hab ▸ hd), by omega⟩
    · rintro ⟨hd, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hb
      have h1 : d ^ 2 ∣ n := hab ▸ Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd 2) a
      refine ⟨⟨hdpos, ?_⟩, h1⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ n := Nat.le_of_dvd (by omega) h1
  rw [hset]
  have hsum : ∑ d ∈ b.divisors, (μ d : ℝ) = if b = 1 then 1 else 0 := by
    have := coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℝ)) (x := b)
    rw [coe_moebius_mul_coe_zeta] at this
    simp only [intCoe_apply] at this
    rw [← this]
    split_ifs with h
    · simp [h]
    · simp [one_apply_ne h]
  rw [hsum]
  by_cases hb1 : b = 1
  · subst hb1
    simp at hab; subst hab
    simp only [↓reduceIte]
    have := moebius_sq_eq_one_of_squarefree hsq
    exact_mod_cast this.symm
  · rw [if_neg hb1]
    have hns : ¬ Squarefree n := by
      intro h
      have := h b (by rw [← hab, ← sq]; exact Dvd.intro a rfl)
      exact hb1 (Nat.isUnit_iff.1 this)
    rw [moebius_eq_zero_of_not_squarefree hns]; simp

/-- `Q(x) = ∑_{d ≤ x} μ(d) ⌊x/d²⌋`. -/
theorem Q_eq_sum (x : ℕ) : Q x = ∑ d ∈ Icc 1 x, (μ d : ℝ) * ((x / d ^ 2 : ℕ) : ℝ) := by
  have h1 : Q x = ∑ n ∈ Icc 1 x, ∑ d ∈ (Icc 1 n).filter (fun d => d ^ 2 ∣ n), (μ d : ℝ) := by
    rw [Q]; exact sum_congr rfl fun n hn => (sum_sq_dvd_moebius n (mem_Icc.1 hn).1).symm
  rw [h1]
  rw [sum_comm' (t' := Icc 1 x) (s' := fun d => (Icc 1 x).filter (fun n => d ^ 2 ∣ n))]
  · refine sum_congr rfl fun d hd => ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have : (Icc 1 x).filter (fun n => d ^ 2 ∣ n) = (Ioc 0 x).filter (fun n => d ^ 2 ∣ n) := by
      rw [Icc_one_eq_Ioc_zero]
    rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  · intro n d
    simp only [mem_Icc, mem_filter]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, ⟨hd1, hd2⟩, hdn⟩
      exact ⟨⟨⟨hn1, hn2⟩, hdn⟩, hd1, le_trans hd2 hn2⟩
    · rintro ⟨⟨⟨hn1, hn2⟩, hdn⟩, hd1, hd2⟩
      refine ⟨⟨hn1, hn2⟩, ⟨hd1, ?_⟩, hdn⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ n := Nat.le_of_dvd (by omega) hdn

/-! ### Lemma 5(a) -/

theorem sum_inv_sq_le (m K : ℕ) (hm : 1 ≤ m) (hK : 1 ≤ K) :
    ∑ k ∈ range K, 1 / ((m + k : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 + 1 / m - 1 / ((m + K - 1 : ℕ) : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [sum_range_succ]
    have h1 : (1 : ℝ) ≤ ((m + K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + K - 1)
    have e1 : ((m + K : ℕ) : ℝ) = ((m + K - 1 : ℕ) : ℝ) + 1 := by
      rw [show m + K = (m + K - 1) + 1 by omega]; push_cast; ring
    have e2 : ((m + (K + 1) - 1 : ℕ) : ℝ) = ((m + K - 1 : ℕ) : ℝ) + 1 := by
      rw [show m + (K + 1) - 1 = (m + K - 1) + 1 by omega]; push_cast; ring
    rw [e1, e2]
    set t := ((m + K - 1 : ℕ) : ℝ)
    have : 1 / (t + 1) ^ 2 ≤ 1 / t - 1 / (t + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem tsum_tail_le (m : ℕ) (hm : 1 ≤ m) :
    |∑' k : ℕ, (μ (k + m) : ℝ) / ((k + m : ℕ) : ℝ) ^ 2| ≤ 1 / (m : ℝ) ^ 2 + 1 / m := by
  have hs : Summable (fun k : ℕ => (μ (k + m) : ℝ) / ((k + m : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff m).2 summable_moebius_div_sq
  have hsa : Summable (fun k : ℕ => 1 / ((k + m : ℕ) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff m).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using this
  calc |∑' k : ℕ, (μ (k + m) : ℝ) / ((k + m : ℕ) : ℝ) ^ 2|
      ≤ ∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ 2 := by
        have h1 := norm_tsum_le_tsum_norm (f := fun k : ℕ => (μ (k + m) : ℝ) / ((k + m : ℕ) : ℝ) ^ 2)
          hs.norm
        simp only [Real.norm_eq_abs] at h1
        refine h1.trans (Summable.tsum_le_tsum (fun k => ?_) hs.abs hsa)
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + m : ℕ) : ℝ) ^ 2)]
        exact div_le_div_of_nonneg_right (abs_moebius_le_one' _) (by positivity)
    _ ≤ 1 / (m : ℝ) ^ 2 + 1 / m := by
        refine hsa.tsum_le_of_sum_range_le fun K => ?_
        rcases Nat.eq_zero_or_pos K with rfl | hK
        · simp; positivity
        · have := sum_inv_sq_le m K hm hK
          have h0 : (0 : ℝ) ≤ 1 / ((m + K - 1 : ℕ) : ℝ) := by positivity
          calc ∑ i ∈ range K, 1 / ((i + m : ℕ) : ℝ) ^ 2
              = ∑ k ∈ range K, 1 / ((m + k : ℕ) : ℝ) ^ 2 :=
                sum_congr rfl fun k _ => by rw [add_comm]
            _ ≤ _ := this
            _ ≤ _ := by linarith

theorem nat_div_cast_bounds (x n : ℕ) (hn : 0 < n) :
    (x : ℝ) / n - 1 < ((x / n : ℕ) : ℝ) ∧ ((x / n : ℕ) : ℝ) ≤ (x : ℝ) / n := by
  have h1 := Nat.floor_div_eq_div (K := ℝ) x n
  constructor
  · rw [← h1]; have := Nat.lt_floor_add_one ((x : ℝ) / n); linarith
  · exact Nat.cast_div_le

/-- **Lemma 5(a)**: `|Q(x) − κx| ≤ 2√x + 1`. -/
theorem abs_Q_sub_le (x : ℕ) : |Q x - κ * x| ≤ 2 * Real.sqrt x + 1 := by
  set z := Nat.sqrt x with hz
  have hzx : z ≤ x := Nat.sqrt_le_self x
  have hQ : Q x = ∑ d ∈ Icc 1 z, (μ d : ℝ) * ((x / d ^ 2 : ℕ) : ℝ) := by
    rw [Q_eq_sum]
    have hsub : Icc 1 z ⊆ Icc 1 x := Icc_subset_Icc le_rfl hzx
    rw [← sum_subset hsub]
    intro d hd hdn
    simp only [mem_Icc, not_and, not_le] at hd hdn
    have hlt : z < d := hdn hd.1
    have : x < d ^ 2 := by
      exact Nat.sqrt_lt'.1 hlt
    rw [Nat.div_eq_of_lt this]; simp
  have hκ : κ = ∑ d ∈ Icc 1 z, (μ d : ℝ) / (d : ℝ) ^ 2 +
      ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2 := by
    rw [← hasSum_moebius_div_sq.tsum_eq, ← summable_moebius_div_sq.sum_add_tsum_nat_add (z + 1)]
    congr 1
    have hr : range (z + 1) = insert 0 (Icc 1 z) := by
      ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hr, sum_insert (by simp)]; simp
  have hsx : (z : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' x
  have hxz : (x : ℝ) < ((z : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' x
  have hsxz : Real.sqrt x < (z : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]; exact hxz
  -- the main decomposition
  have hdec : Q x - κ * x = ∑ d ∈ Icc 1 z, (μ d : ℝ) * (((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2) -
      x * ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2 := by
    rw [hQ, hκ, add_mul, mul_comm (∑' k : ℕ, _) (x : ℝ)]
    simp only [mul_sub, sum_sub_distrib, sum_mul]
    have : ∀ d ∈ Icc 1 z, (μ d : ℝ) / (d : ℝ) ^ 2 * x = (μ d : ℝ) * ((x : ℝ) / (d : ℝ) ^ 2) :=
      fun d _ => by ring
    rw [sum_congr rfl this]; ring
  have h1 : |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| ≤ z := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ d ∈ Icc 1 z, |(μ d : ℝ) * (((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| ≤ 1 := by
      intro d hd
      have hd0 : 0 < d ^ 2 := by have := (mem_Icc.1 hd).1; positivity
      obtain ⟨h1, h2⟩ := nat_div_cast_bounds x (d ^ 2) hd0
      push_cast at h1 h2
      rw [abs_mul]
      have : |((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc |(μ d : ℝ)| * |((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2| ≤ 1 * 1 :=
            mul_le_mul (abs_moebius_le_one' d) this (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    refine (sum_le_sum this).trans (le_of_eq ?_)
    simp
  have h2 : |(x : ℝ) * ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2| ≤
      1 + Real.sqrt x := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x)]
    have ht := tsum_tail_le (z + 1) (by omega)
    have hz1 : (0 : ℝ) < (z : ℝ) + 1 := by positivity
    push_cast at ht
    calc (x : ℝ) * |∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2|
        ≤ x * (1 / ((z : ℝ) + 1) ^ 2 + 1 / ((z : ℝ) + 1)) := by
          gcongr; push_cast; exact ht
      _ = x / ((z : ℝ) + 1) ^ 2 + x / ((z : ℝ) + 1) := by ring
      _ ≤ 1 + Real.sqrt x := by
          gcongr
          · rw [div_le_one (by positivity)]; exact hxz.le
          · rw [div_le_iff₀ hz1]
            have hsq := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) x)
            nlinarith [Real.sqrt_nonneg (x : ℝ)]
  rw [hdec]
  calc |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2) -
        x * ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2|
      ≤ |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((x / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| +
        |(x : ℝ) * ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2| := abs_sub _ _
    _ ≤ z + (1 + Real.sqrt x) := add_le_add h1 h2
    _ ≤ 2 * Real.sqrt x + 1 := by linarith

theorem Q_le (x : ℕ) : Q x ≤ κ * x + 2 * Real.sqrt x + 1 := by
  have := abs_Q_sub_le x; rw [abs_le] at this; linarith

theorem Q_ge (x : ℕ) : κ * x - 2 * Real.sqrt x - 1 ≤ Q x := by
  have := abs_Q_sub_le x; rw [abs_le] at this; linarith

/-! ### Lemma 5(b) -/

theorem inv_sqrt_le_two_mul_sub {k : ℕ} (hk : 1 ≤ k) :
    1 / Real.sqrt (k + 1 : ℕ) ≤ 2 * (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) := by
  have h1 : 0 < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have h2 : Real.sqrt k ≤ Real.sqrt (k + 1 : ℕ) := Real.sqrt_le_sqrt (by push_cast; linarith)
  have h3 : Real.sqrt (k + 1 : ℕ) ^ 2 - Real.sqrt k ^ 2 = 1 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
  rw [div_le_iff₀ h1]
  nlinarith [Real.sqrt_nonneg (k : ℝ)]

theorem sum_inv_sqrt_le (J : ℕ) (hJ : 1 ≤ J) :
    ∑ k ∈ Icc 1 J, 1 / Real.sqrt k ≤ 2 * Real.sqrt J - 1 := by
  induction J, hJ using Nat.le_induction with
  | base => simp; norm_num
  | succ J hJ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have := inv_sqrt_le_two_mul_sub hJ
    linarith

theorem one_sub_sqrt_div_le (i : ℕ) (hi : 1 ≤ i) :
    1 - Real.sqrt i / Real.sqrt (i + 1 : ℕ) ≤ 1 / (2 * i + 1) := by
  set a := Real.sqrt i
  set b := Real.sqrt (i + 1 : ℕ)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  have ha2 : a ^ 2 = i := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = i + 1 := by rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have e1 : (2 * (i : ℝ) + 1) = a ^ 2 + b ^ 2 := by rw [ha2, hb2]; ring
  have e2 : b ^ 2 - a ^ 2 = 1 := by rw [ha2, hb2]; ring
  rw [one_sub_div hb.ne', div_le_div_iff₀ hb (by positivity), e1, one_mul]
  nlinarith [mul_nonneg ha (sq_nonneg (b - a))]

theorem two_div_le_log (i : ℕ) (hi : 1 ≤ i) : 2 / (2 * (i : ℝ) + 1) ≤ Real.log (1 + 1 / (i : ℝ)) := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  set t : ℝ := 1 / (2 * i + 1)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := LogCert.hasSum_atanh ht0 ht1
  have := sum_le_hasSum (range 1) (fun k _ => by positivity) hs
  simp at this
  have e : (1 + t) / (1 - t) = 1 + 1 / (i : ℝ) := by
    simp only [t]; field_simp; ring
  rw [e] at this
  calc 2 / (2 * (i : ℝ) + 1) = 2 * t := by simp only [t]; ring
    _ ≤ _ := by linarith

theorem sum_log_one_add_inv (J : ℕ) :
    ∑ i ∈ Ico 1 J, Real.log (1 + 1 / (i : ℝ)) = Real.log J := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  have : ∀ i ∈ Ico 1 J, Real.log (1 + 1 / (i : ℝ)) =
      Real.log (((i + 1 : ℕ) : ℝ)) - Real.log ((i : ℕ) : ℝ) := by
    intro i hi; rw [← log_succ_sub_log (mem_Ico.1 hi).1]; push_cast; ring
  rw [sum_congr rfl this, sum_Ico_sub_telescope (fun i => Real.log ((i : ℕ) : ℝ)) hJ]
  simp

/-- **Lemma 5(b)** (discrete form). -/
theorem sum_sq_div_sqrt_le (J : ℕ) :
    ∑ j ∈ Icc 1 J, (μ j : ℝ) ^ 2 / Real.sqrt j ≤ κ * (2 * Real.sqrt J - 1) + 4 + Real.log J := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp; linarith [κ_hi]
  set g : ℕ → ℝ := fun j => 1 / Real.sqrt j with hg
  have habel := sum_mul_eq_abel (fun j => (μ j : ℝ) ^ 2) g J
  have hl : ∑ j ∈ Icc 1 J, (μ j : ℝ) ^ 2 / Real.sqrt j = ∑ k ∈ Icc 1 J, (μ k : ℝ) ^ 2 * g k :=
    sum_congr rfl fun k _ => by simp only [hg]; ring
  rw [hl, habel]
  change Q J * g J - ∑ i ∈ Ico 1 J, Q i * (g (i + 1) - g i) ≤ _
  have hgdec : ∀ i : ℕ, 1 ≤ i → 0 ≤ g i - g (i + 1) := by
    intro i hi
    simp only [hg, sub_nonneg]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by exact_mod_cast hi))
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hgJ : 0 ≤ g J := by simp only [hg]; positivity
  set B : ℕ → ℝ := fun i => κ * i + 2 * Real.sqrt i + 1 with hB
  have step1 : Q J * g J - ∑ i ∈ Ico 1 J, Q i * (g (i + 1) - g i) ≤
      B J * g J + ∑ i ∈ Ico 1 J, B i * (g i - g (i + 1)) := by
    have e : Q J * g J - ∑ i ∈ Ico 1 J, Q i * (g (i + 1) - g i) =
        Q J * g J + ∑ i ∈ Ico 1 J, Q i * (g i - g (i + 1)) := by
      rw [sub_eq_add_neg, ← sum_neg_distrib]; congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [e]
    gcongr with i hi
    · exact Q_le J
    · exact hgdec i (mem_Ico.1 hi).1
    · exact Q_le i
  -- the `κ` part: `J g(J) + ∑ i (g i − g(i+1)) = ∑_{k ≤ J} g(k)`
  have hκpart := sum_mul_eq_abel (fun _ => (1 : ℝ)) g J
  simp only [one_mul, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    at hκpart
  have hsqrt := sum_inv_sqrt_le J hJ
  have hsg : ∑ k ∈ Icc 1 J, g k = ∑ k ∈ Icc 1 J, 1 / Real.sqrt k := rfl
  -- the error part
  have herr1 : (2 * Real.sqrt J + 1) * g J ≤ 3 := by
    simp only [hg]
    have h1 : (1 : ℝ) ≤ Real.sqrt J := by rw [Real.one_le_sqrt]; exact_mod_cast hJ
    rw [mul_one_div, div_le_iff₀ (by linarith)]; linarith
  have herr2 : ∑ i ∈ Ico 1 J, (2 * Real.sqrt i) * (g i - g (i + 1)) ≤ Real.log J := by
    rw [← sum_log_one_add_inv J]
    refine sum_le_sum fun i hi => ?_
    have hi1 := (mem_Ico.1 hi).1
    have hs : 0 < Real.sqrt i := Real.sqrt_pos.2 (by exact_mod_cast hi1)
    have e : (2 * Real.sqrt i) * (g i - g (i + 1)) = 2 * (1 - Real.sqrt i / Real.sqrt (i + 1 : ℕ)) := by
      simp only [hg]; field_simp
    rw [e]
    have := one_sub_sqrt_div_le i hi1
    have := two_div_le_log i hi1
    have : 2 * (1 - Real.sqrt i / Real.sqrt (i + 1 : ℕ)) ≤ 2 / (2 * (i : ℝ) + 1) := by
      rw [show 2 / (2 * (i : ℝ) + 1) = 2 * (1 / (2 * i + 1)) by ring]; linarith
    linarith
  have herr3 : ∑ i ∈ Ico 1 J, (g i - g (i + 1)) ≤ 1 := by
    have := sum_Ico_sub_telescope g hJ
    rw [show ∑ i ∈ Ico 1 J, (g i - g (i + 1)) = -∑ i ∈ Ico 1 J, (g (i + 1) - g i) by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring, this]
    simp only [hg, Nat.cast_one, Real.sqrt_one, div_one]
    have : 0 ≤ 1 / Real.sqrt J := by positivity
    linarith
  have e1 : ∑ i ∈ Ico 1 J, B i * (g i - g (i + 1)) =
      κ * ∑ i ∈ Ico 1 J, (i : ℝ) * (g i - g (i + 1)) +
      ∑ i ∈ Ico 1 J, (2 * Real.sqrt i) * (g i - g (i + 1)) + ∑ i ∈ Ico 1 J, (g i - g (i + 1)) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by simp only [hB]; ring
  have e2 : ∑ i ∈ Ico 1 J, (i : ℝ) * (g i - g (i + 1)) = -∑ i ∈ Ico 1 J, (i : ℝ) * (g (i + 1) - g i) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
  have hBJ : B J * g J = κ * (J * g J) + (2 * Real.sqrt J + 1) * g J := by simp only [hB]; ring
  have hκ := κ_pos
  have hsum_g : (J : ℝ) * g J - ∑ i ∈ Ico 1 J, (i : ℝ) * (g (i + 1) - g i) ≤ 2 * Real.sqrt J - 1 := by
    rw [← hκpart]; exact hsqrt
  have := mul_le_mul_of_nonneg_left hsum_g hκ.le
  calc Q J * g J - ∑ i ∈ Ico 1 J, Q i * (g (i + 1) - g i)
      ≤ B J * g J + ∑ i ∈ Ico 1 J, B i * (g i - g (i + 1)) := step1
    _ ≤ κ * (2 * Real.sqrt J - 1) + 4 + Real.log J := by
        rw [e1, e2, hBJ]; nlinarith

/-! ### Lemma 5(d) -/

theorem sum_delta_sq_le (J : ℕ) :
    ∑ k ∈ Icc 1 J, (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 ≤ 2 := by
  have key : ∀ J : ℕ, 2 ≤ J →
      ∑ k ∈ Icc 1 J, (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 ≤ 2 - 1 / ((J : ℝ) - 1) := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base =>
      rw [show Icc 1 2 = {1, 2} by rfl, sum_pair (by norm_num)]
      have h1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      norm_num
      rw [abs_le]; constructor <;> linarith
    | succ J hJ ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hJ' : (2 : ℝ) ≤ J := by exact_mod_cast hJ
      push_cast
      rw [add_sub_cancel_right]
      have hd : Real.log ((J : ℝ) + 1) - Real.log J ≤ 1 / J := by
        have := log_succ_sub_log (n := J) (by omega)
        rw [this]
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (J : ℝ) by positivity)
        linarith
      have hd0 : 0 ≤ Real.log ((J : ℝ) + 1) - Real.log J :=
        sub_nonneg.2 (Real.log_le_log (by positivity) (by linarith))
      have : (Real.log ((J : ℝ) + 1) - Real.log J) ^ 2 ≤ 1 / (J : ℝ) ^ 2 := by
        rw [one_div, ← inv_pow, ← one_div]; exact pow_le_pow_left₀ hd0 hd 2
      have h3 : 1 / (J : ℝ) ^ 2 ≤ 1 / ((J : ℝ) - 1) - 1 / J := by
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
  rcases Nat.lt_or_ge J 2 with h | h
  · interval_cases J
    · simp
    · simp
  · have := key J h
    have : 0 < 1 / ((J : ℝ) - 1) := by
      have : (2 : ℝ) ≤ J := by exact_mod_cast h
      apply div_pos one_pos; linarith
    linarith

/-- **Lemma 5(d)** (discrete form). -/
theorem sum_sq_div_log_le {J : ℕ} {D eLo eHi : ℝ} (hJ : 1 ≤ J) (hJD : (J : ℝ) < D)
    (hQ1 : ∀ i : ℕ, 1 ≤ i → i ≤ J → κ * Real.log i + eLo ≤ Q1 i ∧ Q1 i ≤ κ * Real.log i + eHi) :
    ∑ j ∈ Icc 1 J, (μ j : ℝ) ^ 2 / (j * Real.log (D / j)) ≤
      κ * (Real.log (Real.log D / (Real.log D - Real.log J)) + 2 / (Real.log D - Real.log J) ^ 2) +
        (eHi - eLo) / (Real.log D - Real.log J) + eLo / Real.log D := by
  set L := Real.log D with hL
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hD : 0 < D := by linarith
  have hLℓ : Real.log J < L := Real.log_lt_log (by linarith) hJD
  have hℓ0 : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg hJ1
  have hL0 : 0 < L := by linarith
  set g : ℕ → ℝ := fun j => 1 / (L - Real.log j) with hg
  have hlogle : ∀ j : ℕ, j ≤ J → Real.log j ≤ Real.log J := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hℓ0]
    · exact Real.log_le_log (by exact_mod_cast hj0) (by exact_mod_cast hj)
  have hgpos : ∀ j : ℕ, j ≤ J → 0 < g j := by
    intro j hj; simp only [hg]; have := hlogle j hj; apply div_pos one_pos; linarith
  have hginc : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ J → 0 ≤ g (i + 1) - g i := by
    intro i hi hiJ
    simp only [hg, sub_nonneg]
    have h1 := hlogle (i + 1) hiJ
    have h2 : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
    apply one_div_le_one_div_of_le (by linarith); linarith
  have hl : ∑ j ∈ Icc 1 J, (μ j : ℝ) ^ 2 / (j * Real.log (D / j)) =
      ∑ k ∈ Icc 1 J, (μ k : ℝ) ^ 2 / k * g k := by
    refine sum_congr rfl fun k hk => ?_
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.1 hk).1
    simp only [hg]
    rw [Real.log_div hD.ne' hk1.ne', ← hL]
    have : 0 < L - Real.log k := by have := hlogle k (mem_Icc.1 hk).2; linarith
    field_simp
  rw [hl, sum_mul_eq_abel]
  change Q1 J * g J - ∑ i ∈ Ico 1 J, Q1 i * (g (i + 1) - g i) ≤ _
  have step1 : Q1 J * g J - ∑ i ∈ Ico 1 J, Q1 i * (g (i + 1) - g i) ≤
      (κ * Real.log J + eHi) * g J - ∑ i ∈ Ico 1 J, (κ * Real.log i + eLo) * (g (i + 1) - g i) := by
    have h1 : Q1 J * g J ≤ (κ * Real.log J + eHi) * g J :=
      mul_le_mul_of_nonneg_right (hQ1 J hJ le_rfl).2 (hgpos J le_rfl).le
    have h2 : ∑ i ∈ Ico 1 J, (κ * Real.log i + eLo) * (g (i + 1) - g i) ≤
        ∑ i ∈ Ico 1 J, Q1 i * (g (i + 1) - g i) := by
      refine sum_le_sum fun i hi => ?_
      obtain ⟨hi1, hi2⟩ := mem_Ico.1 hi
      exact mul_le_mul_of_nonneg_right (hQ1 i hi1 hi2.le).1 (hginc i hi1 hi2)
    linarith
  -- the `κ` bracket
  set f : ℕ → ℝ := fun k => Real.log k - Real.log ((k : ℝ) - 1) with hf
  have hfsum : ∀ i : ℕ, ∑ k ∈ Icc 1 i, f k = Real.log i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [sum_Icc_succ_top (by omega), ih]; simp only [hf]; push_cast; rw [add_sub_cancel_right]; ring
  have hbr := sum_mul_eq_abel f g J
  simp only [hfsum] at hbr
  have hκbr : ∑ k ∈ Icc 1 J, f k * g k ≤
      Real.log (L / (L - Real.log J)) + 2 / (L - Real.log J) ^ 2 := by
    have hpt : ∀ k ∈ Icc 1 J, f k * g k ≤
        (Real.log (L - Real.log ((k : ℝ) - 1)) - Real.log (L - Real.log k)) +
          f k ^ 2 / (L - Real.log J) ^ 2 := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      set a := Real.log ((k : ℝ) - 1)
      set b := Real.log (k : ℝ)
      have ha0 : 0 ≤ a ∨ (k : ℝ) - 1 = 0 := by
        rcases eq_or_lt_of_le hk1' with h | h
        · right; linarith
        · left; exact Real.log_nonneg (by
            have : (2 : ℝ) ≤ k := by
              have : 2 ≤ k := by
                by_contra hc; push Not at hc
                have : k = 1 := by omega
                subst this; simp at h
              exact_mod_cast this
            linarith)
      have ha : 0 ≤ a := by rcases ha0 with h | h <;> simp_all [a]
      have hab : a ≤ b := by
        rcases eq_or_lt_of_le hk1' with h | h
        · simp only [a, b, ← h]; simp
        · exact Real.log_le_log (by linarith) (by linarith)
      have hbJ : b ≤ Real.log J := hlogle k hk2
      have hLb : 0 < L - b := by linarith
      have hLa : L - b ≤ L - a := by linarith
      simp only [hf, hg]
      change (b - a) * (1 / (L - b)) ≤ (Real.log (L - a) - Real.log (L - b)) + (b - a) ^ 2 / (L - Real.log J) ^ 2
      have hLa0 : 0 < L - a := by linarith
      have e1 : (b - a) * (1 / (L - b)) = (b - a) / (L - a) + (b - a) ^ 2 / ((L - a) * (L - b)) := by
        field_simp; ring
      rw [e1]
      have i1 : (b - a) / (L - a) ≤ Real.log (L - a) - Real.log (L - b) := by
        rw [← Real.log_div hLa0.ne' hLb.ne']
        have := Real.one_sub_inv_le_log_of_pos (show 0 < (L - a) / (L - b) by positivity)
        rw [inv_div] at this
        have e2 : 1 - (L - b) / (L - a) = (b - a) / (L - a) := by field_simp; ring
        linarith
      have i2 : (b - a) ^ 2 / ((L - a) * (L - b)) ≤ (b - a) ^ 2 / (L - Real.log J) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by nlinarith)
        rw [sq]; exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, ← sum_div]
    have htel : ∑ k ∈ Icc 1 J, (Real.log (L - Real.log ((k : ℝ) - 1)) - Real.log (L - Real.log k)) =
        Real.log L - Real.log (L - Real.log J) := by
      have := sum_Icc_sub_telescope (fun k : ℕ => -Real.log (L - Real.log ((k : ℝ) - 1))) J
      rw [show ∑ k ∈ Icc 1 J, (Real.log (L - Real.log ((k : ℝ) - 1)) - Real.log (L - Real.log k)) =
        ∑ k ∈ Icc 1 J, (-Real.log (L - Real.log (((k + 1 : ℕ) : ℝ) - 1)) -
          -Real.log (L - Real.log ((k : ℝ) - 1))) from sum_congr rfl fun k _ => by
            push_cast; rw [add_sub_cancel_right]; ring,
        this]
      push_cast; rw [add_sub_cancel_right]; simp; ring
    rw [htel, ← Real.log_div hL0.ne' (by linarith : L - Real.log J ≠ 0)]
    gcongr
    · exact sum_delta_sq_le J
  have hg1 : g 1 = 1 / L := by simp [hg]
  have hgJ : g J = 1 / (L - Real.log J) := rfl
  have htel' : ∑ i ∈ Ico 1 J, (g (i + 1) - g i) = g J - g 1 := sum_Ico_sub_telescope g hJ
  have hfinal : (κ * Real.log J + eHi) * g J - ∑ i ∈ Ico 1 J, (κ * Real.log i + eLo) * (g (i + 1) - g i) =
      κ * ∑ k ∈ Icc 1 J, f k * g k + (eHi - eLo) * g J + eLo * g 1 := by
    have e : ∑ i ∈ Ico 1 J, (κ * Real.log i + eLo) * (g (i + 1) - g i) =
        κ * ∑ i ∈ Ico 1 J, Real.log i * (g (i + 1) - g i) + eLo * ∑ i ∈ Ico 1 J, (g (i + 1) - g i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
    rw [e, hbr, htel']; ring
  have hκ := κ_pos
  calc Q1 J * g J - ∑ i ∈ Ico 1 J, Q1 i * (g (i + 1) - g i)
      ≤ _ := step1
    _ = _ := hfinal
    _ ≤ κ * (Real.log (L / (L - Real.log J)) + 2 / (L - Real.log J) ^ 2) + (eHi - eLo) * g J + eLo * g 1 := by
        gcongr
    _ = _ := by rw [hg1, hgJ]; ring

end TernaryGoldbach.RSBounds.Moebius003
