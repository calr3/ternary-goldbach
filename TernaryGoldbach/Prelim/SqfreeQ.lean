import TernaryGoldbach.Prelim.SqfreeCount

/-!
# The number of squarefree integers up to `x`

`Q(x) = #{n ≤ x : n squarefree} = ∑_{d ≤ √x} μ(d) ⌊x/d²⌋`, hence `|Q(x) − (6/π²) x| ≤ 3√x` for `x ≥ 1`
(`Q_sub_le`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sqf

/-- `Q(x)`. -/
noncomputable def Qs (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, if Squarefree n then (1 : ℝ) else 0

/-- `6/π²`. -/
noncomputable def kap : ℝ := 6 / Real.pi ^ 2

theorem kap_tsum : ∑' m : ℕ, (μ m : ℝ) / (m : ℝ) ^ 2 = kap := by
  have h := tsum_coprime_moebius_div_sq (P := 1) one_ne_zero
  simp only [Nat.coprime_one_right_eq_true, if_true, Nat.primeFactors_one, prod_empty, div_one] at h
  exact h

theorem summable_mu_sq : Summable (fun m : ℕ => (μ m : ℝ) / (m : ℝ) ^ 2) := by
  have h := summable_coprime_moebius_div_sq 1
  simpa using h

/-- `Q(N) = ∑_{d ≤ N} μ(d) ⌊N/d²⌋`. -/
theorem Qs_eq (N : ℕ) : Qs N = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
  unfold Qs
  rw [Nat.floor_natCast]
  have e1 : ∀ l ∈ Icc 1 N, (if Squarefree l then (1 : ℝ) else 0) =
      ∑ m ∈ l.divisors.filter (fun m => m * m ∣ l), (μ m : ℝ) := by
    intro l hl; rw [sum_moebius_sq_dvd (by have := (mem_Icc.1 hl).1; omega)]
  rw [sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun m => (Icc 1 N).filter (fun l => m * m ∣ l))]
  · refine sum_congr rfl fun d hd => ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have : (Icc 1 N).filter (fun l => d * d ∣ l) = (Ioc 0 N).filter (fun l => d * d ∣ l) := by
      congr 1
    rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  · intro l m
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hl1, hlN⟩, ⟨hml, -⟩, hmm⟩
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hml (by omega)
      exact ⟨⟨⟨hl1, hlN⟩, hmm⟩, hm1, le_trans (Nat.le_of_dvd (by omega) hml) hlN⟩
    · rintro ⟨⟨⟨hl1, hlN⟩, hmm⟩, hm1, hmN⟩
      exact ⟨⟨hl1, hlN⟩, ⟨(Nat.dvd_mul_right m m).trans hmm, by omega⟩, hmm⟩

theorem Qs_floor (x : ℝ) : Qs x = Qs ⌊x⌋₊ := by unfold Qs; rw [Nat.floor_natCast]

theorem Qs_nonneg (x : ℝ) : 0 ≤ Qs x := sum_nonneg fun n _ => by split_ifs <;> norm_num

theorem Qs_le (x : ℝ) : Qs x ≤ ⌊x⌋₊ := by
  unfold Qs
  calc ∑ n ∈ Icc 1 ⌊x⌋₊, (if Squarefree n then (1 : ℝ) else 0) ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) :=
        sum_le_sum fun n _ => by split_ifs <;> norm_num
    _ = ⌊x⌋₊ := by simp

theorem kap_pos : 0 < kap := by unfold kap; positivity

theorem kap_le_one : kap ≤ 1 := by
  unfold kap; rw [div_le_one (by positivity)]
  nlinarith [Real.pi_gt_three]

/-- **`|Q(x) − (6/π²) x| ≤ 3√x`** for `x ≥ 1`. -/
theorem Q_sub_le {x : ℝ} (hx : 1 ≤ x) : |Qs x - kap * x| ≤ 3 * √x := by
  have hx0 : 0 < x := by linarith
  have hsx : 1 ≤ √x := by rw [Real.one_le_sqrt]; exact hx
  rcases lt_or_ge x 4 with h4 | h4
  · -- small `x`: `0 ≤ Q, κx ≤ x ≤ 2√x`
    have h1 := Qs_nonneg x
    have h2 : Qs x ≤ x := (Qs_le x).trans (Nat.floor_le hx0.le)
    have h3 : kap * x ≤ x := by nlinarith [kap_le_one]
    have h3' : 0 ≤ kap * x := by nlinarith [kap_pos]
    have hxs : x ≤ 2 * √x := by
      have := Real.sq_sqrt hx0.le
      nlinarith [Real.sqrt_nonneg x, show √x < 2 by rw [Real.sqrt_lt' (by norm_num)]; linarith]
    rw [abs_le]; constructor <;> nlinarith
  · set N := ⌊x⌋₊ with hN
    set z := ⌊√x⌋₊ with hz
    have hz1 : 2 ≤ z := Nat.le_floor (by
      rw [show ((2 : ℕ) : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num]
      exact Real.sqrt_le_sqrt h4)
    have hzr : (z : ℝ) ≤ √x := Nat.floor_le (Real.sqrt_nonneg _)
    have hzr2 : √x < z + 1 := Nat.lt_floor_add_one _
    have hsq := Real.sq_sqrt hx0.le
    -- terms `d > z` of `Q` vanish
    have hQ : Qs x = ∑ d ∈ Icc 1 z, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
      rw [Qs_floor, Qs_eq, ← hN, show Icc 1 N = Ioc 0 N by ext; simp; omega]
      have hzN : z ≤ N := by
        apply Nat.floor_le_floor
        nlinarith
      rw [← Finset.sum_Ioc_consecutive _ (show 0 ≤ z by omega) hzN]
      rw [show Ioc 0 z = Icc 1 z by ext; simp; omega]
      have : ∑ d ∈ Ioc z N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) = 0 := by
        refine sum_eq_zero fun d hd => ?_
        have hdz : z + 1 ≤ d := (mem_Ioc.1 hd).1
        have : N < d * d := by
          have h1 : (N : ℝ) ≤ x := Nat.floor_le hx0.le
          have h2 : ((z : ℝ) + 1) ≤ d := by exact_mod_cast hdz
          have h3 : x < ((d * d : ℕ) : ℝ) := by push_cast; nlinarith
          exact_mod_cast lt_of_le_of_lt h1 h3
        rw [Nat.div_eq_of_lt this]; simp
      rw [show Icc 1 z = Ioc 0 z by ext; simp; omega, this, add_zero]
    -- `κ = ∑_{d ≤ z} + tail`
    have hk := kap_tsum
    rw [← summable_mu_sq.sum_add_tsum_nat_add (z + 1)] at hk
    have hrange : ∑ d ∈ range (z + 1), (μ d : ℝ) / (d : ℝ) ^ 2 = ∑ d ∈ Icc 1 z, (μ d : ℝ) / (d : ℝ) ^ 2 := by
      rw [range_eq_Ico, show Ico 0 (z + 1) = insert 0 (Icc 1 z) by ext; simp; omega, sum_insert (by simp)]
      simp
    rw [hrange] at hk
    set T := ∑' k : ℕ, (μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2 with hT
    have hTle : |T| ≤ 1 / z := by
      have htail := Small.tsum_inv_sq_tail (M := z + 1) (by omega)
      have hsum2 : Summable (fun k : ℕ => 1 / ((k + (z + 1) : ℕ) : ℝ) ^ 2) := by
        have := (Real.summable_one_div_nat_pow.2 one_lt_two).comp_injective (add_left_injective (z + 1))
        simpa [Function.comp_def] using this
      calc |T| ≤ ∑' k : ℕ, |(μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2| := by
            rw [hT]
            have hs := (summable_mu_sq.comp_injective (add_left_injective (z + 1)))
            exact (norm_tsum_le_tsum_norm hs.norm).trans le_rfl
        _ ≤ ∑' k : ℕ, 1 / ((k + (z + 1) : ℕ) : ℝ) ^ 2 := by
            refine (Summable.tsum_le_tsum (fun k => ?_) ?_ hsum2)
            · have hb0 : (0 : ℝ) < ((k + (z + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
              have hb : (0 : ℝ) < ((k + (z + 1) : ℕ) : ℝ) ^ 2 := pow_pos hb0 2
              have hm : |(μ (k + (z + 1)) : ℝ)| ≤ 1 := by
                have := ArithmeticFunction.abs_moebius_le_one (n := k + (z + 1)); exact_mod_cast this
              show |(μ (k + (z + 1)) : ℝ) / ((k + (z + 1) : ℕ) : ℝ) ^ 2| ≤ 1 / ((k + (z + 1) : ℕ) : ℝ) ^ 2
              rw [abs_div, abs_of_pos hb]
              exact div_le_div_of_nonneg_right hm hb.le
            · exact (summable_mu_sq.comp_injective (add_left_injective (z + 1))).abs
        _ ≤ 1 / (((z + 1 : ℕ) : ℝ) - 1) := htail
        _ = 1 / z := by push_cast; ring_nf
    -- the difference
    have hdiff : Qs x - kap * x =
        ∑ d ∈ Icc 1 z, (μ d : ℝ) * (((N / (d * d) : ℕ) : ℝ) - x / (d : ℝ) ^ 2) - x * T := by
      rw [hQ, ← hk, add_mul, sum_mul, ← sub_sub, ← sum_sub_distrib]
      congr 1
      · exact sum_congr rfl fun d _ => by ring
      · ring
    have hterm : ∀ d ∈ Icc 1 z, |(μ d : ℝ) * (((N / (d * d) : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| ≤ 1 := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.1 hd).1
      have e : ((N / (d * d) : ℕ) : ℝ) = ⌊x / (d : ℝ) ^ 2⌋₊ := by
        rw [hN, show (d : ℝ) ^ 2 = ((d * d : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_natCast]
      rw [e, abs_mul]
      have h1 := Nat.floor_le (show 0 ≤ x / (d : ℝ) ^ 2 by positivity)
      have h2 := Nat.lt_floor_add_one (x / (d : ℝ) ^ 2)
      have hm : |(μ d : ℝ)| ≤ 1 := by have := ArithmeticFunction.abs_moebius_le_one (n := d); exact_mod_cast this
      have : |((⌊x / (d : ℝ) ^ 2⌋₊ : ℕ) : ℝ) - x / (d : ℝ) ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (μ d : ℝ), abs_nonneg (((⌊x / (d : ℝ) ^ 2⌋₊ : ℕ) : ℝ) - x / (d : ℝ) ^ 2)]
    have hsum : |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((N / (d * d) : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| ≤ z := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
      simp
    have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
    have hxT : |x * T| ≤ x / z := by
      rw [abs_mul, abs_of_pos hx0]
      calc x * |T| ≤ x * (1 / z) := mul_le_mul_of_nonneg_left hTle hx0.le
        _ = x / z := by ring
    have hxz : x / z ≤ 2 * √x := by
      rw [div_le_iff₀ hz0]
      have : √x / 2 ≤ z := by nlinarith
      nlinarith
    rw [hdiff]
    calc |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((N / (d * d) : ℕ) : ℝ) - x / (d : ℝ) ^ 2) - x * T|
        ≤ |∑ d ∈ Icc 1 z, (μ d : ℝ) * (((N / (d * d) : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| + |x * T| :=
          abs_sub _ _
      _ ≤ z + 2 * √x := add_le_add hsum (hxT.trans hxz)
      _ ≤ 3 * √x := by linarith

/-- `μ²` as a real 0/1 function. -/
noncomputable def sq (n : ℕ) : ℝ := if Squarefree n then 1 else 0

theorem sq_nonneg (n : ℕ) : 0 ≤ sq n := by unfold sq; split_ifs <;> norm_num
theorem sq_le_one (n : ℕ) : sq n ≤ 1 := by unfold sq; split_ifs <;> norm_num

theorem Qs_nat_succ (n : ℕ) : Qs ((n + 1 : ℕ) : ℝ) = Qs (n : ℝ) + sq (n + 1) := by
  unfold Qs sq; rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega)]

theorem Qs_upper {t : ℝ} (ht : 1 ≤ t) : Qs t ≤ kap * t + 3 * √t := by
  have := Q_sub_le ht; rw [abs_le] at this; linarith [this.2]

/-- **`∑_{j ≤ J} μ²(j)/√j ≤ 2κ√J + 4.5 + 1.5 log J`** for `J ≥ 1`. -/
theorem sum_sq_div_sqrt (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Icc 1 J, sq j / √(j : ℝ) ≤ 2 * kap * √(J : ℝ) + 4.5 + 1.5 * Real.log J := by
  -- Abel: `∑_{j ≤ J} sq j / √j = Q(J)/√J + ∑_{j < J} Q(j) (1/√j − 1/√(j+1))`
  have habel : ∀ J : ℕ, 1 ≤ J → ∑ j ∈ Icc 1 J, sq j / √(j : ℝ) =
      Qs (J : ℝ) / √(J : ℝ) + ∑ j ∈ Ico 1 J, Qs (j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base =>
      simp [Qs, sq, Finset.filter_singleton, squarefree_one]
    | succ J hJ ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Ico_succ_top hJ, Qs_nat_succ]
      push_cast
      ring
  rw [habel J hJ]
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hsJ : 0 < √(J : ℝ) := Real.sqrt_pos.2 (by linarith)
  -- each term: `Q(j)(1/√j − 1/√(j+1)) ≤ κ j(...) + 3√j(...)`, and the pieces telescope
  have hterm : ∀ j ∈ Ico 1 J, Qs (j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) ≤
      kap * (√((j : ℝ) + 1) - √(j : ℝ)) + 1.5 * (Real.log ((j : ℝ) + 1) - Real.log j) := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.1 hj).1
    have hj0 : 0 < (j : ℝ) := by linarith
    have s0 : 0 < √(j : ℝ) := Real.sqrt_pos.2 hj0
    have s1 : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    have hss : √(j : ℝ) ≤ √((j : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hd : 0 ≤ 1 / √(j : ℝ) - 1 / √((j : ℝ) + 1) :=
      sub_nonneg.2 (one_div_le_one_div_of_le s0 hss)
    have hQ := Qs_upper hj1
    have e0 := Real.sq_sqrt hj0.le
    have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ j + 1 by linarith)
    -- `j (1/√j − 1/√(j+1)) ≤ √(j+1) − √j`
    have k1 : (j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) ≤ √((j : ℝ) + 1) - √(j : ℝ) := by
      rw [div_sub_div _ _ s0.ne' s1.ne', mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_pos s0 s1]
    -- `√j (1/√j − 1/√(j+1)) = 1 − √j/√(j+1) ≤ log(j+1) − log j` scaled by `1/2`
    have k2 : √(j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) ≤ (Real.log ((j : ℝ) + 1) - Real.log j) / 2 := by
      have hl : Real.log ((j : ℝ) + 1) - Real.log j = 2 * Real.log (√((j : ℝ) + 1) / √(j : ℝ)) := by
        rw [Real.log_div s1.ne' s0.ne', Real.log_sqrt (by linarith), Real.log_sqrt hj0.le]; ring
      rw [hl]
      have := Real.one_sub_inv_le_log_of_pos (show 0 < √((j : ℝ) + 1) / √(j : ℝ) by positivity)
      rw [inv_div] at this
      have e : √(j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) = 1 - √(j : ℝ) / √((j : ℝ) + 1) := by
        field_simp
      rw [e]; linarith
    calc Qs (j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1))
        ≤ (kap * j + 3 * √(j : ℝ)) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hQ hd
      _ = kap * ((j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1))) +
          3 * (√(j : ℝ) * (1 / √(j : ℝ) - 1 / √((j : ℝ) + 1))) := by ring
      _ ≤ _ := by nlinarith [kap_pos]
  have htel1 : ∀ J : ℕ, 1 ≤ J → ∑ j ∈ Ico 1 J, (√((j : ℝ) + 1) - √(j : ℝ)) = √(J : ℝ) - 1 := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base => simp
    | succ J hJ ih => rw [Finset.sum_Ico_succ_top hJ, ih]; push_cast; ring
  have htel2 : ∀ J : ℕ, 1 ≤ J → ∑ j ∈ Ico 1 J, (Real.log ((j : ℝ) + 1) - Real.log j) = Real.log J := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base => simp
    | succ J hJ ih => rw [Finset.sum_Ico_succ_top hJ, ih]; push_cast; ring
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, htel1 J hJ, htel2 J hJ] at hsum
  have hQJ : Qs (J : ℝ) / √(J : ℝ) ≤ kap * √(J : ℝ) + 3 := by
    rw [div_le_iff₀ hsJ]
    have := Qs_upper hJr
    have e := Real.mul_self_sqrt (show (0 : ℝ) ≤ J by linarith)
    have : (kap * √(J : ℝ) + 3) * √(J : ℝ) = kap * J + 3 * √(J : ℝ) := by rw [add_mul, mul_assoc, e]
    linarith
  nlinarith [kap_pos]

end TernaryGoldbach.Prelim.Sqf
