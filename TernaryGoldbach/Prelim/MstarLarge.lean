import TernaryGoldbach.Prelim.MstarReduce
import TernaryGoldbach.Prelim.LiouvilleBound
import TernaryGoldbach.Prelim.RamareMoebius
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `S(y) log y ≤ 0.8` for `y ≥ e¹⁰`

`S(y) = ∑_{w ≤ √y} |m(y/w²)|/w²` (`MstarReduce.lean`). With `z = y/w²`, each term is bounded by
* Ramaré's `|m(z)| ≤ 0.03/log z` for `z ≥ 11815` (`RamareMoebius`): when `w⁴ ≤ y`, `log z ≥ ½ log y`,
  so the term is at most `0.06/(w² log y)`, and these add up to at most `0.12/log y`; when `w⁴ > y`,
  `log z ≥ 9`, so the term is at most `1/(300 w²)`, and these add up to at most
  `(2/300)/(W + 1)` with `W = ⌊y^{1/4}⌋`, while `log y < 4(W + 1)`;
* the kernel-checked `|m(z)| ≤ √(2/z)` for `z < 11815` (`SmallMoebius.lean`): the term is at most
  `√2/(w √y)`, and these add up to at most `√2 (1 + log √y)/√y`.
With `t = log √y ≥ 5`, the total is at most `0.12 + 8/300 + 2√2 t(1 + t) e^{−t}`, and
`t(1 + t) ≤ 30 e^{t−5}` for `t ≥ 5`, so it is at most `0.12 + 0.027 + 0.574 < 0.8`.
-/

open Finset

namespace TernaryGoldbach.Prelim

theorem log_11815_ge : (9 : ℝ) ≤ Real.log 11815 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 := by gcongr
    _ ≤ 11815 := by norm_num

theorem exp_5_ge : (148 : ℝ) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (148 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := by gcongr

/-- `t(1 + t) e^{−t} ≤ 30 e^{−5}` for `t ≥ 5`. -/
theorem mul_succ_div_exp_le {t : ℝ} (ht : 5 ≤ t) :
    t * (1 + t) / Real.exp t ≤ 30 / Real.exp 5 := by
  set s := t - 5
  have hs : 0 ≤ s := by simp only [s]; linarith
  have hexp : Real.exp t = Real.exp 5 * Real.exp s := by
    rw [← Real.exp_add]; congr 1; simp only [s]; ring
  have hq := Real.quadratic_le_exp_of_nonneg hs
  have he5 : 0 < Real.exp 5 := Real.exp_pos 5
  have hes : 0 < Real.exp s := Real.exp_pos s
  rw [hexp, div_le_div_iff₀ (by positivity) he5]
  have ht' : t = s + 5 := by simp only [s]; ring
  rw [ht']
  have : (s + 5) * (1 + (s + 5)) ≤ 30 * Real.exp s := by nlinarith
  nlinarith

/-- **`S(y) log y ≤ 0.8` for `y ≥ e¹⁰`**, from Ramaré's bound and the kernel-checked `√(2/z)`. -/
theorem Sm_mul_log_le_large [Fact RamareMoebius] {y : ℝ} (hy : Real.exp 10 ≤ y) :
    Sm y * Real.log y ≤ 0.8 := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 10) hy
  have hly : 10 ≤ Real.log y := by rw [Real.le_log_iff_exp_le hy0]; exact hy
  have hly0 : 0 < Real.log y := by linarith
  set n := Nat.sqrt ⌊y⌋₊ with hn
  set u := √y with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hy0
  have hlu : Real.log u = Real.log y / 2 := Real.log_sqrt hy0.le
  -- the three pieces
  set P : ℕ → ℝ := fun w => if (w : ℝ) ^ 4 ≤ y then 0.06 / ((w * w : ℕ) * Real.log y) else 0
  set Q : ℕ → ℝ := fun w => if y < (w : ℝ) ^ 4 then 1 / 300 / (w * w : ℕ) else 0
  set R : ℕ → ℝ := fun w => √2 / (w * u)
  have hterm : ∀ w ∈ Icc 1 n,
      |msumR (y / (w * w : ℕ))| / (w * w : ℕ) ≤ P w + Q w + R w := by
    intro w hw
    have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
    have hwn : w ≤ n := (mem_Icc.1 hw).2
    have hwr : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    have hww : (0 : ℝ) < (w * w : ℕ) := by exact_mod_cast Nat.mul_pos hw1 hw1
    have hwwc : ((w * w : ℕ) : ℝ) = (w : ℝ) ^ 2 := by push_cast; ring
    have hwwy : ((w * w : ℕ) : ℝ) ≤ y := by
      have h1 : w * w ≤ ⌊y⌋₊ := Nat.le_sqrt.1 hwn
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le hy0.le)
    set z := y / (w * w : ℕ) with hz
    have hz1 : 1 ≤ z := by rw [hz, le_div_iff₀ hww, one_mul]; exact hwwy
    have hP0 : 0 ≤ P w := by simp only [P]; split_ifs <;> positivity
    have hQ0 : 0 ≤ Q w := by simp only [Q]; split_ifs <;> positivity
    have hR0 : 0 ≤ R w := by simp only [R]; positivity
    rcases le_or_gt 11815 z with hzL | hzS
    · -- Ramaré's bound
      have hm : |msumR z| ≤ 0.03 / Real.log z := ramare_moebius hzL
      have hlz9 : 9 ≤ Real.log z := log_11815_ge.trans (Real.log_le_log (by norm_num) hzL)
      by_cases h4 : (w : ℝ) ^ 4 ≤ y
      · -- `log z ≥ ½ log y`
        have hlz : Real.log y / 2 ≤ Real.log z := by
          have hzu : u ≤ z := by
            rw [hz, le_div_iff₀ hww, hwwc]
            have h2 : (w : ℝ) ^ 2 ≤ u := Real.le_sqrt_of_sq_le (by nlinarith)
            have : u * u = y := Real.mul_self_sqrt hy0.le
            nlinarith
          rw [← hlu]; exact Real.log_le_log hu0 hzu
        have hb : |msumR z| ≤ 0.06 / Real.log y := by
          refine hm.trans ?_
          rw [div_le_div_iff₀ (by linarith) hly0]
          linarith
        have hPw : P w = 0.06 / ((w * w : ℕ) * Real.log y) := by simp only [P, h4, ↓reduceIte]
        calc |msumR z| / (w * w : ℕ) ≤ 0.06 / Real.log y / (w * w : ℕ) :=
              div_le_div_of_nonneg_right hb hww.le
          _ = P w := by rw [hPw, div_div, mul_comm]
          _ ≤ P w + Q w + R w := by linarith
      · -- `log z ≥ 9`
        push Not at h4
        have hb : |msumR z| ≤ 1 / 300 := by
          refine hm.trans ?_
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
        have hQw : Q w = 1 / 300 / (w * w : ℕ) := by simp only [Q, h4, ↓reduceIte]
        calc |msumR z| / (w * w : ℕ) ≤ 1 / 300 / (w * w : ℕ) :=
              div_le_div_of_nonneg_right hb hww.le
          _ = Q w := hQw.symm
          _ ≤ P w + Q w + R w := by linarith
    · -- the kernel's `√(2/z)`
      have hm : |msumR z| ≤ √(2 / z) := abs_sum_moebius_div_le_sqrt (by linarith) hzS
      have hsq : √(2 / z) / (w * w : ℕ) = R w := by
        simp only [R, hz]
        rw [div_div_eq_mul_div, Real.sqrt_div' _ hy0.le, ← hu, hwwc]
        have hw0 : (0 : ℝ) < w := by linarith
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hw0.le]
        field_simp
      calc |msumR z| / (w * w : ℕ) ≤ √(2 / z) / (w * w : ℕ) :=
            div_le_div_of_nonneg_right hm hww.le
        _ = R w := hsq
        _ ≤ P w + Q w + R w := by linarith
  have hS : Sm y ≤ ∑ w ∈ Icc 1 n, P w + ∑ w ∈ Icc 1 n, Q w + ∑ w ∈ Icc 1 n, R w := by
    rw [← sum_add_distrib, ← sum_add_distrib, Sm]
    exact sum_le_sum hterm
  -- `∑ 1/w² ≤ 2` and its tail
  have hIcc : ∀ m : ℕ, Icc 1 m = Ioo 0 (m + 1) := fun m => by ext; simp; omega
  have hinv : ∀ w : ℕ, ((w * w : ℕ) : ℝ)⁻¹ = ((w : ℝ) ^ 2)⁻¹ := fun w => by push_cast; ring_nf
  have hPs : (∑ w ∈ Icc 1 n, P w) * Real.log y ≤ 0.12 := by
    have h1 : ∀ w ∈ Icc 1 n, P w ≤ 0.06 / Real.log y * ((w : ℝ) ^ 2)⁻¹ := by
      intro w hw
      have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
      have hww : ((w * w : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hw1 hw1).ne'
      simp only [P]
      split_ifs
      · rw [← hinv]; apply le_of_eq; field_simp
      · positivity
    have h2 : ∑ w ∈ Icc 1 n, ((w : ℝ) ^ 2)⁻¹ ≤ 2 := by
      rw [hIcc]
      have := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
      norm_num at this
      exact this
    calc (∑ w ∈ Icc 1 n, P w) * Real.log y
        ≤ (0.06 / Real.log y * ∑ w ∈ Icc 1 n, ((w : ℝ) ^ 2)⁻¹) * Real.log y := by
          rw [mul_sum]; gcongr with w hw; exact h1 w hw
      _ ≤ (0.06 / Real.log y * 2) * Real.log y := by gcongr
      _ = 0.12 := by field_simp; norm_num
  have hQs : (∑ w ∈ Icc 1 n, Q w) * Real.log y ≤ 8 / 300 := by
    set W := Nat.sqrt n with hW
    -- `y < (W + 1)⁴`
    have hyW : y < ((W + 1 : ℕ) : ℝ) ^ 4 := by
      have h1 : n < (W + 1) * (W + 1) := Nat.lt_succ_sqrt n
      have h2 : ⌊y⌋₊ < (n + 1) * (n + 1) := Nat.lt_succ_sqrt _
      have h3 : ⌊y⌋₊ + 1 ≤ ((W + 1) * (W + 1)) * ((W + 1) * (W + 1)) := by
        have : n + 1 ≤ (W + 1) * (W + 1) := h1
        nlinarith
      have h4 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
      have h5 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ (((W + 1) * (W + 1)) * ((W + 1) * (W + 1)) : ℕ) := by
        exact_mod_cast h3
      push_cast at h5 ⊢
      nlinarith
    have hW1 : (0 : ℝ) < ((W + 1 : ℕ) : ℝ) := by positivity
    have hlogW : Real.log y < 4 * ((W + 1 : ℕ) : ℝ) := by
      have h1 : Real.log y < Real.log (((W + 1 : ℕ) : ℝ) ^ 4) := Real.log_lt_log hy0 hyW
      rw [Real.log_pow] at h1
      have h2 := Real.log_le_sub_one_of_pos hW1
      push_cast at h1 h2 ⊢
      linarith
    -- the terms with `y < w⁴` have `w > W`
    have h1 : ∑ w ∈ Icc 1 n, Q w ≤ 1 / 300 * ∑ w ∈ Ioo W (n + 1), ((w : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      have hsub : ∀ w ∈ Icc 1 n, Q w ≤ if w ∈ Ioo W (n + 1) then 1 / 300 * ((w : ℝ) ^ 2)⁻¹ else 0 := by
        intro w hw
        simp only [Q]
        split_ifs with h4 hmem
        · rw [← hinv]; ring_nf; exact le_rfl
        · exfalso
          apply hmem
          have hwn : w ≤ n := (mem_Icc.1 hw).2
          refine mem_Ioo.2 ⟨?_, by omega⟩
          by_contra hle
          push Not at hle
          have hwW : w * w ≤ n := Nat.le_sqrt.1 hle
          have hn' : n * n ≤ ⌊y⌋₊ := Nat.sqrt_le' _ |>.trans_eq' (by ring)
          have : (w * w) * (w * w) ≤ ⌊y⌋₊ := le_trans (Nat.mul_le_mul hwW hwW) hn'
          have h5 : (((w * w) * (w * w) : ℕ) : ℝ) ≤ y :=
            le_trans (by exact_mod_cast this) (Nat.floor_le hy0.le)
          push_cast at h5
          nlinarith
        · positivity
        · exact le_rfl
      refine (sum_le_sum hsub).trans ?_
      rw [← sum_filter]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro w hw
      exact (mem_filter.1 hw).2
    have h2 : ∑ w ∈ Ioo W (n + 1), ((w : ℝ) ^ 2)⁻¹ ≤ 2 / ((W + 1 : ℕ) : ℝ) := by
      have := sum_Ioo_inv_sq_le (α := ℝ) W (n + 1)
      push_cast at this ⊢
      exact this
    have hQ0 : 0 ≤ ∑ w ∈ Icc 1 n, Q w :=
      sum_nonneg fun w _ => by simp only [Q]; split_ifs <;> positivity
    calc (∑ w ∈ Icc 1 n, Q w) * Real.log y
        ≤ (1 / 300 * (2 / ((W + 1 : ℕ) : ℝ))) * (4 * ((W + 1 : ℕ) : ℝ)) := by
          refine mul_le_mul (h1.trans (by gcongr)) hlogW.le hly0.le (by positivity)
      _ = 8 / 300 := by field_simp; norm_num
  have hRs : (∑ w ∈ Icc 1 n, R w) * Real.log y ≤ 0.58 := by
    have hn1 : 1 ≤ n := by
      rw [hn, Nat.le_sqrt, one_mul]
      have : (1 : ℝ) ≤ y := by
        have := Real.add_one_le_exp 10
        linarith
      exact Nat.le_floor (by exact_mod_cast this)
    have hnu : (n : ℝ) ≤ u := by
      rw [hu]
      apply Real.le_sqrt_of_sq_le
      have h1 : n * n ≤ ⌊y⌋₊ := Nat.sqrt_le' _ |>.trans_eq' (by ring)
      have : ((n * n : ℕ) : ℝ) ≤ y := le_trans (by exact_mod_cast h1) (Nat.floor_le hy0.le)
      push_cast at this
      nlinarith
    have hsumR : ∑ w ∈ Icc 1 n, R w = √2 / u * ∑ w ∈ Icc 1 n, (w : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun w _ => ?_
      simp only [R]
      field_simp
    have hharm : ∑ w ∈ Icc 1 n, (w : ℝ)⁻¹ ≤ 1 + Real.log u := by
      have h := harmonic_le_one_add_log n
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      have : Real.log n ≤ Real.log u := Real.log_le_log (by exact_mod_cast hn1) hnu
      linarith
    set t := Real.log u with ht
    have ht5 : 5 ≤ t := by rw [hlu]; linarith
    have hut : u = Real.exp t := (Real.exp_log hu0).symm
    have hly2 : Real.log y = 2 * t := by rw [hlu]; ring
    have hsqrt2 : √2 ≤ 1.4143 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hkey := mul_succ_div_exp_le ht5
    have he5 := exp_5_ge
    rw [hsumR, hly2]
    calc (√2 / u * ∑ w ∈ Icc 1 n, (w : ℝ)⁻¹) * (2 * t)
        ≤ (√2 / u * (1 + t)) * (2 * t) := by gcongr
      _ = 2 * √2 * (t * (1 + t) / Real.exp t) := by rw [hut]; field_simp
      _ ≤ 2 * 1.4143 * (30 / Real.exp 5) := by gcongr
      _ ≤ 2 * 1.4143 * (30 / 148) := by gcongr
      _ ≤ 0.58 := by norm_num
  calc Sm y * Real.log y
      ≤ (∑ w ∈ Icc 1 n, P w + ∑ w ∈ Icc 1 n, Q w + ∑ w ∈ Icc 1 n, R w) * Real.log y :=
        mul_le_mul_of_nonneg_right hS hly0.le
    _ = (∑ w ∈ Icc 1 n, P w) * Real.log y + (∑ w ∈ Icc 1 n, Q w) * Real.log y +
        (∑ w ∈ Icc 1 n, R w) * Real.log y := by ring
    _ ≤ 0.12 + 8 / 300 + 0.58 := by linarith
    _ ≤ 0.8 := by norm_num

end TernaryGoldbach.Prelim
