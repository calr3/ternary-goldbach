/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.TailAux
import RSBounds.Moebius003.JSum
import RSBounds.Moebius003.Schoenfeld
import RSBounds.Moebius003.ElMarraki
import RSBounds.Moebius003.Cells

/-!
# §5 of the note: beyond `D_end`

Proposition 10 (`|N(D)| ≤ ν_∞ D` for `D ≥ D_end`, with `ν_∞ = 0.014`, `ν̄ = 0.017`, `θ = 3/20`)
and Corollary 11 (`|m(n)| log(n + 1) ≤ 0.03` for `n ≥ D_end`).

Lemma 1 is applied with `y = Y = ⌊D^θ⌋`, so `l = log Y ∈ (θL − 10⁻⁹, θL]`. Every term of the bound
`Φ` is then bounded by its value at `L = 160` through elementary monotonicity, and the resulting
numerical inequality is checked by `norm_num`, with `log(20/17)` and `log(1/(θ − 10⁻⁹/160))`
bounded through `LogCert`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

/-! ### Numerical facts -/

theorem log_Dend_ge : (160 : ℝ) ≤ Real.log Dend := by
  have h2 : (160 : ℚ) ≤ LogCert.logLo Dend := by unfold Dend; decide +kernel
  calc (160 : ℝ) = ((160 : ℚ) : ℝ) := by norm_num
    _ ≤ ((LogCert.logLo Dend : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ ≤ Real.log ((Dend : ℚ) : ℝ) := LogCert.logLo_le (by unfold Dend; norm_num)
    _ = Real.log Dend := by norm_num

theorem log_Dmid_le : Real.log Dmid ≤ (135.8 : ℝ) := by
  have h2 : LogCert.logHi Dmid ≤ (135.8 : ℚ) := by unfold Dmid; decide +kernel
  calc Real.log Dmid = Real.log ((Dmid : ℚ) : ℝ) := by norm_num
    _ ≤ ((LogCert.logHi Dmid : ℚ) : ℝ) := LogCert.le_logHi (by unfold Dmid; norm_num)
    _ ≤ ((135.8 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ = 135.8 := by norm_num

theorem log_20_17_le : Real.log (20 / 17) ≤ (0.162519 : ℝ) := by
  have h2 : LogCert.logHi (20 / 17) ≤ (0.162519 : ℚ) := by decide +kernel
  calc Real.log (20 / 17) = Real.log (((20 / 17 : ℚ)) : ℝ) := by norm_num
    _ ≤ ((LogCert.logHi (20 / 17) : ℚ) : ℝ) := LogCert.le_logHi (by norm_num)
    _ ≤ ((0.162519 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ = 0.162519 := by norm_num

/-- `r₀ = 1/(θ − 10⁻⁹/160)`. -/
def r0 : ℚ := 1 / (3 / 20 - 1 / (160 * 10 ^ 9))

theorem log_r0_le : Real.log (r0 : ℝ) ≤ (1.89712 : ℝ) := by
  have h2 : LogCert.logHi r0 ≤ (1.89712 : ℚ) := by unfold r0; decide +kernel
  calc Real.log (r0 : ℝ) ≤ ((LogCert.logHi r0 : ℚ) : ℝ) := LogCert.le_logHi (by unfold r0; norm_num)
    _ ≤ ((1.89712 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ = 1.89712 := by norm_num

theorem exp2_le_Dmid : Real.exp 2 ≤ (Dmid : ℝ) := by
  have : Real.exp 2 ≤ 2.7182818286 ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  have h2 : (2.7182818286 : ℝ) ^ 2 ≤ Dmid := by unfold Dmid; norm_num
  linarith

theorem X0_le_Dmid : X0 ≤ Dmid := by unfold X0 Dmid; norm_num

theorem Dmid_le_Dend : Dmid ≤ Dend := by unfold Dmid Dend; norm_num

/-! ### The numerical inequality of Proposition 10 -/

theorem tail_numeric {L l ε : ℝ} (hL : 160 ≤ L) (hl1 : 3 / 20 * L - 1 / 10 ^ 9 ≤ l)
    (hl2 : l ≤ 3 / 20 * L) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10 ^ 8) :
    2 * 0.014 * (Real.log L - Real.log (L - l)) + 2 * (0.017 * lam0) * (1 / (L - l) - 1 / L) +
      C5 * (0.014 / (l * (L - l)) + 0.017 * lam0 / (l * (L - l) ^ 2)) +
      C5 * (κ * (Real.log (L / l) + 2 / l ^ 2) + (eHi - eLo) / l + eLo / L) +
      0.017 * lam0 / L ^ 2 + ε ≤ 0.014 * (1 - 1 / L) := by
  have hL0 : 0 < L := by linarith
  have hl0 : (24 : ℝ) - 1 / 10 ^ 9 ≤ l := by linarith
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl0
  have ha : 17 / 20 * L ≤ L - l := by linarith
  have ha136 : (136 : ℝ) ≤ L - l := by linarith
  have hapos : 0 < L - l := by linarith
  -- each term
  have t1 : Real.log L - Real.log (L - l) ≤ 0.162519 := by
    rw [← Real.log_div hL0.ne' hapos.ne']
    refine le_trans (Real.log_le_log (div_pos hL0 hapos) ?_) log_20_17_le
    rw [div_le_div_iff₀ hapos (by norm_num)]; linarith
  have t2 : 1 / (L - l) - 1 / L ≤ (3 / 17) / 160 := by
    have h1 : 1 / (L - l) ≤ 1 / (17 / 20 * L) := one_div_le_one_div_of_le (by positivity) ha
    have e : 1 / (17 / 20 * L) - 1 / L = (3 / 17) / L := by field_simp; ring
    have h2 : (3 / 17) / L ≤ (3 / 17) / 160 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    linarith
  have t3 : 1 / (l * (L - l)) ≤ 1 / ((24 - 1 / 10 ^ 9) * 136) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul hl0 ha136 (by norm_num) hlpos.le)
  have t4 : 1 / (l * (L - l) ^ 2) ≤ 1 / ((24 - 1 / 10 ^ 9) * 136 ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul hl0 (pow_le_pow_left₀ (by norm_num) ha136 2) (by norm_num) hlpos.le)
  have t5 : Real.log (L / l) ≤ 1.89712 := by
    refine le_trans (Real.log_le_log (div_pos hL0 hlpos) ?_) log_r0_le
    have : L * (3 / 20 - 1 / (160 * 10 ^ 9)) ≤ l := by nlinarith
    rw [div_le_iff₀ hlpos]
    unfold r0; push_cast
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by norm_num)]
    linarith
  have t5' : 0 ≤ Real.log (L / l) := Real.log_nonneg (by rw [le_div_iff₀ hlpos]; linarith)
  have t6 : 2 / l ^ 2 ≤ 2 / (24 - 1 / 10 ^ 9) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hl0 2)
  have t7 : (eHi - eLo) / l ≤ 0.21 / (24 - 1 / 10 ^ 9) := by
    rw [show eHi - eLo = 0.21 by norm_num [eHi, eLo]]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl0
  have t8 : eLo / L ≤ 0.96 / 160 := by
    rw [show eLo = 0.96 by norm_num [eLo]]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have t9 : 0.017 * 1.107 / L ^ 2 ≤ 0.017 * 1.107 / 160 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
  have t10 : 0.014 * (1 - 1 / 160) ≤ 0.014 * (1 - 1 / L) := by
    have : 1 / L ≤ 1 / 160 := one_div_le_one_div_of_le (by norm_num) hL
    linarith
  have hκ := κ_hi
  have hκ0 := κ_pos
  have hC5 : C5 = 0.0077629 := rfl
  have hlam : lam0 = 1.107 := rfl
  -- assemble
  have e1 : 0.014 / (l * (L - l)) = 0.014 * (1 / (l * (L - l))) := by ring
  have e2 : 0.017 * lam0 / (l * (L - l) ^ 2) = 0.017 * lam0 * (1 / (l * (L - l) ^ 2)) := by ring
  rw [e1, e2]
  have hk : κ * (Real.log (L / l) + 2 / l ^ 2) ≤ 0.6079274 * (1.89712 + 2 / (24 - 1 / 10 ^ 9) ^ 2) :=
    mul_le_mul hκ (add_le_add t5 t6) (by positivity) (by norm_num)
  rw [hC5, hlam]
  have hB : (0.0077629 : ℝ) * (0.014 * (1 / (l * (L - l))) + 0.017 * 1.107 * (1 / (l * (L - l) ^ 2))) ≤
      0.0077629 * (0.014 * (1 / ((24 - 1 / 10 ^ 9) * 136)) + 0.017 * 1.107 * (1 / ((24 - 1 / 10 ^ 9) * 136 ^ 2))) := by
    gcongr
  have hJ : (0.0077629 : ℝ) * (κ * (Real.log (L / l) + 2 / l ^ 2) + (eHi - eLo) / l + eLo / L) ≤
      0.0077629 * (0.6079274 * (1.89712 + 2 / (24 - 1 / 10 ^ 9) ^ 2) + 0.21 / (24 - 1 / 10 ^ 9) + 0.96 / 160) := by
    gcongr
  have hA : 2 * 0.014 * (Real.log L - Real.log (L - l)) + 2 * (0.017 * 1.107) * (1 / (L - l) - 1 / L) ≤
      2 * 0.014 * 0.162519 + 2 * (0.017 * 1.107) * ((3 / 17) / 160) := by
    gcongr
  have hnum : 2 * 0.014 * 0.162519 + 2 * (0.017 * 1.107) * ((3 / 17) / 160) +
      0.0077629 * (0.014 * (1 / ((24 - 1 / 10 ^ 9) * 136)) + 0.017 * 1.107 * (1 / ((24 - 1 / 10 ^ 9) * 136 ^ 2))) +
      0.0077629 * (0.6079274 * (1.89712 + 2 / (24 - 1 / 10 ^ 9) ^ 2) + 0.21 / (24 - 1 / 10 ^ 9) + 0.96 / 160) +
      0.017 * 1.107 / 160 ^ 2 + 1 / 10 ^ 8 ≤ (0.014 : ℝ) * (1 - 1 / 160) := by norm_num
  linarith [hA, hB, hJ, t9, hε, hnum, t10]

/-! ### The three sums of Lemma 1 beyond `D_end` -/

theorem klog_mono {D : ℝ} {k : ℕ} (hk : 1 ≤ k) (hD : 0 < D)
    (hB : 4 ≤ Real.log (D / ((k : ℝ) + 1))) :
    (k : ℝ) * Real.log (D / k) ≤ ((k : ℝ) + 1) * Real.log (D / ((k : ℝ) + 1)) ∧
      (k : ℝ) * Real.log (D / k) ^ 2 ≤ ((k : ℝ) + 1) * Real.log (D / ((k : ℝ) + 1)) ^ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set B := Real.log (D / k)
  set B' := Real.log (D / ((k : ℝ) + 1))
  have hδ : B - B' = Real.log ((k : ℝ) + 1) - Real.log k := by
    simp only [B, B']
    rw [Real.log_div hD.ne' (by linarith), Real.log_div hD.ne' (by linarith)]; ring
  have hδ1 : B - B' ≤ 1 / k := by rw [hδ]; exact log_succ_sub_le hk
  have hδ0 : 0 ≤ B - B' := by rw [hδ]; exact sub_nonneg.2 (Real.log_le_log (by linarith) (by linarith))
  have hkδ : (k : ℝ) * (B - B') ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hδ1 (by linarith : (0 : ℝ) ≤ k)
    rwa [mul_one_div_cancel (by linarith)] at this
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ B')]

theorem ksum_tail (h : Inputs) {D Y : ℕ} (hY2 : 2 ≤ Y) (hYD : (Y : ℝ) < D)
    (hDY : Dmid ≤ D / Y) (hN0 : ∀ t : ℕ, X0 ≤ t → t < D → |N t| ≤ 0.017 * t)
    (hN1 : ∀ t : ℕ, Dmid ≤ t → t < D → |N t| ≤ 0.014 * t) (hB : 4 ≤ Real.log ((D : ℝ) / Y)) :
    ∑ k ∈ Icc 2 Y, |Λ k - 1| * |M (D / k)| ≤ 2 * C0B * Y +
      D * (2 * 0.014 * (Real.log (Real.log D) - Real.log (Real.log ((D : ℝ) / Y))) +
        2 * (0.017 * lam0) * (1 / Real.log ((D : ℝ) / Y) - 1 / Real.log D)) := by
  have hDpos : (0 : ℝ) < D := lt_trans (by positivity) hYD
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  set g1 : ℕ → ℝ := fun k => 1 / (k * Real.log ((D : ℝ) / k)) with hg1
  set g2 : ℕ → ℝ := fun k => 1 / (k * Real.log ((D : ℝ) / k) ^ 2) with hg2
  have hlogk : ∀ k : ℕ, 1 ≤ k → k ≤ Y → 4 ≤ Real.log ((D : ℝ) / k) := by
    intro k hk1 hk2
    refine hB.trans (Real.log_le_log (by positivity) ?_)
    exact div_le_div_of_nonneg_left hDpos.le (by exact_mod_cast hk1) (by exact_mod_cast hk2)
  have hpt : ∀ k ∈ Icc 2 Y, |Λ k - 1| * |M (D / k)| ≤
      |Λ k - 1| * C0B + 0.014 * D * (|Λ k - 1| * g1 k) + 0.017 * lam0 * D * (|Λ k - 1| * g2 k) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    set u := D / k with hu
    have hu1 : Dmid ≤ u := le_trans hDY (Nat.div_le_div_left hk2 (by omega))
    have hu2 : u < D := Nat.div_lt_self (by exact_mod_cast hDpos) (by omega)
    have hX : X0 ≤ u := le_trans X0_le_Dmid hu1
    have hM := M_tail h hN0 hX hu2.le
    have hNu := hN1 u hu1 hu2
    have hupos : (0 : ℝ) < u := by exact_mod_cast (by unfold X0 at hX; omega : 0 < u)
    have hue2 : Real.exp 2 ≤ (u : ℝ) := exp2_le_Dmid.trans (by exact_mod_cast hu1)
    have hue1 : Real.exp 1 ≤ (u : ℝ) := le_trans (Real.exp_le_exp.2 (by norm_num)) hue2
    have hlogu : 0 < Real.log (u : ℝ) := lt_of_lt_of_le one_pos (one_le_log_of hue1)
    have hur : (u : ℝ) ≤ D / k := by rw [hu]; exact Nat.cast_div_le
    have h1 : |N u| / Real.log u ≤ 0.014 * (u / Real.log u) := by
      rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hNu hlogu.le
    have h2 := div_log_mono hue1 hur
    have h3 := div_log_sq_mono hue2 hur
    have e1 : ((D : ℝ) / k) / Real.log (D / k) = D * g1 k := by simp only [hg1]; field_simp
    have e2 : ((D : ℝ) / k) / Real.log (D / k) ^ 2 = D * g2 k := by simp only [hg2]; field_simp
    have hMu : |M u| ≤ C0B + 0.014 * D * g1 k + 0.017 * lam0 * D * g2 k := by
      have hl : (0 : ℝ) ≤ 0.017 * lam0 := by unfold lam0; norm_num
      have : 0.017 * lam0 * u / Real.log u ^ 2 ≤ 0.017 * lam0 * (D * g2 k) := by
        rw [mul_div_assoc, ← e2]; exact mul_le_mul_of_nonneg_left h3 hl
      have : 0.014 * (u / Real.log u) ≤ 0.014 * (D * g1 k) := by
        rw [← e1]; exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      nlinarith
    have ha0 : 0 ≤ |Λ k - 1| := abs_nonneg _
    calc |Λ k - 1| * |M u| ≤ |Λ k - 1| * (C0B + 0.014 * D * g1 k + 0.017 * lam0 * D * g2 k) :=
          mul_le_mul_of_nonneg_left hMu ha0
      _ = _ := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, ← mul_sum]
  have hA := A_le h (n := Y) (by omega)
  have hAY : ∑ k ∈ Icc 2 Y, |Λ k - 1| = A Y := rfl
  have hw1 := sum_weight_le h (K := Y) g1 (fun k hk1 hk2 => by
      simp only [hg1]
      have := (klog_mono (D := D) (k := k) (by omega) hDpos (by
        have := hlogk (k + 1) (by omega) (by omega); push_cast at this; exact this)).1
      apply one_div_le_one_div_of_le _ (by push_cast; exact this)
      have := hlogk k (by omega) hk2.le
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      positivity)
    (by simp only [hg1]; have := hlogk Y (by omega) le_rfl; positivity)
  have hw2 := sum_weight_le h (K := Y) g2 (fun k hk1 hk2 => by
      simp only [hg2]
      have := (klog_mono (D := D) (k := k) (by omega) hDpos (by
        have := hlogk (k + 1) (by omega) (by omega); push_cast at this; exact this)).2
      apply one_div_le_one_div_of_le _ (by push_cast; exact this)
      have := hlogk k (by omega) hk2.le
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      positivity)
    (by simp only [hg2]; have := hlogk Y (by omega) le_rfl; positivity)
  have hs1 := sum_inv_klog_le (D := D) hY2 hYD hB
  have hs2 := sum_inv_klog_sq_le (D := D) hY2 hYD hB
  have hC0 : (0 : ℝ) ≤ C0B := by unfold C0B; norm_num
  have hl : (0 : ℝ) ≤ 0.017 * lam0 := by unfold lam0; norm_num
  have t1 : (∑ k ∈ Icc 2 Y, |Λ k - 1|) * C0B ≤ 2 * C0B * Y := by
    rw [hAY]; nlinarith
  have t2 : 0.014 * D * ∑ k ∈ Icc 2 Y, |Λ k - 1| * g1 k ≤
      D * (2 * 0.014 * (Real.log (Real.log D) - Real.log (Real.log ((D : ℝ) / Y)))) := by
    have := mul_le_mul_of_nonneg_left (hw1.trans (mul_le_mul_of_nonneg_left hs1 (by norm_num)))
      (by positivity : (0 : ℝ) ≤ 0.014 * D)
    linarith
  have t3 : 0.017 * lam0 * D * ∑ k ∈ Icc 2 Y, |Λ k - 1| * g2 k ≤
      D * (2 * (0.017 * lam0) * (1 / Real.log ((D : ℝ) / Y) - 1 / Real.log D)) := by
    have := mul_le_mul_of_nonneg_left (hw2.trans (mul_le_mul_of_nonneg_left hs2 (by norm_num)))
      (by positivity : (0 : ℝ) ≤ 0.017 * lam0 * D)
    linarith
  rw [mul_add]
  linarith

theorem bdry_tail (h : Inputs) {D Y : ℕ} (hYe : Real.exp 22 ≤ Y) (hYD : (Y : ℝ) < D)
    (hDY : Dmid ≤ D / Y) (hN0 : ∀ t : ℕ, X0 ≤ t → t < D → |N t| ≤ 0.017 * t)
    (hN1 : ∀ t : ℕ, Dmid ≤ t → t < D → |N t| ≤ 0.014 * t) :
    |ρ Y| * |M (D / Y)| ≤ C5 * Y / Real.log Y *
      (C0B + 0.014 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y)) +
        0.017 * lam0 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y) ^ 2)) := by
  have hρ := rho_S_nat h hYe
  have hDpos : (0 : ℝ) < D := lt_trans (lt_of_lt_of_le (Real.exp_pos 22) hYe) hYD
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos 22) hYe
  set u := D / Y with hu
  have hu2 : u < D := Nat.div_lt_self (by exact_mod_cast hDpos) (by
    have : (1 : ℝ) < Y := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (by norm_num)) hYe
    exact_mod_cast this)
  have hX : X0 ≤ u := le_trans X0_le_Dmid hDY
  have hM := M_tail h hN0 hX hu2.le
  have hNu := hN1 u hDY hu2
  have hupos : (0 : ℝ) < u := by exact_mod_cast (by unfold X0 at hX; omega : 0 < u)
  have hue2 : Real.exp 2 ≤ (u : ℝ) := exp2_le_Dmid.trans (by exact_mod_cast hDY)
  have hue1 : Real.exp 1 ≤ (u : ℝ) := le_trans (Real.exp_le_exp.2 (by norm_num)) hue2
  have hlogu : 0 < Real.log (u : ℝ) := lt_of_lt_of_le one_pos (one_le_log_of hue1)
  have hur : (u : ℝ) ≤ D / Y := by rw [hu]; exact Nat.cast_div_le
  have h1 : |N u| / Real.log u ≤ 0.014 * (u / Real.log u) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hNu hlogu.le
  have h2 := div_log_mono hue1 hur
  have h3 := div_log_sq_mono hue2 hur
  have hl : (0 : ℝ) ≤ 0.017 * lam0 := by unfold lam0; norm_num
  have hMu : |M u| ≤ C0B + 0.014 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y)) +
      0.017 * lam0 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y) ^ 2) := by
    have : 0.017 * lam0 * u / Real.log u ^ 2 ≤ 0.017 * lam0 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y) ^ 2) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h3 hl
    have : 0.014 * (u / Real.log u) ≤ 0.014 * (((D : ℝ) / Y) / Real.log ((D : ℝ) / Y)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  exact mul_le_mul hρ hMu (abs_nonneg _) (by
    have : 0 < Real.log (Y : ℝ) := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.2 (by norm_num)) hYe)
    unfold C5; positivity)

theorem jsum_tail (h : Inputs) {D Y : ℕ} (hYe : Real.exp 22 ≤ Y) (hYD : (Y : ℝ) < D) :
    |∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j)| ≤
      C5 * D * (κ * (Real.log (Real.log D / Real.log Y) + 2 / Real.log Y ^ 2) +
        (eHi - eLo) / Real.log Y + eLo / Real.log D) +
      (κ * (D / Y) + 2 * Real.sqrt ((D : ℝ) / Y) + 1) := by
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos 22) hYe
  have hDpos : (0 : ℝ) < D := lt_trans hYpos hYD
  have hY1 : (1 : ℝ) < Y := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (by norm_num)) hYe
  have hYn : 0 < Y := by exact_mod_cast hYpos
  have hYDn : Y ≤ D := by exact_mod_cast hYD.le
  set J := D / Y with hJ
  have hJ1 : 1 ≤ J := (Nat.le_div_iff_mul_le hYn).2 (by omega)
  have hJr : (J : ℝ) ≤ D / Y := by rw [hJ]; exact Nat.cast_div_le
  have hpt : ∀ j ∈ Icc 1 J, |(μ j : ℝ) * ρ (D / j)| ≤
      C5 * D * ((μ j : ℝ) ^ 2 / (j * Real.log (D / j))) + (μ j : ℝ) ^ 2 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hv : (Y : ℝ) ≤ (D : ℝ) / j := by
      rw [le_div_iff₀ hjpos]
      have := (Nat.le_div_iff_mul_le hYn).1 hj2
      exact_mod_cast (by linarith [mul_comm j Y] : Y * j ≤ D)
    have hfl : D / j = ⌊(D : ℝ) / j⌋₊ := (Nat.floor_div_eq_div (K := ℝ) D j).symm
    have hρ := rho_S h (hYe.trans hv)
    rw [← hfl] at hρ
    have hlog : 0 < Real.log ((D : ℝ) / j) := Real.log_pos (by linarith)
    rw [abs_mul, abs_moebius_eq_sq]
    have hμ0 : 0 ≤ (μ j : ℝ) ^ 2 := sq_nonneg _
    calc (μ j : ℝ) ^ 2 * |ρ (D / j)| ≤ (μ j : ℝ) ^ 2 * (C5 * (D / j) / Real.log (D / j) + 1) :=
          mul_le_mul_of_nonneg_left hρ hμ0
      _ = C5 * D * ((μ j : ℝ) ^ 2 / (j * Real.log (D / j))) + (μ j : ℝ) ^ 2 := by field_simp
  have hmain : |∑ j ∈ Icc 1 J, (μ j : ℝ) * ρ (D / j)| ≤
      C5 * D * ∑ j ∈ Icc 1 J, (μ j : ℝ) ^ 2 / (j * Real.log (D / j)) + Q J := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans (le_of_eq ?_))
    rw [sum_add_distrib, ← mul_sum]; rfl
  refine hmain.trans ?_
  have hJD : (J : ℝ) < D := lt_of_le_of_lt hJr (by rw [div_lt_iff₀ hYpos]; nlinarith)
  have h5d := sum_sq_div_log_le (J := J) (D := D) (eLo := eLo) (eHi := eHi) hJ1 hJD
    (fun i hi1 _ => Q1_bounds hi1)
  set L := Real.log D
  set l := Real.log (Y : ℝ)
  have hl0 : 0 < l := Real.log_pos hY1
  have hℓ : Real.log (J : ℝ) ≤ L - l := by
    have := Real.log_le_log (by exact_mod_cast hJ1) hJr
    rwa [Real.log_div hDpos.ne' hYpos.ne'] at this
  have hW : l ≤ L - Real.log J := by linarith
  have hWpos : 0 < L - Real.log J := lt_of_lt_of_le hl0 hW
  have hℓ0 : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ1)
  have hL0 : 0 < L := by linarith
  have hκ0 := κ_pos
  have hbound : κ * (Real.log (L / (L - Real.log J)) + 2 / (L - Real.log J) ^ 2) +
      (eHi - eLo) / (L - Real.log J) + eLo / L ≤
      κ * (Real.log (L / l) + 2 / l ^ 2) + (eHi - eLo) / l + eLo / L := by
    have a1 : Real.log (L / (L - Real.log J)) ≤ Real.log (L / l) :=
      Real.log_le_log (div_pos hL0 hWpos) (div_le_div_of_nonneg_left hL0.le hl0 hW)
    have a2 : 2 / (L - Real.log J) ^ 2 ≤ 2 / l ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hl0.le hW 2)
    have a3 : (eHi - eLo) / (L - Real.log J) ≤ (eHi - eLo) / l :=
      div_le_div_of_nonneg_left (by norm_num [eHi, eLo]) hl0 hW
    have := mul_le_mul_of_nonneg_left (add_le_add a1 a2) hκ0.le
    linarith
  have hQ := Q_le J
  have hsJ : Real.sqrt (J : ℝ) ≤ Real.sqrt ((D : ℝ) / Y) := Real.sqrt_le_sqrt hJr
  have hC5 : (0 : ℝ) ≤ C5 * D := by unfold C5; positivity
  have := mul_le_mul_of_nonneg_left (h5d.trans hbound) hC5
  have hκJ : κ * J ≤ κ * (D / Y) := mul_le_mul_of_nonneg_left hJr hκ0.le
  linarith

/-! ### Proposition 10 -/

theorem exp22_ge : (10 ^ 9 : ℝ) ≤ Real.exp 22 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 22 = Real.exp 1 ^ 22 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (10 ^ 9 : ℝ) ≤ 2.7182818283 ^ 22 := by norm_num
    _ ≤ Real.exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) h.le 22

theorem exp136_ge_Dmid : (Dmid : ℝ) ≤ Real.exp 136 := by
  have h1 := log_Dmid_le
  have hD : (0 : ℝ) < Dmid := by unfold Dmid; norm_num
  calc (Dmid : ℝ) = Real.exp (Real.log Dmid) := (Real.exp_log hD).symm
    _ ≤ Real.exp 136 := Real.exp_le_exp.2 (by linarith)

/-- The small terms of Proposition 10. -/
theorem eps_small {D Y : ℝ} {l : ℝ} (hD : (Dend : ℝ) ≤ D) (hY : 10 ^ 9 ≤ Y) (hl : 1 ≤ l)
    (hDY : (Dmid : ℝ) ≤ D / Y) :
    (2 + C0B) / D + 2 * C0B * Y / D + C5 * C0B * Y / (l * D) + κ / Y + 2 * Real.sqrt (D / Y) / D
      ≤ 1 / 10 ^ 8 := by
  have hC0B : C0B = 1743 := rfl
  have hC5 : C5 = 0.0077629 := rfl
  have hDend : (Dend : ℝ) = 306985 * 10 ^ 64 := by unfold Dend; norm_num
  have hDmid : (Dmid : ℝ) = 942467 * 10 ^ 53 := by unfold Dmid; norm_num
  rw [hC0B, hC5]
  rw [hDend] at hD
  rw [hDmid] at hDY
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hD
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by norm_num) hY
  have hYD : Y / D ≤ 1 / (942467 * 10 ^ 53) := by
    rw [div_le_div_iff₀ hDpos (by norm_num), one_mul]
    rw [le_div_iff₀ hYpos] at hDY; linarith
  have h1 : (2 + 1743) / D ≤ (2 + 1743) / (306985 * 10 ^ 64 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD
  have h2 : 2 * 1743 * Y / D = 2 * 1743 * (Y / D) := by ring
  have h3 : 0.0077629 * 1743 * Y / (l * D) ≤ 0.0077629 * 1743 * (Y / D) := by
    rw [show 0.0077629 * 1743 * Y / (l * D) = 0.0077629 * 1743 * (Y / D) / l by
      field_simp]
    exact div_le_self (by positivity) hl
  have h4 : κ / Y ≤ 0.6079274 / 10 ^ 9 := div_le_div₀ (by norm_num) κ_hi (by norm_num) hY
  have h5 : 2 * Real.sqrt (D / Y) / D ≤ 2 / Real.sqrt D := by
    have hsD : Real.sqrt (D / Y) ≤ Real.sqrt D :=
      Real.sqrt_le_sqrt (div_le_self hDpos.le (by linarith))
    have hsDpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
    have hsq : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
    calc 2 * Real.sqrt (D / Y) / D ≤ 2 * Real.sqrt D / D := by gcongr
      _ = 2 / Real.sqrt D := by
          rw [div_eq_div_iff hDpos.ne' hsDpos.ne', mul_assoc, hsq]
  have h6 : (10 ^ 20 : ℝ) ≤ Real.sqrt D := by
    rw [Real.le_sqrt (by norm_num) hDpos.le]; nlinarith
  have h7 : 2 / Real.sqrt D ≤ 2 / 10 ^ 20 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h6
  have h8 : 2 * 1743 * (Y / D) ≤ 2 * 1743 * (1 / (942467 * 10 ^ 53)) :=
    mul_le_mul_of_nonneg_left hYD (by norm_num)
  have h9 : 0.0077629 * 1743 * (Y / D) ≤ 0.0077629 * 1743 * (1 / (942467 * 10 ^ 53)) :=
    mul_le_mul_of_nonneg_left hYD (by norm_num)
  have : (2 + 1743) / (306985 * 10 ^ 64 : ℝ) + 2 * 1743 * (1 / (942467 * 10 ^ 53)) +
      0.0077629 * 1743 * (1 / (942467 * 10 ^ 53)) + 0.6079274 / 10 ^ 9 + 2 / 10 ^ 20 ≤
      (1 / 10 ^ 8 : ℝ) := by norm_num
  linarith

/-- **Proposition 10**: `|N(D)| ≤ 0.014 D` for every `D ≥ D_end`. -/
theorem prop10 (h : Inputs) (hc : CellsResult) : ∀ D : ℕ, Dend ≤ D → |N D| ≤ 0.014 * D := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro hD
  have hN0 : ∀ t : ℕ, X0 ≤ t → t < D → |N t| ≤ 0.017 * t := by
    intro t h1 h2
    by_cases ht : t < Dend
    · exact hc.nuBar t h1 ht
    · have := ih t h2 (by omega)
      have : (0 : ℝ) ≤ t := by positivity
      nlinarith
  have hN1 : ∀ t : ℕ, Dmid ≤ t → t < D → |N t| ≤ 0.014 * t := by
    intro t h1 h2
    by_cases ht : t < Dend
    · exact hc.nuInf t h1 ht
    · exact ih t h2 (by omega)
  have hDe : (Dend : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by unfold Dend; norm_num) hDe
  set L := Real.log D with hLdef
  have hL : 160 ≤ L := log_Dend_ge.trans (Real.log_le_log (by unfold Dend; norm_num) hDe)
  have hDexp : (D : ℝ) = Real.exp L := (Real.exp_log hDpos).symm
  set Y := ⌊(D : ℝ) ^ ((3 : ℝ) / 20)⌋₊ with hYdef
  have hrp : (D : ℝ) ^ ((3 : ℝ) / 20) = Real.exp (3 / 20 * L) := by
    rw [Real.rpow_def_of_pos hDpos, ← hLdef]; congr 1; ring
  have hY1 : (Y : ℝ) ≤ Real.exp (3 / 20 * L) := by
    rw [← hrp]; exact Nat.floor_le (by positivity)
  have hY2 : Real.exp (3 / 20 * L) < Y + 1 := by rw [← hrp]; exact Nat.lt_floor_add_one _
  have he24 : Real.exp 24 ≤ Real.exp (3 / 20 * L) := Real.exp_le_exp.2 (by linarith)
  have he22 : Real.exp 22 + 1 ≤ Real.exp 24 := by
    have : Real.exp 24 = Real.exp 22 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h2 : 3 ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2; linarith
    have : 1 ≤ Real.exp 22 := Real.one_le_exp (by norm_num)
    nlinarith
  have hYe : Real.exp 22 ≤ Y := by linarith
  have hY9 : (10 ^ 9 : ℝ) ≤ Y := exp22_ge.trans hYe
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by norm_num) hY9
  have hYn : 2 ≤ Y := by
    have : (2 : ℝ) ≤ Y := le_trans (by norm_num) hY9
    exact_mod_cast this
  set l := Real.log (Y : ℝ) with hldef
  have hl2 : l ≤ 3 / 20 * L := by
    rw [hldef, show 3 / 20 * L = Real.log (Real.exp (3 / 20 * L)) by rw [Real.log_exp]]
    exact Real.log_le_log hYpos hY1
  have hl1 : 3 / 20 * L - 1 / 10 ^ 9 ≤ l := by
    have h1 : 3 / 20 * L < Real.log ((Y : ℝ) + 1) := by
      rw [show 3 / 20 * L = Real.log (Real.exp (3 / 20 * L)) by rw [Real.log_exp]]
      exact Real.log_lt_log (Real.exp_pos _) hY2
    have h2 : Real.log ((Y : ℝ) + 1) - l ≤ 1 / Y := log_succ_sub_le (by omega)
    have h3 : 1 / (Y : ℝ) ≤ 1 / 10 ^ 9 := one_div_le_one_div_of_le (by norm_num) hY9
    linarith
  have hl0 : 1 ≤ l := by linarith
  have hYD : (Y : ℝ) < D := by
    rw [hDexp]; exact lt_of_le_of_lt hY1 (Real.exp_lt_exp.2 (by linarith))
  have hDYr : (Dmid : ℝ) ≤ (D : ℝ) / Y := by
    refine exp136_ge_Dmid.trans ?_
    rw [le_div_iff₀ hYpos, hDexp]
    calc Real.exp 136 * Y ≤ Real.exp (17 / 20 * L) * Real.exp (3 / 20 * L) :=
          mul_le_mul (Real.exp_le_exp.2 (by linarith)) hY1 hYpos.le (Real.exp_pos _).le
      _ = Real.exp L := by rw [← Real.exp_add]; ring_nf
  have hDY : Dmid ≤ D / Y := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.le_floor hDYr
  have hlogDY : Real.log ((D : ℝ) / Y) = L - l := Real.log_div hDpos.ne' hYpos.ne'
  have hB : 4 ≤ Real.log ((D : ℝ) / Y) := by rw [hlogDY]; linarith
  have hLl : 0 < L - l := by linarith
  -- Lemma 1 at `(D, Y)`
  have hYDn : Y ≤ D := by exact_mod_cast hYD.le
  have hS := schoenfeld_identity (x := D) (y := Y) (by omega) hYDn
  have hk := ksum_tail h hYn hYD hDY hN0 hN1 hB
  have hb := bdry_tail h hYe hYD hDY hN0 hN1
  have hj := jsum_tail h hYe hYD
  have hMD := M_tail h hN0 (le_trans X0_le_Dmid (le_trans Dmid_le_Dend hD)) le_rfl
  rw [hlogDY] at hk hb
  rw [← hldef, ← hLdef] at hj
  have hksum : |∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k)| ≤ ∑ k ∈ Icc 2 Y, |Λ k - 1| * |M (D / k)| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => abs_mul _ _))
  have hNtri : |N D| ≤ |M D| + 1 + |∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k)| +
      |∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j)| + |ρ Y| * |M (D / Y)| := by
    have e : N D = M D - ∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k) -
        ∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j) + ρ Y * M (D / Y) - 1 := by linarith
    rw [e, ← abs_mul]
    have a1 := abs_sub (M D - ∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k) -
      ∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j) + ρ Y * M (D / Y)) 1
    have a2 := abs_add_le (M D - ∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k) -
      ∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j)) (ρ Y * M (D / Y))
    have a3 := abs_sub (M D - ∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k))
      (∑ j ∈ Icc 1 (D / Y), (μ j : ℝ) * ρ (D / j))
    have a4 := abs_sub (M D) (∑ k ∈ Icc 2 Y, (Λ k - 1) * M (D / k))
    rw [abs_one] at a1
    linarith
  -- rewrite the boundary bound in units of `D`
  have hb' : |ρ Y| * |M (D / Y)| ≤ C5 * C0B * Y / l +
      D * (C5 * (0.014 / (l * (L - l)) + 0.017 * lam0 / (l * (L - l) ^ 2))) := by
    rw [← hldef] at hb
    refine hb.trans (le_of_eq ?_)
    have hl' : l ≠ 0 := by linarith
    have hLl' : L - l ≠ 0 := hLl.ne'
    have hYne : (Y : ℝ) ≠ 0 := hYpos.ne'
    field_simp
    ring
  -- the numerical lemma
  set ε := (2 + C0B) / D + 2 * C0B * Y / D + C5 * C0B * Y / (l * D) + κ / Y +
    2 * Real.sqrt ((D : ℝ) / Y) / D with hε
  have hε1 := eps_small (D := D) (Y := Y) (l := l) hDe hY9 hl0 hDYr
  have hε0 : 0 ≤ ε := by
    rw [hε]
    have hk0 := κ_pos.le
    have hc0 : (0 : ℝ) ≤ C0B := by norm_num [C0B]
    have hc5 : (0 : ℝ) ≤ C5 := by norm_num [C5]
    have hlD : 0 ≤ l * (D : ℝ) := mul_nonneg (by linarith) hDpos.le
    have t1 : 0 ≤ (2 + C0B) / (D : ℝ) := div_nonneg (by linarith) hDpos.le
    have t2 : 0 ≤ 2 * C0B * (Y : ℝ) / D :=
      div_nonneg (mul_nonneg (mul_nonneg two_pos.le hc0) hYpos.le) hDpos.le
    have t3 : 0 ≤ C5 * C0B * (Y : ℝ) / (l * D) :=
      div_nonneg (mul_nonneg (mul_nonneg hc5 hc0) hYpos.le) hlD
    have t4 : 0 ≤ κ / (Y : ℝ) := div_nonneg hk0 hYpos.le
    have t5 : 0 ≤ 2 * Real.sqrt ((D : ℝ) / Y) / D :=
      div_nonneg (mul_nonneg two_pos.le (Real.sqrt_nonneg _)) hDpos.le
    linarith
  have hnum := tail_numeric hL hl1 hl2 hε0 hε1
  -- assemble: `|N(D)| (1 − 1/L) ≤ D · 0.014 (1 − 1/L)`
  have hM' : |M D| ≤ C0B + |N D| / L + 0.017 * lam0 * D / L ^ 2 := hMD
  have hL0 : 0 < L := by linarith
  have key : |N D| * (1 - 1 / L) ≤ D * (2 * 0.014 * (Real.log L - Real.log (L - l)) +
      2 * (0.017 * lam0) * (1 / (L - l) - 1 / L) +
      C5 * (0.014 / (l * (L - l)) + 0.017 * lam0 / (l * (L - l) ^ 2)) +
      C5 * (κ * (Real.log (L / l) + 2 / l ^ 2) + (eHi - eLo) / l + eLo / L) +
      0.017 * lam0 / L ^ 2 + ε) := by
    have e1 : |N D| * (1 - 1 / L) = |N D| - |N D| / L := by ring
    have e2 : D * ε = (2 + C0B) + 2 * C0B * Y + C5 * C0B * Y / l + κ * (D / Y) +
        2 * Real.sqrt ((D : ℝ) / Y) := by
      rw [hε]; field_simp
    have e3 : (0.017 * lam0 * D / L ^ 2 : ℝ) = D * (0.017 * lam0 / L ^ 2) := by ring
    rw [← hLdef] at hk
    linarith only [hNtri, hM', hksum, hk, hj, hb', e1, e2, e3]
  have hfac : 0 < 1 - 1 / L := by
    rw [sub_pos, div_lt_one hL0]; linarith
  have := le_trans key (mul_le_mul_of_nonneg_left hnum hDpos.le)
  have h2 : |N D| * (1 - 1 / L) ≤ 0.014 * D * (1 - 1 / L) := by
    have e4 : (D : ℝ) * (0.014 * (1 - 1 / L)) = 0.014 * D * (1 - 1 / L) := by ring
    linarith only [this, e4]
  exact le_of_mul_le_mul_right h2 hfac

/-! ### Corollary 11 -/

theorem log_Dend_le : Real.log Dend ≤ (160.1 : ℝ) := by
  have h2 : LogCert.logHi Dend ≤ (160.1 : ℚ) := by unfold Dend; decide +kernel
  calc Real.log Dend = Real.log ((Dend : ℚ) : ℝ) := by norm_num
    _ ≤ ((LogCert.logHi Dend : ℚ) : ℝ) := LogCert.le_logHi (by unfold Dend; norm_num)
    _ ≤ ((160.1 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ = 160.1 := by norm_num

theorem exp5_le_Dmid : Real.exp 5 ≤ (Dmid : ℝ) := by
  have : Real.exp 5 ≤ 3 ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) 5
  have h2 : (3 : ℝ) ^ 5 ≤ Dmid := by unfold Dmid; norm_num
  linarith

theorem exp1_le_Dend : Real.exp 1 ≤ (Dend : ℝ) := by
  have h2 : (3 : ℝ) ≤ Dend := by unfold Dend; norm_num
  linarith [Real.exp_one_lt_d9]

/-- `S(n) ≤ S(X₀) + ∑_{X₀ ≤ t < n} |M(t)|/t`. -/
theorem S_split {n : ℕ} (hn : X0 ≤ n) : S n ≤ S X0 + ∑ t ∈ Ico X0 n, |M t| / t := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hm1 : 1 ≤ m := le_trans (by unfold X0; norm_num) hm
    rw [S_succ hm1, sum_Ico_succ_top hm]
    have h1 := log_one_add_inv_le m hm1
    have h2 : |M m| * Real.log (1 + 1 / (m : ℝ)) ≤ |M m| / m := by
      rw [show |M m| / (m : ℝ) = |M m| * (1 / m) by ring]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith

/-- `∑_{a ≤ t < n} 1/t ≤ 2 (log n − log a)`. -/
theorem sum_inv_le_two_log {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    ∑ t ∈ Ico a n, 1 / (t : ℝ) ≤ 2 * (Real.log n - Real.log a) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ico_succ_top hm]
    have hm1 : 1 ≤ m := le_trans ha hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h1 := log_one_add_ge (v := 1 / (m : ℝ)) (by positivity)
    have h2 := log_succ_sub_log hm1
    have e : 2 * (1 / (m : ℝ)) / (2 + 1 / m) = 2 / (2 * m + 1) := by
      field_simp
    rw [e] at h1
    have h3 : 1 / (m : ℝ) ≤ 2 * (2 / (2 * m + 1)) := by
      rw [div_le_iff₀ hmpos, show 2 * (2 / (2 * (m : ℝ) + 1)) * m = 4 * m / (2 * m + 1) by ring,
        le_div_iff₀ (by positivity)]
      linarith
    push_cast
    linarith

/-- `∑_{X₀ ≤ t < n} 1/log t ≤ n/20.72`. -/
theorem sum_inv_log_const {n : ℕ} (hn : X0 ≤ n) :
    ∑ t ∈ Ico X0 n, 1 / Real.log t ≤ n / 20.72 := by
  induction n, hn using Nat.le_induction with
  | base => simp; positivity
  | succ m hm ih =>
    rw [sum_Ico_succ_top hm]
    have hl : 20.72 ≤ Real.log m :=
      log_X0_ge.trans (Real.log_le_log (by unfold X0; norm_num) (by exact_mod_cast hm))
    have : 1 / Real.log m ≤ 1 / 20.72 := one_div_le_one_div_of_le (by norm_num) hl
    push_cast
    have e : ((m : ℝ) + 1) / 20.72 = m / 20.72 + 1 / 20.72 := by ring
    rw [e]
    linarith

/-- `L²/n ≤ 16/10³⁴` for `n ≥ D_end`. -/
theorem log_sq_div_le {x : ℝ} (hx : (Dend : ℝ) ≤ x) : Real.log x ^ 2 / x ≤ 16 / 10 ^ 34 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by unfold Dend; norm_num) hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; ring
  have h2 := log_le_two_sqrt hs
  have h3 : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
  have hL0 : 0 ≤ Real.log x := by
    have : (1 : ℝ) ≤ x := le_trans (by unfold Dend; norm_num) hx
    exact Real.log_nonneg this
  have h4 : Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
    have := Real.sq_sqrt hs.le
    nlinarith
  have h5 : (10 ^ 34 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]
    have : (Dend : ℝ) = 306985 * 10 ^ 64 := by unfold Dend; norm_num
    rw [this] at hx
    nlinarith
  have h6 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  calc Real.log x ^ 2 / x ≤ 16 * Real.sqrt x / x := div_le_div_of_nonneg_right h4 hx0.le
    _ = 16 / Real.sqrt x := by rw [div_eq_div_iff hx0.ne' hs.ne', mul_assoc, h6]
    _ ≤ 16 / 10 ^ 34 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h5

/-- **Corollary 11**: `|m(n)| log(n + 1) ≤ 0.03` for `n ≥ D_end`. -/
theorem tail (h : Inputs) (hc : CellsResult) {n : ℕ} (hn : Dend ≤ n) :
    |msum n| * Real.log (n + 1) ≤ 0.03 := by
  have hP := prop10 h hc
  have hN0 : ∀ t : ℕ, X0 ≤ t → t < n → |N t| ≤ 0.017 * t := by
    intro t h1 h2
    by_cases ht : t < Dend
    · exact hc.nuBar t h1 ht
    · have := hP t (by omega)
      have : (0 : ℝ) ≤ t := by positivity
      linarith
  have hDmn : Dmid ≤ n := le_trans Dmid_le_Dend hn
  have hX0n : X0 ≤ n := le_trans X0_le_Dmid hDmn
  have hxe : (Dend : ℝ) ≤ n := by exact_mod_cast hn
  have hDend0 : (0 : ℝ) < Dend := by unfold Dend; norm_num
  have hx : (0 : ℝ) < n := lt_of_lt_of_le hDend0 hxe
  have hC0B : (0 : ℝ) ≤ C0B := by norm_num [C0B]
  have hlam : lam0 = 1.107 := rfl
  set L := Real.log (n : ℝ) with hLdef
  have hL : 160 ≤ L := log_Dend_ge.trans (Real.log_le_log hDend0 hxe)
  have hL0 : 0 < L := by linarith
  -- `|M(n)|`
  have hMn : |M n| ≤ C0B + 0.014 * n / L + 0.017 * lam0 * n / L ^ 2 := by
    have h1 := M_tail h hN0 hX0n le_rfl
    have h2 := hP n hn
    have h3 : |N n| / L ≤ 0.014 * n / L := div_le_div_of_nonneg_right h2 hL0.le
    rw [← hLdef] at h1
    linarith
  -- `S(n)`
  have hS : S n ≤ I0B + 2 * C0B * L + 0.017 * (Dmid / 20.72) + 0.014 * ((n : ℝ) / (L - 2)) +
      0.017 * lam0 * (lam0 * n / L ^ 2) := by
    have h1 := S_split hX0n
    have h2 := S_X0_le h
    have hpt : ∀ t ∈ Ico X0 n, |M t| / t ≤ C0B * (1 / (t : ℝ)) +
        0.017 * lam0 * (1 / Real.log t ^ 2) + |N t| / t * (1 / Real.log t) := by
      intro t ht
      rw [mem_Ico] at ht
      have hM := M_tail h hN0 ht.1 ht.2.le
      have ht1 : 1 < t := lt_of_lt_of_le (by unfold X0; norm_num) ht.1
      have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
      have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast ht1)
      rw [div_le_iff₀ htpos]
      have e : (C0B * (1 / (t : ℝ)) + 0.017 * lam0 * (1 / Real.log t ^ 2) +
          |N t| / t * (1 / Real.log t)) * t =
          C0B + |N t| / Real.log t + 0.017 * lam0 * t / Real.log t ^ 2 := by
        field_simp
        ring
      linarith
    have hsum := sum_le_sum hpt
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
    have hA1 : ∑ t ∈ Ico X0 n, 1 / (t : ℝ) ≤ 2 * L := by
      have h3 := sum_inv_le_two_log (a := X0) (n := n) (by unfold X0; norm_num) hX0n
      have h4 : 0 ≤ Real.log (X0 : ℝ) := by linarith [log_X0_ge]
      rw [← hLdef] at h3
      linarith
    have hA4 : ∑ t ∈ Ico X0 n, 1 / Real.log t ^ 2 ≤ lam0 * n / L ^ 2 := sum_inv_log_sq_le hX0n
    have hsplit := sum_Ico_consecutive (fun t : ℕ => |N t| / t * (1 / Real.log t)) X0_le_Dmid hDmn
    have hB1 : ∑ t ∈ Ico X0 Dmid, |N t| / t * (1 / Real.log t) ≤ 0.017 * (Dmid / 20.72) := by
      calc _ ≤ ∑ t ∈ Ico X0 Dmid, 0.017 * (1 / Real.log t) := by
            refine sum_le_sum fun t ht => ?_
            rw [mem_Ico] at ht
            have ht1 : 1 < t := lt_of_lt_of_le (by unfold X0; norm_num) ht.1
            have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
            have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast ht1)
            apply mul_le_mul_of_nonneg_right _ (one_div_pos.2 hlt).le
            rw [div_le_iff₀ htpos]; exact hN0 t ht.1 (by omega)
        _ = 0.017 * ∑ t ∈ Ico X0 Dmid, 1 / Real.log t := by rw [mul_sum]
        _ ≤ 0.017 * (Dmid / 20.72) :=
            mul_le_mul_of_nonneg_left (sum_inv_log_const X0_le_Dmid) (by norm_num)
    have hB2 : ∑ t ∈ Ico Dmid n, |N t| / t * (1 / Real.log t) ≤ 0.014 * ((n : ℝ) / (L - 2)) := by
      calc _ ≤ ∑ t ∈ Ico Dmid n, 0.014 * (1 / Real.log t) := by
            refine sum_le_sum fun t ht => ?_
            rw [mem_Ico] at ht
            have ht1 : 1 < t := lt_of_lt_of_le (by unfold Dmid; norm_num) ht.1
            have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
            have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast ht1)
            apply mul_le_mul_of_nonneg_right _ (one_div_pos.2 hlt).le
            rw [div_le_iff₀ htpos]
            by_cases htD : t < Dend
            · exact hc.nuInf t ht.1 htD
            · exact hP t (by omega)
        _ = 0.014 * ∑ t ∈ Ico Dmid n, 1 / Real.log t := by rw [mul_sum]
        _ ≤ 0.014 * ((n : ℝ) / (L - 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have h3 := sum_inv_log_le exp5_le_Dmid hDmn
            rw [← hLdef] at h3
            have h4 : 20.72 ≤ Real.log (Dmid : ℝ) :=
              log_X0_ge.trans (Real.log_le_log (by unfold X0; norm_num)
                (by exact_mod_cast X0_le_Dmid))
            have h5 : 0 ≤ (Dmid : ℝ) / (Real.log Dmid - 2) :=
              div_nonneg (by positivity) (by linarith)
            linarith
    have hc1 : C0B * ∑ t ∈ Ico X0 n, 1 / (t : ℝ) ≤ C0B * (2 * L) :=
      mul_le_mul_of_nonneg_left hA1 hC0B
    have hc2 : 0.017 * lam0 * ∑ t ∈ Ico X0 n, 1 / Real.log t ^ 2 ≤
        0.017 * lam0 * (lam0 * n / L ^ 2) :=
      mul_le_mul_of_nonneg_left hA4 (by rw [hlam]; norm_num)
    linarith
  -- El Marraki
  have hn1 : 1 ≤ n := le_trans (by unfold Dend; norm_num) hn
  have hel := el_marraki (x := n) hn1
  rw [← hLdef] at hel
  set K : ℝ := C0B + I0B + 0.017 * (Dmid / 20.72) with hK
  set A : ℝ := 0.014 / L + 0.014 / (L - 2) + 0.017 * lam0 * (1 + lam0) / L ^ 2 + K / n +
    (2 * C0B + 1) * (L / n) with hA
  have hL2 : L - 2 ≠ 0 := by linarith
  have hmA : |msum n| ≤ A := by
    have hsum : |M n| + S n + L ≤ n * A := by
      have e : (n : ℝ) * A = 0.014 * n / L + 0.014 * ((n : ℝ) / (L - 2)) +
          0.017 * lam0 * n / L ^ 2 + 0.017 * lam0 * (lam0 * n / L ^ 2) + K + (2 * C0B + 1) * L := by
        rw [hA]
        field_simp
        ring
      rw [e, hK]
      linarith
    have e2 : |M n| / n + S n / n + L / n = (|M n| + S n + L) / n := by ring
    have h3 : (|M n| + S n + L) / n ≤ A := by
      rw [div_le_iff₀ hx]; linarith
    linarith
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hmA
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ L + 1 / n := by
    have := log_succ_sub_le (t := n) hn1
    rw [← hLdef] at this
    linarith
  have hlog1pos : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have step1 : |msum n| * Real.log (n + 1) ≤ A * (L + 1 / n) :=
    mul_le_mul hmA hlog1 hlog1pos hA0
  -- the pieces
  have hK0 : 0 ≤ K := by rw [hK]; unfold C0B I0B Dmid; norm_num
  have q4 : L / n ≤ 160.1 / Dend :=
    (log_div_anti exp1_le_Dend hxe).trans (div_le_div_of_nonneg_right log_Dend_le hDend0.le)
  have q5 : L ^ 2 / n ≤ 16 / 10 ^ 34 := log_sq_div_le hxe
  have q6 : 1 / (n : ℝ) ≤ 1 / Dend := one_div_le_one_div_of_le hDend0 hxe
  have q7 : K / n ≤ K / Dend := div_le_div_of_nonneg_left hK0 hDend0 hxe
  have q2 : L * (0.014 / (L - 2)) ≤ 0.014 * (1 + 2 / 158) := by
    have e : L * (0.014 / (L - 2)) = 0.014 * (1 + 2 / (L - 2)) := by
      field_simp; ring
    have : 2 / (L - 2) ≤ 2 / 158 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    rw [e]; linarith
  have q2' : 0.014 / (L - 2) ≤ 0.014 / 158 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have q1' : 0.014 / L ≤ 0.014 / 160 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have hc3 : 0.017 * lam0 * (1 + lam0) = 0.017 * 1.107 * 2.107 := by rw [hlam]; norm_num
  have q3 : L * (0.017 * lam0 * (1 + lam0) / L ^ 2) ≤ 0.017 * 1.107 * 2.107 / 160 := by
    have e : L * (0.017 * lam0 * (1 + lam0) / L ^ 2) = 0.017 * 1.107 * 2.107 / L := by
      rw [hc3]; field_simp
    rw [e]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have q3' : 0.017 * lam0 * (1 + lam0) / L ^ 2 ≤ 0.017 * 1.107 * 2.107 / 160 ^ 2 := by
    rw [hc3]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hC1 : (0 : ℝ) ≤ 2 * C0B + 1 := by linarith
  have q8 : (2 * C0B + 1) * (L / n) ≤ (2 * C0B + 1) * (160.1 / Dend) :=
    mul_le_mul_of_nonneg_left q4 hC1
  have hA1 : A ≤ 1 := by
    have : 0.014 / 160 + 0.014 / 158 + 0.017 * 1.107 * 2.107 / 160 ^ 2 + K / Dend +
        (2 * C0B + 1) * (160.1 / Dend) ≤ (1 : ℝ) := by
      rw [hK]; unfold C0B I0B Dend Dmid; norm_num
    rw [hA]; linarith
  have e3 : A * (L + 1 / n) = 0.014 + L * (0.014 / (L - 2)) +
      L * (0.017 * lam0 * (1 + lam0) / L ^ 2) + K * (L / n) + (2 * C0B + 1) * (L ^ 2 / n) +
      A * (1 / n) := by
    rw [hA]; field_simp
  have q9 : K * (L / n) ≤ K * (160.1 / Dend) := mul_le_mul_of_nonneg_left q4 hK0
  have q10 : (2 * C0B + 1) * (L ^ 2 / n) ≤ (2 * C0B + 1) * (16 / 10 ^ 34) :=
    mul_le_mul_of_nonneg_left q5 hC1
  have q11 : A * (1 / n) ≤ 1 * (1 / Dend) :=
    mul_le_mul hA1 q6 (by positivity) zero_le_one
  have hfin : 0.014 + 0.014 * (1 + 2 / 158) + 0.017 * 1.107 * 2.107 / 160 + K * (160.1 / Dend) +
      (2 * C0B + 1) * (16 / 10 ^ 34) + 1 * (1 / Dend) ≤ (0.03 : ℝ) := by
    rw [hK]; unfold C0B I0B Dend Dmid; norm_num
  linarith

end TernaryGoldbach.RSBounds.Moebius003
