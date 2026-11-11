/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.KSum
import RSBounds.Moebius003.SquarefreeData

/-!
# Proposition 8, step 1: the `j`-sum

`|∑_{j ≤ D/y} μ(j) ρ(D/j)| ≤ D · J`, where, with `V = 10¹⁰`,
`J = [D₊ > V] C₅ J_sq + 1.6κ/√y + 0.8(4 − κ + log(D₊/y))/√D₋ + κ/y + 2/√(D₋ y) + 1/D₋` and
`J_sq = κ (log(L₊/log V) + 2/log² V) + 0.21/log V + 0.96/L₋` (Lemma 5(b), (c), (d) in their
discrete forms, and Lemma 5(a)).
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

/-- `V = 10¹⁰`. -/
def Vn : ℕ := 10 ^ 10

/-- `C₅` as a rational. -/
def C5q : ℚ := 77629 / 10 ^ 7

/-- A lower bound for `log V`. -/
def logVLo : ℚ := LogCert.logLo (10 ^ 10)

theorem logVLo_le : (logVLo : ℝ) ≤ Real.log Vn := by
  have := LogCert.logLo_le (q := (10 ^ 10 : ℚ)) (by norm_num)
  rw [show ((Vn : ℕ) : ℝ) = ((10 ^ 10 : ℚ) : ℝ) by norm_num [Vn]]
  exact this

theorem logVLo_pos : (23 : ℚ) ≤ logVLo := by unfold logVLo; decide +kernel

/-- The bound for `∑_{j ≤ D/V} μ²(j)/(j log(D/j))`. -/
def jsqW (Lm Lp : ℚ) : ℚ :=
  kHi * (LogCert.logHi (Lp / logVLo) + 2 / logVLo ^ 2) + (eHiQ - eLoQ) / logVLo + eLoQ / Lm

/-- The bound for the `j`-sum, divided by `D`. -/
def jW (Dlo Dhi y : ℕ) (sD sy Lm Lp : ℚ) : ℚ :=
  (if Vn < Dhi then C5q * jsqW Lm Lp else 0) + 8 / 5 * kHi / sy +
    4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD + kHi / y + 2 / (sD * sy) + 1 / Dlo

theorem abs_moebius_eq_sq (j : ℕ) : |(μ j : ℝ)| = (μ j : ℝ) ^ 2 := by
  rcases moebius_eq_or j with h | h | h <;> simp [h]

theorem C5_eq : C5 = (C5q : ℝ) := by unfold C5 C5q; norm_num

theorem logVLo_ge23 : (23 : ℝ) ≤ logVLo := by
  have h23 := logVLo_pos
  have : ((23 : ℚ) : ℝ) ≤ logVLo := by exact_mod_cast h23
  have e : ((23 : ℚ) : ℝ) = 23 := by norm_num
  linarith

attribute [local irreducible] LogCert.logHi LogCert.logLo in
theorem jsqW_nonneg {Lm Lp : ℚ} (hLm0 : 0 < Lm) (hLpV : (logVLo : ℝ) ≤ Lp) :
    (0 : ℝ) ≤ jsqW Lm Lp := by
  have hV0 : (0 : ℝ) < logVLo := lt_of_lt_of_le (by norm_num) logVLo_ge23
  have hq : (0 : ℚ) < Lp / logVLo := by
    have h1 : (0 : ℚ) < logVLo := lt_of_lt_of_le (by norm_num) logVLo_pos
    have h2 : (0 : ℝ) < Lp := lt_of_lt_of_le hV0 hLpV
    have h3 : (0 : ℚ) < Lp := by exact_mod_cast h2
    positivity
  have h1 := LogCert.le_logHi hq
  have h2 : 0 ≤ Real.log (((Lp / logVLo : ℚ) : ℝ)) := by
    apply Real.log_nonneg; push_cast; rw [le_div_iff₀ hV0]; linarith
  have h3 : (0 : ℝ) ≤ ((LogCert.logHi (Lp / logVLo) : ℚ) : ℝ) := le_trans h2 h1
  unfold jsqW; push_cast
  have : (0 : ℝ) ≤ (kHi : ℝ) := by norm_num [kHi]
  have : (0 : ℝ) ≤ ((eHiQ : ℚ) : ℝ) - eLoQ := by norm_num [eHiQ, eLoQ]
  have hLm0' : (0 : ℝ) < Lm := by exact_mod_cast hLm0
  have : (0 : ℝ) ≤ (eLoQ : ℝ) / Lm := div_nonneg (by norm_num [eLoQ]) hLm0'.le
  positivity

attribute [local irreducible] LogCert.logHi LogCert.logLo in
theorem jsq_part {D J1 : ℕ} {Lm Lp : ℚ} (hJ1pos : 1 ≤ J1) (hJ1D : (J1 : ℝ) < D)
    (hJ1r : (J1 : ℝ) ≤ D / Vn) (hLm0 : 0 < Lm) (hLmL : (Lm : ℝ) ≤ Real.log D)
    (hLLp : Real.log D ≤ Lp) :
    ∑ j ∈ Icc 1 J1, (μ j : ℝ) ^ 2 / (j * Real.log (D / j)) ≤ (jsqW Lm Lp : ℝ) := by
  have hκ := κ_mem
  have hDpos : (0 : ℝ) < D := by
    have : (1 : ℝ) ≤ J1 := by exact_mod_cast hJ1pos
    linarith
  have h5d := sum_sq_div_log_le (J := J1) (D := D) (eLo := eLo) (eHi := eHi) hJ1pos hJ1D
    (fun i hi1 _ => Q1_bounds hi1)
  refine h5d.trans ?_
  set L := Real.log D
  set ℓ := Real.log (J1 : ℝ)
  have hJ1pos_r : (0 : ℝ) < J1 := by exact_mod_cast hJ1pos
  have hW : Real.log Vn ≤ L - ℓ := by
    have : ℓ ≤ Real.log ((D : ℝ) / Vn) := Real.log_le_log hJ1pos_r hJ1r
    rw [Real.log_div hDpos.ne' (by unfold Vn; norm_num)] at this
    linarith
  have hV0 := logVLo_ge23
  have hV0' : (0 : ℝ) < logVLo := lt_of_lt_of_le (by norm_num) hV0
  have hWlo : (logVLo : ℝ) ≤ L - ℓ := logVLo_le.trans hW
  have hWpos : 0 < L - ℓ := lt_of_lt_of_le hV0' hWlo
  have hLm0' : (0 : ℝ) < Lm := by exact_mod_cast hLm0
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by exact_mod_cast hJ1pos)
  have hL0 : 0 < L := lt_of_lt_of_le hLm0' hLmL
  have hratio : L / (L - ℓ) ≤ Lp / logVLo := by
    rw [div_le_div_iff₀ hWpos hV0']
    exact mul_le_mul hLLp hWlo hV0'.le (le_trans hL0.le hLLp)
  have hq : (0 : ℚ) < Lp / logVLo := by
    have h1 : (0 : ℚ) < logVLo := lt_of_lt_of_le (by norm_num) logVLo_pos
    have h2 : (0 : ℝ) < Lp := lt_of_lt_of_le hL0 hLLp
    have h3 : (0 : ℚ) < Lp := by exact_mod_cast h2
    positivity
  have hlog1 : Real.log (L / (L - ℓ)) ≤ LogCert.logHi (Lp / logVLo) := by
    have h1 := LogCert.le_logHi hq
    push_cast at h1
    exact (Real.log_le_log (div_pos hL0 hWpos) hratio).trans h1
  have hlog0 : 0 ≤ Real.log (L / (L - ℓ)) := Real.log_nonneg (by
    rw [le_div_iff₀ hWpos]; linarith)
  have hsq : 2 / (L - ℓ) ^ 2 ≤ 2 / (logVLo : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hV0'.le hWlo 2)
  have he1 : (eHi - eLo) / (L - ℓ) ≤ ((eHiQ : ℝ) - eLoQ) / logVLo := by
    have : eHi - eLo = ((eHiQ : ℝ) - eLoQ) := by norm_num [eHi, eLo, eHiQ, eLoQ]
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num [eHiQ, eLoQ]) hV0' hWlo
  have he2 : eLo / L ≤ (eLoQ : ℝ) / Lm := by
    have : eLo = (eLoQ : ℝ) := by norm_num [eLo, eLoQ]
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num [eLoQ]) hLm0' hLmL
  have hκk : κ * (Real.log (L / (L - ℓ)) + 2 / (L - ℓ) ^ 2) ≤
      (kHi : ℝ) * (LogCert.logHi (Lp / logVLo) + 2 / (logVLo : ℝ) ^ 2) := by
    apply mul_le_mul hκ.2 (add_le_add hlog1 hsq) (by positivity) (by norm_num [kHi])
  unfold jsqW; push_cast
  linarith

attribute [local irreducible] LogCert.logHi LogCert.logLo LogCert.sqrtLo in
theorem jsum_bound (h : Inputs) {Dlo Dhi D y : ℕ} {sD sy Lm Lp : ℚ}
    (hX0 : X0 ≤ Dlo) (hy1 : 1500 ≤ y) (hy2 : y ≤ 2 ^ 20) (hy33 : 33 * y ≤ Dlo)
    (hD1 : Dlo ≤ D) (hD2 : D < Dhi)
    (hsD0 : 0 < sD) (hsD : (sD : ℝ) ≤ Real.sqrt Dlo) (hsy0 : 0 < sy) (hsy : (sy : ℝ) ≤ Real.sqrt y)
    (hLm0 : 0 < Lm) (hLm : (Lm : ℝ) ≤ Real.log Dlo) (hLp : Real.log Dhi ≤ Lp) :
    |∑ j ∈ Icc 1 (D / y), (μ j : ℝ) * ρ (D / j)| ≤ D * (jW Dlo Dhi y sD sy Lm Lp : ℝ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < D)
  have hDlopos : (0 : ℝ) < Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < Dlo)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hsy' : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hsD' : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  have hsDD : Real.sqrt Dlo ≤ Real.sqrt D := Real.sqrt_le_sqrt (by exact_mod_cast hD1)
  have hsqD : Real.sqrt (D : ℝ) * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
  have hsqy : Real.sqrt (y : ℝ) * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
  have hsD0' : (0 : ℝ) < sD := by exact_mod_cast hsD0
  have hsy0' : (0 : ℝ) < sy := by exact_mod_cast hsy0
  have hκ := κ_mem
  have hκ0 := κ_pos
  have hJ12' : D / Vn ≤ D / y := Nat.div_le_div_left (by unfold Vn; omega) (by omega)
  have hJ2pos' : 1 ≤ D / y := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  set J1 := D / Vn with hJ1
  set J2 := D / y with hJ2
  have hJ12 : J1 ≤ J2 := hJ12'
  have hJ2pos : 1 ≤ J2 := hJ2pos'
  clear_value J1 J2
  have hJ2real : (J2 : ℝ) ≤ D / y := by rw [hJ2]; exact Nat.cast_div_le
  -- termwise bounds
  have hS : ∀ j ∈ Icc 1 J1, |(μ j : ℝ) * ρ (D / j)| ≤
      C5 * D * ((μ j : ℝ) ^ 2 / (j * Real.log (D / j))) + (μ j : ℝ) ^ 2 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hv : (Vn : ℝ) ≤ (D : ℝ) / j := by
      rw [le_div_iff₀ hjpos]
      exact_mod_cast (by have := (Nat.le_div_iff_mul_le (by unfold Vn; omega)).1 (hJ1 ▸ hj2); linarith [mul_comm j Vn])
    have hv22 : Real.exp 22 ≤ (D : ℝ) / j := le_trans exp22_le (by unfold Vn at hv; exact_mod_cast hv)
    have hfl : D / j = ⌊(D : ℝ) / j⌋₊ := (Nat.floor_div_eq_div (K := ℝ) D j).symm
    have hρ := rho_S h hv22
    rw [← hfl] at hρ
    have hlog : 0 < Real.log ((D : ℝ) / j) := Real.log_pos (by
      have : (1 : ℝ) < Vn := by unfold Vn; norm_num
      linarith)
    rw [abs_mul, abs_moebius_eq_sq]
    have hμ0 : 0 ≤ (μ j : ℝ) ^ 2 := sq_nonneg _
    calc (μ j : ℝ) ^ 2 * |ρ (D / j)| ≤ (μ j : ℝ) ^ 2 * (C5 * (D / j) / Real.log (D / j) + 1) :=
          mul_le_mul_of_nonneg_left hρ hμ0
      _ = C5 * D * ((μ j : ℝ) ^ 2 / (j * Real.log (D / j))) + (μ j : ℝ) ^ 2 := by
          field_simp
  have hP : ∀ j ∈ Ioc J1 J2, |(μ j : ℝ) * ρ (D / j)| ≤
      4 / 5 * Real.sqrt D * ((μ j : ℝ) ^ 2 / Real.sqrt j) + (μ j : ℝ) ^ 2 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Ioc.1 hj
    have hjpos' : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le _) hj1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hjpos'
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.2 hjpos
    have hvy : (1500 : ℝ) ≤ (D : ℝ) / j := by
      rw [le_div_iff₀ hjpos]
      have := (Nat.le_div_iff_mul_le (by omega)).1 (hJ2 ▸ hj2)
      have : (y : ℝ) * j ≤ D := by exact_mod_cast (by linarith [mul_comm j y])
      have : (1500 : ℝ) ≤ y := by exact_mod_cast hy1
      nlinarith
    have hvV : (D : ℝ) / j ≤ 10 ^ 10 := by
      rw [div_le_iff₀ hjpos]
      have h1 : D < (J1 + 1) * Vn := by
        rw [hJ1]
        have h3 := Nat.div_add_mod D Vn
        have h4 := Nat.mod_lt D (show Vn > 0 by unfold Vn; norm_num)
        nlinarith
      have h2 : (J1 + 1) * Vn ≤ j * Vn := Nat.mul_le_mul_right _ hj1
      have : D ≤ j * Vn := by omega
      have : (D : ℝ) ≤ j * Vn := by exact_mod_cast this
      unfold Vn at this; push_cast at this; linarith
    have hfl : D / j = ⌊(D : ℝ) / j⌋₊ := (Nat.floor_div_eq_div (K := ℝ) D j).symm
    have hρ := rho_P h hvy hvV
    rw [← hfl] at hρ
    rw [abs_mul, abs_moebius_eq_sq]
    have hμ0 : 0 ≤ (μ j : ℝ) ^ 2 := sq_nonneg _
    have hsq : Real.sqrt ((D : ℝ) / j) = Real.sqrt D / Real.sqrt j := Real.sqrt_div' _ hjpos.le
    calc (μ j : ℝ) ^ 2 * |ρ (D / j)| ≤ (μ j : ℝ) ^ 2 * (0.8 * Real.sqrt ((D : ℝ) / j) + 1) :=
          mul_le_mul_of_nonneg_left hρ hμ0
      _ = 4 / 5 * Real.sqrt D * ((μ j : ℝ) ^ 2 / Real.sqrt j) + (μ j : ℝ) ^ 2 := by
          rw [hsq]; field_simp; ring
  -- assemble the three parts
  set A := ∑ j ∈ Icc 1 J1, (μ j : ℝ) ^ 2 / (j * Real.log (D / j)) with hA
  set B := ∑ j ∈ Icc 1 J2, (μ j : ℝ) ^ 2 / Real.sqrt j with hB
  have hsplit : Icc 1 J2 = Icc 1 J1 ∪ Ioc J1 J2 := by
    ext j; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 J1) (Ioc J1 J2) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  have hQsplit : Q J2 = ∑ j ∈ Icc 1 J1, (μ j : ℝ) ^ 2 + ∑ j ∈ Ioc J1 J2, (μ j : ℝ) ^ 2 := by
    rw [Q, hsplit, sum_union hdisj]
  have hBsub : ∑ j ∈ Ioc J1 J2, (μ j : ℝ) ^ 2 / Real.sqrt j ≤ B := by
    rw [hB, hsplit, sum_union hdisj]
    have : 0 ≤ ∑ j ∈ Icc 1 J1, (μ j : ℝ) ^ 2 / Real.sqrt j := sum_nonneg fun _ _ => by positivity
    linarith
  have hmain : |∑ j ∈ Icc 1 J2, (μ j : ℝ) * ρ (D / j)| ≤ C5 * D * A + 4 / 5 * Real.sqrt D * B + Q J2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [hsplit, sum_union hdisj]
    have h1 := sum_le_sum hS
    have h2 := sum_le_sum hP
    rw [sum_add_distrib, ← mul_sum] at h1
    rw [sum_add_distrib, ← mul_sum] at h2
    have h3 : 4 / 5 * Real.sqrt D * ∑ j ∈ Ioc J1 J2, (μ j : ℝ) ^ 2 / Real.sqrt j ≤ 4 / 5 * Real.sqrt D * B :=
      mul_le_mul_of_nonneg_left hBsub (by positivity)
    rw [hQsplit]
    linarith
  refine hmain.trans ?_
  -- the parts
  have hB' := sum_sq_div_sqrt_le J2
  have hQ' := Q_le J2
  have hsJ2 : Real.sqrt (J2 : ℝ) ≤ Real.sqrt D / Real.sqrt y := by
    rw [← Real.sqrt_div' _ hypos.le]; exact Real.sqrt_le_sqrt hJ2real
  have hJ2pos_r : (1 : ℝ) ≤ J2 := by exact_mod_cast hJ2pos
  have hlogJ2 : Real.log J2 ≤ LogCert.logHi ((Dhi : ℚ) / y) := by
    have h1 : Real.log (J2 : ℝ) ≤ Real.log ((Dhi : ℝ) / y) := by
      apply Real.log_le_log (by linarith)
      refine hJ2real.trans ?_
      gcongr
    have h2 := LogCert.le_logHi (q := (Dhi : ℚ) / y) (by
      have : (0 : ℚ) < Dhi := by exact_mod_cast (by omega : 0 < Dhi)
      have : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
      positivity)
    push_cast at h2
    linarith
  have hlogJ2' : 0 ≤ Real.log (J2 : ℝ) := Real.log_nonneg hJ2pos_r
  have hsDsD : Real.sqrt D * sD ≤ D := by
    calc Real.sqrt D * sD ≤ Real.sqrt D * Real.sqrt D :=
          mul_le_mul_of_nonneg_left (hsD.trans hsDD) (Real.sqrt_nonneg _)
      _ = D := hsqD
  have hsqrtD_le : Real.sqrt D ≤ D / sD := by rw [le_div_iff₀ hsD0']; exact hsDsD
  have hBpart : 4 / 5 * Real.sqrt D * B ≤
      D * (8 / 5 * (kHi : ℝ) / sy + 4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD) := by
    have e1 : κ * (2 * Real.sqrt J2 - 1) + 4 + Real.log J2 ≤
        2 * κ * (Real.sqrt D / Real.sqrt y) + (4 - κ + Real.log J2) := by nlinarith
    have hB2 := hB'.trans e1
    have hpos1 : 0 ≤ 4 - κ + Real.log J2 := by linarith [κ_hi]
    have t1 : 4 / 5 * Real.sqrt D * (2 * κ * (Real.sqrt D / Real.sqrt y)) ≤ D * (8 / 5 * (kHi : ℝ) / sy) := by
      have : 4 / 5 * Real.sqrt D * (2 * κ * (Real.sqrt D / Real.sqrt y)) = D * (8 / 5 * κ / Real.sqrt y) := by
        have e : 4 / 5 * Real.sqrt D * (2 * κ * (Real.sqrt D / Real.sqrt y)) =
            8 / 5 * κ * (Real.sqrt D * Real.sqrt D) / Real.sqrt y := by ring
        rw [e, hsqD]; ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ hDpos.le
      apply div_le_div₀ (by norm_num [kHi]) (by linarith [hκ.2]) hsy0' hsy
    have t2 : 4 / 5 * Real.sqrt D * (4 - κ + Real.log J2) ≤
        D * (4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD) := by
      have hk : 4 - κ + Real.log J2 ≤ 4 - kLo + LogCert.logHi ((Dhi : ℚ) / y) := by linarith [hκ.1]
      calc 4 / 5 * Real.sqrt D * (4 - κ + Real.log J2)
          ≤ 4 / 5 * (D / sD) * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) := by
            have h4 : 4 / 5 * Real.sqrt D ≤ 4 / 5 * (D / sD) := by linarith
            have h5 : (0 : ℝ) ≤ 4 / 5 * (D / sD) := by positivity
            exact mul_le_mul h4 hk hpos1 h5
        _ = D * (4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD) := by ring
    calc 4 / 5 * Real.sqrt D * B ≤ 4 / 5 * Real.sqrt D * (2 * κ * (Real.sqrt D / Real.sqrt y) + (4 - κ + Real.log J2)) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
      _ ≤ _ := by rw [mul_add, mul_add]; linarith [t1, t2]
  have hQpart : Q J2 ≤ D * ((kHi : ℝ) / y + 2 / (sD * sy) + 1 / Dlo) := by
    have t1 : κ * J2 ≤ D * ((kHi : ℝ) / y) := by
      calc κ * J2 ≤ kHi * (D / y) := mul_le_mul hκ.2 hJ2real (by positivity) (by
            have : (0 : ℝ) ≤ kHi := by norm_num [kHi]
            exact this)
        _ = D * ((kHi : ℝ) / y) := by ring
    have t2 : 2 * Real.sqrt J2 ≤ D * (2 / (sD * sy)) := by
      calc 2 * Real.sqrt J2 ≤ 2 * (Real.sqrt D / sy) := by
            gcongr; exact hsJ2.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hsy0' hsy)
        _ ≤ 2 * ((D / sD) / sy) := by gcongr
        _ = D * (2 / (sD * sy)) := by field_simp
    have t3 : (1 : ℝ) ≤ D * (1 / Dlo) := by
      rw [mul_one_div, le_div_iff₀ hDlopos, one_mul]; exact_mod_cast hD1
    linarith
  have hApart : C5 * D * A ≤ D * ((if Vn < Dhi then C5q * jsqW Lm Lp else 0 : ℚ) : ℝ) := by
    have hC50 : (0 : ℝ) ≤ C5 := by unfold C5; norm_num
    by_cases hJ10 : J1 = 0
    · have hA0 : A = 0 := by rw [hA, hJ10]; simp
      rw [hA0, mul_zero]
      split_ifs with hV
      · have hLpV : (logVLo : ℝ) ≤ Lp := by
          have h1 := logVLo_le
          have h2 : Real.log Vn ≤ Real.log Dhi :=
            Real.log_le_log (by unfold Vn; norm_num) (by exact_mod_cast hV.le)
          exact h1.trans (h2.trans hLp)
        have hj := jsqW_nonneg hLm0 hLpV
        have : (0 : ℝ) ≤ C5q := by norm_num [C5q]
        push_cast
        exact mul_nonneg hDpos.le (mul_nonneg this hj)
      · simp
    · have hJ1pos : 1 ≤ J1 := Nat.one_le_iff_ne_zero.2 hJ10
      have hDV : Vn ≤ D := by
        have := (Nat.le_div_iff_mul_le (by unfold Vn; norm_num)).1 (hJ1 ▸ hJ1pos); omega
      have hV : Vn < Dhi := lt_of_le_of_lt hDV hD2
      rw [if_pos hV]
      have hJ1D : (J1 : ℝ) < D := by
        have : J1 < D := hJ1 ▸ Nat.div_lt_self (by unfold X0 at hX0; omega) (by unfold Vn; norm_num)
        exact_mod_cast this
      have hJ1r : (J1 : ℝ) ≤ D / Vn := by rw [hJ1]; exact Nat.cast_div_le
      have hLmL : (Lm : ℝ) ≤ Real.log D := hLm.trans (Real.log_le_log hDlopos (by exact_mod_cast hD1))
      have hLLp : Real.log D ≤ Lp := (Real.log_le_log hDpos (by exact_mod_cast hD2.le)).trans hLp
      have hAle := jsq_part hJ1pos hJ1D hJ1r hLm0 hLmL hLLp
      rw [← hA] at hAle
      push_cast
      rw [← C5_eq]
      calc C5 * D * A ≤ C5 * D * (jsqW Lm Lp : ℝ) := mul_le_mul_of_nonneg_left hAle (by positivity)
        _ = D * (C5 * (jsqW Lm Lp : ℝ)) := by ring
  unfold jW
  rw [Rat.cast_add, Rat.cast_add, Rat.cast_add, Rat.cast_add, Rat.cast_add]
  have e1 : (((8 / 5 * kHi / sy : ℚ)) : ℝ) = 8 / 5 * (kHi : ℝ) / sy := by push_cast; ring
  have e2 : (((4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD : ℚ)) : ℝ) =
      4 / 5 * (4 - kLo + LogCert.logHi ((Dhi : ℚ) / y)) / sD := by push_cast; ring
  have e3 : (((kHi / y : ℚ)) : ℝ) = (kHi : ℝ) / y := by push_cast; ring
  have e4 : (((2 / (sD * sy) : ℚ)) : ℝ) = 2 / (sD * sy) := by push_cast; ring
  have e5 : (((1 / Dlo : ℚ)) : ℝ) = 1 / Dlo := by push_cast; ring
  rw [e1, e2, e3, e4, e5]
  have := hBpart
  have := hQpart
  have := hApart
  rw [mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [mul_add] at hBpart
  rw [mul_add, mul_add] at hQpart
  linarith

end TernaryGoldbach.RSBounds.Moebius003
