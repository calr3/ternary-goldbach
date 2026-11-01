import TernaryGoldbach.Explicit.EtaPlusMellin
import TernaryGoldbach.Explicit.ExplicitBoundGen
import TernaryGoldbach.Explicit.MellinPlancherelGen

/-!
# The explicit-formula bounds for `η₊(t) e(δt)`

`PlancherelData (fP δ) 3.4 1`, `∫₀^∞ (log v)² η₊(v)² dv ≤ 3.15² (1 − √π/2) ≤ 1.129`, and the bounds of
`EtaPlusMellin` in `norm_SsumG_le_gen` (`χ` primitive `≠ 1`) and `norm_SsumG_zeta_le_gen` (`ζ`), under GRH
up to `T₀ ≥ 200 + max(10π|δ|, 50)`. `A ≥ ∫₀^∞ η₊²` is a parameter.
-/

open Complex MeasureTheory Set Filter Metric FourierTransform
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.Helfgott (etaPlus)

theorem norm_PhiG_fP_le (δ u : ℝ) : ‖PhiG (fP δ) u‖ ≤ 3.4 * Real.exp (-(1 * |u|)) := by
  rw [PhiG, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := norm_fP_le (δ := δ) (Real.exp_pos (-u)).le
  have e1 : Real.exp (-(1 / 2) * u) * (Real.exp (-u) * Real.exp (-Real.exp (-u) ^ 2 / 2)) =
      Real.exp (-(3 / 2) * u + -Real.exp (-u) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (-(1 / 2) * u) * ‖fP δ (Real.exp (-u))‖
      ≤ Real.exp (-(1 / 2) * u) * (3.15 * (Real.exp (-u) * Real.exp (-Real.exp (-u) ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 3.15 * Real.exp (-(3 / 2) * u + -Real.exp (-u) ^ 2 / 2) := by rw [← e1]; ring
    _ ≤ 3.4 * Real.exp (-(1 * |u|)) := by
        rcases le_total 0 u with hu | hu
        · rw [abs_of_nonneg hu]
          have h0 : Real.exp (-(3 / 2) * u + -Real.exp (-u) ^ 2 / 2) ≤ Real.exp (-(1 * u)) := by
            apply Real.exp_le_exp.2
            have := sq_nonneg (Real.exp (-u))
            nlinarith
          have hp := Real.exp_pos (-(1 * u))
          linarith
        · rw [abs_of_nonpos hu]
          set a := -u with ha
          have ha0 : 0 ≤ a := by linarith
          have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by linarith)
          have hsq : Real.exp (-u) ^ 2 = Real.exp (2 * a) := by
            rw [← Real.exp_nat_mul]; congr 1
          rw [hsq]
          have hle : -(3 / 2) * u + -Real.exp (2 * a) / 2 ≤ 1 / 16 + -(1 * -u) := by
            have hu' : u = -a := by rw [ha]; ring
            rw [hu']; nlinarith [sq_nonneg (a - 3 / 4)]
          have h16 : Real.exp (1 / 16) ≤ 1.07 := by
            have := Real.exp_bound' (x := 1 / 16) (by norm_num) (by norm_num) (n := 3) (by norm_num)
            norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
          calc 3.15 * Real.exp (-(3 / 2) * u + -Real.exp (2 * a) / 2)
              ≤ 3.15 * Real.exp (1 / 16 + -(1 * -u)) := by gcongr
            _ = 3.15 * (Real.exp (1 / 16) * Real.exp (-(1 * -u))) := by rw [Real.exp_add]
            _ ≤ 3.15 * (1.07 * Real.exp (-(1 * -u))) := by gcongr
            _ ≤ 3.4 * Real.exp (-(1 * -u)) := by nlinarith [Real.exp_pos (-(1 * -u))]

theorem continuous_PhiG_fP (δ : ℝ) : Continuous (PhiG (fP δ)) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  unfold PhiG
  refine (by fun_prop : Continuous fun u : ℝ => Real.exp (-(1 / 2) * u)).continuousAt.smul ?_
  exact ContinuousAt.comp (g := fP δ) (continuousAt_fP δ (Real.exp_pos (-u)))
    (by fun_prop : ContinuousAt (fun u : ℝ => Real.exp (-u)) u)

theorem plancherelData_fP (δ : ℝ) : PlancherelData (fP δ) 3.4 1 where
  cont := continuous_PhiG_fP δ
  c_pos := one_pos
  bound := norm_PhiG_fP_le δ

theorem norm_fP_sq (δ v : ℝ) : ‖fP δ v‖ ^ 2 = etaPlus v ^ 2 := by rw [norm_fP, sq_abs]

/-- `∫₀^∞ (log v)² η₊(v)² dv ≤ 1.129`. -/
theorem integral_log_sq_etaPlus_sq_le :
    ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * etaPlus v ^ 2 ≤ 1.129 := by
  have i5 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 3) (by norm_num) (by norm_num)
  have i3 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 1) (by norm_num) (by norm_num)
  have i4 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 2) (by norm_num) (by norm_num)
  set R : ℝ → ℝ := fun v => 3.15 ^ 2 * (v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ)) + v ^ (1:ℝ) * Real.exp (-v ^ (2:ℝ)) -
    2 * (v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ)))) with hR
  have j1 : IntegrableOn (fun v : ℝ => v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ)) +
      v ^ (1:ℝ) * Real.exp (-v ^ (2:ℝ))) (Ioi 0) := i5.add i3
  have j2 : IntegrableOn (fun v : ℝ => 2 * (v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ)))) (Ioi 0) := i4.const_mul 2
  have iR : IntegrableOn R (Ioi 0) := (j1.sub j2).const_mul _
  have hpt : ∀ v ∈ Ioi (0:ℝ), Real.log v ^ 2 * etaPlus v ^ 2 ≤ R v := by
    intro v (hv : 0 < v)
    have h := log_sq_le v hv
    have he : etaPlus v ^ 2 ≤ 3.15 ^ 2 * (v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ))) := by
      have h1 := norm_fP_le (δ := 0) hv.le
      rw [norm_fP] at h1
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      have hnp : etaPlus v ^ 2 ≤ 3.15 ^ 2 * (v ^ 2 * Real.exp (-v ^ 2)) := by
        refine this.trans (le_of_eq ?_)
        have e : Real.exp (-v ^ 2 / 2) ^ 2 = Real.exp (-v ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [mul_pow, mul_pow, e]
      simpa [Real.rpow_two] using hnp
    have e : R v = (v + v⁻¹ - 2) * (3.15 ^ 2 * (v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ)))) := by
      simp only [hR]
      have h3 : v ^ (3:ℝ) = v * v ^ (2:ℝ) := by
        rw [show (3:ℝ) = 1 + 2 by norm_num, Real.rpow_add hv, Real.rpow_one]
      have h1 : v ^ (1:ℝ) = v⁻¹ * v ^ (2:ℝ) := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.rpow_add hv, Real.rpow_one, ← mul_assoc,
          inv_mul_cancel₀ hv.ne', one_mul]
      rw [h3, h1]; ring
    rw [e]
    have hlog0 := sq_nonneg (Real.log v)
    calc Real.log v ^ 2 * etaPlus v ^ 2 ≤ Real.log v ^ 2 * (3.15 ^ 2 * (v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ)))) :=
          mul_le_mul_of_nonneg_left he hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)
  have iL : IntegrableOn (fun v => Real.log v ^ 2 * etaPlus v ^ 2) (Ioi 0) := by
    refine iR.mono' ((Real.measurable_log.pow_const 2).mul
      (TernaryGoldbach.MajorArcs.measurable_etaPlus.pow_const 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt v hv
  refine (setIntegral_mono_on iL iR measurableSet_Ioi hpt).trans ?_
  have hs : ∫ v in Ioi (0:ℝ), R v = 3.15 ^ 2 * ((∫ v in Ioi (0:ℝ), v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ))) +
      (∫ v in Ioi (0:ℝ), v ^ (1:ℝ) * Real.exp (-v ^ (2:ℝ))) -
        2 * ∫ v in Ioi (0:ℝ), v ^ (2:ℝ) * Real.exp (-v ^ (2:ℝ))) := by
    rw [← integral_add i5 i3, ← integral_const_mul, ← integral_sub j1 j2, ← integral_const_mul]
  rw [hs, integral_rpow_exp_sq (by norm_num), integral_rpow_exp_sq (by norm_num),
    integral_rpow_exp_sq (by norm_num)]
  rw [show ((3:ℝ) + 1) / 2 = 2 by norm_num, show ((1:ℝ) + 1) / 2 = 1 by norm_num,
    show ((2:ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_two, Real.Gamma_one,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have := sqrt_pi_bounds.1
  nlinarith

theorem integral_norm_sq_flineG_fP_le (δ : ℝ) {A : ℝ}
    (hA : ∫ v in Ioi (0:ℝ), etaPlus v ^ 2 ≤ A) :
    ∫ t, ‖flineG (fP δ) t‖ ^ 2 ≤ 2 * π * A := by
  rw [integral_norm_sq_flineG (plancherelData_fP δ)]
  simp_rw [norm_fP_sq]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

theorem integral_norm_sq_flineDG_fP_le (δ : ℝ) :
    ∫ t, ‖flineDG (fP δ) t‖ ^ 2 ≤ 2 * π * 1.129 := by
  rw [integral_norm_sq_flineDG (plancherelData_fP δ)]
  simp_rw [norm_fP_sq]
  exact mul_le_mul_of_nonneg_left integral_log_sq_etaPlus_sq_le (by positivity)

theorem norm_mellin_fP_vert (δ y : ℝ) :
    ‖mellin (fP δ) (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Cg * (300 * Real.exp 1) * (2 * aH) * Real.exp (-(thP δ * |y|)) := by
  have h := norm_mellin_fP_uniform δ (s := ((-1 / 2 : ℝ) : ℂ) + y * I) (by simp) (by simp; norm_num)
  simpa using h

theorem Kv_fP_nonneg : 0 ≤ Cg * (300 * Real.exp 1) * (2 * aH) := by
  have := Cg_nonneg; have := aH_pos; positivity

/-- **The explicit-formula bound for `η₊`, `χ` primitive `≠ 1`.** -/
theorem norm_SsumG_fP_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ} (hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0)
    (hG : ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2)
    {A : ℝ} (hA0 : 0 < A) (hA : ∫ v in Ioi (0:ℝ), etaPlus v ^ 2 ≤ A) :
    ‖SsumG χ (fP δ) x‖ ≤ Cg * 300 * (2 * aH) * Z3g (BP N) 0 +
      √x * E1g (BP N) T0 (2 * π * A) (2 * π * 1.129) +
      x * E2g (BP N) 11 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB (rhoA δ) +
      x ^ (-(1 / 2) : ℝ) * VgL (DN N) (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π) := by
  have h200 : 0 ≤ T0 - 200 := by linarith [le_max_right (10 * π * |δ|) 50]
  have hCa : 0 ≤ Cg * (2 * aH) := by have := Cg_nonneg; have := aH_pos; positivity
  exact norm_SsumG_le_gen hχ hχ1 (goodSmoothing_fP δ) hx (by linarith [le_max_right (10 * π * |δ|) 50])
    hG (norm_mellin_fP_zero δ) (mellin_half_eq (fP δ)) (hasDerivAt_flineG (plancherelData_fP δ))
    (continuous_flineDG (plancherelData_fP δ)) (by positivity) (by positivity)
    (integrable_norm_sq_flineG (plancherelData_fP δ)) (integrable_norm_sq_flineDG (plancherelData_fP δ))
    (integral_norm_sq_flineG_fP_le δ hA) (integral_norm_sq_flineDG_fP_le δ)
    (mul_nonneg hCa (EB_nonneg h200)) (mul_nonneg hCa (EA_nonneg _ δ)) (Real.exp_pos _).le rhoB_lt_one
    (Real.exp_pos _).le (rhoA_lt_one δ) (fun s h1 h2 h3 => norm_mellin_fP_tail hT0 h1 h2 h3)
    (thP_pos δ) Kv_fP_nonneg (norm_mellin_fP_vert δ)

/-- **The explicit-formula bound for `η₊`, `ζ`.** -/
theorem norm_SsumG_fP_zeta_le (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ}
    (hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2)
    {A : ℝ} (hA0 : 0 < A) (hA : ∫ v in Ioi (0:ℝ), etaPlus v ^ 2 ≤ A) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fP δ) x - mellin (fP δ) 1 * x‖ ≤
      Cg * 300 * (2 * aH) * Z3g BPz2 0 + √x * E1g BPz2 T0 (2 * π * A) (2 * π * 1.129) +
      x * E2g BPz2 10 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB (rhoA δ) +
      x ^ (-(1 / 2) : ℝ) * VgL 3 (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π) := by
  have h200 : 0 ≤ T0 - 200 := by linarith [le_max_right (10 * π * |δ|) 50]
  have hCa : 0 ≤ Cg * (2 * aH) := by have := Cg_nonneg; have := aH_pos; positivity
  exact norm_SsumG_zeta_le_gen (goodSmoothing_fP δ) hx (by linarith [le_max_right (10 * π * |δ|) 50])
    hRH (norm_mellin_fP_zero δ) (mellin_half_eq (fP δ)) (hasDerivAt_flineG (plancherelData_fP δ))
    (continuous_flineDG (plancherelData_fP δ)) (by positivity) (by positivity)
    (integrable_norm_sq_flineG (plancherelData_fP δ)) (integrable_norm_sq_flineDG (plancherelData_fP δ))
    (integral_norm_sq_flineG_fP_le δ hA) (integral_norm_sq_flineDG_fP_le δ)
    (mul_nonneg hCa (EB_nonneg h200)) (mul_nonneg hCa (EA_nonneg _ δ)) (Real.exp_pos _).le rhoB_lt_one
    (Real.exp_pos _).le (rhoA_lt_one δ) (fun s h1 h2 h3 => norm_mellin_fP_tail hT0 h1 h2 h3)
    (thP_pos δ) Kv_fP_nonneg (norm_mellin_fP_vert δ)

end TernaryGoldbach.Explicit
