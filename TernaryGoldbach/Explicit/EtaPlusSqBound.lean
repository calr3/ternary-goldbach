import TernaryGoldbach.Explicit.EtaPlusSq

/-!
# The explicit-formula bounds for `η₊²` and `η₊² log` (`ζ`)

`PlancherelData` for `φ₁ = η₊²` and `φ₂ = η₊² log` (`|Φ(u)| ≤ 9.93 e^{−|u|}`); the `L²` moments on `ℜs = 1/2`
from `η₊² ≤ 9.9225 v² e^{−v²}` and `log² v ≤ v + 1/v`; the tails above `T₀ = 500` (rate `0.6`); and
`norm_SsumG_zeta_le_gen` for both.
-/

open Complex MeasureTheory Set Filter Metric FourierTransform
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.Helfgott (etaPlus)

/-! ## Plancherel data -/

theorem continuous_PhiG_of {φ : ℝ → ℂ} (h : ∀ y, 0 < y → ContinuousAt φ y) : Continuous (PhiG φ) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  unfold PhiG
  refine (by fun_prop : Continuous fun u : ℝ => Real.exp (-(1 / 2) * u)).continuousAt.smul ?_
  exact ContinuousAt.comp (g := φ) (h _ (Real.exp_pos (-u)))
    (by fun_prop : ContinuousAt (fun u : ℝ => Real.exp (-u)) u)

theorem exp_neg_sq (u : ℝ) : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem PhiG_phi1_le (u : ℝ) : ‖PhiG phi1 u‖ ≤ 9.93 * Real.exp (-(1 * |u|)) := by
  rw [PhiG, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_phi1]
  have h := etaPlus_sq_le (Real.exp_pos (-u)).le
  rw [exp_neg_sq] at h
  have key : Real.exp (-(1 / 2) * u) * (Real.exp (-2 * u) * Real.exp (-Real.exp (-2 * u))) ≤
      Real.exp (-(1 * |u|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]; have := Real.exp_pos (-2 * u); linarith
    · rw [abs_of_nonpos hu]
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ -2 * u by linarith)
      nlinarith [sq_nonneg (u + 0.375)]
  have h0 : 0 ≤ Real.exp (-(1 / 2) * u) := (Real.exp_pos _).le
  calc Real.exp (-(1 / 2) * u) * etaPlus (Real.exp (-u)) ^ 2
      ≤ Real.exp (-(1 / 2) * u) * (9.9225 * (Real.exp (-2 * u) * Real.exp (-Real.exp (-2 * u)))) :=
        mul_le_mul_of_nonneg_left h h0
    _ = 9.9225 * (Real.exp (-(1 / 2) * u) * (Real.exp (-2 * u) * Real.exp (-Real.exp (-2 * u)))) := by
        ring
    _ ≤ 9.93 * Real.exp (-(1 * |u|)) := by nlinarith [Real.exp_pos (-(1 * |u|))]

theorem norm_phi2 (v : ℝ) : ‖phi2 v‖ = |Real.log v| * etaPlus v ^ 2 := by
  rw [phi2, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_phi1]

theorem PhiG_phi2_le (u : ℝ) : ‖PhiG phi2 u‖ ≤ 9.93 * Real.exp (-(1 * |u|)) := by
  rw [PhiG, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_phi2, Real.log_exp, abs_neg]
  have h := etaPlus_sq_le (Real.exp_pos (-u)).le
  rw [exp_neg_sq] at h
  set X := -(1 / 2) * u + (-2 * u + -Real.exp (-2 * u)) with hX
  have hY : |u| ≤ Real.exp (-|u| - X) := by
    refine le_trans ?_ (Real.add_one_le_exp _)
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]; have := Real.exp_pos (-2 * u); rw [hX]; linarith
    · rw [abs_of_nonpos hu]
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ -2 * u by linarith)
      rw [hX]; nlinarith [sq_nonneg (u + 0.625)]
  have e2 : Real.exp (-(1 / 2) * u) * (Real.exp (-2 * u) * Real.exp (-Real.exp (-2 * u))) =
      Real.exp X := by rw [hX, Real.exp_add, Real.exp_add]
  have key : |u| * (Real.exp (-(1 / 2) * u) * (Real.exp (-2 * u) * Real.exp (-Real.exp (-2 * u)))) ≤
      Real.exp (-(1 * |u|)) := by
    rw [e2]
    calc |u| * Real.exp X ≤ Real.exp (-|u| - X) * Real.exp X :=
          mul_le_mul_of_nonneg_right hY (Real.exp_pos _).le
      _ = Real.exp (-(1 * |u|)) := by rw [← Real.exp_add]; congr 1; ring
  have h0 : 0 ≤ Real.exp (-(1 / 2) * u) := (Real.exp_pos _).le
  calc Real.exp (-(1 / 2) * u) * (|u| * etaPlus (Real.exp (-u)) ^ 2)
      ≤ Real.exp (-(1 / 2) * u) * (|u| * (9.9225 * (Real.exp (-2 * u) *
          Real.exp (-Real.exp (-2 * u))))) := by gcongr
    _ = 9.9225 * (|u| * (Real.exp (-(1 / 2) * u) * (Real.exp (-2 * u) *
          Real.exp (-Real.exp (-2 * u))))) := by ring
    _ ≤ 9.93 * Real.exp (-(1 * |u|)) := by nlinarith [Real.exp_pos (-(1 * |u|))]

theorem plancherelData_phi1 : PlancherelData phi1 9.93 1 where
  cont := continuous_PhiG_of fun y hy => continuousAt_phi1 hy
  c_pos := one_pos
  bound := PhiG_phi1_le

theorem plancherelData_phi2 : PlancherelData phi2 9.93 1 where
  cont := continuous_PhiG_of fun y hy => continuousAt_phi2 hy
  c_pos := one_pos
  bound := PhiG_phi2_le

/-! ## The `L²` moments -/

theorem rpow_nat' {v : ℝ} (k : ℕ) : v ^ (k : ℝ) = v ^ k := Real.rpow_natCast v k

theorem norm_phi1_sq_le {v : ℝ} (hv : 0 < v) :
    ‖phi1 v‖ ^ 2 ≤ 98.4561 * (v ^ 4 * Real.exp (-v ^ 2)) := by
  rw [norm_phi1]
  have h := etaPlus_sq_le hv.le
  have := pow_le_pow_left₀ (sq_nonneg _) h 2
  refine this.trans ?_
  have hE := Real.exp_pos (-v ^ 2)
  have hE1 : Real.exp (-v ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg v])
  have hv4 : 0 ≤ v ^ 4 := by positivity
  have : (9.9225 * (v ^ 2 * Real.exp (-v ^ 2))) ^ 2 = 98.45600625 * (v ^ 4 * Real.exp (-v ^ 2) ^ 2) := by
    ring
  rw [this]
  have h2 : Real.exp (-v ^ 2) ^ 2 ≤ Real.exp (-v ^ 2) := by nlinarith
  have := mul_le_mul_of_nonneg_left h2 hv4
  nlinarith

theorem log_sq_le' {v : ℝ} (hv : 0 < v) : Real.log v ^ 2 ≤ v + v⁻¹ := by
  have := log_sq_le v hv
  linarith

/-- `∫₀^∞ v^k e^{−v²} dv` for the moments used. -/
theorem integrableOn_mom (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ k * Real.exp (-v ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := (k : ℝ)) (by
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by norm_num)
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp only [rpow_nat', Real.rpow_two]

theorem integral_mom (k : ℕ) :
    ∫ v in Ioi (0:ℝ), v ^ k * Real.exp (-v ^ 2) = (1 / 2) * Real.Gamma ((k + 1) / 2) := by
  rw [← integral_rpow_exp_sq (q := (k : ℝ)) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [rpow_nat', Real.rpow_two]

theorem Gamma_three_halves : Real.Gamma (3 / 2) = 1 / 2 * √π := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]

theorem Gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * √π := by
  rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Gamma_five_halves]; ring

theorem integral_phi1_sq_le : ∫ v in Ioi (0:ℝ), ‖phi1 v‖ ^ 2 ≤ 65.5 := by
  have hi := (integrableOn_mom 4).const_mul 98.4561
  refine (integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity) hi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) =>
      norm_phi1_sq_le hv))).trans ?_
  rw [integral_const_mul, integral_mom]
  rw [show ((4:ℕ) + 1 : ℝ) / 2 = 5 / 2 by norm_num, Gamma_five_halves]
  have := sqrt_pi_bounds.2
  nlinarith

theorem integral_log_sq_phi1_sq_le :
    ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * ‖phi1 v‖ ^ 2 ≤ 147.7 := by
  have hi := ((integrableOn_mom 5).add (integrableOn_mom 3)).const_mul 98.4561
  refine (integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity) hi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_))).trans ?_
  · have h1 := log_sq_le' hv
    have h2 := norm_phi1_sq_le hv
    have h0 : 0 ≤ Real.log v ^ 2 := sq_nonneg _
    have hE := Real.exp_pos (-v ^ 2)
    calc Real.log v ^ 2 * ‖phi1 v‖ ^ 2 ≤ (v + v⁻¹) * (98.4561 * (v ^ 4 * Real.exp (-v ^ 2))) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 98.4561 * (v ^ 5 * Real.exp (-v ^ 2) + v ^ 3 * Real.exp (-v ^ 2)) := by
          field_simp
  · rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add (integrableOn_mom 5) (integrableOn_mom 3), integral_mom, integral_mom]
    rw [show ((5:ℕ) + 1 : ℝ) / 2 = 3 by norm_num, show ((3:ℕ) + 1 : ℝ) / 2 = 2 by norm_num,
      show (3:ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]
    norm_num

theorem norm_phi2_sq (v : ℝ) : ‖phi2 v‖ ^ 2 = Real.log v ^ 2 * ‖phi1 v‖ ^ 2 := by
  rw [phi2, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem integral_phi2_sq_le : ∫ v in Ioi (0:ℝ), ‖phi2 v‖ ^ 2 ≤ 147.7 := by
  simp_rw [norm_phi2_sq]; exact integral_log_sq_phi1_sq_le

theorem integral_log_sq_phi2_sq_le :
    ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * ‖phi2 v‖ ^ 2 ≤ 338.2 := by
  have hi := (((integrableOn_mom 6).add ((integrableOn_mom 4).const_mul 2)).add
    (integrableOn_mom 2)).const_mul 98.4561
  refine (integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity) hi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_))).trans ?_
  · rw [norm_phi2_sq]
    have h1 := log_sq_le' hv
    have h1' : Real.log v ^ 2 * Real.log v ^ 2 ≤ (v + v⁻¹) * (v + v⁻¹) :=
      mul_le_mul h1 h1 (sq_nonneg _) (by positivity)
    have h2 := norm_phi1_sq_le hv
    have hE := Real.exp_pos (-v ^ 2)
    calc Real.log v ^ 2 * (Real.log v ^ 2 * ‖phi1 v‖ ^ 2)
        = (Real.log v ^ 2 * Real.log v ^ 2) * ‖phi1 v‖ ^ 2 := by ring
      _ ≤ ((v + v⁻¹) * (v + v⁻¹)) * (98.4561 * (v ^ 4 * Real.exp (-v ^ 2))) :=
          mul_le_mul h1' h2 (by positivity) (by positivity)
      _ = 98.4561 * (v ^ 6 * Real.exp (-v ^ 2) + 2 * (v ^ 4 * Real.exp (-v ^ 2)) +
          v ^ 2 * Real.exp (-v ^ 2)) := by field_simp; ring
  · rw [integral_const_mul]
    simp only [Pi.add_apply]
    have i64 : IntegrableOn (fun v : ℝ => v ^ 6 * Real.exp (-v ^ 2) + 2 * (v ^ 4 * Real.exp (-v ^ 2)))
        (Ioi 0) := (integrableOn_mom 6).add ((integrableOn_mom 4).const_mul 2)
    rw [integral_add i64 (integrableOn_mom 2), integral_add (integrableOn_mom 6)
      ((integrableOn_mom 4).const_mul 2), integral_const_mul, integral_mom, integral_mom, integral_mom]
    rw [show ((6:ℕ) + 1 : ℝ) / 2 = 7 / 2 by norm_num, show ((4:ℕ) + 1 : ℝ) / 2 = 5 / 2 by norm_num,
      show ((2:ℕ) + 1 : ℝ) / 2 = 3 / 2 by norm_num, Gamma_seven_halves, Gamma_five_halves,
      Gamma_three_halves]
    have := sqrt_pi_bounds.2
    nlinarith

/-! ## Tails above `T₀ = 500`, the line `ℜs = −1/2`, `M(0)` -/

theorem floor_window_le {y : ℝ} (hy : 500 < y) : (⌊(y - 500) / 4.4⌋₊ : ℝ) * 4.4 ≤ y - 500 := by
  have := Nat.floor_le (show 0 ≤ (y - 500) / 4.4 by apply div_nonneg <;> linarith)
  rwa [le_div_iff₀ (by norm_num)] at this

theorem exp_window_le {y : ℝ} (hy : 500 < y) (a : ℝ) :
    Real.exp (a + 240) * Real.exp (-(0.6 * y)) ≤
      Real.exp (a - 60) * Real.exp (-2.64) ^ ⌊(y - 500) / 4.4⌋₊ := by
  have hk := floor_window_le hy
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

theorem phi1_tail (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (hT : 500 < |s.im|) :
    ‖mellin phi1 s‖ ≤ (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (-60) * Real.exp (-2.64) ^ ⌊(|s.im| - 500) / 4.4⌋₊ +
      0 * 0 ^ ⌊(|s.im| - 500) / 4.4⌋₊ := by
  have h := norm_mellin_phi1_le (c := 0.6) (by norm_num) le_rfl (s := s) (by linarith) (by linarith)
  have he := exp_window_le hT 0
  rw [zero_add, zero_sub] at he
  have hc : 0 ≤ (Cg * (2 * aH)) ^ 2 * 8 := by positivity
  rw [zero_mul, add_zero]
  refine h.trans ?_
  calc (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * 0.6) * Real.exp (-(0.6 * |s.im|))
      = (Cg * (2 * aH)) ^ 2 * 8 * (Real.exp 240 * Real.exp (-(0.6 * |s.im|))) := by norm_num; ring
    _ ≤ (Cg * (2 * aH)) ^ 2 * 8 * (Real.exp (-60) * Real.exp (-2.64) ^ ⌊(|s.im| - 500) / 4.4⌋₊) :=
        mul_le_mul_of_nonneg_left he hc
    _ = _ := by ring

theorem phi2_tail (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (hT : 500 < |s.im|) :
    ‖mellin phi2 s‖ ≤ 2 * (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (0.3 - 60) *
      Real.exp (-2.64) ^ ⌊(|s.im| - 500) / 4.4⌋₊ + 0 * 0 ^ ⌊(|s.im| - 500) / 4.4⌋₊ := by
  have h := norm_mellin_phi2_le (c := 0.6) (by norm_num) le_rfl (s := s) (by linarith) (by linarith)
  have he := exp_window_le hT 0.3
  have hc : 0 ≤ 2 * (Cg * (2 * aH)) ^ 2 * 8 := by positivity
  rw [zero_mul, add_zero]
  refine h.trans ?_
  have e1 : Real.exp (400 * 0.6) * Real.exp (0.6 / 2) = Real.exp (0.3 + 240) := by
    rw [← Real.exp_add]; norm_num
  calc 2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * 0.6) * Real.exp (0.6 / 2)) *
        Real.exp (-(0.6 * |s.im|))
      = 2 * (Cg * (2 * aH)) ^ 2 * 8 * ((Real.exp (400 * 0.6) * Real.exp (0.6 / 2)) *
          Real.exp (-(0.6 * |s.im|))) := by ring
    _ = 2 * (Cg * (2 * aH)) ^ 2 * 8 * (Real.exp (0.3 + 240) * Real.exp (-(0.6 * |s.im|))) := by rw [e1]
    _ ≤ 2 * (Cg * (2 * aH)) ^ 2 * 8 * (Real.exp (0.3 - 60) * Real.exp (-2.64) ^ ⌊(|s.im| - 500) / 4.4⌋₊) :=
        mul_le_mul_of_nonneg_left he hc
    _ = _ := by ring

theorem phi1_vert (y : ℝ) : ‖mellin phi1 (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
    (Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 * Real.exp (-(1 / 400 * |y|)) := by
  have h := norm_mellin_phi1_le (c := 1 / 400) (by norm_num) (by norm_num)
    (s := ((-1 / 2 : ℝ) : ℂ) + y * I) (by simp; norm_num) (by simp; norm_num)
  rw [show (400:ℝ) * (1 / 400) = 1 by norm_num] at h
  simpa using h

theorem phi2_vert (y : ℝ) : ‖mellin phi2 (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
    2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 * Real.exp (1 / 800)) * Real.exp (-(1 / 400 * |y|)) := by
  have h := norm_mellin_phi2_le (c := 1 / 400) (by norm_num) (by norm_num)
    (s := ((-1 / 2 : ℝ) : ℂ) + y * I) (by simp) (by simp; norm_num)
  rw [show (400:ℝ) * (1 / 400) = 1 by norm_num, show (1 / 400 : ℝ) / 2 = 1 / 800 by norm_num] at h
  simpa using h

theorem phi1_zero : ‖mellin phi1 0‖ ≤ (Cg * (2 * aH)) ^ 2 * 8 := by
  have h := norm_mellin_phi1_le (c := 0) le_rfl (by norm_num) (s := 0) (by simp) (by simp)
  simpa using h

theorem phi2_zero : ‖mellin phi2 0‖ ≤ 2 * ((Cg * (2 * aH)) ^ 2 * 8) := by
  have h := norm_mellin_phi2_le (c := 0) le_rfl (by norm_num) (s := 0) (by simp; norm_num) (by simp; norm_num)
  simpa using h

/-! ## The explicit-formula bounds -/

theorem rhoP_lt_one : Real.exp (-2.64) < 1 := by rw [Real.exp_lt_one_iff]; norm_num

/-- **`η₊²`**: `|Σ Λ(n) η₊²(n/x) − x ∫η₊²| ≤ G₀ Z₃ + √x E₁ + x E₂ + x^{−1/2} V/2π` under RH up to `500`. -/
theorem norm_SsumG_phi1_le {x : ℝ} (hx : 1 ≤ x)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 500 → ρ.re = 1 / 2) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) phi1 x - mellin phi1 1 * x‖ ≤
      (Cg * (2 * aH)) ^ 2 * 8 * Z3g BPz2 0 + √x * E1g BPz2 500 (2 * π * 65.5) (2 * π * 147.7) +
      x * E2g BPz2 10 500 ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp (-60)) 0 (Real.exp (-2.64)) 0 +
      x ^ (-(1 / 2) : ℝ) * VgL 3 ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1) (1 / 400) / (2 * π) := by
  have hp := plancherelData_phi1
  refine norm_SsumG_zeta_le_gen goodSmoothing_phi1 hx (by norm_num) hRH phi1_zero (mellin_half_eq phi1)
    (hasDerivAt_flineG hp) (continuous_flineDG hp) (by positivity) (by positivity)
    (integrable_norm_sq_flineG hp) (integrable_norm_sq_flineDG hp) ?_ ?_ (by positivity) le_rfl
    (Real.exp_pos _).le rhoP_lt_one le_rfl zero_lt_one phi1_tail (by norm_num) (by positivity) phi1_vert
  · rw [integral_norm_sq_flineG hp]
    exact mul_le_mul_of_nonneg_left integral_phi1_sq_le (by positivity)
  · rw [integral_norm_sq_flineDG hp]
    exact mul_le_mul_of_nonneg_left integral_log_sq_phi1_sq_le (by positivity)

/-- **`η₊² log`**: the same for `Σ Λ(n) η₊²(n/x) log(n/x) − x ∫η₊² log`. -/
theorem norm_SsumG_phi2_le {x : ℝ} (hx : 1 ≤ x)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 500 → ρ.re = 1 / 2) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) phi2 x - mellin phi2 1 * x‖ ≤
      2 * ((Cg * (2 * aH)) ^ 2 * 8) * Z3g BPz2 0 + √x * E1g BPz2 500 (2 * π * 147.7) (2 * π * 338.2) +
      x * E2g BPz2 10 500 (2 * (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (0.3 - 60)) 0 (Real.exp (-2.64)) 0 +
      x ^ (-(1 / 2) : ℝ) * VgL 3 (2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 * Real.exp (1 / 800)))
        (1 / 400) / (2 * π) := by
  have hp := plancherelData_phi2
  refine norm_SsumG_zeta_le_gen goodSmoothing_phi2 hx (by norm_num) hRH phi2_zero (mellin_half_eq phi2)
    (hasDerivAt_flineG hp) (continuous_flineDG hp) (by positivity) (by positivity)
    (integrable_norm_sq_flineG hp) (integrable_norm_sq_flineDG hp) ?_ ?_ (by positivity) le_rfl
    (Real.exp_pos _).le rhoP_lt_one le_rfl zero_lt_one phi2_tail (by norm_num) (by positivity) phi2_vert
  · rw [integral_norm_sq_flineG hp]
    exact mul_le_mul_of_nonneg_left integral_phi2_sq_le (by positivity)
  · rw [integral_norm_sq_flineDG hp]
    exact mul_le_mul_of_nonneg_left integral_log_sq_phi2_sq_le (by positivity)

end TernaryGoldbach.Explicit
