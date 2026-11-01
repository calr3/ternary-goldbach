import TernaryGoldbach.MajorArcs.Prop942
import TernaryGoldbach.MajorArcs.Cor713
import TernaryGoldbach.Explicit.EtaPlusCg

/-!
# [B, Thm 7.1.4] from [B, Prop 9.4.2] (proved) and Platt's verification

`η₊(t) = h₂₀₀(t) t e^{-t²/2}` ([B, (9.63)], our `etaPlus`). From `prop_9_4_2` (our constants) with
* `q = 1`: `T₀ = 10⁸`, `|δ| ≤ 6·10⁵`: `|E| ≤ 10⁻¹⁸ + 6.24·10⁶/√x`;
* `q ≥ 2`: `T₀ = 10⁸/q` (odd `q ≤ 1.5·10⁵`, `|δ| ≤ 6·10⁵/q`; even `q ≤ 1.25·10⁵`, `|δ| ≤ 1.2·10⁶/q`) or
  `T₀ = 200 + 7.5·10⁷/q` (even `1.25·10⁵ < q ≤ 3·10⁵`): `|E| ≤ (7.5·10⁻⁸ + 7.7·10⁶/√x)/√q`,
for `x ≥ 4.9·10²⁶`. ([B]: `4.772·10⁻¹¹ + 251400/√x` and `1.3482·10⁻¹⁴ + 1.617·10⁻¹⁰/q + (499900/√q + 52)/√x`
for `x ≥ 10¹²`.)
-/

open Real MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (e Schar)
open TernaryGoldbach.Helfgott (etaPlus)
open TernaryGoldbach.Explicit (Cg aH Z3g ZLg E1g E2g c3g BP BPz2 EB EA rhoB rhoA VgL DN thP thetaD Jl ZL
  Z3 c3 two_aH_le cA_le cA_nonneg)

/-! ## Constants -/

theorem cE0_le : Cg * 300 * (2 * aH) ≤ 38772 := by
  have := cA_le
  have e : Cg * 300 * (2 * aH) = 300 * (Cg * (2 * aH)) := by ring
  rw [e]; linarith

theorem cKv_le : Cg * (300 * Real.exp 1) * (2 * aH) ≤ 1.054e5 := by
  have h1 := cA_le
  have h0 := cA_nonneg
  have he := Real.exp_one_lt_d9
  have e : Cg * (300 * Real.exp 1) * (2 * aH) = 300 * Real.exp 1 * (Cg * (2 * aH)) := by ring
  rw [e]
  have : 300 * Real.exp 1 * (Cg * (2 * aH)) ≤ 300 * 2.7182818286 * 129.24 :=
    mul_le_mul (by linarith) h1 h0 (by norm_num)
  linarith

theorem cKv_nonneg : 0 ≤ Cg * (300 * Real.exp 1) * (2 * aH) := by
  have := Explicit.Cg_nonneg; have := Explicit.aH_pos; positivity

theorem thP_bounds {δ : ℝ} (hδ : |δ| ≤ 6e5) :
    2 / thP δ ≤ 4.2858e6 ∧ 2 / thP δ ^ 2 ≤ 9.1838e12 := by
  have hθ : 0.28 / 600001 ≤ thP δ := by
    unfold thP
    refine le_min ?_ (by norm_num)
    unfold thetaD
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hθ0 : (0:ℝ) < 0.28 / 600001 := by norm_num
  constructor
  · calc 2 / thP δ ≤ 2 / (0.28 / 600001) := div_le_div_of_nonneg_left (by norm_num) hθ0 hθ
      _ ≤ 4.2858e6 := by norm_num
  · calc 2 / thP δ ^ 2 ≤ 2 / (0.28 / 600001) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hθ0.le hθ 2)
      _ ≤ 9.1838e12 := by norm_num

theorem DN_le {q : ℕ} [NeZero q] (hq3 : q ≤ 300000) : DN q ≤ 133.48 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  unfold DN
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hl1 : Real.log q ≤ 12.62 := (Real.log_le_log hq0 hq3').trans log_3e5_le
  have hl2 : Real.log (q + 1) ≤ 12.62 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log300001_le
  have := log512_le
  have := neg_log0355_le
  push_cast; linarith

theorem log2_const_le : 2 / Real.log 2 + 4.8 ≤ 7.6855 := by
  have := Real.log_two_gt_d9
  rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith)]; nlinarith

theorem log2_const_nonneg : 0 ≤ 2 / Real.log 2 + 4.8 := by
  have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity

/-- The vertical-line constant. -/
theorem VgL_le {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 133.48) {δ : ℝ} (hδ : |δ| ≤ 6e5) :
    VgL D (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) ≤ 2e19 := by
  obtain ⟨h1, h2⟩ := thP_bounds hδ
  have hθ0 := Explicit.thP_pos δ
  unfold VgL
  have hX : (D + 37) * (2 / thP δ) + 2.6 * (2 / thP δ ^ 2) ≤ (133.48 + 37) * 4.2858e6 + 2.6 * 9.1838e12 := by
    gcongr
  have hX0 : 0 ≤ (D + 37) * (2 / thP δ) + 2.6 * (2 / thP δ ^ 2) := by positivity
  have hK := cKv_le
  have hK0 := cKv_nonneg
  have hl := log2_const_le
  have hl0 := log2_const_nonneg
  calc Cg * (300 * Real.exp 1) * (2 * aH) * (2 / Real.log 2 + 4.8) *
        ((D + 37) * (2 / thP δ) + 2.6 * (2 / thP δ ^ 2))
      ≤ 1.054e5 * 7.6855 * ((133.48 + 37) * 4.2858e6 + 2.6 * 9.1838e12) := by gcongr
    _ ≤ 2e19 := by norm_num

/-! ## `E₂`: a generic bound -/

theorem E2_gen_le {B : ℝ → ℝ} {κ T0 δ T1 u0 Z C IA EBb EAb : ℝ}
    (hT1 : 7 ≤ T1) (hT1' : T1 ≤ T0 - 200)
    (hEBb : 0.892 * (T1 * Real.exp (-(0.1598 * T1))) ≤ EBb)
    (hu0 : 10 ≤ u0) (hu : δ ≠ 0 → u0 ≤ (T0 - 200) / (π * |δ|))
    (hEAb : 0.588 * (u0 ^ 2 * Real.exp (-0.1065 * u0 ^ 2)) ≤ EAb)
    (hZ0 : 0 ≤ Z3g B T0) (hZ : Z3g B T0 ≤ Z) (hC0 : 0 ≤ c3g κ T0) (hC : c3g κ T0 ≤ C)
    (hIA : 1 / (1 - rhoA δ) ≤ IA) :
    E2g B κ T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB (rhoA δ) ≤
      129.24 * (EBb * (2 * Z * 2.1768 + 2 * C * 2.1768 ^ 2) + EAb * (2 * Z * IA + 2 * C * IA ^ 2)) := by
  have hEB : EB (T0 - 200) ≤ EBb := by
    unfold EB
    have hm := mul_exp_anti (c := 0.1598) (t₀ := T1) (t := T0 - 200) (by norm_num) (by linarith) hT1'
    rw [show -0.1598 * (T0 - 200) = -(0.1598 * (T0 - 200)) by ring, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans hEBb
  have hEB0 := Explicit.EB_nonneg (by linarith : (0:ℝ) ≤ T0 - 200)
  have hEBb0 : 0 ≤ EBb := hEB0.trans hEB
  have hEAb0 : 0 ≤ EAb := le_trans (by positivity) hEAb
  have hEA : EA (T0 - 200) δ ≤ EAb := by
    unfold EA
    split_ifs with hδ0
    · exact hEAb0
    · have hg := Explicit.gauss_sq_anti hu0 (hu hδ0)
      calc 0.588 * ((T0 - 200) / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * ((T0 - 200) / (π * |δ|)) ^ 2)
          = 0.588 * (((T0 - 200) / (π * |δ|)) ^ 2 *
              Real.exp (-0.1065 * ((T0 - 200) / (π * |δ|)) ^ 2)) := by ring
        _ ≤ 0.588 * (u0 ^ 2 * Real.exp (-0.1065 * u0 ^ 2)) := by gcongr
        _ ≤ EAb := hEAb
  have hEA0 := Explicit.EA_nonneg (T0 - 200) δ
  have hB := rhoB_le
  have hB1 : 1 / (1 - rhoB) ≤ 2.1768 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ 1 / (1 - rhoB) := by rw [one_div]; exact inv_nonneg.2 (by linarith)
  have hA0 : 0 ≤ 1 / (1 - rhoA δ) := by
    have := Explicit.rhoA_lt_one δ; rw [one_div]; exact inv_nonneg.2 (by linarith)
  have hIA0 : 0 ≤ IA := hA0.trans hIA
  have hZp : 0 ≤ Z := hZ0.trans hZ
  have hCp : 0 ≤ C := hC0.trans hC
  unfold E2g
  rw [div_eq_mul_one_div (2 * Z3g B T0) (1 - rhoB), div_eq_mul_one_div (2 * c3g κ T0) ((1 - rhoB) ^ 2),
    div_eq_mul_one_div (2 * Z3g B T0) (1 - rhoA δ),
    div_eq_mul_one_div (2 * c3g κ T0) ((1 - rhoA δ) ^ 2), ← one_div_pow, ← one_div_pow]
  have hX : 2 * Z3g B T0 * (1 / (1 - rhoB)) + 2 * c3g κ T0 * (1 / (1 - rhoB)) ^ 2 ≤
      2 * Z * 2.1768 + 2 * C * 2.1768 ^ 2 := by
    have h1 : Z3g B T0 * (1 / (1 - rhoB)) ≤ Z * 2.1768 := mul_le_mul hZ hB1 hB0 hZp
    have h2 : c3g κ T0 * (1 / (1 - rhoB)) ^ 2 ≤ C * 2.1768 ^ 2 :=
      mul_le_mul hC (pow_le_pow_left₀ hB0 hB1 2) (by positivity) hCp
    linarith
  have hY : 2 * Z3g B T0 * (1 / (1 - rhoA δ)) + 2 * c3g κ T0 * (1 / (1 - rhoA δ)) ^ 2 ≤
      2 * Z * IA + 2 * C * IA ^ 2 := by
    have h1 : Z3g B T0 * (1 / (1 - rhoA δ)) ≤ Z * IA := mul_le_mul hZ hIA hA0 hZp
    have h2 : c3g κ T0 * (1 / (1 - rhoA δ)) ^ 2 ≤ C * IA ^ 2 :=
      mul_le_mul hC (pow_le_pow_left₀ hA0 hIA 2) (by positivity) hCp
    linarith
  have hX0 : 0 ≤ 2 * Z3g B T0 * (1 / (1 - rhoB)) + 2 * c3g κ T0 * (1 / (1 - rhoB)) ^ 2 := by
    positivity
  have hY0 : 0 ≤ 2 * Z3g B T0 * (1 / (1 - rhoA δ)) + 2 * c3g κ T0 * (1 / (1 - rhoA δ)) ^ 2 := by
    positivity
  have hcA := cA_le
  have hcA0 := cA_nonneg
  have hEB' : Cg * (2 * aH) * EB (T0 - 200) ≤ 129.24 * EBb := mul_le_mul hcA hEB hEB0 (by norm_num)
  have hEA' : Cg * (2 * aH) * EA (T0 - 200) δ ≤ 129.24 * EAb := mul_le_mul hcA hEA hEA0 (by norm_num)
  have h1 := mul_le_mul hEB' hX hX0 (by positivity)
  have h2 := mul_le_mul hEA' hY hY0 (by positivity)
  linarith

/-! ## Exponential bounds -/

theorem exp_neg_3995_le : Real.exp (-(0.1598 * 250)) ≤ 4.47e-18 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge 39 (u := 0.95) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem exp_neg_4213_le : Real.exp (-0.1065 * (19.89:ℝ) ^ 2) ≤ 5.05e-19 := by
  refine (Real.exp_le_exp.2 (show -0.1065 * (19.89:ℝ) ^ 2 ≤ -(42 + 0.13) by norm_num)).trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge 42 (u := 0.13) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem exp_neg57_le : Real.exp (-0.1065 * (23.3:ℝ) ^ 2) ≤ 1.76e-25 := by
  refine (Real.exp_le_exp.2 (show -0.1065 * (23.3:ℝ) ^ 2 ≤ -(57:ℕ) by norm_num)).trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge 57
  norm_num at this ⊢; linarith

theorem EBb_small {T1 : ℝ} (h : 74 ≤ 0.1598 * T1) {c : ℝ} (hc : 0.892 * (T1 * 1e-32) ≤ c) :
    0.892 * (T1 * Real.exp (-(0.1598 * T1))) ≤ c := by
  have hT : 0 ≤ T1 := by linarith
  have he : Real.exp (-(0.1598 * T1)) ≤ 1e-32 :=
    (Real.exp_le_exp.2 (by linarith : -(0.1598 * T1) ≤ -74)).trans exp_neg74_le
  exact le_trans (by gcongr) hc

theorem EAb_265 : 0.588 * ((26.5:ℝ) ^ 2 * Real.exp (-0.1065 * (26.5:ℝ) ^ 2)) ≤ 4.13e-30 := by
  have he : Real.exp (-0.1065 * (26.5:ℝ) ^ 2) ≤ 1e-32 :=
    (Real.exp_le_exp.2 (by norm_num)).trans exp_neg74_le
  calc 0.588 * ((26.5:ℝ) ^ 2 * Real.exp (-0.1065 * (26.5:ℝ) ^ 2)) ≤ 0.588 * ((26.5:ℝ) ^ 2 * 1e-32) := by
        gcongr
    _ ≤ 4.13e-30 := by norm_num

theorem EAb_1989 : 0.588 * ((19.89:ℝ) ^ 2 * Real.exp (-0.1065 * (19.89:ℝ) ^ 2)) ≤ 1.2e-16 := by
  calc 0.588 * ((19.89:ℝ) ^ 2 * Real.exp (-0.1065 * (19.89:ℝ) ^ 2)) ≤
        0.588 * ((19.89:ℝ) ^ 2 * 5.05e-19) := by gcongr; exact exp_neg_4213_le
    _ ≤ 1.2e-16 := by norm_num

theorem EAb_233 : 0.588 * ((23.3:ℝ) ^ 2 * Real.exp (-0.1065 * (23.3:ℝ) ^ 2)) ≤ 6e-23 := by
  calc 0.588 * ((23.3:ℝ) ^ 2 * Real.exp (-0.1065 * (23.3:ℝ) ^ 2)) ≤
        0.588 * ((23.3:ℝ) ^ 2 * 1.76e-25) := by gcongr; exact exp_neg57_le
    _ ≤ 6e-23 := by norm_num

/-- `1/(1 − ρ_A) ≤ 1 + π(D + 1)/8.492` for `|δ| ≤ D`. -/
theorem IA_le {δ D IA : ℝ} (hδ : |δ| ≤ D) (h : 1 + 3.1416 * (D + 1) / (1.93 * 4.4) ≤ IA) :
    1 / (1 - rhoA δ) ≤ IA := by
  have hpi := Real.pi_lt_d4
  unfold rhoA
  refine (Explicit.inv_one_sub_exp_neg_le (by positivity)).trans ?_
  rw [one_div_div]
  have : π * (|δ| + 1) / (1.93 * 4.4) ≤ 3.1416 * (D + 1) / (1.93 * 4.4) :=
    div_le_div_of_nonneg_right (mul_le_mul hpi.le (by linarith) (by positivity)
      (by linarith [abs_nonneg δ])) (by norm_num)
  linarith

theorem c3g_le {κ T0 Tm C : ℝ} (hκ : 0 ≤ κ) (hTm : 0 < Tm) (hT : Tm ≤ T0)
    (h : κ * 4.4 ≤ C * (Tm * 1.2039)) : c3g κ T0 ≤ C := by
  unfold c3g
  have hl := log_ratio_3_ge
  have hT0 : 0 < T0 := lt_of_lt_of_le hTm hT
  rw [div_div, div_le_iff₀ (mul_pos hT0 (by linarith))]
  have hC : 0 ≤ C := by
    by_contra hC; push Not at hC
    have : C * (Tm * 1.2039) < 0 := mul_neg_of_neg_of_pos hC (by positivity)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hT hC, mul_le_mul_of_nonneg_left hl (mul_nonneg hC hT0.le)]

theorem c3g_nonneg {κ T0 : ℝ} (hκ : 0 ≤ κ) (hT0 : 0 < T0) : 0 ≤ c3g κ T0 :=
  div_nonneg (by positivity) (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le

theorem u_le {δ D u0 T0 q : ℝ} (hq : 0 < q) (hδ : |δ| ≤ D / q) (hu0 : 0 ≤ u0)
    (h : u0 * (3.1416 * (D / q)) ≤ T0 - 200) : δ ≠ 0 → u0 ≤ (T0 - 200) / (π * |δ|) := by
  intro hδ0
  have hpi := Real.pi_lt_d4
  have hd : 0 < |δ| := abs_pos.2 hδ0
  rw [le_div_iff₀ (by positivity)]
  have h1 : π * |δ| ≤ 3.1416 * (D / q) := mul_le_mul hpi.le hδ (abs_nonneg _) (by norm_num)
  exact (mul_le_mul_of_nonneg_left h1 hu0).trans h

/-! ## `E₁` -/

theorem E1P_le {q : ℕ} [NeZero q] {T0 Cq Z S1 S2 : ℝ} (hT0 : 0 ≤ T0) (hA : T0 + 3.48 ≤ Cq / q)
    (hZ : ZL q T0 ≤ Z) (hS1 : 2 * 3.1416 * 0.6403 * (2 * Cq) ≤ S1 ^ 2)
    (hS2 : 2 * 3.1416 * 1.129 * (2 * Cq) ≤ S2 ^ 2) (hS1p : 0 ≤ S1) (hS2p : 0 ≤ S2) :
    E1g (BP q) T0 (2 * π * 0.6403) (2 * π * 1.129) ≤ Z * (S1 / 3.48 + S2) / √q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs0 : 0 < √(q:ℝ) := Real.sqrt_pos.2 hq0
  set A := (Jl T0 : ℝ) * 3.48 with hAdef
  have hA1 : A ≤ T0 + 3.48 := by
    rw [hAdef]; unfold Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ T0 / 3.48 by positivity)
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hA2 : A ≤ Cq / q := hA1.trans hA
  have hA0 : 0 ≤ A := by positivity
  have hCq : 0 ≤ Cq := by
    have := hA0.trans hA2
    rwa [le_div_iff₀ hq0, zero_mul] at this
  have hpi := Real.pi_lt_d4
  have hsq : ∀ c K : ℝ, 0 ≤ c → 0 ≤ K → 2 * 3.1416 * c * (2 * Cq) ≤ K ^ 2 →
      √(2 * π * c * (2 * A)) ≤ K / √q := by
    intro c K hc hK h
    have h1 : 2 * π * c * (2 * A) ≤ K ^ 2 / q := by
      calc 2 * π * c * (2 * A) ≤ 2 * 3.1416 * c * (2 * (Cq / q)) := by gcongr
        _ = (2 * 3.1416 * c * (2 * Cq)) / q := by ring
        _ ≤ K ^ 2 / q := div_le_div_of_nonneg_right h hq0.le
    calc √(2 * π * c * (2 * A)) ≤ √(K ^ 2 / q) := Real.sqrt_le_sqrt h1
      _ = K / √q := by rw [Real.sqrt_div' _ hq0.le, Real.sqrt_sq hK]
  have h1 := hsq 0.6403 S1 (by norm_num) hS1p hS1
  have h2 := hsq 1.129 S2 (by norm_num) hS2p hS2
  have hZ0 := Explicit.ZL_nonneg q T0
  show ZL q T0 * ((1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A))) ≤ _
  have hX : (1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)) ≤
      (S1 / 3.48 + S2) / √q := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 3.48)
    have e : (1 / 3.48) * (S1 / √q) + S2 / √q = (S1 / 3.48 + S2) / √q := by field_simp
    linarith
  have hX0 : 0 ≤ (1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)) := by positivity
  calc ZL q T0 * ((1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)))
      ≤ Z * ((S1 / 3.48 + S2) / √q) := mul_le_mul hZ hX hX0 (hZ0.trans hZ)
    _ = Z * (S1 / 3.48 + S2) / √q := by ring

theorem log825_le : Real.log 825.48 ≤ 6.7162 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 6 (u := 0.7162) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log1018_le : Real.log 1018.1 ≤ 6.926 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 6 (u := 0.926) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem logBP_R3_le {q : ℕ} [NeZero q] (hq3 : q ≤ 300000) {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ 803.48) :
    Real.log (BP q T / 0.355) ≤ 210.46 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  rw [Explicit.log_BP_eq, abs_of_nonneg hT0]
  have hl1 : Real.log q ≤ 12.62 := (Real.log_le_log hq0 hq3').trans log_3e5_le
  have hl2 : Real.log (q + 1) ≤ 12.62 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log300001_le
  have h3 : Real.log (T + 22) ≤ 6.7162 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log825_le
  have h4 : Real.log (1.25 * (T + 11)) ≤ 6.926 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log1018_le
  have := log1400_le
  have := neg_log0355_le
  linarith

theorem ZL_R3_le {q : ℕ} [NeZero q] (hq1 : 125000 < q) (hq3 : q ≤ 300000) :
    ZL q (200 + 7.5e7 / q) ≤ 143.21 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1' : (125000:ℝ) < q := by exact_mod_cast hq1
  have hT : 7.5e7 / (q:ℝ) ≤ 600 := by rw [div_le_iff₀ hq0]; linarith
  unfold ZL
  have h := logBP_R3_le hq3 (T := 200 + 7.5e7 / q + 3.48) (by positivity) (by linarith)
  have hl := log_ratio_23_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.log_BP_pos q (200 + 7.5e7 / q + 3.48)]

theorem Z3_R3_le {q : ℕ} [NeZero q] (hq1 : 125000 < q) (hq3 : q ≤ 300000) :
    Z3 q (200 + 7.5e7 / q) ≤ 174.82 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1' : (125000:ℝ) < q := by exact_mod_cast hq1
  have hT : 7.5e7 / (q:ℝ) ≤ 600 := by rw [div_le_iff₀ hq0]; linarith
  unfold Z3
  have h := logBP_R3_le hq3 (T := 200 + 7.5e7 / q) (by positivity) (by linarith)
  have hl := log_ratio_3_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.log_BP_pos q (200 + 7.5e7 / q)]

/-! ## `E₂` in the four ranges -/

theorem E2_R1 {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq : q ≤ 150000) {δ : ℝ} (hδ : |δ| ≤ 600000 / q) :
    E2g (BP q) 11 (1e8 / q) (Cg * (2 * aH) * EB (1e8 / q - 200))
      (Cg * (2 * aH) * EA (1e8 / q - 200) δ) rhoB (rhoA δ) ≤ 1e-18 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq' : (q:ℝ) ≤ 150000 := by exact_mod_cast hq
  have hT : (666.66:ℝ) ≤ 1e8 / q := by rw [le_div_iff₀ hq0]; nlinarith
  have hD : |δ| ≤ 300000 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  refine (E2_gen_le (T1 := 466) (u0 := 26.5) (Z := 177.26) (C := 0.0604) (IA := 1.11e5) (EBb := 5e-30)
    (EAb := 4.13e-30) (by norm_num) (by linarith) (EBb_small (by norm_num) (by norm_num)) (by norm_num)
    (u_le hq0 hδ (by norm_num) ?_) EAb_265 (Explicit.Z3_nonneg q _) (Z3_le hq2 (by omega))
    (c3g_nonneg (by norm_num) (by linarith)) (c3g_le (by norm_num) (by norm_num) hT (by norm_num))
    (IA_le hD (by norm_num))).trans (by norm_num)
  rw [show (26.5 : ℝ) * (3.1416 * (600000 / q)) = (26.5 * 3.1416 * 600000) / q by ring,
    show (1e8 : ℝ) / q - 200 = (1e8 - 200 * q) / q by field_simp]
  exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

theorem E2_R2s {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq : q ≤ 60000) {δ : ℝ} (hδ : |δ| ≤ 1200000 / q) :
    E2g (BP q) 11 (1e8 / q) (Cg * (2 * aH) * EB (1e8 / q - 200))
      (Cg * (2 * aH) * EA (1e8 / q - 200) δ) rhoB (rhoA δ) ≤ 2e-11 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq' : (q:ℝ) ≤ 60000 := by exact_mod_cast hq
  have hT : (1666.66:ℝ) ≤ 1e8 / q := by rw [le_div_iff₀ hq0]; nlinarith
  have hD : |δ| ≤ 600000 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  refine (E2_gen_le (T1 := 600) (u0 := 23.3) (Z := 177.26) (C := 0.0242) (IA := 2.22e5) (EBb := 6e-30)
    (EAb := 6e-23) (by norm_num) (by linarith) (EBb_small (by norm_num) (by norm_num)) (by norm_num)
    (u_le hq0 hδ (by norm_num) ?_) EAb_233 (Explicit.Z3_nonneg q _) (Z3_le hq2 (by omega))
    (c3g_nonneg (by norm_num) (by linarith)) (c3g_le (by norm_num) (by norm_num) hT (by norm_num))
    (IA_le hD (by norm_num))).trans (by norm_num)
  rw [show (23.3 : ℝ) * (3.1416 * (1200000 / q)) = (23.3 * 3.1416 * 1200000) / q by ring,
    show (1e8 : ℝ) / q - 200 = (1e8 - 200 * q) / q by field_simp]
  exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

theorem E2_R2m {q : ℕ} [NeZero q] (hq1 : 60000 ≤ q) (hq : q ≤ 125000) {δ : ℝ}
    (hδ : |δ| ≤ 1200000 / q) :
    E2g (BP q) 11 (1e8 / q) (Cg * (2 * aH) * EB (1e8 / q - 200))
      (Cg * (2 * aH) * EA (1e8 / q - 200) δ) rhoB (rhoA δ) ≤ 4.84e-11 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1' : (60000:ℝ) ≤ q := by exact_mod_cast hq1
  have hq' : (q:ℝ) ≤ 125000 := by exact_mod_cast hq
  have hT : (800:ℝ) ≤ 1e8 / q := by rw [le_div_iff₀ hq0]; nlinarith
  have hD : |δ| ≤ 20 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  refine (E2_gen_le (T1 := 600) (u0 := 19.89) (Z := 177.26) (C := 0.0503) (IA := 8.77) (EBb := 6e-30)
    (EAb := 1.2e-16) (by norm_num) (by linarith) (EBb_small (by norm_num) (by norm_num)) (by norm_num)
    (u_le hq0 hδ (by norm_num) ?_) EAb_1989 (Explicit.Z3_nonneg q _) (Z3_le (by omega) (by omega))
    (c3g_nonneg (by norm_num) (by linarith)) (c3g_le (by norm_num) (by norm_num) hT (by norm_num))
    (IA_le hD (by norm_num))).trans (by norm_num)
  rw [show (19.89 : ℝ) * (3.1416 * (1200000 / q)) = (19.89 * 3.1416 * 1200000) / q by ring,
    show (1e8 : ℝ) / q - 200 = (1e8 - 200 * q) / q by field_simp]
  exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

theorem E2_R3 {q : ℕ} [NeZero q] (hq1 : 125000 < q) (hq : q ≤ 300000) {δ : ℝ}
    (hδ : |δ| ≤ 1200000 / q) :
    E2g (BP q) 11 (200 + 7.5e7 / q) (Cg * (2 * aH) * EB (200 + 7.5e7 / q - 200))
      (Cg * (2 * aH) * EA (200 + 7.5e7 / q - 200) δ) rhoB (rhoA δ) ≤ 1.2524e-10 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1' : (125000:ℝ) < q := by exact_mod_cast hq1
  have hq' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq
  have hT250 : (250:ℝ) ≤ 7.5e7 / q := by rw [le_div_iff₀ hq0]; nlinarith
  have hT : (450:ℝ) ≤ 200 + 7.5e7 / q := by linarith
  have hD : |δ| ≤ 9.6 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  have hEB : 0.892 * ((250:ℝ) * Real.exp (-(0.1598 * 250))) ≤ 1e-15 := by
    have := exp_neg_3995_le
    nlinarith
  refine (E2_gen_le (T1 := 250) (u0 := 19.89) (Z := 174.82) (C := 0.0894) (IA := 4.922) (EBb := 1e-15)
    (EAb := 1.2e-16) (by norm_num) (by linarith) hEB (by norm_num)
    (u_le hq0 hδ (by norm_num) ?_) EAb_1989 (Explicit.Z3_nonneg q _) (Z3_R3_le hq1 hq)
    (c3g_nonneg (by norm_num) (by linarith)) (c3g_le (by norm_num) (by norm_num) hT (by norm_num))
    (IA_le hD (by norm_num))).trans (by norm_num)
  rw [show (19.89 : ℝ) * (3.1416 * (1200000 / q)) = (19.89 * 3.1416 * 1200000) / q by ring,
    show (200 + 7.5e7 / q - 200 : ℝ) = 7.5e7 / q by ring]
  exact div_le_div_of_nonneg_right (by norm_num) hq0.le

/-! ## The errors -/

theorem sqrt_x_ge' {x : ℝ} (hx : 4.9e26 ≤ x) : 2.2135e13 ≤ √x :=
  Real.le_sqrt_of_sq_le (by nlinarith)

theorem combine_err {s y a b c d K : ℝ} (hs : 0 < s) (hy : 0 < y) (ha : a ≤ 1e-17 / s) (hb : b ≤ K / s)
    (hK : K ≤ 7.66e6) (hc : c ≤ 6.9e-8 / s) (hd : d ≤ 1e-17 / s) :
    a + b / y + c + d ≤ (7.5e-8 + 7.7e6 / y) / s := by
  have hb' : b / y ≤ K / s / y := div_le_div_of_nonneg_right hb hy.le
  have h1 : K / s / y ≤ 7.7e6 / y / s := by
    rw [div_div, div_div, mul_comm s y]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : 1e-17 / s + 6.9e-8 / s + 1e-17 / s ≤ 7.5e-8 / s := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hs.le
  rw [add_div]
  linarith

/-- **The error for `q ≥ 2`**, given `E₁ ≤ K/√q` and `E₂ ≤ E₂'`, `547.73 E₂' ≤ 6.9·10⁻⁸`. -/
theorem errP_le_of {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} [NeZero q] (hq3 : q ≤ 300000) {T0 δ K E2b : ℝ}
    (hδ : |δ| ≤ 6e5)
    (hE1 : E1g (BP q) T0 (2 * π * 0.6403) (2 * π * 1.129) ≤ K / √q) (hK : K ≤ 7.66e6)
    (hE2 : E2g (BP q) 11 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB
      (rhoA δ) ≤ E2b) (hE2b : E2b * 547.73 ≤ 6.9e-8) :
    errP q T0 δ x ≤ (7.5e-8 + 7.7e6 / √x) / √q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  have hs : 0 < √(q:ℝ) := Real.sqrt_pos.2 hq0
  have hsq : √(q:ℝ) ≤ 547.73 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hx0 : 0 < x := by linarith
  have hsx := sqrt_x_ge' hx
  have hinv : ∀ c : ℝ, 0 ≤ c → c / 547.73 ≤ c / √q := fun c hc =>
    div_le_div_of_nonneg_left hc hs hsq
  -- `E₀`
  have hZ : Z3g (BP q) 0 ≤ 136.61 := by
    have h := E0b_le (q := q) hq3
    unfold Explicit.E0b at h
    unfold Z3g
    linarith
  have hZ0 : 0 ≤ Z3g (BP q) 0 := Explicit.Z3_nonneg q 0
  have ha : Cg * 300 * (2 * aH) * Z3g (BP q) 0 / x ≤ 1e-17 / √q := by
    refine le_trans ?_ (hinv _ (by norm_num))
    have hc := cE0_le
    have hc0 : 0 ≤ Cg * 300 * (2 * aH) := by have := cA_nonneg; nlinarith
    have h1 : Cg * 300 * (2 * aH) * Z3g (BP q) 0 ≤ 38772 * 136.61 := mul_le_mul hc hZ hZ0 (by norm_num)
    rw [div_le_iff₀ hx0]
    have : 1e-17 / 547.73 * 4.9e26 ≤ 1e-17 / 547.73 * x := mul_le_mul_of_nonneg_left hx (by norm_num)
    have : (38772 * 136.61 : ℝ) ≤ 1e-17 / 547.73 * 4.9e26 := by norm_num
    linarith
  -- the vertical line
  have hV := VgL_le (Explicit.DN_nonneg q) (DN_le hq3) hδ
  have hV0 : 0 ≤ VgL (DN q) (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) := by
    unfold VgL
    have := cKv_nonneg; have := log2_const_nonneg; have := Explicit.DN_nonneg q
    have := Explicit.thP_pos δ
    positivity
  have hd : VgL (DN q) (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π * (x * √x)) ≤
      1e-17 / √q := by
    refine le_trans ?_ (hinv _ (by norm_num))
    have hpi := Real.pi_gt_three
    have hxx : 1e26 * 2e13 ≤ x * √x := mul_le_mul (by linarith) (by linarith) (by norm_num) hx0.le
    rw [div_le_iff₀ (by positivity)]
    have : 1e-17 / 547.73 * (2 * 3 * (1e26 * 2e13)) ≤ 1e-17 / 547.73 * (2 * π * (x * √x)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); nlinarith
    have : (2e19 : ℝ) ≤ 1e-17 / 547.73 * (2 * 3 * (1e26 * 2e13)) := by norm_num
    linarith
  have hc : E2g (BP q) 11 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB
      (rhoA δ) ≤ 6.9e-8 / √q := by
    refine hE2.trans (le_trans ?_ (hinv _ (by norm_num)))
    rw [le_div_iff₀ (by norm_num)]; exact hE2b
  unfold errP
  exact combine_err hs (by linarith) ha hE1 hK hc hd

/-- **The error for `q = 1`** at `T₀ = 10⁸`. -/
theorem errPZ_le {x : ℝ} (hx : 4.9e26 ≤ x) {δ : ℝ} (hδ : |δ| ≤ 6e5) :
    errPZ 1e8 δ x ≤ 1e-18 + 6.24e6 / √x := by
  have hx0 : 0 < x := by linarith
  have hsx := sqrt_x_ge' hx
  -- `E₁`
  have hE1 : E1g BPz2 1e8 (2 * π * 0.6403) (2 * π * 1.129) ≤ 6.24e6 := by
    set A := (Jl 1e8 : ℝ) * 3.48 with hA
    have hA1 : A ≤ 1e8 + 3.48 := by
      rw [hA]; unfold Jl; push_cast
      have := Nat.floor_le (show (0:ℝ) ≤ 1e8 / 3.48 by positivity)
      rw [le_div_iff₀ (by norm_num)] at this
      linarith
    have hA0 : 0 ≤ A := by positivity
    have hpi := Real.pi_lt_d4
    have h1 : √(2 * π * 0.6403 * (2 * A)) ≤ 28367 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
    have h2 : √(2 * π * 1.129 * (2 * A)) ≤ 37667 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
    have hZ := ZLz_le
    have hZ0 : 0 ≤ ZLg BPz2 1e8 :=
      div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le
        (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
    unfold E1g
    rw [← hA]
    have hX : (1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)) ≤ 45818.5 := by
      have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 3.48)
      norm_num at this ⊢; linarith
    have hX0 : 0 ≤ (1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)) := by
      positivity
    calc ZLg BPz2 1e8 * ((1 / 3.48) * √(2 * π * 0.6403 * (2 * A)) + √(2 * π * 1.129 * (2 * A)))
        ≤ 136.1 * 45818.5 := mul_le_mul hZ hX hX0 (by norm_num)
      _ ≤ 6.24e6 := by norm_num
  -- `E₂`
  have hD : |δ| ≤ 6e5 / (1:ℝ) := by simpa using hδ
  have hZ0 : 0 ≤ Z3g BPz2 1e8 :=
    div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  have hE2 : E2g BPz2 10 1e8 (Cg * (2 * aH) * EB (1e8 - 200)) (Cg * (2 * aH) * EA (1e8 - 200) δ) rhoB
      (rhoA δ) ≤ 1e-19 := by
    refine (E2_gen_le (T1 := 1000) (u0 := 26.5) (Z := 166.2) (C := 3.66e-7) (IA := 2.22e5) (EBb := 9e-30)
      (EAb := 4.13e-30) (by norm_num) (by norm_num) (EBb_small (by norm_num) (by norm_num)) (by norm_num)
      (u_le one_pos hD (by norm_num) (by norm_num)) EAb_265 hZ0 Z3z_le
      (c3g_nonneg (by norm_num) (by norm_num)) (c3g_le (by norm_num) (by norm_num) le_rfl (by norm_num))
      (IA_le hδ (by norm_num))).trans (by norm_num)
  -- `E₀`, `V`
  have hZ : Z3g BPz2 0 ≤ 33.23 := by
    unfold Z3g
    have h := log_BPz2_zero_le
    have hl := log_ratio_3_ge
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Explicit.polyDatum_zeta2.log_pos 0]
  have hZ00 : 0 ≤ Z3g BPz2 0 :=
    div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  have ha : Cg * 300 * (2 * aH) * Z3g BPz2 0 / x ≤ 1e-20 := by
    have hc := cE0_le
    have hc0 : 0 ≤ Cg * 300 * (2 * aH) := by have := cA_nonneg; nlinarith
    have h1 : Cg * 300 * (2 * aH) * Z3g BPz2 0 ≤ 38772 * 33.23 := mul_le_mul hc hZ hZ00 (by norm_num)
    rw [div_le_iff₀ hx0]
    nlinarith
  have hV := VgL_le (D := 3) (by norm_num) (by norm_num) hδ
  have hd : VgL 3 (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π * (x * √x)) ≤ 1e-20 := by
    have hpi := Real.pi_gt_three
    have hxx : 1e26 * 2e13 ≤ x * √x := mul_le_mul (by linarith) (by linarith) (by norm_num) hx0.le
    rw [div_le_iff₀ (by positivity)]
    have : 1e-20 * (2 * 3 * (1e26 * 2e13)) ≤ 1e-20 * (2 * π * (x * √x)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); nlinarith
    have : (2e19 : ℝ) ≤ 1e-20 * (2 * 3 * (1e26 * 2e13)) := by norm_num
    linarith
  have hb : E1g BPz2 1e8 (2 * π * 0.6403) (2 * π * 1.129) / √x ≤ 6.24e6 / √x :=
    div_le_div_of_nonneg_right hE1 (Real.sqrt_nonneg _)
  unfold errPZ
  linarith

/-! ## [B, Thm 7.1.4] -/

theorem hT0_of {q δ D T0 : ℝ} (hq : 0 < q) (hδ : |δ| ≤ D / q) (h1 : 10 * 3.1416 * D / q ≤ T0 - 200)
    (h2 : 250 ≤ T0) : 200 + max (10 * π * |δ|) 50 ≤ T0 := by
  have hpi := Real.pi_lt_d4
  have : 10 * π * |δ| ≤ 10 * 3.1416 * (D / q) :=
    mul_le_mul (by linarith) hδ (abs_nonneg _) (by norm_num)
  have e : 10 * 3.1416 * (D / q) = 10 * 3.1416 * D / q := by ring
  have := max_le (show 10 * π * |δ| ≤ T0 - 200 by linarith) (show (50:ℝ) ≤ T0 - 200 by linarith)
  linarith

/-- **[B, Thm 7.1.4], `q = 1`** (our constants), from `prop_9_4_2` at `T₀ = 10⁸` and Platt's
verification: for `x ≥ 4.9·10²⁶`, `|δ| ≤ 6·10⁵`, `S_{η₊}(δ/x, x) = η̂₊(-δ) x + E x`,
`|E| ≤ 10⁻¹⁸ + 6.24·10⁶/√x`. -/
theorem thm_7_1_4_one {x : ℝ} (hx : 4.9e26 ≤ x) (χ : DirichletCharacter ℂ 1) {δ : ℝ}
    (hδ : |δ| ≤ 600000) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x‖ ≤ (1e-18 + 6.24e6 / √x) * x := by
  have hχ : χ.IsPrimitive := by
    rw [Subsingleton.elim χ 1]; exact DirichletCharacter.isPrimitive_one_level_one
  have hT0 : 200 + max (10 * π * |δ|) 50 ≤ (1e8 : ℝ) :=
    hT0_of (q := 1) one_pos (by simpa using hδ) (by norm_num) (by norm_num)
  have hG : GRHUpTo χ 1e8 := by
    have := platt_odd (q := 1) odd_one (by norm_num) χ hχ
    simpa using this
  have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 hG
  simp only [ite_true] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  unfold err942N
  simp only [ite_true]
  exact errPZ_le hx (by linarith)

/-- **[B, Thm 7.1.4], odd `q ≤ 150000`** (Platt's verification at `10⁸/q`), our constants:
`|E| ≤ (7.5·10⁻⁸ + 7.7·10⁶/√x)/√q` for `x ≥ 4.9·10²⁶`, `|δ| ≤ 6·10⁵/q`. -/
theorem thm_7_1_4_odd {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} [NeZero q] (hodd : Odd q) (hq : q ≤ 150000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 600000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤
      ((7.5e-8 + 7.7e6 / √x) / √q) * x := by
  have hx0 : 0 < x := by linarith
  have hsx := sqrt_x_ge' hx
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hq1 : q = 1
  · subst hq1
    rw [if_pos rfl]
    refine (thm_7_1_4_one hx χ (by simpa using hδ)).trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
    simp only [Nat.cast_one, Real.sqrt_one, div_one]
    have : 6.24e6 / √x ≤ 7.7e6 / √x := div_le_div_of_nonneg_right (by norm_num) (by linarith)
    linarith
  have hq3 : 3 ≤ q := by obtain ⟨k, hk⟩ := hodd; omega
  have hq2 : 2 ≤ q := by omega
  have hq3' : (3:ℝ) ≤ q := by exact_mod_cast hq3
  have hq' : (q:ℝ) ≤ 150000 := by exact_mod_cast hq
  have hT0 : 200 + max (10 * π * |δ|) 50 ≤ 1e8 / q := by
    refine hT0_of hq0 hδ ?_ (by rw [le_div_iff₀ hq0]; nlinarith)
    rw [show (1e8 : ℝ) / q - 200 = (1e8 - 200 * q) / q by field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith) hq0.le
  have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 (platt_odd hodd (by omega) χ hχ)
  rw [if_neg hq1] at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
  unfold err942N
  rw [if_neg hq1]
  have hD : |δ| ≤ 6e5 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  refine errP_le_of hx (by omega) hD (E1P_le (Cq := 1.010467e8) (Z := 145.21) (S1 := 28515) (S2 := 37864)
    (by positivity) ?_ (ZL_le hq2 (by omega)) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (E2_R1 hq2 hq hδ) (by norm_num)
  rw [show (1e8 : ℝ) / q + 3.48 = (1e8 + 3.48 * q) / q by field_simp]
  exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

/-- **[B, Thm 7.1.4], even `q ≤ 300000`** (Platt's verification at `max(10⁸/q, 200 + 7.5·10⁷/q)`), our
constants: `|E| ≤ (7.5·10⁻⁸ + 7.7·10⁶/√x)/√q` for `x ≥ 4.9·10²⁶`, `|δ| ≤ 1.2·10⁶/q`. -/
theorem thm_7_1_4_even {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} [NeZero q] (heven : Even q) (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 1200000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤
      ((7.5e-8 + 7.7e6 / √x) / √q) * x := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : 2 ≤ q := by obtain ⟨k, hk⟩ := heven; have := NeZero.ne q; omega
  have hq1 : q ≠ 1 := by omega
  have hq' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hD : |δ| ≤ 6e5 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  by_cases h125 : q ≤ 125000
  · have h125' : (q:ℝ) ≤ 125000 := by exact_mod_cast h125
    have hT0 : 200 + max (10 * π * |δ|) 50 ≤ 1e8 / q := by
      refine hT0_of hq0 hδ ?_ (by rw [le_div_iff₀ hq0]; nlinarith)
      rw [show (1e8 : ℝ) / q - 200 = (1e8 - 200 * q) / q by field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith) hq0.le
    have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 (platt_grh hq χ hχ)
    rw [if_neg hq1] at h ⊢
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
    unfold err942N
    rw [if_neg hq1]
    have hE1 := E1P_le (q := q) (T0 := 1e8 / q) (Cq := 1.010467e8) (Z := 145.21) (S1 := 28515) (S2 := 37864)
      (by positivity) (by
        rw [show (1e8 : ℝ) / q + 3.48 = (1e8 + 3.48 * q) / q by field_simp]
        exact div_le_div_of_nonneg_right (by nlinarith) hq0.le)
      (ZL_le hq2 hq) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    by_cases h60 : q ≤ 60000
    · exact errP_le_of hx hq hD hE1 (by norm_num) (E2_R2s hq2 h60 hδ) (by norm_num)
    · exact errP_le_of hx hq hD hE1 (by norm_num) (E2_R2m (by omega) h125 hδ) (by norm_num)
  · have h125' : (125000:ℝ) < q := by exact_mod_cast (not_le.1 h125)
    have hT0 : 200 + max (10 * π * |δ|) 50 ≤ 200 + 7.5e7 / q := by
      refine hT0_of hq0 hδ ?_ (by
        have : (250:ℝ) ≤ 7.5e7 / q := by rw [le_div_iff₀ hq0]; nlinarith
        linarith)
      rw [show (200 + 7.5e7 / q - 200 : ℝ) = 7.5e7 / q by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hq0.le
    have hG : GRHUpTo χ (200 + 7.5e7 / q) :=
      (platt_even heven (by omega) χ hχ).mono (le_max_right _ _)
    have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 hG
    rw [if_neg hq1] at h ⊢
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
    unfold err942N
    rw [if_neg hq1]
    refine errP_le_of hx hq hD (E1P_le (Cq := 1.36044e8) (Z := 143.21) (S1 := 33086) (S2 := 43934)
      (by positivity) ?_ (ZL_R3_le (not_le.1 h125) hq) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num) (E2_R3 (not_le.1 h125) hq hδ) (by norm_num)
    rw [show (200 + 7.5e7 / q + 3.48 : ℝ) = (203.48 * q + 7.5e7) / q by field_simp; ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

end TernaryGoldbach.MajorArcs
