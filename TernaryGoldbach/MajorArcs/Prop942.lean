import TernaryGoldbach.MajorArcs.EtaPlusL2
import TernaryGoldbach.MajorArcs.Prop932
import TernaryGoldbach.Explicit.EtaPlusBound

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.ButhePsi] [Fact TernaryGoldbach.RamareMoebius]

/-!
# [H, Prop 9.4.2] (proved, with our constants)

For `η₊` (`H = 200`), `χ` primitive mod `q`, GRH up to `T₀ ≥ 200 + max(10π|δ|, 50)`, `x ≥ 1`:
`Σ Λ(n) χ(n) e(δn/x) η₊(n/x) = [q = 1] η̂₊(−δ) x + O*(err942N) x`, from `Explicit.norm_SsumG_fP_le`
(`q ≥ 2`) and `Explicit.norm_SsumG_fP_zeta_le` (`q = 1`), with `∫ η₊² ≤ 0.6403` (`EtaPlusL2`).
-/

open Real MeasureTheory FourierTransform Set
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (Schar)
open TernaryGoldbach.Helfgott (etaPlus)
open TernaryGoldbach.Explicit (SsumG fP Cg aH Z3g E1g E2g BP BPz2 EB EA rhoB rhoA VgL DN thP)

theorem integral_etaPlus_sq_le : ∫ v in Ioi (0:ℝ), etaPlus v ^ 2 ≤ 0.6403 := by
  have h := abs_integral_sq_etaPlus_sub_le
  rw [integral_sq_etaPlus_eq_Ioi] at h
  linarith [(abs_le.1 h).2]

theorem Schar_eq_SsumG_fP {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) :
    Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) = SsumG χ (fP δ) x := by
  unfold Schar SsumG
  congr 1; ext n
  unfold fP TernaryGoldbach.e
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * ((n : ℂ) * ((δ : ℂ) / (x : ℂ)))) =
    2 * π * Complex.I * δ * ((n : ℂ) / (x : ℂ)) by ring]
  ring

theorem mellin_fP_one (δ : ℝ) : mellin (fP δ) 1 = 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, mellin]
  set g : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * -δ) * Complex.I) • ((etaPlus v : ℝ) : ℂ) with hg
  have hR : ∫ v : ℝ, g v = ∫ v in Ioi (0:ℝ), g v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      have : u ≤ 0 := not_lt.1 hu
      simp [hg, etaPlus_of_nonpos this])).symm
  rw [hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hg, sub_self, Complex.cpow_zero, one_smul, fP, smul_eq_mul]
  push_cast; ring_nf

/-- The error term for `q ≥ 2`. -/
noncomputable def errP (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  Cg * 300 * (2 * aH) * Z3g (BP q) 0 / x + E1g (BP q) T0 (2 * π * 0.6403) (2 * π * 1.129) / √x +
    E2g (BP q) 11 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB (rhoA δ) +
    VgL (DN q) (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π * (x * √x))

/-- The error term for `q = 1`. -/
noncomputable def errPZ (T0 δ x : ℝ) : ℝ :=
  Cg * 300 * (2 * aH) * Z3g BPz2 0 / x + E1g BPz2 T0 (2 * π * 0.6403) (2 * π * 1.129) / √x +
    E2g BPz2 10 T0 (Cg * (2 * aH) * EB (T0 - 200)) (Cg * (2 * aH) * EA (T0 - 200) δ) rhoB (rhoA δ) +
    VgL 3 (Cg * (300 * Real.exp 1) * (2 * aH)) (thP δ) / (2 * π * (x * √x))

noncomputable def err942N (q : ℕ) (T0 δ x : ℝ) : ℝ := if q = 1 then errPZ T0 δ x else errP q T0 δ x

theorem rearrange {x E0 E1 E2 V : ℝ} (hx : 0 < x) :
    E0 + √x * E1 + x * E2 + x ^ (-(1 / 2) : ℝ) * V / (2 * π) =
      (E0 / x + E1 / √x + E2 + V / (2 * π * (x * √x))) * x := by
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx
  have hs : √x * √x = x := Real.mul_self_sqrt hx.le
  have hrp : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrp]
  set s := √x with hs_def
  rw [← hs]
  field_simp

/-- **[H, Prop 9.4.2]** (proved, with our constants). -/
theorem prop_9_4_2 {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0) (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤ err942N q T0 δ x * x := by
  have hx0 : 0 < x := by linarith
  unfold err942N
  rw [Schar_eq_SsumG_fP]
  by_cases hq : q = 1
  · subst hq
    have hχ1 : χ = 1 := Subsingleton.elim _ _
    subst hχ1
    simp only [if_true]; rw [← mellin_fP_one]
    have hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2 := by
      intro ρ h0 h1 h2 h3
      exact hG ρ (by rw [Explicit.LFunction_one_mod_one]; exact h0) h1 h2 h3
    refine (Explicit.norm_SsumG_fP_zeta_le δ hx hT0 hRH (by norm_num) integral_etaPlus_sq_le).trans
      (le_of_eq ?_)
    unfold errPZ
    exact rearrange hx0
  · simp only [hq, if_false, sub_zero]
    refine (Explicit.norm_SsumG_fP_le hχ (ne_one_of_primitive hq hχ) δ hx hT0
      (fun ρ h0 h1 h2 h3 => hG ρ h0 h1 h2 h3) (by norm_num) integral_etaPlus_sq_le).trans (le_of_eq ?_)
    unfold errP
    exact rearrange hx0

end TernaryGoldbach.MajorArcs
