import TernaryGoldbach.MajorArcs.HHFourier
import TernaryGoldbach.MajorArcs.Prop715

/-!
# `‖η₊‖₂²` and `∫_{|ξ|<T} |η̂₊(ξ)|² dξ`

* `‖η₊‖₂² = 0.640206 + O*(1.951·10⁻⁶)`: from the numerical axiom `integral_etaPlus_sq_log` ([B, (9.94)]),
  letting `x → ∞` (`∫ η₊² log(xt) = (log x) ‖η₊‖₂² + ∫ η₊² log t`).
* For `T ≥ 4`: `‖η₊‖₂² − 0.001 ≤ ∫_{|ξ|<T} |η̂₊|² ≤ ‖η₊‖₂²` (Plancherel; the tail is at most
  `2·98/(2πT)⁴ + 2‖η₊ − η◦‖₂²`, `EtaCirc.lean`, `HHFourier.lean`).
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (etaPlus)

theorem abs_log_le {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 1 / t := by
  rw [abs_le]; constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
    rw [Real.log_inv] at this
    have : 0 < t := ht
    rw [one_div]; linarith
  · have := Real.log_le_sub_one_of_pos ht
    have : 0 < 1 / t := by positivity
    linarith

theorem sq_mul_exp_le (t : ℝ) : t ^ 2 * Real.exp (-t ^ 2 / 2) ≤ 2 := by
  have h := Real.add_one_le_exp (t ^ 2 / 2)
  have he : Real.exp (-t ^ 2 / 2) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show -t ^ 2 / 2 + t ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hpos := Real.exp_pos (-t ^ 2 / 2)
  nlinarith [sq_nonneg t]

/-- `η₊(t)² |log t| ≤ 2·3.15² · t e^{-t²/2}` on `t > 0`. -/
theorem sq_etaPlus_mul_abs_log_le {t : ℝ} (ht : 0 < t) :
    etaPlus t ^ 2 * |Real.log t| ≤ 2 * 3.15 ^ 2 * 3 * (t * Real.exp (-(1 / 2) * t ^ 2)) := by
  have hg : 0 ≤ t * Real.exp (-(1 / 2) * t ^ 2) := by positivity
  have h1 : |etaPlus t| ≤ 3.15 * (t * Real.exp (-(1 / 2) * t ^ 2)) := by
    have := abs_etaPlus_le_gauss t
    rwa [abs_of_nonneg hg] at this
  have h2 : etaPlus t ^ 2 ≤ 3.15 ^ 2 * (t * Real.exp (-(1 / 2) * t ^ 2)) ^ 2 := by
    rw [← sq_abs, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hl := abs_log_le ht
  -- `(t e^{-t²/2})² (t + 1/t) = t e^{-t²/2} · (t² e^{-t²/2} + e^{-t²/2})`
  have hE : Real.exp (-(1 / 2) * t ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE0 := Real.exp_pos (-(1 / 2) * t ^ 2)
  have h3 : t ^ 2 * Real.exp (-(1 / 2) * t ^ 2) ≤ 2 := by
    have := sq_mul_exp_le t; rwa [show -t ^ 2 / 2 = -(1 / 2) * t ^ 2 by ring] at this
  have key : (t * Real.exp (-(1 / 2) * t ^ 2)) ^ 2 * (t + 1 / t) ≤
      3 * (t * Real.exp (-(1 / 2) * t ^ 2)) := by
    have e : (t * Real.exp (-(1 / 2) * t ^ 2)) ^ 2 * (t + 1 / t) =
        (t * Real.exp (-(1 / 2) * t ^ 2)) * (t ^ 2 * Real.exp (-(1 / 2) * t ^ 2) +
          Real.exp (-(1 / 2) * t ^ 2)) := by field_simp
    rw [e, mul_comm 3]
    exact mul_le_mul_of_nonneg_left (by linarith) hg
  calc etaPlus t ^ 2 * |Real.log t| ≤ 3.15 ^ 2 * (t * Real.exp (-(1 / 2) * t ^ 2)) ^ 2 * (t + 1 / t) :=
        mul_le_mul h2 hl (abs_nonneg _) (by positivity)
    _ ≤ 3.15 ^ 2 * (3 * (t * Real.exp (-(1 / 2) * t ^ 2))) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left key (by norm_num)
    _ ≤ 2 * 3.15 ^ 2 * 3 * (t * Real.exp (-(1 / 2) * t ^ 2)) := by nlinarith

theorem integrableOn_sq_etaPlus : IntegrableOn (fun t => etaPlus t ^ 2) (Ioi 0) := by
  have h := (memLp_two_iff_integrable_sq_norm measurable_etaPlus.aestronglyMeasurable).1 memLp_etaPlus
  refine (h.integrableOn).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.norm_eq_abs, sq_abs]

theorem integrableOn_sq_etaPlus_log : IntegrableOn (fun t => etaPlus t ^ 2 * Real.log t) (Ioi 0) := by
  have hg : Integrable fun t : ℝ => 2 * 3.15 ^ 2 * 3 * (t * Real.exp (-(1 / 2) * t ^ 2)) :=
    (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul _
  refine Integrable.mono' hg.integrableOn
    ((measurable_etaPlus.pow_const 2).mul Real.measurable_log).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact sq_etaPlus_mul_abs_log_le ht

theorem integral_sq_etaPlus_eq_Ioi : ∫ t, etaPlus t ^ 2 = ∫ t in Ioi 0, etaPlus t ^ 2 := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
  rw [etaPlus_of_nonpos (not_lt.1 ht)]; ring

/-- **`‖η₊‖₂² = 0.640206 + O*(1.951·10⁻⁶)`** (from the numerical axiom `integral_etaPlus_sq_log`). -/
theorem abs_integral_sq_etaPlus_sub_le :
    |(∫ t, etaPlus t ^ 2) - 0.640206| ≤ 1.951e-6 := by
  rw [integral_sq_etaPlus_eq_Ioi]
  set A := ∫ t in Ioi 0, etaPlus t ^ 2
  set B := ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log t
  have hlin : ∀ x : ℝ, 0 < x →
      ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t) = Real.log x * A + B := by
    intro x hx
    rw [← integral_const_mul, ← integral_add (integrableOn_sq_etaPlus.const_mul _)
      integrableOn_sq_etaPlus_log]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.log_mul hx.ne' ht0.ne']; ring
  have h1 := MajorArcs.integral_etaPlus_sq_log (x := 1) le_rfl
  rw [hlin 1 one_pos, Real.log_one] at h1
  norm_num at h1
  set L : ℝ := 1e6
  have hx : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by norm_num)
  have h2 := MajorArcs.integral_etaPlus_sq_log hx
  rw [hlin _ (Real.exp_pos L), Real.log_exp] at h2
  -- `|L (A - 0.640206) + (B + 0.021095)| ≤ 1.95e-6 L + 5.3e-7`, `|B + 0.021095| ≤ 5.3e-7`
  have hL : (0 : ℝ) < L := by norm_num
  rw [abs_le] at h1 h2 ⊢
  constructor
  · by_contra hc
    push Not at hc
    nlinarith
  · by_contra hc
    push Not at hc
    nlinarith

theorem integral_sq_etaPlus_bounds :
    0.640204 ≤ ∫ t, etaPlus t ^ 2 ∧ ∫ t, etaPlus t ^ 2 ≤ 0.640208 := by
  have := abs_integral_sq_etaPlus_sub_le
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

/-! ## The truncated `L²` norm of `η̂₊` -/

/-- `η₊` as a complex function. -/
noncomputable def etaPC (t : ℝ) : ℂ := (etaPlus t : ℂ)

/-- `η◦` as a complex function. -/
noncomputable def etaOC (t : ℝ) : ℂ := (etaO t : ℂ)

theorem integrable_etaPC : Integrable etaPC := integrable_etaPlus.ofReal
theorem memLp_etaPC : MemLp etaPC 2 := memLp_etaPlus.ofReal
theorem integrable_etaOC : Integrable etaOC := integrable_etaO.ofReal
theorem memLp_etaOC : MemLp etaOC 2 := memLp_etaO.ofReal

theorem integrable_fourier_integrand {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * I) • f v) := by
  refine hf.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * I)).aestronglyMeasurable).smul
      hf.aestronglyMeasurable
  · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem fourier_sub_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 f ξ - 𝓕 g ξ = 𝓕 (fun t => f t - g t) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,
    ← integral_sub (integrable_fourier_integrand hf ξ) (integrable_fourier_integrand hg ξ)]
  congr 1; ext t; rw [smul_sub]

theorem integral_norm_sq_fourier_etaPC : ∫ ξ, ‖𝓕 etaPC ξ‖ ^ 2 = ∫ t, etaPlus t ^ 2 := by
  rw [TernaryGoldbach.integral_norm_sq_fourier integrable_etaPC memLp_etaPC]
  congr 1; ext t; rw [etaPC, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integrable_norm_sq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    Integrable fun ξ => ‖𝓕 f ξ‖ ^ 2 := by
  have h := TernaryGoldbach.memLp_fourier h1 h2
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

/-- **Tail of `η̂₊`**: `∫_{|ξ| ≥ T} |η̂₊|² ≤ 2·98/(2πT)⁴ + 19.5/200²`. -/
theorem tail_etaPlus_le {T : ℝ} (hT : 0 < T) :
    ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 etaPC ξ‖ ^ 2 ≤ 2 * (98 / (2 * π * T) ^ 4) + 19.5 / 200 ^ 2 := by
  set D : ℝ → ℂ := fun t => etaPC t - etaOC t
  have hD1 : Integrable D := integrable_etaPC.sub integrable_etaOC
  have hD2 : MemLp D 2 := memLp_etaPC.sub memLp_etaOC
  have hmeas : MeasurableSet {ξ : ℝ | T ≤ |ξ|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have iO := integrable_norm_sq_fourier integrable_etaOC memLp_etaOC
  have iD := integrable_norm_sq_fourier hD1 hD2
  have hpt : ∀ ξ, ‖𝓕 etaPC ξ‖ ^ 2 ≤ 2 * ‖𝓕 etaOC ξ‖ ^ 2 + 2 * ‖𝓕 D ξ‖ ^ 2 := by
    intro ξ
    have e : 𝓕 etaPC ξ = 𝓕 etaOC ξ + 𝓕 D ξ := by
      rw [← fourier_sub_of_integrable integrable_etaPC integrable_etaOC]; ring
    rw [e]
    have := norm_add_le (𝓕 etaOC ξ) (𝓕 D ξ)
    nlinarith [norm_nonneg (𝓕 etaOC ξ + 𝓕 D ξ), norm_nonneg (𝓕 etaOC ξ), norm_nonneg (𝓕 D ξ),
      sq_nonneg (‖𝓕 etaOC ξ‖ - ‖𝓕 D ξ‖)]
  have hDint : ∫ ξ, ‖𝓕 D ξ‖ ^ 2 ≤ 19.5 / 2 / 200 ^ 2 := by
    rw [TernaryGoldbach.integral_norm_sq_fourier hD1 hD2]
    have : (fun t => ‖D t‖ ^ 2) = fun t => (etaPlus t - etaO t) ^ 2 := by
      ext t; simp only [D, etaPC, etaOC]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this]; exact integral_sq_etaPlus_sub_etaO_le
  have hO : ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 etaOC ξ‖ ^ 2 ≤ 98 / (2 * π * T) ^ 4 := tail_etaO_le hT
  have iO2 : Integrable fun ξ => 2 * ‖𝓕 etaOC ξ‖ ^ 2 := iO.const_mul 2
  have iD2 : Integrable fun ξ => 2 * ‖𝓕 D ξ‖ ^ 2 := iD.const_mul 2
  have iOD : Integrable fun ξ => 2 * ‖𝓕 etaOC ξ‖ ^ 2 + 2 * ‖𝓕 D ξ‖ ^ 2 := iO2.add iD2
  calc ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 etaPC ξ‖ ^ 2
      ≤ ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, (2 * ‖𝓕 etaOC ξ‖ ^ 2 + 2 * ‖𝓕 D ξ‖ ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          iOD.integrableOn (Filter.Eventually.of_forall hpt)
    _ = 2 * (∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 etaOC ξ‖ ^ 2) +
          2 * ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 D ξ‖ ^ 2 := by
        rw [integral_add iO2.integrableOn iD2.integrableOn, integral_const_mul, integral_const_mul]
    _ ≤ 2 * (98 / (2 * π * T) ^ 4) + 2 * (19.5 / 2 / 200 ^ 2) := by
        gcongr
        exact (setIntegral_le_integral iD (Filter.Eventually.of_forall fun _ => by positivity)).trans hDint
    _ = 2 * (98 / (2 * π * T) ^ 4) + 19.5 / 200 ^ 2 := by ring

/-- **The main-term integral**: for `T ≥ 4`,
`0.6392 ≤ ∫_{|ξ|<T} |η̂₊(ξ)|² dξ ≤ 0.640208`. -/
theorem integral_fourier_etaPlus_Ioo_bounds {T : ℝ} (hT : 4 ≤ T) :
    0.6392 ≤ ∫ ξ in Ioo (-T) T, ‖𝓕 etaPC ξ‖ ^ 2 ∧ ∫ ξ in Ioo (-T) T, ‖𝓕 etaPC ξ‖ ^ 2 ≤ 0.640208 := by
  have hT0 : 0 < T := by linarith
  have hint := integrable_norm_sq_fourier integrable_etaPC memLp_etaPC
  have hcompl : (Ioo (-T) T)ᶜ = {ξ : ℝ | T ≤ |ξ|} := by
    ext ξ; simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_setOf_eq, le_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; exact h
    · rintro (h | h)
      · right; exact h
      · left; linarith
  have hsplit := integral_add_compl (s := Ioo (-T) T) measurableSet_Ioo hint
  rw [hcompl, integral_norm_sq_fourier_etaPC] at hsplit
  have htail := tail_etaPlus_le hT0
  have htail0 : 0 ≤ ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 etaPC ξ‖ ^ 2 :=
    setIntegral_nonneg ((isClosed_le continuous_const continuous_abs).measurableSet)
      fun _ _ => by positivity
  have hb := integral_sq_etaPlus_bounds
  have hπ := Real.pi_gt_d2
  have hc : 2 * (98 / (2 * π * T) ^ 4) ≤ 0.0005 := by
    have h1 : (25.12 : ℝ) ≤ 2 * π * T := by nlinarith
    have h2 : (25.12 : ℝ) ^ 4 ≤ (2 * π * T) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    have h3 : 98 / (2 * π * T) ^ 4 ≤ 98 / 25.12 ^ 4 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) h2
    have : (98 : ℝ) / 25.12 ^ 4 ≤ 0.00025 := by norm_num
    linarith
  constructor
  · nlinarith
  · linarith

end TernaryGoldbach.MajorArcs
