import TernaryGoldbach.MajorArcs.Prop932
import TernaryGoldbach.MajorArcs.Eta2Moments

/-!
# [H, Cor 9.3.3] from [H, Prop 9.3.2]

`η_* = η₂ *_M η` (our `etaU`) with `η(t) = t² e^{-t²/2}`: by (9.59),
`Σ Λ(n) χ(n) e(δn/x) η_*(n/x) = ∫_{1/4}^1 S_{η,χ}(δ/x, wx) η₂(w) dw/w`, and Prop 9.3.2 at scale `wx`
(with `δ ↦ δw`) gives the main term `η̂_*(-δ) x` and the error `x ∫ err(δw, wx) η₂(w) dw`, bounded with
the moments of `η₂` (`Eta2Moments.lean`).
-/

open Real Set MeasureTheory FourierTransform Filter
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (e Schar)
open TernaryGoldbach.Helfgott (eta2 phi mellinConv etaStar κ)
open TernaryGoldbach.MinorArcs (etaU etaStar_eq_etaU integrable_phi phi_nonneg)

theorem phiPos_nonneg (t : ℝ) : 0 ≤ phiPos t := by
  unfold phiPos; split_ifs
  · exact phi_nonneg t
  · exact le_rfl

theorem phiPos_le_phi (t : ℝ) : phiPos t ≤ phi t := by
  unfold phiPos; split_ifs
  · exact le_rfl
  · exact phi_nonneg t

theorem measurable_phi : Measurable phi := by
  unfold TernaryGoldbach.Helfgott.phi; fun_prop

theorem measurable_phiPos : Measurable phiPos := by
  unfold phiPos
  exact Measurable.ite measurableSet_Ioi measurable_phi measurable_const

theorem integrable_phiPos : Integrable phiPos := by
  refine integrable_phi.mono' measurable_phiPos.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (phiPos_nonneg t)]
  exact phiPos_le_phi t

theorem eta2_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : eta2 t = 0 := by
  unfold TernaryGoldbach.Helfgott.eta2; rw [if_neg (not_lt.2 ht)]

/-- `η_*(u) = ∫_{r>0} η₂(r) η(u/r) dr/r` for all `u` (with `η` cut off at `0`). -/
theorem etaU_eq (u : ℝ) : etaU u = ∫ r in Ioi 0, eta2 r * phiPos (u / r) / r := by
  rcases le_or_gt u 0 with hu | hu
  · have h1 : etaU u = 0 := by
      unfold etaU
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ)) fun w (hw : 0 < w) => by
        simp only [eta2_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hu hw.le), zero_mul,
          zero_div]]
      simp
    rw [h1, setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ)) fun r (hr : 0 < r) => by
      unfold phiPos
      rw [if_neg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hu hr.le))]; simp]
    simp
  · have hκ : (0:ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
    have h1 : etaU u = etaStar (u / κ) := by
      rw [etaStar_eq_etaU (by positivity), mul_div_cancel₀ _ hκ.ne']
    rw [h1, etaStar, mul_div_cancel₀ _ hκ.ne', mellinConv]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    unfold phiPos; rw [if_pos (by positivity)]

/-- `η̂_*(s) = ∫_{r>0} η₂(r) η̂(rs) dr`. -/
theorem fourier_etaU (s : ℝ) :
    𝓕 (fun u => (etaU u : ℂ)) s = ∫ r in Ioi 0, (eta2 r : ℂ) * 𝓕 (fun u => (phiPos u : ℂ)) (r * s) := by
  set F : ℝ → ℝ → ℂ := fun u r => e (-(u * s)) * ((eta2 r * phiPos (u / r) / r : ℝ) : ℂ) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact (TernaryGoldbach.continuous_e.comp ((continuous_fst.mul continuous_const).neg)).measurable
    · refine Complex.measurable_ofReal.comp ?_
      exact ((TernaryGoldbach.Helfgott.continuous_eta2.measurable.comp measurable_snd).mul
        (measurable_phiPos.comp (measurable_fst.div measurable_snd))).div measurable_snd
  have hnorm : ∀ u, ∀ r, 0 < r → ‖F u r‖ = eta2 r / r * phiPos (u / r) := fun u r hr => by
    simp only [hF, norm_mul, TernaryGoldbach.norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_of_nonneg (eta2_nonneg r), abs_of_nonneg (phiPos_nonneg _),
      abs_of_pos hr]; ring
  have hIφ : ∀ r, 0 < r → ∫ u, phiPos (u / r) = r * ∫ u, phiPos u := fun r hr => by
    rw [Measure.integral_comp_div, abs_of_pos hr, smul_eq_mul]
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r (hr : 0 < r) => ?_)
      refine Integrable.mono' ((integrable_phiPos.comp_div hr.ne').const_mul (eta2 r / r)) ?_
        (Eventually.of_forall fun u => (hnorm u r hr).le)
      refine (Measurable.mul ?_ ?_).aestronglyMeasurable
      · exact (TernaryGoldbach.continuous_e.comp ((continuous_id.mul continuous_const).neg)).measurable
      · exact Complex.measurable_ofReal.comp (show Measurable fun u : ℝ => eta2 r * phiPos (u / r) / r
          from (measurable_const.mul (measurable_phiPos.comp (measurable_id.div_const r))).div_const r)
    · have h : ∀ r ∈ Ioi (0:ℝ), ∫ u, ‖Function.uncurry F (u, r)‖ = eta2 r * ∫ u, phiPos u := by
        intro r (hr : 0 < r)
        simp only [Function.uncurry_apply_pair]
        rw [integral_congr_ae (Eventually.of_forall fun u => hnorm u r hr), integral_const_mul,
          hIφ r hr]
        field_simp
      have hI := integrableOn_eta2_mul (g := fun _ => ∫ u, phiPos u) continuousOn_const
      exact hI.congr_fun (fun r hr => (h r hr).symm) measurableSet_Ioi
  have h1 : 𝓕 (fun u => (etaU u : ℂ)) s = ∫ u, ∫ r in Ioi (0:ℝ), F u r := by
    rw [TernaryGoldbach.fourier_eq_integral_e]
    congr 1; ext u
    simp only [hF, etaU_eq u]
    rw [integral_const_mul, integral_complex_ofReal]
  rw [h1, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have e1 : ∫ u, F u r = ((eta2 r / r : ℝ) : ℂ) * ∫ u, e (-(u * s)) * (phiPos (u / r) : ℂ) := by
    rw [← integral_const_mul]; congr 1; ext u; simp only [hF]; push_cast; ring
  have e2 : ∫ u, e (-(u * s)) * (phiPos (u / r) : ℂ) = (r : ℂ) * 𝓕 (fun u => (phiPos u : ℂ)) (r * s) := by
    have h := TernaryGoldbach.fourier_comp_affine (fun u => (phiPos u : ℂ)) (inv_pos.2 hr) 0 s
    rw [TernaryGoldbach.fourier_eq_integral_e] at h
    simp only [add_zero, zero_mul, zero_div, TernaryGoldbach.e_zero, one_mul, inv_inv] at h
    rw [show s / r⁻¹ = r * s by field_simp, Complex.ofReal_inv, inv_inv] at h
    rw [← h]; congr 1; ext u; rw [div_eq_inv_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [e1, e2]; push_cast; field_simp


/-! ### Bounds and summability -/

theorem phi_le_two_exp (t : ℝ) : phi t ≤ 2 * Real.exp (-t ^ 2 / 4) := by
  have h1 := Real.add_one_le_exp (t ^ 2 / 4 - 1)
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have h3 : Real.exp (t ^ 2 / 4 - 1) = Real.exp (t ^ 2 / 4) * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have ht : t ^ 2 ≤ 2 * Real.exp (t ^ 2 / 4) := by
    have : 0 < Real.exp (t ^ 2 / 4) := Real.exp_pos _
    nlinarith
  unfold TernaryGoldbach.Helfgott.phi
  have e : Real.exp (-t ^ 2 / 2) = Real.exp (-t ^ 2 / 4) * Real.exp (-t ^ 2 / 4) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (t ^ 2 / 4) * Real.exp (-t ^ 2 / 4) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [e]
  calc t ^ 2 * (Real.exp (-t ^ 2 / 4) * Real.exp (-t ^ 2 / 4))
      ≤ 2 * Real.exp (t ^ 2 / 4) * (Real.exp (-t ^ 2 / 4) * Real.exp (-t ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ = 2 * Real.exp (-t ^ 2 / 4) := by
        rw [show 2 * Real.exp (t ^ 2 / 4) * (Real.exp (-t ^ 2 / 4) * Real.exp (-t ^ 2 / 4)) =
          2 * (Real.exp (t ^ 2 / 4) * Real.exp (-t ^ 2 / 4)) * Real.exp (-t ^ 2 / 4) by ring, e2]
        ring

theorem phi_scale_le {n : ℕ} {x r : ℝ} (hx : 0 < x) (hr : 0 < r) (hr1 : r ≤ 1) :
    phi (n / (r * x)) ≤ 2 * Real.exp (-(n / x) ^ 2 / 4) := by
  refine (phi_le_two_exp _).trans ?_
  gcongr
  have h : (n / x : ℝ) ≤ n / (r * x) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity)
    nlinarith
  have h0 : (0 : ℝ) ≤ n / x := by positivity
  nlinarith

theorem summable_gauss {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4)) := by
  have h := TernaryGoldbach.Helfgott.summable_vonMangoldt_mul (η := fun t => 2 * Real.exp (-t ^ 2 / 4))
    (C := 2) (c := 1 / 4) (k := 0) hx (by norm_num) fun t _ => by
      rw [abs_of_nonneg (by positivity)]; ring_nf; exact le_rfl
  refine h.congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem summable_phi_terms {X : ℝ} (hX : 0 < X) :
    Summable fun n : ℕ => ‖((Λ n * phi (n / X) : ℝ) : ℂ)‖ :=
  TernaryGoldbach.Helfgott.summable_vonMangoldt_mul (C := 1) (c := 1 / 2) (k := 2) hX (by norm_num)
    fun t _ => by
      unfold TernaryGoldbach.Helfgott.phi
      rw [abs_of_nonneg (by positivity)]; ring_nf; exact le_rfl

theorem continuous_fourier_phiPos : Continuous (𝓕 (fun u => (phiPos u : ℂ))) := by
  have hI : Integrable (fun u => (phiPos u : ℂ)) := integrable_phiPos.ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hI

theorem norm_fourier_phiPos_le (w : ℝ) : ‖𝓕 (fun u => (phiPos u : ℂ)) w‖ ≤ ∫ u, phiPos u := by
  refine (Real.norm_fourier_le_integral_norm _ w).trans (le_of_eq ?_)
  congr 1; ext u; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phiPos_nonneg u)]


/-! ### The averaged error term -/

/-- The error term of [H, Cor 9.3.3] as obtained from (9.57) and the `η₂`-moments (we keep the
coefficient `1.578` on the `δ`-exponential, as [H, §9.6] does). -/
noncomputable def err933 (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ) +
    1.37259 * (1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / √x +
    (3 * 1.92182 + 11 * |δ|) / x + (Real.log q + 6) * (2.74517 + 6 * 1.37259 * |δ|) / (x * √x)

theorem expδ_nonneg (T0 δ : ℝ) : 0 ≤ expδ T0 δ := by
  unfold expδ; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem expδ_mono {T0 δ r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : expδ T0 (δ * r) ≤ expδ T0 δ := by
  unfold expδ
  by_cases hδ : δ = 0
  · simp [hδ]
  · have hδr : δ * r ≠ 0 := mul_ne_zero hδ hr.ne'
    rw [if_neg hδr, if_neg hδ, Real.exp_le_exp]
    have h1 : (π * (δ * r)) ^ 2 ≤ (π * δ) ^ 2 := by
      have : (π * (δ * r)) ^ 2 = (π * δ) ^ 2 * r ^ 2 := by ring
      rw [this]
      have : r ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ (π * δ) ^ 2 := sq_nonneg _
      nlinarith
    have h0 : 0 < (π * (δ * r)) ^ 2 := by positivity
    have : T0 ^ 2 / (π * δ) ^ 2 ≤ T0 ^ 2 / (π * (δ * r)) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) h0 h1
    rw [mul_div_assoc, mul_div_assoc]
    linarith

/-- `err_{η,χ}(δw, wx)` against the four moments. -/
noncomputable def Er (q : ℕ) (T0 δ x r : ℝ) : ℝ :=
  (T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ) +
      11 * |δ| / x) +
    ((1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / √x +
      (Real.log q + 6) * (6 * |δ|) / (x * √x)) * (1 / √r) +
    3 / x * (1 / r) + (Real.log q + 6) / (x * √x) * (1 / (r * √r))

theorem log_nonneg_of {q : ℕ} (hq : 1 ≤ q) {T0 : ℝ} (hT0 : 50 ≤ T0) :
    0 ≤ Real.log (q * T0 / (2 * π)) ∧ 0 ≤ Real.log (q * T0) ∧ 0 ≤ Real.log q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpi := Real.pi_lt_d2
  refine ⟨Real.log_nonneg ?_, Real.log_nonneg (by nlinarith), Real.log_nonneg hq'⟩
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem err932_le_Er {q : ℕ} (hq : 1 ≤ q) {T0 : ℝ} (hT0 : 50 ≤ T0) {δ x r : ℝ} (hx : 0 < x)
    (hr : 0 < r) (hr1 : r ≤ 1) : err932 q T0 (δ * r) (r * x) ≤ Er q T0 δ x r := by
  obtain ⟨hL1, hL2, hL3⟩ := log_nonneg_of hq hT0
  have hT : 0 ≤ T0 := by linarith
  have h1 : T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 (δ * r)) ≤
      T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ) := by
    have := expδ_mono (T0 := T0) (δ := δ) hr hr1
    have : 0 ≤ T0 * Real.log (q * T0 / (2 * π)) := mul_nonneg hT hL1
    gcongr
  have hsr : 0 < √r := Real.sqrt_pos.2 hr
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have hsrx : √(r * x) = √r * √x := Real.sqrt_mul hr.le x
  have hab : |δ * r| = |δ| * r := by rw [abs_mul, abs_of_pos hr]
  unfold err932 Er
  rw [hsrx, hab]
  have e : (1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / (√r * √x) +
      (3 + 11 * (|δ| * r)) / (r * x) + (Real.log q + 6) * (1 + 6 * (|δ| * r)) / (r * x * (√r * √x)) =
      11 * |δ| / x + ((1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / √x +
        (Real.log q + 6) * (6 * |δ|) / (x * √x)) * (1 / √r) +
      3 / x * (1 / r) + (Real.log q + 6) / (x * √x) * (1 / (r * √r)) := by
    have hrr : √r * √r = r := Real.mul_self_sqrt hr.le
    field_simp
    nlinarith [hrr]
  linarith

theorem continuousOn_Er (q : ℕ) (T0 δ x : ℝ) :
    ContinuousOn (Er q T0 δ x) (Icc (1 / 4) 1) := by
  unfold Er
  refine ((continuousOn_const.add (continuousOn_const.mul (contOn_inv_sqrt (by norm_num)))).add
    (continuousOn_const.mul (contOn_inv (by norm_num)))).add
    (continuousOn_const.mul (contOn_inv_mul_sqrt (by norm_num)))

theorem integral_eta2_Er_le {q : ℕ} (hq : 1 ≤ q) {T0 : ℝ} (hT0 : 50 ≤ T0) {δ x : ℝ} (hx : 0 < x) :
    ∫ r in Ioi 0, eta2 r * Er q T0 δ x r ≤ err933 q T0 δ x := by
  obtain ⟨hL1, hL2, hL3⟩ := log_nonneg_of hq hT0
  set c0 := T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ) +
      11 * |δ| / x
  set c1 := (1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / √x +
      (Real.log q + 6) * (6 * |δ|) / (x * √x)
  set c2 := 3 / x
  set c3 := (Real.log q + 6) / (x * √x)
  have hI0 := integrableOn_eta2_mul (g := fun _ => (1 : ℝ)) continuousOn_const
  have hI1 := integrableOn_eta2_mul (g := fun r => 1 / √r) (contOn_inv_sqrt (by norm_num))
  have hI2 := integrableOn_eta2_mul (g := fun r => 1 / r) (contOn_inv (by norm_num))
  have hI3 := integrableOn_eta2_mul (g := fun r => 1 / (r * √r)) (contOn_inv_mul_sqrt (by norm_num))
  have e : (fun r => eta2 r * Er q T0 δ x r) = fun r =>
      ((c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) + c2 * (eta2 r * (1 / r))) +
        c3 * (eta2 r * (1 / (r * √r))) := by
    funext r; unfold Er; ring
  have hA : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) (Ioi 0) :=
    (hI0.const_mul c0).add (hI1.const_mul c1)
  have hB : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r)) +
      c2 * (eta2 r * (1 / r))) (Ioi 0) := hA.add (hI2.const_mul c2)
  rw [e, integral_add hB (hI3.const_mul c3), integral_add hA (hI2.const_mul c2),
    integral_add (hI0.const_mul c0) (hI1.const_mul c1), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp only [mul_one]
  rw [moment0]
  have m1 := moment_half
  have m2 := moment_one
  have m3 := moment_3half
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  have := mul_le_mul_of_nonneg_left m1 hc1
  have := mul_le_mul_of_nonneg_left m2 hc2
  have := mul_le_mul_of_nonneg_left m3 hc3
  have hfin : c0 * 1 + c1 * 1.37259 + c2 * 1.92182 + c3 * 2.74517 = err933 q T0 δ x := by
    simp only [c0, c1, c2, c3]; unfold err933; field_simp; ring
  linarith


/-! ## The error for `q ≥ 2` -/

open TernaryGoldbach.Explicit (E0b E1b E2b Vb errZ E2g E1g Z3g BPz2 Vz EB EA rhoB rhoA)

/-- `errZ(T₀, δr, rx)` against the moments (`q = 1`). -/
noncomputable def ErZ (T0 δ x r : ℝ) : ℝ :=
  E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) +
    E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / √x * (1 / √r) +
    112 * Z3g BPz2 0 / x * (1 / r) + Vz δ / (2 * π * (x * √x)) * (1 / (r * √r))

theorem errZ_le_ErZ {T0 δ : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) {x r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hr1 : r ≤ 1) : errZ T0 (δ * r) (r * x) ≤ ErZ T0 δ x r := by
  unfold errZ ErZ
  have hT00 : 0 < T0 := by linarith [le_max_right (10 * π * |δ|) 50]
  have h10 : 10 * π * |δ| ≤ T0 := (le_max_left _ _).trans hT0
  have hE2 := Explicit.E2z_mono hT00 hr hr1 h10
  have hV := Explicit.Vz_mono (δ := δ) hr hr1
  have hsr : √(r * x) = √r * √x := Real.sqrt_mul hr.le x
  have hsr0 : 0 < √r := Real.sqrt_pos.2 hr
  have hsx0 : 0 < √x := Real.sqrt_pos.2 hx
  rw [hsr]
  have e1 : E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / (√r * √x) =
      E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / √x * (1 / √r) := by field_simp
  have e2 : 112 * Z3g BPz2 0 / (r * x) = 112 * Z3g BPz2 0 / x * (1 / r) := by field_simp
  have e3 : Vz (δ * r) / (2 * π * (r * x * (√r * √x))) ≤
      Vz δ / (2 * π * (x * √x)) * (1 / (r * √r)) := by
    rw [show Vz δ / (2 * π * (x * √x)) * (1 / (r * √r)) = Vz δ / (2 * π * (r * x * (√r * √x))) by
      field_simp]
    exact div_le_div_of_nonneg_right hV (by positivity)
  rw [e1, e2]; linarith

/-- `err_new(q, T₀, δr, rx)` against the moments. -/
noncomputable def ErNew (q : ℕ) (T0 δ x r : ℝ) : ℝ :=
  E2b q T0 δ + E1b q T0 / √x * (1 / √r) + E0b q / x * (1 / r) +
    Vb q δ / (2 * π * (x * √x)) * (1 / (r * √r))

noncomputable def ErN (q : ℕ) (T0 δ x r : ℝ) : ℝ := if q = 1 then ErZ T0 δ x r else ErNew q T0 δ x r

theorem errNew_le_ErNew {q : ℕ} [NeZero q] {T0 δ : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) {x r : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hr1 : r ≤ 1) : errNew q T0 (δ * r) (r * x) ≤ ErNew q T0 δ x r := by
  unfold errNew ErNew
  have hT00 : 0 < T0 := by linarith [le_max_right (10 * π * |δ|) 50]
  have h10 : 10 * π * |δ| ≤ T0 := (le_max_left _ _).trans hT0
  have hE2 := Explicit.E2b_mono (N := q) hT00 hr hr1 h10
  have hV := Explicit.Vb_mono (N := q) (δ := δ) hr hr1
  have hsr : √(r * x) = √r * √x := Real.sqrt_mul hr.le x
  have hsr0 : 0 < √r := Real.sqrt_pos.2 hr
  have hsx0 : 0 < √x := Real.sqrt_pos.2 hx
  rw [hsr]
  have e1 : E1b q T0 / (√r * √x) = E1b q T0 / √x * (1 / √r) := by field_simp
  have e2 : E0b q / (r * x) = E0b q / x * (1 / r) := by field_simp
  have e3 : Vb q (δ * r) / (2 * π * (r * x * (√r * √x))) ≤
      Vb q δ / (2 * π * (x * √x)) * (1 / (r * √r)) := by
    rw [show Vb q δ / (2 * π * (x * √x)) * (1 / (r * √r)) = Vb q δ / (2 * π * (r * x * (√r * √x))) by
      field_simp]
    exact div_le_div_of_nonneg_right hV (by positivity)
  rw [e1, e2]; linarith

theorem err932N_le_ErN {q : ℕ} [NeZero q] {T0 δ : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) {x r : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hr1 : r ≤ 1) : err932N q T0 (δ * r) (r * x) ≤ ErN q T0 δ x r := by
  unfold err932N ErN
  split_ifs with h
  · exact errZ_le_ErZ hT0 hx hr hr1
  · exact errNew_le_ErNew hT0 hx hr hr1

theorem continuousOn_ErN (q : ℕ) (T0 δ x : ℝ) : ContinuousOn (ErN q T0 δ x) (Icc (1 / 4) 1) := by
  unfold ErN
  split_ifs
  · unfold ErZ
    exact ((continuousOn_const.add (continuousOn_const.mul (contOn_inv_sqrt (by norm_num)))).add
      (continuousOn_const.mul (contOn_inv (by norm_num)))).add
      (continuousOn_const.mul (contOn_inv_mul_sqrt (by norm_num)))
  · unfold ErNew
    exact ((continuousOn_const.add (continuousOn_const.mul (contOn_inv_sqrt (by norm_num)))).add
      (continuousOn_const.mul (contOn_inv (by norm_num)))).add
      (continuousOn_const.mul (contOn_inv_mul_sqrt (by norm_num)))

/-- The averaged error for `q ≥ 2`. -/
noncomputable def err933New (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  E2b q T0 δ + 1.37259 * E1b q T0 / √x + 1.92182 * E0b q / x +
    2.74517 * Vb q δ / (2 * π * (x * √x))

/-- The averaged error for `q = 1`. -/
noncomputable def err933Z (T0 δ x : ℝ) : ℝ :=
  E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ) +
    1.37259 * E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / √x +
    1.92182 * (112 * Z3g BPz2 0) / x + 2.74517 * Vz δ / (2 * π * (x * √x))

/-- The error of `cor_9_3_3`. -/
noncomputable def err933N (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  if q = 1 then err933Z T0 δ x else err933New q T0 δ x

theorem integral_eta2_ErZ_le (T0 δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ r in Ioi 0, eta2 r * ErZ T0 δ x r ≤ err933Z T0 δ x := by
  set c0 := E2g BPz2 10 T0 (EB T0) (EA T0 δ) rhoB (rhoA δ)
  set c1 := E1g BPz2 T0 (2 * π * 0.6647) (2 * π * 0.1707) / √x
  set c2 := 112 * Z3g BPz2 0 / x
  set c3 := Vz δ / (2 * π * (x * √x))
  have hI0 := integrableOn_eta2_mul (g := fun _ => (1 : ℝ)) continuousOn_const
  have hI1 := integrableOn_eta2_mul (g := fun r => 1 / √r) (contOn_inv_sqrt (by norm_num))
  have hI2 := integrableOn_eta2_mul (g := fun r => 1 / r) (contOn_inv (by norm_num))
  have hI3 := integrableOn_eta2_mul (g := fun r => 1 / (r * √r)) (contOn_inv_mul_sqrt (by norm_num))
  have e : (fun r => eta2 r * ErZ T0 δ x r) = fun r =>
      ((c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) + c2 * (eta2 r * (1 / r))) +
        c3 * (eta2 r * (1 / (r * √r))) := by
    funext r; unfold ErZ; ring
  have hA : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) (Ioi 0) :=
    (hI0.const_mul c0).add (hI1.const_mul c1)
  have hB : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r)) +
      c2 * (eta2 r * (1 / r))) (Ioi 0) := hA.add (hI2.const_mul c2)
  rw [e, integral_add hB (hI3.const_mul c3), integral_add hA (hI2.const_mul c2),
    integral_add (hI0.const_mul c0) (hI1.const_mul c1), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp only [mul_one]
  rw [moment0]
  have m1 := moment_half
  have m2 := moment_one
  have m3 := moment_3half
  have hc1 : 0 ≤ c1 := div_nonneg (Explicit.E1z_nonneg T0) (Real.sqrt_nonneg _)
  have hc2 : 0 ≤ c2 := div_nonneg (mul_nonneg (by norm_num) Explicit.Z3z_nonneg) hx.le
  have hc3 : 0 ≤ c3 := div_nonneg (Explicit.Vz_nonneg δ) (by positivity)
  have := mul_le_mul_of_nonneg_left m1 hc1
  have := mul_le_mul_of_nonneg_left m2 hc2
  have := mul_le_mul_of_nonneg_left m3 hc3
  have hfin : c0 * 1 + c1 * 1.37259 + c2 * 1.92182 + c3 * 2.74517 = err933Z T0 δ x := by
    simp only [c0, c1, c2, c3]; unfold err933Z; ring
  linarith

theorem integral_eta2_ErNew_le (q : ℕ) [NeZero q] (T0 δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ r in Ioi 0, eta2 r * ErNew q T0 δ x r ≤ err933New q T0 δ x := by
  set c0 := E2b q T0 δ
  set c1 := E1b q T0 / √x
  set c2 := E0b q / x
  set c3 := Vb q δ / (2 * π * (x * √x))
  have hI0 := integrableOn_eta2_mul (g := fun _ => (1 : ℝ)) continuousOn_const
  have hI1 := integrableOn_eta2_mul (g := fun r => 1 / √r) (contOn_inv_sqrt (by norm_num))
  have hI2 := integrableOn_eta2_mul (g := fun r => 1 / r) (contOn_inv (by norm_num))
  have hI3 := integrableOn_eta2_mul (g := fun r => 1 / (r * √r)) (contOn_inv_mul_sqrt (by norm_num))
  have e : (fun r => eta2 r * ErNew q T0 δ x r) = fun r =>
      ((c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) + c2 * (eta2 r * (1 / r))) +
        c3 * (eta2 r * (1 / (r * √r))) := by
    funext r; unfold ErNew; ring
  have hA : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r))) (Ioi 0) :=
    (hI0.const_mul c0).add (hI1.const_mul c1)
  have hB : IntegrableOn (fun r => c0 * (eta2 r * 1) + c1 * (eta2 r * (1 / √r)) +
      c2 * (eta2 r * (1 / r))) (Ioi 0) := hA.add (hI2.const_mul c2)
  rw [e, integral_add hB (hI3.const_mul c3), integral_add hA (hI2.const_mul c2),
    integral_add (hI0.const_mul c0) (hI1.const_mul c1), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp only [mul_one]
  rw [moment0]
  have m1 := moment_half
  have m2 := moment_one
  have m3 := moment_3half
  have hc1 : 0 ≤ c1 := div_nonneg (Explicit.E1b_nonneg q T0) (Real.sqrt_nonneg _)
  have hc2 : 0 ≤ c2 := div_nonneg (Explicit.E0b_nonneg q) hx.le
  have hc3 : 0 ≤ c3 := div_nonneg (Explicit.Vb_nonneg q δ) (by positivity)
  have := mul_le_mul_of_nonneg_left m1 hc1
  have := mul_le_mul_of_nonneg_left m2 hc2
  have := mul_le_mul_of_nonneg_left m3 hc3
  have hfin : c0 * 1 + c1 * 1.37259 + c2 * 1.92182 + c3 * 2.74517 = err933New q T0 δ x := by
    simp only [c0, c1, c2, c3]; unfold err933New; ring
  linarith

theorem integral_eta2_ErN_le {q : ℕ} [NeZero q] {T0 : ℝ} (hT0 : 50 ≤ T0) (δ : ℝ) {x : ℝ}
    (hx : 0 < x) : ∫ r in Ioi 0, eta2 r * ErN q T0 δ x r ≤ err933N q T0 δ x := by
  unfold ErN err933N
  split_ifs with h
  · exact integral_eta2_ErZ_le T0 δ hx
  · exact integral_eta2_ErNew_le q T0 δ hx

theorem continuous_phi : Continuous phi := by
  unfold TernaryGoldbach.Helfgott.phi; fun_prop

theorem eta2_div_nonneg (r : ℝ) : 0 ≤ eta2 r / r := by
  rcases le_or_gt r 0 with h | h
  · rw [eta2_eq_zero_of_nonpos h, zero_div]
  · exact div_nonneg (eta2_nonneg r) h.le

theorem mem_Ioo_of_eta2_ne {r : ℝ} (h : eta2 r ≠ 0) : r ∈ Ioo (1 / 4 : ℝ) 1 := by
  by_contra h'; exact h (TernaryGoldbach.Helfgott.eta2_eq_zero h')

/-- **[H, Cor 9.3.3]** (error `err933N`: [H]'s for `q = 1`, ours for `q ≥ 2`), from [H, Prop 9.3.2]
by averaging over `η₂` (9.59). Let `η_* = η₂ *_M η`,
`η(t) = t² e^{-t²/2}`, `x ≥ 4`, `χ` primitive mod `q`, GRH for `L(s, χ)` up to `T₀ ≥ max(10π|δ|, 50)`.
Then `Σ Λ(n) χ(n) e(δn/x) η_*(n/x) = [q = 1] η̂_*(-δ) x + O*(err933) x`. -/
theorem cor_9_3_3 {x : ℝ} (hx : 4 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * etaU (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * x else 0)‖ ≤ err933N q T0 δ x * x := by
  have hx0 : 0 < x := by linarith
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hT50 : 50 ≤ T0 := (le_max_right _ _).trans hT0
  set μ : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμ
  set w : ℝ → ℝ := fun r => eta2 r / r with hw
  set M : ℝ → ℂ := fun r => if q = 1 then
    𝓕 (fun u => (phiPos u : ℂ)) (-(δ * r)) * ((r * x : ℝ) : ℂ) else 0 with hM
  set A : ℝ → ℂ := fun r => Schar χ (fun n => ((Λ n * phi (n / (r * x)) : ℝ) : ℂ)) (δ / x) with hA
  set G : ℝ → ℂ := fun r => (w r : ℂ) * M r with hGdef
  set term : ℕ → ℝ → ℂ := fun n r =>
    (w r : ℂ) * (((Λ n * phi (n / (r * x)) : ℝ) : ℂ) * χ (n : ZMod q) * e (n * (δ / x))) with hterm
  set F : ℕ → ℝ → ℂ := fun n r => term n r - if n = 0 then G r else 0 with hF
  set f : ℝ → ℂ := fun r => (w r : ℂ) * (A r - M r) with hf
  set C : ℝ := ∑' n : ℕ, Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4)) with hC
  have hsg := summable_gauss hx0
  have hC0 : 0 ≤ C := tsum_nonneg fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  set Iφ : ℝ := ∫ u, phiPos u with hIφ
  -- continuity on `(0, ∞)`
  have hwc : ContinuousOn w (Ioi 0) :=
    TernaryGoldbach.Helfgott.continuous_eta2.continuousOn.div continuousOn_id
      fun r (hr : 0 < r) => hr.ne'
  have hMc : ContinuousOn M (Ioi 0) := by
    simp only [hM]
    split_ifs
    · exact ((continuous_fourier_phiPos.comp (continuous_const.mul continuous_id).neg).mul
        (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const))).continuousOn
    · exact continuousOn_const
  have hGc : ContinuousOn G (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul hMc
  have hnormG : ∀ r, 0 < r → ‖G r‖ ≤ eta2 r * (x * Iφ) := by
    intro r hr
    show ‖((eta2 r / r : ℝ) : ℂ) * M r‖ ≤ _
    simp only [hM, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (eta2_div_nonneg r)]
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r * x)]
      have := norm_fourier_phiPos_le (-(δ * r))
      calc eta2 r / r * (‖𝓕 (fun u => (phiPos u : ℂ)) (-(δ * r))‖ * (r * x))
          ≤ eta2 r / r * (Iφ * (r * x)) := by
            gcongr
            · exact eta2_div_nonneg r
          _ = eta2 r * (x * Iφ) := by field_simp
    · simp only [norm_zero, mul_zero]
      exact mul_nonneg (eta2_nonneg r) (mul_nonneg hx0.le (integral_nonneg phiPos_nonneg))
  have hGint : Integrable G μ := by
    refine Integrable.mono' (integrableOn_eta2_mul (g := fun _ => x * Iφ) continuousOn_const)
      (hGc.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => hnormG r hr)
  -- the dominating functions
  set bnd : ℕ → ℝ → ℝ := fun n r =>
    w r * (Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4))) + (if n = 0 then ‖G r‖ else 0) with hbnd
  have hterm0 : ∀ r, term 0 r = 0 := fun r => by simp [hterm]
  have hnorm_term : ∀ n, ∀ r, 0 < r → ‖term n r‖ ≤ w r * (Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4))) := by
    intro n r hr
    have hχ1 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    show ‖((eta2 r / r : ℝ) : ℂ) * (((Λ n * phi (n / (r * x)) : ℝ) : ℂ) * χ (n : ZMod q) *
      e (n * (δ / x)))‖ ≤ eta2 r / r * (Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4)))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, TernaryGoldbach.norm_e, mul_one, abs_of_nonneg (eta2_div_nonneg r),
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (phi_nonneg _))]
    by_cases hη : eta2 r = 0
    · simp [hη]
    · have hr1 := (mem_Ioo_of_eta2_ne hη).2.le
      have hph := phi_scale_le (n := n) hx0 hr hr1
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hw0 := eta2_div_nonneg r
      have hp0 := phi_nonneg (n / (r * x))
      calc eta2 r / r * (Λ n * phi (n / (r * x)) * ‖χ (n : ZMod q)‖)
          ≤ eta2 r / r * (Λ n * (2 * Real.exp (-(n / x) ^ 2 / 4)) * 1) := by gcongr
        _ = _ := by ring
  have hphic : ∀ n : ℕ, ContinuousOn (fun r : ℝ => phi (n / (r * x))) (Ioi 0) := fun n =>
    continuous_phi.comp_continuousOn (continuousOn_const.div (continuousOn_id.mul continuousOn_const)
      fun r (hr : 0 < r) => mul_ne_zero hr.ne' hx0.ne')
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (term n) (Ioi 0) :=
      (Complex.continuous_ofReal.comp_continuousOn hwc).mul
        (((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (hphic n))).mul
          continuousOn_const).mul continuousOn_const)
    refine h1.sub ?_
    by_cases hn : n = 0
    · simp only [hn, if_true]; exact hGc
    · simp only [hn, if_false]; exact continuousOn_const
  have h_bound : ∀ n, ∀ᵐ r ∂μ, ‖F n r‖ ≤ bnd n r := by
    intro n
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r (hr : 0 < r) => ?_)
    by_cases hn : n = 0
    · subst hn
      simp only [hF, hbnd, hterm0, if_true, zero_sub, norm_neg, Nat.cast_zero,
        ArithmeticFunction.map_zero, zero_mul, mul_zero, zero_add, le_refl]
    · simp only [hF, hbnd, hn, if_false, sub_zero, add_zero]
      exact hnorm_term n r hr
  have bound_summable : ∀ᵐ r ∂μ, Summable fun n => bnd n r :=
    Eventually.of_forall fun r => (hsg.mul_left (w r)).add (hasSum_ite_eq 0 ‖G r‖).summable
  have htsum : ∀ r, ∑' n, bnd n r = w r * C + ‖G r‖ := fun r => by
    simp only [hbnd]
    rw [(hsg.mul_left (w r)).tsum_add (hasSum_ite_eq 0 ‖G r‖).summable, tsum_mul_left, tsum_ite_eq]
  have bound_integrable : Integrable (fun r => ∑' n, bnd n r) μ := by
    simp only [htsum]
    refine Integrable.add ?_ hGint.norm
    have h := integrableOn_eta2_mul (g := fun r => C * (1 / r)) (continuousOn_const.mul (contOn_inv (by norm_num)))
    refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [hw]; ring
  have h_lim : ∀ᵐ r ∂μ, HasSum (fun n => F n r) (f r) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r (hr : 0 < r) => ?_)
    have hsum : Summable fun n : ℕ => ((Λ n * phi (n / (r * x)) : ℝ) : ℂ) * χ (n : ZMod q) *
        e (n * (δ / x)) := by
      refine (summable_phi_terms (X := r * x) (by positivity)).of_norm_bounded fun n => ?_
      rw [norm_mul, norm_mul, TernaryGoldbach.norm_e, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    have h1 : HasSum (fun n => term n r) ((w r : ℂ) * A r) := hsum.hasSum.mul_left (w r : ℂ)
    have h2 := h1.sub (hasSum_ite_eq 0 (G r))
    convert h2 using 1
    simp only [hf, hGdef]; ring
  have hS := hasSum_integral_of_dominated_convergence bnd hFmeas h_bound bound_summable
    bound_integrable h_lim
  -- the integrals of the `F n`
  have hIF : ∀ n, ∫ r, F n r ∂μ = ((Λ n * etaU (n / x) : ℝ) : ℂ) * χ (n : ZMod q) * e (n * (δ / x)) -
      if n = 0 then ∫ r, G r ∂μ else 0 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [hF, hterm0, zero_sub, if_true, integral_neg, Nat.cast_zero,
        ArithmeticFunction.map_zero, zero_mul, Complex.ofReal_zero, zero_sub]
    · simp only [hF, hn, if_false, sub_zero]
      have e1 : ∀ r, term n r = ((w r * (Λ n * phi (n / (r * x))) : ℝ) : ℂ) *
          (χ (n : ZMod q) * e (n * (δ / x))) := fun r => by simp only [hterm]; push_cast; ring
      simp only [e1]
      rw [integral_mul_const, integral_complex_ofReal]
      have e2 : ∫ r, w r * (Λ n * phi (n / (r * x))) ∂μ = Λ n * etaU (n / x) := by
        rw [etaU_eq, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have : phiPos (n / x / r) = phi (n / (r * x)) := by
          unfold phiPos; rw [if_pos (by positivity)]; congr 1; field_simp
        simp only [hw, this]; ring
      rw [e2]; push_cast; ring
  have hc : HasSum (fun n : ℕ => ((Λ n * etaU (n / x) : ℝ) : ℂ) * χ (n : ZMod q) * e (n * (δ / x)))
      (∫ r, f r ∂μ + ∫ r, G r ∂μ) := by
    have := (hS.add (hasSum_ite_eq 0 (∫ r, G r ∂μ)))
    simp only [hIF, sub_add_cancel] at this
    exact this
  have hSchar : Schar χ (fun n => ((Λ n * etaU (n / x) : ℝ) : ℂ)) (δ / x) =
      ∫ r, f r ∂μ + ∫ r, G r ∂μ := hc.tsum_eq
  -- the main term
  have hIG : ∫ r, G r ∂μ = if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * x else 0 := by
    by_cases h1 : q = 1
    · rw [if_pos h1, fourier_etaU, ← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
      simp only [hGdef, hM, hw, if_pos h1]
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [show -(δ * r) = r * -δ by ring]
      push_cast; field_simp
    · rw [if_neg h1]
      simp only [hGdef, hM, if_neg h1, mul_zero, integral_zero]
  -- the bound
  have hB : Integrable (fun r => x * (eta2 r * ErN q T0 δ x r)) μ :=
    (integrableOn_eta2_mul (continuousOn_ErN q T0 δ x)).const_mul x
  have hpt : ∀ᵐ r ∂μ, ‖f r‖ ≤ x * (eta2 r * ErN q T0 δ x r) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r (hr : 0 < r) => ?_)
    by_cases hη : eta2 r = 0
    · simp [hf, hw, hη]
    · obtain ⟨hr4, hr1⟩ := mem_Ioo_of_eta2_ne hη
      have hT0' : max (10 * π * |δ * r|) 50 ≤ T0 := by
        refine le_trans (max_le_max ?_ le_rfl) hT0
        rw [abs_mul, abs_of_pos hr]
        have h0 : 0 ≤ 10 * π * |δ| := by have := Real.pi_pos; positivity
        calc 10 * π * (|δ| * r) = 10 * π * |δ| * r := by ring
          _ ≤ 10 * π * |δ| * 1 := mul_le_mul_of_nonneg_left hr1.le h0
          _ = 10 * π * |δ| := mul_one _
      have hp := prop_9_3_2 (x := r * x) (by nlinarith) (δ * r) χ hχ hT0' hG
      rw [show δ * r / (r * x) = δ / x by field_simp] at hp
      have hE := err932N_le_ErN (q := q) hT0 hx0 hr hr1.le
      show ‖((eta2 r / r : ℝ) : ℂ) * (A r - M r)‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eta2_div_nonneg r)]
      have hw0 := eta2_div_nonneg r
      have he0 := eta2_nonneg r
      calc eta2 r / r * ‖A r - M r‖ ≤ eta2 r / r * (err932N q T0 (δ * r) (r * x) * (r * x)) :=
            mul_le_mul_of_nonneg_left hp hw0
        _ = x * (eta2 r * err932N q T0 (δ * r) (r * x)) := by field_simp
        _ ≤ x * (eta2 r * ErN q T0 δ x r) := by gcongr
  have key : Schar χ (fun n => ((Λ n * etaU (n / x) : ℝ) : ℂ)) (δ / x) -
      (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * x else 0) = ∫ r, f r ∂μ := by
    rw [hSchar, hIG]; ring
  rw [key]
  calc ‖∫ r, f r ∂μ‖ ≤ ∫ r, ‖f r‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, x * (eta2 r * ErN q T0 δ x r) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun r => norm_nonneg _) hB hpt
    _ = x * ∫ r, eta2 r * ErN q T0 δ x r ∂μ := integral_const_mul _ _
    _ ≤ x * err933N q T0 δ x := mul_le_mul_of_nonneg_left (integral_eta2_ErN_le hT50 δ hx0) hx0.le
    _ = err933N q T0 δ x * x := mul_comm _ _

end TernaryGoldbach.MajorArcs
