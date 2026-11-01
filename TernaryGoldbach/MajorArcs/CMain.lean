import TernaryGoldbach.MajorArcs.HHFourier2
import TernaryGoldbach.MajorArcs.Cor933
import TernaryGoldbach.MajorArcs.EtaPlusL2

/-!
# [B, Ch. 11, (11.6)]: the main-term constant `C_{η◦,η_*}`

`(η◦ ∗ η◦)(ρ) = ⟨η◦, η◦(· + 2 − ρ)⟩` (symmetry `η◦(2 − t) = η◦(t)`), and since translation preserves
`‖·‖₂`, polarization gives `(η◦ ∗ η◦)(ρ) = ‖η◦‖₂² − ½‖η◦(· + s) − η◦‖₂²` (`s = 2 − ρ`). With the
Lipschitz bound `|η◦'| ≤ 2.1` and supports of total length `≤ 4`:
`(η◦ ∗ η◦)(ρ) ≥ ‖η◦‖₂² − 8.82 (2 − ρ)²` ([B, (11.5)] has `2.71 ‖η◦'‖₂²` in place of `8.82`).
-/

open Real MeasureTheory Set

namespace TernaryGoldbach.MajorArcs

/-! ## `η◦`: symmetry and a Lipschitz bound -/

theorem P0_symm (t : ℝ) : P0 (2 - t) = P0 t := by unfold P0; ring_nf

theorem etaO_symm (t : ℝ) : etaO (2 - t) = etaO t := by
  unfold etaO
  by_cases h : t ∈ Icc (0 : ℝ) 2
  · have h' : 2 - t ∈ Icc (0 : ℝ) 2 := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_mem h', indicator_of_mem h, P0_symm]
  · have h' : 2 - t ∉ Icc (0 : ℝ) 2 := fun hm => h ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [indicator_of_notMem h', indicator_of_notMem h]

theorem aux_poly_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : v * (1 - v ^ 2) ^ 2 ≤ 0.3 := by
  nlinarith [sq_nonneg (v ^ 2 - 0.2), mul_nonneg h0 (sq_nonneg (v ^ 2 - 0.2)),
    mul_nonneg h0 (sq_nonneg (v - 0.45)), sq_nonneg (v - 0.45), mul_nonneg h0 (sub_nonneg.2 h1)]

theorem abs_P1_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : |P1 t| ≤ 2.1 := by
  obtain ⟨h0, h2⟩ := ht
  set w := t - 1 with hw
  have hw1 : |w| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hs : t * (2 - t) = 1 - |w| ^ 2 := by rw [sq_abs, hw]; ring
  have hE : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE0 := Real.exp_pos (-(t - 1) ^ 2 / 2)
  have h7 : 0 ≤ 7 - (t - 1) ^ 2 := by nlinarith
  have h7' : 7 - (t - 1) ^ 2 ≤ 7 := by nlinarith
  have hpoly := aux_poly_le (abs_nonneg w) hw1
  unfold P1
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg h7, abs_of_pos hE0, ← hw, abs_pow, hs,
    abs_of_nonneg (by nlinarith [abs_nonneg w] : (0:ℝ) ≤ 1 - |w| ^ 2)]
  have hA : 0 ≤ |w| * (1 - |w| ^ 2) ^ 2 := by
    have : 0 ≤ 1 - |w| ^ 2 := by nlinarith [abs_nonneg w]
    positivity
  calc |w| * (1 - |w| ^ 2) ^ 2 * (7 - (t - 1) ^ 2) * Real.exp (-(t - 1) ^ 2 / 2)
      ≤ (0.3 * 7) * 1 := by
        apply mul_le_mul _ hE hE0.le (by norm_num)
        exact mul_le_mul hpoly h7' h7 (by norm_num)
    _ = 2.1 := by norm_num

theorem P0_lipschitz {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) (hb : b ∈ Icc (0 : ℝ) 2) :
    |P0 a - P0 b| ≤ 2.1 * |a - b| := by
  have h := (convex_Icc (0 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le
    (f := P0) (C := 2.1) (fun t _ => (hasDerivAt_P0 t).differentiableAt)
    (fun t ht => by rw [(hasDerivAt_P0 t).deriv, Real.norm_eq_abs]; exact abs_P1_le ht) hb ha
  simpa [Real.norm_eq_abs] using h

theorem etaO_eq_clamp (t : ℝ) : etaO t = P0 (max 0 (min t 2)) := by
  unfold etaO
  by_cases h : t ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem h, min_eq_left h.2, max_eq_right h.1]
  · rw [indicator_of_notMem h]
    rcases lt_or_ge t 0 with h0 | h0
    · rw [min_eq_left (by linarith), max_eq_left h0.le, P0_zero]
    · have h2 : 2 < t := by by_contra h2; exact h ⟨h0, not_lt.1 h2⟩
      rw [min_eq_right h2.le, max_eq_right (by norm_num), P0_two]

theorem etaO_lipschitz (a b : ℝ) : |etaO a - etaO b| ≤ 2.1 * |a - b| := by
  rw [etaO_eq_clamp, etaO_eq_clamp]
  have hc : ∀ t : ℝ, max 0 (min t 2) ∈ Icc (0 : ℝ) 2 := fun t =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  refine (P0_lipschitz (hc a) (hc b)).trans ?_
  have h1 : |max 0 (min a 2) - max 0 (min b 2)| ≤ |min a 2 - min b 2| := by
    rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
  have h2 : |min a 2 - min b 2| ≤ |a - b| := by
    have := abs_min_sub_min_le_max a 2 b 2; simpa using this
  linarith

theorem etaO_eq_zero_of_notMem {t : ℝ} (h : t ∉ Icc (0 : ℝ) 2) : etaO t = 0 := by
  unfold etaO; rw [indicator_of_notMem h]

theorem integrable_etaO_sq : Integrable fun t => etaO t ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm memLp_etaO.aestronglyMeasurable).1 memLp_etaO
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]

/-- `∫ (η◦(t + s) − η◦(t))² dt ≤ 17.64 s²`. -/
theorem integral_sq_etaO_shift_le (s : ℝ) :
    ∫ t, (etaO (t + s) - etaO t) ^ 2 ≤ 17.64 * s ^ 2 := by
  set A := Icc (0 : ℝ) 2
  set B := Icc (-s) (2 - s)
  have hpt : ∀ t, (etaO (t + s) - etaO t) ^ 2 ≤
      (2.1 * s) ^ 2 * (A.indicator 1 t + B.indicator 1 t) := by
    intro t
    have hL := etaO_lipschitz (t + s) t
    rw [show t + s - t = s by ring] at hL
    have hsq : (etaO (t + s) - etaO t) ^ 2 ≤ (2.1 * s) ^ 2 := by
      rw [← sq_abs, mul_pow, ← sq_abs s]
      have := pow_le_pow_left₀ (abs_nonneg _) hL 2
      rwa [mul_pow] at this
    by_cases hA : t ∈ A
    · have hB0 : (0 : ℝ) ≤ B.indicator 1 t := by
        unfold indicator; split_ifs <;> norm_num
      rw [indicator_of_mem hA, Pi.one_apply]
      nlinarith [sq_nonneg (2.1 * s)]
    · by_cases hB : t ∈ B
      · rw [indicator_of_notMem hA, indicator_of_mem hB, Pi.one_apply]; linarith
      · have h1 : etaO t = 0 := etaO_eq_zero_of_notMem hA
        have h2 : etaO (t + s) = 0 := etaO_eq_zero_of_notMem fun hm =>
          hB ⟨by linarith [hm.1], by linarith [hm.2]⟩
        rw [h1, h2, indicator_of_notMem hA, indicator_of_notMem hB]; simp
  have hiA : Integrable (A.indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hiB : Integrable (B.indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hI : Integrable fun t => (2.1 * s) ^ 2 * (A.indicator 1 t + B.indicator 1 t) :=
    (hiA.add hiB).const_mul _
  calc ∫ t, (etaO (t + s) - etaO t) ^ 2
      ≤ ∫ t, (2.1 * s) ^ 2 * (A.indicator 1 t + B.indicator 1 t) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) hI
          (Filter.Eventually.of_forall hpt)
    _ = (2.1 * s) ^ 2 * (2 + 2) := by
        rw [integral_const_mul, integral_add hiA hiB, integral_indicator_one measurableSet_Icc,
          integral_indicator_one measurableSet_Icc]
        simp only [Real.volume_Icc, measureReal_def]
        rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by linarith)]
        ring
    _ = 17.64 * s ^ 2 := by ring

/-- `(η◦ ∗ η◦)(ρ)`. -/
noncomputable def conv2 (ρ : ℝ) : ℝ := ∫ t, etaO t * etaO (ρ - t)

/-- **[B, (11.5)], with constant `8.82`**: `(η◦ ∗ η◦)(ρ) ≥ ‖η◦‖₂² − 8.82 (2 − ρ)²`. -/
theorem conv2_ge (ρ : ℝ) : (∫ t, etaO t ^ 2) - 8.82 * (2 - ρ) ^ 2 ≤ conv2 ρ := by
  set s := 2 - ρ
  have hsym : ∀ t, etaO (ρ - t) = etaO (t + s) := fun t => by
    rw [← etaO_symm (ρ - t)]; congr 1; simp only [s]; ring
  have hshift : Integrable fun t => etaO (t + s) ^ 2 := integrable_etaO_sq.comp_add_right s
  have hdiff : Integrable fun t => (etaO (t + s) - etaO t) ^ 2 := by
    refine Integrable.mono' ((hshift.add integrable_etaO_sq).const_mul 2) ?_
      (Filter.Eventually.of_forall fun t => ?_)
    · exact ((measurable_etaO.comp (measurable_id.add_const s)).sub measurable_etaO).pow_const 2
        |>.aestronglyMeasurable
    · show ‖(etaO (t + s) - etaO t) ^ 2‖ ≤ 2 * (etaO (t + s) ^ 2 + etaO t ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (etaO (t + s) - etaO t))]
      nlinarith [sq_nonneg (etaO (t + s) + etaO t)]
  have hpt : ∀ t, etaO t * etaO (ρ - t) =
      (etaO t ^ 2 + etaO (t + s) ^ 2 - (etaO (t + s) - etaO t) ^ 2) / 2 := fun t => by
    rw [hsym]; ring
  have heq : conv2 ρ = (∫ t, etaO t ^ 2) - (1 / 2) * ∫ t, (etaO (t + s) - etaO t) ^ 2 := by
    unfold conv2
    simp_rw [hpt]
    have h1 : Integrable fun t => etaO t ^ 2 + etaO (t + s) ^ 2 := integrable_etaO_sq.add hshift
    rw [integral_div, integral_sub h1 hdiff, integral_add integrable_etaO_sq hshift,
      integral_add_right_eq_self (fun t => etaO t ^ 2) s]
    ring
  rw [heq]
  have := integral_sq_etaO_shift_le s
  linarith

/-! ## Moments of `η_*`: `∫ uᵏ η_*(u) du = Mₖ(η₂) Mₖ(φ)` -/

open TernaryGoldbach.Helfgott (eta2 phi κ)
open TernaryGoldbach.MinorArcs (etaU)

theorem eta2_nonneg' (t : ℝ) : 0 ≤ eta2 t := eta2_nonneg t

theorem hasCompactSupport_pow_mul_eta2_div (k : ℕ) {w : ℝ} (hw : 0 < w) :
    HasCompactSupport fun u : ℝ => u ^ k * eta2 (u / w) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := w)) fun u hu => ?_
  have : eta2 (u / w) = 0 := TernaryGoldbach.Helfgott.eta2_eq_zero fun h => hu
    ⟨by have := h.1; have : 0 < u / w := by linarith
        exact (div_pos_iff_of_pos_right hw).1 this |>.le,
     by have := h.2; exact (div_lt_one hw).1 this |>.le⟩
  rw [this, mul_zero]

theorem integral_pow_mul_eta2_div (k : ℕ) {w : ℝ} (hw : 0 < w) :
    ∫ u, u ^ k * eta2 (u / w) = w ^ (k + 1) * ∫ v, v ^ k * eta2 v := by
  have h := Measure.integral_comp_div (fun v => (w * v) ^ k * eta2 v) w
  have e : (fun u : ℝ => (w * (u / w)) ^ k * eta2 (u / w)) = fun u => u ^ k * eta2 (u / w) := by
    ext u; rw [mul_div_cancel₀ _ hw.ne']
  rw [e] at h
  rw [h, abs_of_pos hw, smul_eq_mul]
  have e2 : (fun v : ℝ => (w * v) ^ k * eta2 v) = fun v => w ^ k * (v ^ k * eta2 v) := by
    ext v; ring
  rw [e2, integral_const_mul]; ring

theorem integrableOn_pow_mul_phi (k : ℕ) : IntegrableOn (fun w : ℝ => w ^ k * phi w) (Ioi 0) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (k : ℝ) + 2)
    (by linarith)
  refine h.congr_fun (fun w (hw : 0 < w) => ?_) measurableSet_Ioi
  simp only [phi]
  rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring_nf

theorem integral_pow_mul_etaU (k : ℕ) :
    ∫ u, u ^ k * etaU u = (∫ v, v ^ k * eta2 v) * ∫ w in Ioi (0:ℝ), w ^ k * phi w := by
  set F : ℝ → ℝ → ℝ := fun u w => u ^ k * (eta2 (u / w) * phi w / w) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (measurable_fst.pow_const k).mul
      (((TernaryGoldbach.Helfgott.continuous_eta2.measurable.comp (measurable_fst.div measurable_snd)).mul
        (continuous_phi.measurable.comp measurable_snd)).div measurable_snd)
  have hcu : ∀ w : ℝ, Continuous fun u : ℝ => u ^ k * eta2 (u / w) := fun w =>
    (continuous_pow k).mul (TernaryGoldbach.Helfgott.continuous_eta2.comp (continuous_id.div_const w))
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w (hw : 0 < w) => ?_)
      have := ((hcu w).integrable_of_hasCompactSupport (μ := volume)
        (hasCompactSupport_pow_mul_eta2_div k hw)).mul_const
        (phi w / w)
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [hF, Function.uncurry_apply_pair]; ring
    · have hA : ∀ w ∈ Ioi (0:ℝ), ∫ u, ‖Function.uncurry F (u, w)‖ =
          w ^ k * phi w * ∫ v, |v ^ k * eta2 v| := by
        intro w (hw : 0 < w)
        have hphi : 0 ≤ phi w := by unfold phi; positivity
        have e1 : (fun u => ‖Function.uncurry F (u, w)‖) =
            fun u => (phi w / w) * |u ^ k * eta2 (u / w)| := by
          ext u
          simp only [hF, Function.uncurry_apply_pair, Real.norm_eq_abs]
          rw [show u ^ k * (eta2 (u / w) * phi w / w) = (phi w / w) * (u ^ k * eta2 (u / w)) by ring,
            abs_mul, abs_of_nonneg (by positivity : 0 ≤ phi w / w)]
        rw [e1, integral_const_mul]
        have h := Measure.integral_comp_div (fun v => |(w * v) ^ k * eta2 v|) w
        have e2 : (fun u : ℝ => |(w * (u / w)) ^ k * eta2 (u / w)|) = fun u => |u ^ k * eta2 (u / w)| := by
          ext u; rw [mul_div_cancel₀ _ hw.ne']
        rw [e2] at h
        rw [h, abs_of_pos hw, smul_eq_mul]
        have e3 : (fun v : ℝ => |(w * v) ^ k * eta2 v|) = fun v => w ^ k * |v ^ k * eta2 v| := by
          ext v; rw [mul_pow, mul_assoc, abs_mul, abs_of_nonneg (by positivity : 0 ≤ w ^ k)]
        rw [e3, integral_const_mul]; field_simp
      have hI : IntegrableOn (fun w : ℝ => w ^ k * phi w * ∫ v, |v ^ k * eta2 v|) (Ioi 0) :=
        (integrableOn_pow_mul_phi k).mul_const _
      exact hI.congr_fun (fun w hw => (hA w hw).symm) measurableSet_Ioi
  have h1 : ∫ u, u ^ k * etaU u = ∫ u, ∫ w in Ioi (0:ℝ), F u w := by
    congr 1; ext u; simp only [hF]; rw [integral_const_mul]; rfl
  rw [h1, integral_integral_swap hint, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  simp only [hF]
  have e : (fun u => u ^ k * (eta2 (u / w) * phi w / w)) = fun u => (phi w / w) * (u ^ k * eta2 (u / w)) := by
    ext u; ring
  rw [e, integral_const_mul, integral_pow_mul_eta2_div k hw]
  field_simp; ring

/-! ### The moments of `η₂`: `1, 9/16, 49/144` -/

theorem integral_eq_Ioi_of_eta2 (g : ℝ → ℝ) :
    ∫ v, g v * eta2 v = ∫ v in Ioi 0, eta2 v * g v := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
  · exact setIntegral_congr_fun measurableSet_Ioi fun v _ => by ring
  · intro v hv; rw [eta2_eq_zero_of_nonpos (not_lt.1 hv), mul_zero]

theorem eta2_moment0 : ∫ v, v ^ 0 * eta2 v = 1 := by
  rw [integral_eq_Ioi_of_eta2 (fun v => v ^ 0)]
  simp only [pow_zero, mul_one]; exact moment0

theorem hasDerivAt_r2log {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => 2 * r ^ 2 * Real.log (c * r) - r ^ 2) (4 * Real.log (c * r) * r) r := by
  have h1 := hasDerivAt_log_mul hc hr
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have := ((h2.const_mul 2).mul h1).sub h2
  exact this.congr_deriv (by field_simp; ring)

theorem hasDerivAt_r3log {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => 4 / 3 * r ^ 3 * Real.log (c * r) - 4 / 9 * r ^ 3)
      (4 * Real.log (c * r) * r ^ 2) r := by
  have h1 := hasDerivAt_log_mul hc hr
  have h3 : HasDerivAt (fun r : ℝ => r ^ 3) (3 * r ^ 2) r := by simpa using hasDerivAt_pow 3 r
  have := ((h3.const_mul (4 / 3)).mul h1).sub (h3.const_mul (4 / 9))
  exact this.congr_deriv (by field_simp; ring)

theorem eta2_moment1 : ∫ v, v ^ 1 * eta2 v = 9 / 16 := by
  rw [integral_eq_Ioi_of_eta2 (fun v => v ^ 1), setIntegral_eta2_mul (by fun_prop)]
  have hL := integral_eq_of_deriv (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_r2log (c := 4) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (g := fun r => r) continuousOn_id)
  have hR := integral_eq_of_deriv (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_r2log (c := 1) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (g := fun r => r) continuousOn_id)
  have eL : ∫ r in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * r) * r ^ 1 =
      ∫ r in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * r) * r := by simp only [pow_one]
  have eR : ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * r ^ 1 =
      -∫ r in (1 / 2 : ℝ)..1, 4 * Real.log (1 * r) * r := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext r; rw [one_mul, pow_one]; ring
  rw [eL, eR, hL, hR]
  simp only [one_mul]
  have e1 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  have e2 : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e1, e2, e3, Real.log_one]
  ring

theorem eta2_moment2 : ∫ v, v ^ 2 * eta2 v = 49 / 144 := by
  rw [integral_eq_Ioi_of_eta2 (fun v => v ^ 2), setIntegral_eta2_mul (by fun_prop)]
  have hL := integral_eq_of_deriv (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_r3log (c := 4) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (g := fun r => r ^ 2) (by fun_prop))
  have hR := integral_eq_of_deriv (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_r3log (c := 1) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (g := fun r => r ^ 2) (by fun_prop))
  have eR : ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * r ^ 2 =
      -∫ r in (1 / 2 : ℝ)..1, 4 * Real.log (1 * r) * r ^ 2 := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext r; rw [one_mul]; ring
  rw [eR, hL, hR]
  simp only [one_mul]
  have e1 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  have e2 : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e1, e2, e3, Real.log_one]
  ring

/-! ### The moments of `φ`: `√(π/2), 2, 3√(π/2)` -/

theorem integral_pow_mul_phi_gamma (k : ℕ) :
    ∫ w in Ioi (0:ℝ), w ^ k * phi w =
      (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 2 + 1) / 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ) + 2) (b := 1 / 2) two_pos
    (by linarith) (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  simp only [phi]
  rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, Real.rpow_two]
  ring_nf

theorem sqrt_two_mul_self : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)

theorem rpow_half_neg_eq (a : ℝ) : (1 / 2 : ℝ) ^ (-a) = 2 ^ a := by
  rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]

theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]; ring

theorem phi_moment0 : ∫ w in Ioi (0:ℝ), w ^ 0 * phi w = √(π / 2) := by
  rw [integral_pow_mul_phi_gamma 0]
  norm_num
  rw [rpow_half_neg_eq, Gamma_three_halves,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp
  nlinarith [sqrt_two_mul_self]

theorem phi_moment1 : ∫ w in Ioi (0:ℝ), w ^ 1 * phi w = 2 := by
  rw [integral_pow_mul_phi_gamma 1]
  norm_num

theorem phi_moment2 : ∫ w in Ioi (0:ℝ), w ^ 2 * phi w = 3 * √(π / 2) := by
  rw [integral_pow_mul_phi_gamma 2]
  norm_num
  rw [rpow_half_neg_eq,
    show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Gamma_three_halves,
    show (3 / 2 + 1 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
    ← Real.sqrt_eq_rpow]
  norm_num
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp
  nlinarith [sqrt_two_mul_self]

/-! ## `∫ η_*` and `∫ (u − c)² η_*` -/

theorem etaU_nonneg (u : ℝ) : 0 ≤ etaU u := by
  rw [etaU_eq]
  refine setIntegral_nonneg measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have := phiPos_nonneg (u / r)
  have := eta2_nonneg r
  positivity

theorem etaU_of_nonpos {u : ℝ} (hu : u ≤ 0) : etaU u = 0 := by
  rw [etaU_eq]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r (hr : 0 < r) => ?_
  unfold phiPos
  rw [if_neg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hu hr.le))]; simp

theorem sqrt_pi_div_two_pos : 0 < √(π / 2) := Real.sqrt_pos.2 (by positivity)

theorem integrable_pow_mul_etaU (k : ℕ) (hk : k ≤ 2) : Integrable fun u => u ^ k * etaU u := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_pow_mul_etaU] at h0
  have hpos := sqrt_pi_div_two_pos
  interval_cases k
  · rw [eta2_moment0, phi_moment0] at h0; linarith
  · rw [eta2_moment1, phi_moment1] at h0; norm_num at h0
  · rw [eta2_moment2, phi_moment2] at h0; nlinarith

theorem integrable_etaU : Integrable etaU := by
  have := integrable_pow_mul_etaU 0 (by norm_num)
  simpa using this

theorem integral_etaU : ∫ u, etaU u = √(π / 2) := by
  have := integral_pow_mul_etaU 0
  simp only [pow_zero, one_mul] at this
  rw [this, show (fun v : ℝ => eta2 v) = fun v => v ^ 0 * eta2 v by ext; simp, eta2_moment0,
    show (fun w : ℝ => phi w) = fun w => w ^ 0 * phi w by ext; simp, phi_moment0, one_mul]

/-- `∫ (u − c)² η_*(u) du = (49/48)√(π/2) − (9/4)c + c²√(π/2)`. -/
theorem integral_sq_sub_mul_etaU (c : ℝ) :
    ∫ u, (u - c) ^ 2 * etaU u = 49 / 48 * √(π / 2) - 9 / 4 * c + c ^ 2 * √(π / 2) := by
  have i0 := integrable_pow_mul_etaU 0 (by norm_num)
  have i1 := integrable_pow_mul_etaU 1 (by norm_num)
  have i2 := integrable_pow_mul_etaU 2 (by norm_num)
  have e : (fun u => (u - c) ^ 2 * etaU u) =
      fun u => u ^ 2 * etaU u - 2 * c * (u ^ 1 * etaU u) + c ^ 2 * (u ^ 0 * etaU u) := by
    ext u; ring
  have iA : Integrable fun u => u ^ 2 * etaU u - 2 * c * (u ^ 1 * etaU u) := i2.sub (i1.const_mul _)
  have iB : Integrable fun u => c ^ 2 * (u ^ 0 * etaU u) := i0.const_mul _
  have iC : Integrable fun u => 2 * c * (u ^ 1 * etaU u) := i1.const_mul _
  rw [e, integral_add iA iB, integral_sub i2 iC,
    integral_const_mul, integral_const_mul, integral_pow_mul_etaU, integral_pow_mul_etaU,
    integral_pow_mul_etaU, eta2_moment0, eta2_moment1, eta2_moment2, phi_moment0, phi_moment1,
    phi_moment2]
  ring

/-! ## `C_{η◦,η_*}` -/

/-- `η_*` on the Fourier side: `(η₂ *_M φ)(κσ)` for `σ > 0`, and `0` for `σ ≤ 0`. -/
noncomputable def etaS (σ : ℝ) : ℝ := etaU (κ * σ)

theorem hκpos : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num

theorem integrable_etaS : Integrable etaS := integrable_etaU.comp_mul_left' hκpos.ne'

theorem integral_etaS : ∫ σ, etaS σ = √(π / 2) / κ := by
  unfold etaS
  rw [Measure.integral_comp_mul_left (fun u => etaU u) κ, integral_etaU, abs_of_pos (inv_pos.2 hκpos),
    smul_eq_mul]; ring

theorem integral_sq_sub_mul_etaS (c : ℝ) :
    ∫ σ, (σ - c / κ) ^ 2 * etaS σ =
      (49 / 48 * √(π / 2) - 9 / 4 * c + c ^ 2 * √(π / 2)) / κ ^ 3 := by
  unfold etaS
  have hκ := hκpos
  have e : (fun σ => (σ - c / κ) ^ 2 * etaU (κ * σ)) =
      fun σ => (1 / κ ^ 2) * ((fun u => (u - c) ^ 2 * etaU u) (κ * σ)) := by
    ext σ; simp only; field_simp
  rw [e, integral_const_mul, Measure.integral_comp_mul_left (fun u => (u - c) ^ 2 * etaU u) κ,
    integral_sq_sub_mul_etaU, abs_of_pos (inv_pos.2 hκ), smul_eq_mul]
  field_simp

theorem etaO_le_one (t : ℝ) : |etaO t| ≤ 1 := by
  unfold etaO
  by_cases h : t ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem h]
    unfold P0
    have h1 : 0 ≤ t * (2 - t) := mul_nonneg h.1 (by linarith [h.2])
    have h2 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have h3 : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [abs_of_nonneg (by positivity)]
    calc (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 ^ 3 * 1 := by
          gcongr
      _ = 1 := by norm_num
  · rw [indicator_of_notMem h]; simp

theorem measurable_conv2 : Measurable conv2 := by
  have h : Measurable (Function.uncurry fun ρ t : ℝ => etaO t * etaO (ρ - t)) :=
    (measurable_etaO.comp measurable_snd).mul (measurable_etaO.comp (measurable_fst.sub measurable_snd))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

theorem abs_conv2_le (ρ : ℝ) : |conv2 ρ| ≤ 2 := by
  unfold conv2
  have hb : ∀ t, |etaO t * etaO (ρ - t)| ≤ (Icc (0 : ℝ) 2).indicator 1 t := by
    intro t
    by_cases h : t ∈ Icc (0 : ℝ) 2
    · rw [indicator_of_mem h, Pi.one_apply, abs_mul]
      nlinarith [etaO_le_one t, etaO_le_one (ρ - t), abs_nonneg (etaO t), abs_nonneg (etaO (ρ - t))]
    · rw [indicator_of_notMem h, etaO_eq_zero_of_notMem h]; simp
  have hi : Integrable ((Icc (0 : ℝ) 2).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  calc |∫ t, etaO t * etaO (ρ - t)| ≤ ∫ t, |etaO t * etaO (ρ - t)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, (Icc (0 : ℝ) 2).indicator 1 t :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hi
          (Filter.Eventually.of_forall hb)
    _ = 2 := by
        rw [integral_indicator_one measurableSet_Icc]
        simp only [Real.volume_Icc, measureReal_def]
        rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num

/-- **`C_{η◦,η_*}(M) = ∫∫ η◦(t₁)η◦(t₂)η_*(M − t₁ − t₂) = ∫ (η◦ ∗ η◦)(M − σ) η_*(σ) dσ`** [B, (10.37)]. -/
noncomputable def Cmain (M : ℝ) : ℝ := ∫ σ, conv2 (M - σ) * etaS σ

/-- **[B, (11.6)], with constant `8.82`**: for `M = 2 + c/κ`,
`C_{η◦,η_*}(M) ≥ ‖η◦‖₂² ∫η_* − 8.82 ∫(σ − c/κ)² η_*(σ) dσ`. -/
theorem Cmain_ge (c : ℝ) :
    (∫ t, etaO t ^ 2) * (√(π / 2) / κ) -
        8.82 * ((49 / 48 * √(π / 2) - 9 / 4 * c + c ^ 2 * √(π / 2)) / κ ^ 3) ≤
      Cmain (2 + c / κ) := by
  have hS0 : ∀ σ, 0 ≤ etaS σ := fun σ => etaU_nonneg _
  have hJ : Integrable fun σ => (σ - c / κ) ^ 2 * etaS σ := by
    have h := (integrable_pow_mul_etaU 2 (by norm_num)).sub
      (((integrable_pow_mul_etaU 1 (by norm_num)).const_mul (2 * c)).sub
        ((integrable_pow_mul_etaU 0 (by norm_num)).const_mul (c ^ 2)))
    have h' := h.comp_mul_left' hκpos.ne'
    refine (h'.const_mul (1 / κ ^ 2)).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [Function.comp, etaS, Pi.sub_apply]
    have hκ := hκpos
    field_simp; ring
  have hlow : Integrable fun σ => (∫ t, etaO t ^ 2) * etaS σ - 8.82 * ((σ - c / κ) ^ 2 * etaS σ) :=
    (integrable_etaS.const_mul _).sub (hJ.const_mul _)
  have hC : Integrable fun σ => conv2 (2 + c / κ - σ) * etaS σ := by
    refine Integrable.mono' (integrable_etaS.const_mul 2) ?_ (Filter.Eventually.of_forall fun σ => ?_)
    · exact ((measurable_conv2.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        integrable_etaS.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hS0 σ)]
      exact mul_le_mul_of_nonneg_right (abs_conv2_le _) (hS0 σ)
  have hpt : ∀ σ, (∫ t, etaO t ^ 2) * etaS σ - 8.82 * ((σ - c / κ) ^ 2 * etaS σ) ≤
      conv2 (2 + c / κ - σ) * etaS σ := by
    intro σ
    have h := conv2_ge (2 + c / κ - σ)
    rw [show 2 - (2 + c / κ - σ) = σ - c / κ by ring] at h
    have h2 := mul_le_mul_of_nonneg_right h (hS0 σ)
    linarith
  calc (∫ t, etaO t ^ 2) * (√(π / 2) / κ) -
        8.82 * ((49 / 48 * √(π / 2) - 9 / 4 * c + c ^ 2 * √(π / 2)) / κ ^ 3)
      = ∫ σ, ((∫ t, etaO t ^ 2) * etaS σ - 8.82 * ((σ - c / κ) ^ 2 * etaS σ)) := by
        rw [integral_sub (integrable_etaS.const_mul _) (hJ.const_mul _), integral_const_mul,
          integral_const_mul, integral_etaS, integral_sq_sub_mul_etaS]
    _ ≤ ∫ σ, conv2 (2 + c / κ - σ) * etaS σ := integral_mono hlow hC hpt
    _ = Cmain (2 + c / κ) := rfl

end TernaryGoldbach.MajorArcs
