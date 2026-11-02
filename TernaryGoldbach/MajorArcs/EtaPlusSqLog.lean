import TernaryGoldbach.MajorArcs.HHFourier2
import TernaryGoldbach.MajorArcs.EtaONum

/-!
# [B, (9.94)]: `∫ η₊² log(xt) dt`, from `η◦` and Parseval

With `A = ∫₀^∞ η₊²` and `B = ∫₀^∞ η₊² log t`, `∫ η₊² log(xt) = A log x + B`. Write
`η₊² = η◦² + 2(η₊ − η◦)η◦ + (η₊ − η◦)²`.
* The `η◦` integrals are elementary (`η◦ = (t(2 − t))³ e^{−(t−1)²/2}` on `[0, 2]`); they are a
  computation (`etaO_integrals`).
* `(η₊ − η◦)²`: `‖η₊ − η◦‖₂² ≤ 368/(2·200⁴)` (`HHFourier2.lean`), and with the weight `|log t|` the
  same bound times `0.37`.
* The cross terms: in `u = log t`, `(η₊ − η◦)η◦ dt = (g_H − g)(u) W(u) du` with
  `W = g · e^{3u − e^{2u}}` (and `u W` for the `log t` weight). Since `g − g_H` has its Fourier
  transform supported on `|ξ| > H/2π`, Parseval gives `|∫ (g_H − g) W| ≤ ∫_{|ξ| > H/2π} |ĝ| |Ŵ|`, and
  both tails are `O(H⁻⁴)` (`‖g''‖₂`, `‖W''‖₂`). This replaces [B]'s Cauchy–Schwarz on all of `L²`,
  which loses a factor `10⁶` here.
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (hBase hH etaPlus hP hP' hasDerivAt_hP continuous_hP' hBase_eq_hP)

/-! ### The weights `W₀ = g E` and `W₁ = u g E` -/

/-- `E(u) = e^{3u} e^{−e^{2u}}`. -/
noncomputable def Ew (u : ℝ) : ℝ := Real.exp u ^ 3 * Real.exp (-(Real.exp u) ^ 2)
noncomputable def Ew' (u : ℝ) : ℝ := (3 - 2 * Real.exp u ^ 2) * Ew u
noncomputable def Ew'' (u : ℝ) : ℝ := ((3 - 2 * Real.exp u ^ 2) ^ 2 - 4 * Real.exp u ^ 2) * Ew u

theorem hasDerivAt_Ew (u : ℝ) : HasDerivAt Ew (Ew' u) u := by
  have he := Real.hasDerivAt_exp u
  have h1 := he.pow 3
  have h2 := ((he.pow 2).neg).exp
  have := h1.mul h2
  unfold Ew'
  convert this using 1
  · funext v; simp only [Ew, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply]
  · simp only [Ew, Pi.pow_apply, Pi.neg_apply]; push_cast; ring

theorem hasDerivAt_Ew' (u : ℝ) : HasDerivAt Ew' (Ew'' u) u := by
  have he := Real.hasDerivAt_exp u
  have h1 : HasDerivAt (fun u => 3 - 2 * Real.exp u ^ 2) (-(2 * (2 * Real.exp u * Real.exp u))) u := by
    have := ((he.pow 2).const_mul 2).const_sub 3
    convert this using 1; push_cast; ring
  have := h1.mul (hasDerivAt_Ew u)
  unfold Ew''
  have e : Ew' = fun u => (3 - 2 * Real.exp u ^ 2) * Ew u := rfl
  rw [e]
  convert this using 1
  unfold Ew'; ring

noncomputable def W0 (u : ℝ) : ℝ := gL u * Ew u
noncomputable def W0' (u : ℝ) : ℝ := gL' u * Ew u + gL u * Ew' u
noncomputable def W0'' (u : ℝ) : ℝ := gL'' u * Ew u + 2 * (gL' u * Ew' u) + gL u * Ew'' u

theorem hasDerivAt_W0 (u : ℝ) : HasDerivAt W0 (W0' u) u :=
  (hasDerivAt_gL u).mul (hasDerivAt_Ew u)

theorem hasDerivAt_W0' (u : ℝ) : HasDerivAt W0' (W0'' u) u := by
  have := ((hasDerivAt_gL' u).mul (hasDerivAt_Ew u)).add ((hasDerivAt_gL u).mul (hasDerivAt_Ew' u))
  convert this using 1
  · funext v; simp only [W0', Pi.add_apply, Pi.mul_apply]
  · unfold W0''; ring

noncomputable def W1 (u : ℝ) : ℝ := u * W0 u
noncomputable def W1' (u : ℝ) : ℝ := W0 u + u * W0' u
noncomputable def W1'' (u : ℝ) : ℝ := 2 * W0' u + u * W0'' u

theorem hasDerivAt_W1 (u : ℝ) : HasDerivAt W1 (W1' u) u := by
  have := (hasDerivAt_id' u).mul (hasDerivAt_W0 u)
  convert this using 1
  · funext v; simp only [W1, Pi.mul_apply]
  · unfold W1'; ring

theorem hasDerivAt_W1' (u : ℝ) : HasDerivAt W1' (W1'' u) u := by
  have := (hasDerivAt_W0 u).add ((hasDerivAt_id' u).mul (hasDerivAt_W0' u))
  convert this using 1
  · funext v; simp only [W1', Pi.add_apply, Pi.mul_apply]
  · unfold W1''; ring

/-! ### Fourier tails -/

/-- **`∫_{|ξ| > H/2π} |Ŵ|² ≤ ‖W''‖₂²/H⁴`** for `W ∈ C²` with `W, W', W''` integrable and
`W'' ∈ L²` (as `tail_fourier_gC_le'`). -/
theorem tail_fourier_le_deriv2 {W W' W'' : ℝ → ℝ} (hW : ∀ u, HasDerivAt W (W' u) u)
    (hW' : ∀ u, HasDerivAt W' (W'' u) u) (i0 : Integrable W) (i1 : Integrable W')
    (i2 : Integrable W'') (i22 : Integrable fun u => W'' u ^ 2) {H : ℝ} (hH0 : 0 < H) :
    ∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 (fun u => (W u : ℂ)) ξ‖ ^ 2 ≤
      (∫ u, W'' u ^ 2) / H ^ 4 := by
  set S := Icc (-(H / (2 * π))) (H / (2 * π)) with hS
  have hπ := Real.pi_pos
  set WC : ℝ → ℂ := fun u => (W u : ℂ) with hWC
  set W'C : ℝ → ℂ := fun u => (W' u : ℂ) with hW'C
  set W''C : ℝ → ℂ := fun u => (W'' u : ℂ) with hW''C
  have hint : Integrable WC := i0.ofReal
  have hint' : Integrable W'C := i1.ofReal
  have hint'' : Integrable W''C := i2.ofReal
  have hdiff : Differentiable ℝ WC := fun u => ((hW u).ofReal_comp).differentiableAt
  have hdiff' : Differentiable ℝ W'C := fun u => ((hW' u).ofReal_comp).differentiableAt
  have hder : deriv WC = W'C := by ext u; exact ((hW u).ofReal_comp).deriv
  have hder' : deriv W'C = W''C := by ext u; exact ((hW' u).ofReal_comp).deriv
  have hL2'' : MemLp W''C 2 := by
    refine (memLp_two_iff_integrable_sq_norm hint''.aestronglyMeasurable).2 ?_
    have : (fun u => ‖W''C u‖ ^ 2) = fun u => W'' u ^ 2 := by
      ext u; rw [hW''C, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this]; exact i22
  have hfd1 := Real.fourier_deriv hint hdiff (by rw [hder]; exact hint')
  rw [hder] at hfd1
  have hfd2 := Real.fourier_deriv hint' hdiff' (by rw [hder']; exact hint'')
  rw [hder'] at hfd2
  have hF'' := TernaryGoldbach.memLp_fourier hint'' hL2''
  have hint2 : Integrable fun ξ => ‖𝓕 W''C ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hF''.aestronglyMeasurable).1 hF''
  have hpl := TernaryGoldbach.integral_norm_sq_fourier hint'' hL2''
  have hle : ∀ ξ ∈ Sᶜ, ‖𝓕 WC ξ‖ ^ 2 ≤ ‖𝓕 W''C ξ‖ ^ 2 / H ^ 4 := by
    intro ξ hξ
    have h1 : H ≤ 2 * π * |ξ| := by
      simp only [hS, mem_compl_iff, mem_Icc, not_and_or, not_le] at hξ
      have : H / (2 * π) ≤ |ξ| := by
        rcases hξ with h | h
        · have h0 : 0 ≤ H / (2 * π) := by positivity
          have hneg : ξ < 0 := by linarith
          rw [abs_of_neg hneg]; linarith
        · exact h.le.trans (le_abs_self ξ)
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have e1 : 𝓕 W'C ξ = (2 * π * I * ξ) • 𝓕 WC ξ := congrFun hfd1 ξ
    have e2 : 𝓕 W''C ξ = (2 * π * I * ξ) • 𝓕 W'C ξ := congrFun hfd2 ξ
    have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
      rw [show (2 * π * I * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hπ]
      norm_num
    have e3 : ‖𝓕 W''C ξ‖ = (2 * π * |ξ|) * ((2 * π * |ξ|) * ‖𝓕 WC ξ‖) := by
      rw [e2, e1, smul_eq_mul, smul_eq_mul, norm_mul (2 * π * I * ξ : ℂ),
        norm_mul (2 * π * I * ξ : ℂ), hn]
    rw [e3, le_div_iff₀ (by positivity)]
    have h4 : H ^ 4 ≤ (2 * π * |ξ|) ^ 4 := pow_le_pow_left₀ hH0.le h1 4
    have hn0 := norm_nonneg (𝓕 WC ξ)
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖𝓕 WC ξ‖)]
  have hmeas : MeasurableSet Sᶜ := measurableSet_Icc.compl
  calc ∫ ξ in Sᶜ, ‖𝓕 WC ξ‖ ^ 2 ≤ ∫ ξ in Sᶜ, ‖𝓕 W''C ξ‖ ^ 2 / H ^ 4 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (hint2.div_const _).integrableOn
          ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hle))
    _ ≤ ∫ ξ, ‖𝓕 W''C ξ‖ ^ 2 / H ^ 4 :=
        setIntegral_le_integral (hint2.div_const _)
          (Filter.Eventually.of_forall fun _ => by positivity)
    _ = (∫ u, ‖W''C u‖ ^ 2) / H ^ 4 := by rw [integral_div, hpl]
    _ = (∫ u, W'' u ^ 2) / H ^ 4 := by
        congr 1; congr 1; ext u; rw [hW''C, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### Parseval and the cross term -/

/-- **Parseval** for `L¹ ∩ L²`: `∫ conj(f̂) ĝ = ∫ conj(f) g`. -/
theorem integral_conj_mul_fourier {f g : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2)
    (hg1 : Integrable g) (hg2 : MemLp g 2) :
    ∫ ξ, (starRingEnd ℂ) (𝓕 f ξ) * 𝓕 g ξ = ∫ x, (starRingEnd ℂ) (f x) * g x := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f
  set G : Lp ℂ 2 (volume : Measure ℝ) := hg2.toLp g
  have hF := TernaryGoldbach.fourierL2_ae_eq hf1 hf2
  have hG := TernaryGoldbach.fourierL2_ae_eq hg1 hg2
  have hFf : (F : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hGg : (G : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have h := Lp.inner_fourier_eq F G
  rw [L2.inner_def, L2.inner_def] at h
  simp_rw [RCLike.inner_apply'] at h
  calc ∫ ξ, (starRingEnd ℂ) (𝓕 f ξ) * 𝓕 g ξ
      = ∫ ξ, (starRingEnd ℂ) (((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) *
          ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ :=
        integral_congr_ae (by filter_upwards [hF, hG] with ξ h1 h2; rw [h1, h2])
    _ = ∫ x, (starRingEnd ℂ) ((F : ℝ → ℂ) x) * (G : ℝ → ℂ) x := h
    _ = ∫ x, (starRingEnd ℂ) (f x) * g x :=
        integral_congr_ae (by filter_upwards [hFf, hGg] with x h1 h2; rw [h1, h2])

/-- `∫ g_H(u) w(u) du = ∫ K(ξ) ŵ(−ξ) dξ` (Fubini). -/
theorem integral_gH_mul (H : ℝ) {w : ℝ → ℂ} (hw : Integrable w) (hwc : Continuous w) :
    ∫ u, 𝓕 (Kc H) (-u) * w u = ∫ ξ, Kc H ξ * 𝓕 w (-ξ) := by
  have e1 : ∀ u, 𝓕 (Kc H) (-u) * w u =
      ∫ ξ, Complex.exp (↑(-2 * π * ξ * -u) * I) * Kc H ξ * w u := by
    intro u; rw [Real.fourier_real_eq_integral_exp_smul, ← integral_mul_const]; simp_rw [smul_eq_mul]
  simp_rw [e1]
  rw [integral_integral_swap]
  · congr 1; ext ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1; ext u; rw [smul_eq_mul]; ring_nf
  · refine Integrable.mono' (hw.norm.mul_prod (integrable_Kc H).norm) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · have hK : Measurable (Kc H) :=
        continuous_fourier_gC.measurable.indicator measurableSet_Icc
      exact (((by fun_prop : Measurable fun p : ℝ × ℝ => Complex.exp (↑(-2 * π * p.2 * -p.1) * I)).mul
        (hK.comp measurable_snd)).mul (hwc.measurable.comp measurable_fst)).aestronglyMeasurable
    · rcases p with ⟨u, ξ⟩
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_of_eq (by ring)

/-- `conj(Ŵ(ξ)) = Ŵ(−ξ)` for real `W`. -/
theorem conj_fourier_real (W : ℝ → ℝ) (ξ : ℝ) :
    (starRingEnd ℂ) (𝓕 (fun u => (W u : ℂ)) ξ) = 𝓕 (fun u => (W u : ℂ)) (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  congr 1; ext u
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2; push_cast; ring

/-- **The cross term**: for real `W ∈ L¹ ∩ L²` (continuous) and `λ > 0`,
`|∫ (g_H − g) W| ≤ (λ T_g + T_W/λ)/2`, where `T` is the `L²` mass of the Fourier transform beyond
`H/2π`. -/
theorem abs_cross_le {W : ℝ → ℝ} (iW : Integrable W) (mW : MemLp W 2) (cW : Continuous W)
    (H : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    |(∫ u, (𝓕 (Kc H) (-u) - gC u) * (W u : ℂ)).re| ≤
      (lam * (∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 gC ξ‖ ^ 2) +
        (∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 (fun u => (W u : ℂ)) ξ‖ ^ 2) / lam) / 2 := by
  set S := Icc (-(H / (2 * π))) (H / (2 * π)) with hS
  set WC : ℝ → ℂ := fun u => (W u : ℂ) with hWC
  have iWC : Integrable WC := iW.ofReal
  have mWC : MemLp WC 2 := mW.ofReal
  have cWC : Continuous WC := Complex.continuous_ofReal.comp cW
  have hFg := TernaryGoldbach.memLp_fourier integrable_gC memLp_gC
  have hFW := TernaryGoldbach.memLp_fourier iWC mWC
  -- integrability of the pieces
  have iGH : Integrable fun u => 𝓕 (Kc H) (-u) * WC u :=
    (memLp_gH H).integrable_mul mWC
  have iG : Integrable fun u => gC u * WC u := memLp_gC.integrable_mul mWC
  have hFWneg : MemLp (fun ξ => 𝓕 WC (-ξ)) 2 := hFW.comp_measurePreserving (Measure.measurePreserving_neg _)
  have iK : Integrable fun ξ => Kc H ξ * 𝓕 WC (-ξ) := (memLp_Kc H).integrable_mul hFWneg
  have iFg : Integrable fun ξ => 𝓕 gC ξ * 𝓕 WC (-ξ) := hFg.integrable_mul hFWneg
  -- the two halves
  have h1 : ∫ u, 𝓕 (Kc H) (-u) * WC u = ∫ ξ, Kc H ξ * 𝓕 WC (-ξ) := integral_gH_mul H iWC cWC
  have h2 : (∫ u, gC u * WC u).re = (∫ ξ, 𝓕 gC ξ * 𝓕 WC (-ξ)).re := by
    have hp := integral_conj_mul_fourier integrable_gC memLp_gC iWC mWC
    have e1 : ∫ x, (starRingEnd ℂ) (gC x) * WC x = ∫ x, gC x * WC x := by
      congr 1; ext x; simp [gC, Complex.conj_ofReal]
    have e2 : (∫ ξ, (starRingEnd ℂ) (𝓕 gC ξ) * 𝓕 WC ξ).re = (∫ ξ, 𝓕 gC ξ * 𝓕 WC (-ξ)).re := by
      rw [← Complex.conj_re, ← integral_conj]
      congr 2; ext ξ
      rw [map_mul, Complex.conj_conj, conj_fourier_real W ξ]
    rw [← e1, ← hp, e2]
  -- the difference is `−∫_{Sᶜ} ĝ(ξ) Ŵ(−ξ)`
  have hdiff : (∫ u, (𝓕 (Kc H) (-u) - gC u) * WC u).re =
      -(∫ ξ, Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ)).re := by
    have e : (fun u => (𝓕 (Kc H) (-u) - gC u) * WC u) =
        fun u => 𝓕 (Kc H) (-u) * WC u - gC u * WC u := by ext u; ring
    rw [e, integral_sub iGH iG, Complex.sub_re, h1, h2]
    have hKind : ∀ ξ, Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ) =
        𝓕 gC ξ * 𝓕 WC (-ξ) - Kc H ξ * 𝓕 WC (-ξ) := by
      intro ξ
      have hK : Kc H = S.indicator (𝓕 gC) := rfl
      rw [hK]
      by_cases h : ξ ∈ S
      · rw [indicator_of_notMem (Set.notMem_compl_iff.2 h), indicator_of_mem h]; ring
      · rw [indicator_of_mem (show ξ ∈ Sᶜ from h), indicator_of_notMem h]; ring
    simp_rw [hKind]
    rw [integral_sub iFg iK, Complex.sub_re]; ring
  rw [hdiff, abs_neg]
  -- `|Re ∫ φ| ≤ ∫ ‖φ‖ ≤ ∫ (λ‖ĝ‖² + ‖Ŵ‖²/λ)/2 on Sᶜ`
  have hmeas : MeasurableSet Sᶜ := measurableSet_Icc.compl
  have iA : Integrable fun ξ => ‖𝓕 gC ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hFg.aestronglyMeasurable).1 hFg
  have iB : Integrable fun ξ => ‖𝓕 WC ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hFW.aestronglyMeasurable).1 hFW
  have hpt : ∀ ξ, ‖Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ)‖ ≤
      Sᶜ.indicator (fun ξ => (lam * ‖𝓕 gC ξ‖ ^ 2 + ‖𝓕 WC ξ‖ ^ 2 / lam) / 2) ξ := by
    intro ξ
    have hn : ‖𝓕 WC (-ξ)‖ = ‖𝓕 WC ξ‖ := by
      rw [← conj_fourier_real W ξ, Complex.norm_conj]
    by_cases h : ξ ∈ Sᶜ
    · rw [indicator_of_mem h, indicator_of_mem h, norm_mul, hn]
      have ha := norm_nonneg (𝓕 gC ξ)
      have hb := norm_nonneg (𝓕 WC ξ)
      have : 0 ≤ (lam * ‖𝓕 gC ξ‖ - ‖𝓕 WC ξ‖) ^ 2 := sq_nonneg _
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have e : (lam * ‖𝓕 gC ξ‖ ^ 2 + ‖𝓕 WC ξ‖ ^ 2 / lam) = (lam ^ 2 * ‖𝓕 gC ξ‖ ^ 2 + ‖𝓕 WC ξ‖ ^ 2) / lam := by
        field_simp
      rw [e, le_div_iff₀ hlam]
      nlinarith
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul, norm_zero]
  calc |(∫ ξ, Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ)).re|
      ≤ ‖∫ ξ, Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ ξ, ‖Sᶜ.indicator (𝓕 gC) ξ * 𝓕 WC (-ξ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, Sᶜ.indicator (fun ξ => (lam * ‖𝓕 gC ξ‖ ^ 2 + ‖𝓕 WC ξ‖ ^ 2 / lam) / 2) ξ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (((iA.const_mul lam).add (iB.div_const lam)).div_const 2 |>.indicator hmeas)
          (Filter.Eventually.of_forall hpt)
    _ = (lam * (∫ ξ in Sᶜ, ‖𝓕 gC ξ‖ ^ 2) + (∫ ξ in Sᶜ, ‖𝓕 WC ξ‖ ^ 2) / lam) / 2 := by
        rw [integral_indicator hmeas, integral_div, integral_add (iA.const_mul lam).integrableOn
          (iB.div_const lam).integrableOn, integral_const_mul, integral_div]

/-! ### The weights as functions of `t = eᵘ` -/

/-- `IF W k`: `W(u) = eᵘ · 1_{[0,2]}(eᵘ) k(eᵘ)` (so `W` is integrable when `k` is continuous). -/
def IF (W k : ℝ → ℝ) : Prop := ∀ u, W u = Real.exp u * (Icc (0 : ℝ) 2).indicator k (Real.exp u)

theorem IF.integrable {W k : ℝ → ℝ} (h : IF W k) (hk : Continuous k) : Integrable W := by
  have e : W = fun u => Real.exp u • (Icc (0 : ℝ) 2).indicator k (Real.exp u) := by
    ext u; rw [h u, smul_eq_mul]
  rw [e, integrable_comp_exp]
  exact ((integrable_indicator_iff measurableSet_Icc).2 hk.integrableOn_Icc).integrableOn

theorem IF.sq {W k : ℝ → ℝ} (h : IF W k) : IF (fun u => W u ^ 2) (fun t => t * k t ^ 2) := by
  intro u
  simp only [h u]
  by_cases hm : Real.exp u ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem hm, indicator_of_mem hm]; ring
  · rw [indicator_of_notMem hm, indicator_of_notMem hm]; ring

/-- The pieces of `g` in `t = eᵘ`. -/
theorem gL_cases (u : ℝ) : (Real.exp u ≤ 2 ∧ gL u = hP (Real.exp u) ∧
      gL' u = Real.exp u * hP' (Real.exp u) ∧
      gL'' u = Real.exp u * (Real.exp u * hP'' (Real.exp u) + hP' (Real.exp u))) ∨
    (2 < Real.exp u ∧ gL u = 0 ∧ gL' u = 0 ∧ gL'' u = 0) := by
  have he := Real.exp_pos u
  rcases le_or_gt (Real.exp u) 2 with h | h
  · left
    refine ⟨h, hBase_eq_hP he.le h, ?_, ?_⟩
    · rw [gL', hBd, if_pos h]; ring
    · rw [gL'', hBdd, hBd, if_pos h, if_pos h]; ring
  · right
    refine ⟨h, hBase_of_two_le h.le, ?_, ?_⟩
    · rw [gL', hBd, if_neg (not_le.2 h)]; ring
    · rw [gL'', hBdd, hBd, if_neg (not_le.2 h), if_neg (not_le.2 h)]; ring

/-- From the pieces: `W(u) = eᵘ 1_{[0,2]}(eᵘ) k(eᵘ)` when `W(u) = F(eᵘ, g, g', g'')` vanishes with `g`. -/
theorem IF_of_cases {W k : ℝ → ℝ}
    (h1 : ∀ u, Real.exp u ≤ 2 → gL u = hP (Real.exp u) → gL' u = Real.exp u * hP' (Real.exp u) →
      gL'' u = Real.exp u * (Real.exp u * hP'' (Real.exp u) + hP' (Real.exp u)) →
      W u = Real.exp u * k (Real.exp u))
    (h2 : ∀ u, 2 < Real.exp u → gL u = 0 → gL' u = 0 → gL'' u = 0 → W u = 0) : IF W k := by
  intro u
  have he := Real.exp_pos u
  rcases gL_cases u with ⟨h, a, b, c⟩ | ⟨h, a, b, c⟩
  · rw [indicator_of_mem (show Real.exp u ∈ Icc (0 : ℝ) 2 from ⟨he.le, h⟩)]; exact h1 u h a b c
  · rw [indicator_of_notMem (fun hm => by linarith [hm.2]), mul_zero]; exact h2 u h a b c

/-- The `t`-forms (`W(u) = eᵘ k(eᵘ)` on `eᵘ ≤ 2`). -/
noncomputable def k0 (t : ℝ) : ℝ := hP t * t ^ 2 * Real.exp (-t ^ 2)
noncomputable def k0' (t : ℝ) : ℝ :=
  (t * hP' t + hP t * (3 - 2 * t ^ 2)) * t ^ 2 * Real.exp (-t ^ 2)
noncomputable def k0'' (t : ℝ) : ℝ :=
  (t * (t * hP'' t + hP' t) + 2 * (t * hP' t * (3 - 2 * t ^ 2)) +
    hP t * ((3 - 2 * t ^ 2) ^ 2 - 4 * t ^ 2)) * t ^ 2 * Real.exp (-t ^ 2)
noncomputable def k1 (t : ℝ) : ℝ := (t * Real.log t) * (hP t * t * Real.exp (-t ^ 2))
noncomputable def k1' (t : ℝ) : ℝ :=
  k0 t + (t * Real.log t) * ((t * hP' t + hP t * (3 - 2 * t ^ 2)) * t * Real.exp (-t ^ 2))
noncomputable def k1'' (t : ℝ) : ℝ :=
  2 * k0' t + (t * Real.log t) * ((t * (t * hP'' t + hP' t) + 2 * (t * hP' t * (3 - 2 * t ^ 2)) +
    hP t * ((3 - 2 * t ^ 2) ^ 2 - 4 * t ^ 2)) * t * Real.exp (-t ^ 2))

theorem continuous_hP : Continuous hP := by unfold hP; fun_prop
theorem continuous_hPdd : Continuous hP'' := by unfold hP'' pP pP'; fun_prop
theorem continuous_k0 : Continuous k0 := by
  unfold k0; have := continuous_hP; fun_prop
theorem continuous_k0' : Continuous k0' := by
  unfold k0'; have := continuous_hP; have := continuous_hP'; fun_prop
theorem continuous_k0'' : Continuous k0'' := by
  unfold k0''; have := continuous_hP; have := continuous_hP'; have := continuous_hPdd; fun_prop
theorem continuous_k1 : Continuous k1 := by
  unfold k1; have := continuous_hP; exact Real.continuous_mul_log.mul (by fun_prop)
theorem continuous_k1' : Continuous k1' := by
  unfold k1'; have := continuous_hP; have := continuous_hP'
  exact continuous_k0.add (Real.continuous_mul_log.mul (by fun_prop))
theorem continuous_k1'' : Continuous k1'' := by
  unfold k1''; have := continuous_hP; have := continuous_hP'; have := continuous_hPdd
  exact (continuous_const.mul continuous_k0').add (Real.continuous_mul_log.mul (by fun_prop))

theorem IF_W0 : IF W0 k0 := IF_of_cases
  (fun u _ a _ _ => by simp only [W0, Ew, k0, a]; ring)
  (fun u _ a _ _ => by simp only [W0, a, zero_mul])
theorem IF_W0' : IF W0' k0' := IF_of_cases
  (fun u _ a b _ => by simp only [W0', Ew, Ew', k0', a, b]; ring)
  (fun u _ a b _ => by simp only [W0', a, b]; ring)
theorem IF_W0'' : IF W0'' k0'' := IF_of_cases
  (fun u _ a b c => by simp only [W0'', Ew, Ew', Ew'', k0'', a, b, c]; ring)
  (fun u _ a b c => by simp only [W0'', a, b, c]; ring)
theorem IF_W1 : IF W1 k1 := IF_of_cases
  (fun u _ a _ _ => by simp only [W1, W0, Ew, k1, a, Real.log_exp]; ring)
  (fun u _ a _ _ => by simp only [W1, W0, a]; ring)
theorem IF_W1' : IF W1' k1' := IF_of_cases
  (fun u _ a b _ => by simp only [W1', W0, W0', Ew, Ew', k1', k0, a, b, Real.log_exp]; ring)
  (fun u _ a b _ => by simp only [W1', W0, W0', a, b]; ring)
theorem IF_W1'' : IF W1'' k1'' := IF_of_cases
  (fun u _ a b c => by
    simp only [W1'', W0', W0'', Ew, Ew', Ew'', k1'', k0', a, b, c, Real.log_exp]; ring)
  (fun u _ a b c => by simp only [W1'', W0', W0'', a, b, c]; ring)

theorem integrable_W0 : Integrable W0 := IF_W0.integrable continuous_k0
theorem integrable_W0' : Integrable W0' := IF_W0'.integrable continuous_k0'
theorem integrable_W0'' : Integrable W0'' := IF_W0''.integrable continuous_k0''
theorem integrable_W1 : Integrable W1 := IF_W1.integrable continuous_k1
theorem integrable_W1' : Integrable W1' := IF_W1'.integrable continuous_k1'
theorem integrable_W1'' : Integrable W1'' := IF_W1''.integrable continuous_k1''
theorem integrable_W0_sq : Integrable fun u => W0 u ^ 2 :=
  IF_W0.sq.integrable (by have := continuous_k0; fun_prop)
theorem integrable_W1_sq : Integrable fun u => W1 u ^ 2 :=
  IF_W1.sq.integrable (by have := continuous_k1; fun_prop)
theorem integrable_W0''_sq : Integrable fun u => W0'' u ^ 2 :=
  IF_W0''.sq.integrable (by have := continuous_k0''; fun_prop)
theorem integrable_W1''_sq : Integrable fun u => W1'' u ^ 2 :=
  IF_W1''.sq.integrable (by have := continuous_k1''; fun_prop)

theorem continuous_W0 : Continuous W0 :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_W0 u).continuousAt
theorem continuous_W1 : Continuous W1 :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_W1 u).continuousAt

theorem memLp_W0 : MemLp W0 2 :=
  (memLp_two_iff_integrable_sq continuous_W0.aestronglyMeasurable).2 integrable_W0_sq
theorem memLp_W1 : MemLp W1 2 :=
  (memLp_two_iff_integrable_sq continuous_W1.aestronglyMeasurable).2 integrable_W1_sq

/-! ### `D = g_H − g` and the bounds on its pieces -/

/-- `D(u) = h_H(eᵘ) − g(u)`. -/
noncomputable def Dg (u : ℝ) : ℝ := hH 200 (Real.exp u) - gL u

theorem Dg_C (u : ℝ) : ((Dg u : ℝ) : ℂ) = 𝓕 (Kc 200) (-u) - gC u := by
  have h := hH_eq_fourier_K (H := 200) (by norm_num) (Real.exp_pos u)
  rw [Real.log_exp] at h
  rw [Dg, Complex.ofReal_sub, h, gC]

theorem continuous_gL : Continuous gL :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_gL u).continuousAt

theorem continuous_Dg : Continuous Dg := by
  have e : Dg = fun u => (𝓕 (Kc 200) (-u) - gC u).re := by
    ext u; rw [← Dg_C, Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp (((continuous_fourier_Kc 200).comp continuous_neg).sub
    (Complex.continuous_ofReal.comp continuous_gL))

theorem Dg_sq_eq (u : ℝ) : Dg u ^ 2 = ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 := by
  rw [norm_sub_rev, ← Dg_C, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integrable_Dg_sq : Integrable fun u => Dg u ^ 2 := by
  have hL2 := memLp_gC.sub (memLp_gH 200)
  have hint : Integrable fun u => ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  exact hint.congr (Filter.Eventually.of_forall fun u => (Dg_sq_eq u).symm)

theorem integral_Dg_sq_le : ∫ u, Dg u ^ 2 ≤ 368 / 200 ^ 4 := by
  simp_rw [Dg_sq_eq]
  rw [integral_norm_sq_gC_sub]
  exact tail_fourier_gC_le' (by norm_num)

theorem memLp_Dg : MemLp Dg 2 :=
  (memLp_two_iff_integrable_sq continuous_Dg.aestronglyMeasurable).2 integrable_Dg_sq

theorem memLp_gL : MemLp gL 2 :=
  (memLp_two_iff_integrable_sq continuous_gL.aestronglyMeasurable).2 integrable_gL_sq

/-- The cross term against a real weight `W`, as a real integral. -/
theorem cross_eq {W : ℝ → ℝ} :
    (∫ u, (𝓕 (Kc 200) (-u) - gC u) * (W u : ℂ)).re = ∫ u, Dg u * W u := by
  have e : (fun u => (𝓕 (Kc 200) (-u) - gC u) * (W u : ℂ)) = fun u => ((Dg u * W u : ℝ) : ℂ) := by
    ext u; rw [← Dg_C]; push_cast; ring
  rw [e, integral_complex_ofReal, Complex.ofReal_re]

/-- `|∫ D W| ≤ (λ · 368 + M/λ)/(2 H⁴)` when `‖W''‖₂² ≤ M`. -/
theorem abs_integral_Dg_mul_le {W W' W'' : ℝ → ℝ} (hW : ∀ u, HasDerivAt W (W' u) u)
    (hW' : ∀ u, HasDerivAt W' (W'' u) u) (i0 : Integrable W) (i1 : Integrable W')
    (i2 : Integrable W'') (i22 : Integrable fun u => W'' u ^ 2) (m0 : MemLp W 2)
    (c0 : Continuous W) {M : ℝ} (hM : ∫ u, W'' u ^ 2 ≤ M) {lam : ℝ} (hlam : 0 < lam) :
    |∫ u, Dg u * W u| ≤ (lam * 368 + M / lam) / 2 / 200 ^ 4 := by
  rw [← cross_eq]
  refine (abs_cross_le i0 m0 c0 200 hlam).trans ?_
  have hg := tail_fourier_gC_le' (H := 200) (by norm_num)
  have hw := tail_fourier_le_deriv2 hW hW' i0 i1 i2 i22 (H := 200) (by norm_num)
  have hw' : (∫ u, W'' u ^ 2) / 200 ^ 4 ≤ M / 200 ^ 4 := by gcongr
  have h1 := mul_le_mul_of_nonneg_left hg hlam.le
  have h2 := div_le_div_of_nonneg_right (hw.trans hw') hlam.le
  calc (lam * _ + _ / lam) / 2 ≤ (lam * (368 / 200 ^ 4) + M / 200 ^ 4 / lam) / 2 := by gcongr
    _ = (lam * 368 + M / lam) / 2 / 200 ^ 4 := by field_simp

/-- `E(u) ≤ 1/2`. -/
theorem Ew_le (u : ℝ) : Ew u ≤ 1 / 2 := cube_mul_exp_neg_sq_le (Real.exp_pos u).le

theorem Ew_nonneg (u : ℝ) : 0 ≤ Ew u := by unfold Ew; positivity

/-- `|u| E(u) ≤ 0.37`: with `s = eᵘ`, `≤ s² e^{−s²} ≤ 1/e` for `s ≤ 1` and `≤ s⁴e^{−s²}/e ≤ 4/e³`
for `s ≥ 1`. -/
theorem abs_mul_Ew_le (u : ℝ) : |u| * Ew u ≤ 0.37 := by
  have he := Real.exp_one_gt_d9
  set s := Real.exp u with hs
  have hs0 : 0 < s := Real.exp_pos u
  have hE : Ew u = s ^ 3 * Real.exp (-s ^ 2) := rfl
  rcases le_or_gt u 0 with hu | hu
  · -- `|u| = −u ≤ e^{−u}`, so `|u| E ≤ s² e^{−s²} ≤ e^{−1}`
    have h1 : -u ≤ Real.exp (-u) := by have := Real.add_one_le_exp (-u); linarith
    have h2 : Real.exp (-u) * s = 1 := by rw [hs, ← Real.exp_add]; simp
    have h3 : s ^ 2 * Real.exp (-s ^ 2) ≤ Real.exp (-1) := by
      have := Real.add_one_le_exp (s ^ 2 - 1)
      have e1 : Real.exp (s ^ 2 - 1) * Real.exp (-s ^ 2) = Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; ring
      have := Real.exp_pos (-s ^ 2)
      nlinarith
    have h4 : Real.exp (-1) ≤ 0.37 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    rw [abs_of_nonpos hu, hE]
    have hE0 : 0 ≤ s ^ 3 * Real.exp (-s ^ 2) := by positivity
    calc -u * (s ^ 3 * Real.exp (-s ^ 2)) ≤ Real.exp (-u) * (s ^ 3 * Real.exp (-s ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 hE0
      _ = s ^ 2 * Real.exp (-s ^ 2) * (Real.exp (-u) * s) := by ring
      _ = s ^ 2 * Real.exp (-s ^ 2) := by rw [h2, mul_one]
      _ ≤ 0.37 := h3.trans h4
  · -- `u ≤ e^{u−1} = s/e`, so `|u| E ≤ s⁴ e^{−s²}/e ≤ 4/e³`
    have h1 : u ≤ Real.exp (u - 1) := by have := Real.add_one_le_exp (u - 1); linarith
    have h2 : Real.exp (u - 1) = s * Real.exp (-1) := by rw [hs, ← Real.exp_add]; ring_nf
    have h3 : s ^ 4 * Real.exp (-s ^ 2) ≤ 4 * Real.exp (-2) := by
      have h := Real.add_one_le_exp (s ^ 2 / 2 - 1)
      have hp : 0 ≤ s ^ 2 / 2 := by positivity
      have hsq : (s ^ 2 / 2) ^ 2 ≤ Real.exp (s ^ 2 / 2 - 1) ^ 2 := pow_le_pow_left₀ hp (by linarith) 2
      have e1 : Real.exp (s ^ 2 / 2 - 1) ^ 2 * Real.exp (-s ^ 2) = Real.exp (-2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      have := Real.exp_pos (-s ^ 2)
      nlinarith
    have h4 : 4 * Real.exp (-2) * Real.exp (-1) ≤ 0.37 := by
      rw [mul_assoc, ← Real.exp_add]
      have : Real.exp (-2 + -1) = (Real.exp 1 ^ 3)⁻¹ := by
        rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; norm_num
      rw [this]
      have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
      rw [mul_inv_le_iff₀ (by positivity)]; nlinarith
    rw [abs_of_pos hu, hE]
    have hE0 : 0 ≤ s ^ 3 * Real.exp (-s ^ 2) := by positivity
    calc u * (s ^ 3 * Real.exp (-s ^ 2)) ≤ Real.exp (u - 1) * (s ^ 3 * Real.exp (-s ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 hE0
      _ = s ^ 4 * Real.exp (-s ^ 2) * Real.exp (-1) := by rw [h2]; ring
      _ ≤ 4 * Real.exp (-2) * Real.exp (-1) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 0.37 := h4

/-! ### The `η◦` integrals and the assembly -/

theorem integral_Ioi_etaO_sq_mul (f : ℝ → ℝ) :
    ∫ t in Ioi 0, etaO t ^ 2 * f t = ∫ t in (0:ℝ)..2, P0 t ^ 2 * f t := by
  have e : (fun t => etaO t ^ 2 * f t) = (Icc (0:ℝ) 2).indicator (fun t => P0 t ^ 2 * f t) := by
    ext t; unfold etaO
    by_cases h : t ∈ Icc (0:ℝ) 2
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h]; ring
  have hset : Ioi (0:ℝ) ∩ Icc 0 2 = Ioc 0 2 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h1.le, h3⟩
  rw [e, setIntegral_indicator measurableSet_Icc, hset, intervalIntegral.integral_of_le (by norm_num)]

theorem exp_sq_eq (s : ℝ) : Real.exp (-s ^ 2) = Real.exp (-s ^ 2 / 2) ^ 2 := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem integral_gL_mul_W0 : ∫ u, gL u * W0 u = ∫ t in (0:ℝ)..2, P0 t ^ 2 * 1 := by
  have e : (fun u => gL u * W0 u) = fun u => Real.exp u • (etaO (Real.exp u) ^ 2 * 1) := by
    ext u
    rw [smul_eq_mul, etaO_eq (Real.exp_pos u), W0, Ew, gL, exp_sq_eq]; ring
  rw [e, integral_comp_exp (fun t => etaO t ^ 2 * 1), integral_Ioi_etaO_sq_mul]

theorem integral_gL_mul_W1 : ∫ u, gL u * W1 u = ∫ t in (0:ℝ)..2, P0 t ^ 2 * Real.log t := by
  have e : (fun u => gL u * W1 u) =
      fun u => Real.exp u • (etaO (Real.exp u) ^ 2 * Real.log (Real.exp u)) := by
    ext u
    rw [smul_eq_mul, etaO_eq (Real.exp_pos u), W1, W0, Ew, gL, exp_sq_eq, Real.log_exp]; ring
  rw [e, integral_comp_exp (fun t => etaO t ^ 2 * Real.log t), integral_Ioi_etaO_sq_mul]

/-! ### `‖W₀''‖₂²` and `‖W₁''‖₂²` -/

open TernaryGoldbach.MajorArcs.PolyNum (pH pI continuous_pH integral_pow_mul_pH)

theorem IF.integral {W k : ℝ → ℝ} (h : IF W k) : ∫ u, W u = ∫ t in (0:ℝ)..2, k t := by
  have e : W = fun u => Real.exp u • (Icc (0 : ℝ) 2).indicator k (Real.exp u) := by
    ext u; rw [h u, smul_eq_mul]
  have hset : Ioi (0:ℝ) ∩ Icc 0 2 = Ioc 0 2 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h1.le, h3⟩
  rw [e, integral_comp_exp ((Icc (0 : ℝ) 2).indicator k), setIntegral_indicator measurableSet_Icc,
    hset, intervalIntegral.integral_of_le (by norm_num)]

/-- The polynomial parts: `k₀' = p₀' X`, `k₀'' = p₀'' X`, `k₁'' = 2 p₀' X + (t log t) q X`,
`X = e^{t−1/2} e^{−t²}`. -/
def L0d : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (40 : ℚ), (-64 : ℚ), (14 : ℚ), (22 : ℚ), (-13 : ℚ), (2 : ℚ)]
def L0dd : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (200 : ℚ), (-344 : ℚ), (-46 : ℚ), (318 : ℚ), (-123 : ℚ), (-37 : ℚ), (28 : ℚ), (-4 : ℚ)]
def Lq : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (200 : ℚ), (-344 : ℚ), (-46 : ℚ), (318 : ℚ), (-123 : ℚ), (-37 : ℚ), (28 : ℚ), (-4 : ℚ)]
/-- `t p₀''² = t pH LC`. -/
def LC : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (40000 : ℚ), (-137600 : ℚ), (99936 : ℚ), (158848 : ℚ), (-265868 : ℚ), (40568 : ℚ), (149096 : ℚ), (-95688 : ℚ), (-8227 : ℚ), (27278 : ℚ), (-8063 : ℚ), (-1088 : ℚ), (1080 : ℚ), (-224 : ℚ), (16 : ℚ)]
/-- `t (8 p₀'² + 2 (1 − t)² q²) = t pH LQ1`. -/
def LQ1 : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (80000 : ℚ), (-435200 : ℚ), (843072 : ℚ), (-398208 : ℚ), (-925528 : ℚ), (1462048 : ℚ), (-425096 : ℚ), (-687104 : ℚ), (663402 : ℚ), (-108040 : ℚ), (-139636 : ℚ), (84216 : ℚ), (-9582 : ℚ), (-6944 : ℚ), (3088 : ℚ), (-512 : ℚ), (32 : ℚ)]
/-- `t (8 p₀'² + 2 t² (t − 1)² q²) = t pH LQ2`. -/
def LQ2 : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (92800 : ℚ), (-476160 : ℚ), (872000 : ℚ), (-357504 : ℚ), (-996536 : ℚ), (1481824 : ℚ), (-396904 : ℚ), (-710752 : ℚ), (666546 : ℚ), (-104328 : ℚ), (-141660 : ℚ), (84632 : ℚ), (-9614 : ℚ), (-6944 : ℚ), (3088 : ℚ), (-512 : ℚ), (32 : ℚ)]

theorem k0''_eq (t : ℝ) : k0'' t = pH L0dd t * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) := by
  unfold k0'' hP hP' hP'' pP pP'; simp only [L0dd, pH]; push_cast; ring

theorem k1''_eq (t : ℝ) : k1'' t = 2 * (pH L0d t * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2))) +
    (t * Real.log t) * (pH Lq t * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2))) := by
  unfold k1'' k0' hP hP' hP'' pP pP'; simp only [L0d, Lq, pH]; push_cast; ring

theorem X_sq (t : ℝ) : (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) ^ 2 = Real.exp (2 * t - 1 - 2 * t ^ 2) := by
  rw [← Real.exp_add, sq, ← Real.exp_add]; congr 1; ring

/-- **`‖W₀''‖₂² ≤ 1000`** (value `35.79`; here `e^{2t−1−2t²} ≤ 1`). -/
theorem W0''_sq_le : ∫ u, W0'' u ^ 2 ≤ 1000 := by
  rw [IF_W0''.sq.integral]
  have hmono : ∫ t in (0:ℝ)..2, t * k0'' t ^ 2 ≤ ∫ t in (0:ℝ)..2, t ^ 1 * pH LC t := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun t ht => ?_
    · exact (continuous_id.mul (continuous_k0''.pow 2)).intervalIntegrable _ _
    · exact ((continuous_pow 1).mul (continuous_pH LC)).intervalIntegrable _ _
    · rw [k0''_eq]
      have hid : t ^ 1 * pH LC t = t * pH L0dd t ^ 2 := by simp only [LC, L0dd, pH]; push_cast; ring
      rw [hid]
      have hX : (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) ^ 2 ≤ 1 := by
        rw [X_sq, Real.exp_le_one_iff]; nlinarith [sq_nonneg (t - 1 / 2)]
      have ht0 : 0 ≤ t := ht.1
      calc t * (pH L0dd t * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2))) ^ 2 =
            t * pH L0dd t ^ 2 * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) ^ 2 := by ring
        _ ≤ t * pH L0dd t ^ 2 * 1 := mul_le_mul_of_nonneg_left hX (by positivity)
        _ = _ := by ring
  have hI := integral_pow_mul_pH 0 2 LC 1
  push_cast at hI
  rw [hI] at hmono
  have hq : (pI 0 2 LC 1 : ℚ) ≤ 1000 := by decide +kernel
  have := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at this
  linarith

/-- `|t log t| ≤ 1 − t` on `[0, 1]`. -/
theorem tlog_sq_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : (t * Real.log t) ^ 2 ≤ (1 - t) ^ 2 := by
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; simp
  have hl := Real.log_nonpos h0 h1
  have hl2 := Real.one_sub_inv_le_log_of_pos h
  have : t - 1 ≤ t * Real.log t := by
    have := mul_le_mul_of_nonneg_left hl2 h0
    rw [mul_sub, mul_one, mul_inv_cancel₀ h.ne'] at this; linarith
  have : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hl
  nlinarith

/-- `0 ≤ t log t ≤ t (t − 1)` on `[1, 2]`. -/
theorem tlog_sq_le_two {t : ℝ} (h1 : 1 ≤ t) : (t * Real.log t) ^ 2 ≤ (t * (t - 1)) ^ 2 := by
  have h0 : 0 < t := by linarith
  have hl := Real.log_nonneg h1
  have hl2 := Real.log_le_sub_one_of_pos h0
  have a : 0 ≤ t * Real.log t := mul_nonneg h0.le hl
  have b : t * Real.log t ≤ t * (t - 1) := mul_le_mul_of_nonneg_left hl2 h0.le
  nlinarith

theorem k1''_pt (t : ℝ) (ht0 : 0 ≤ t) (P : ℝ) (hP : (t * Real.log t) ^ 2 ≤ P) :
    t * k1'' t ^ 2 ≤ (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) ^ 2 *
      (t * (8 * pH L0d t ^ 2 + 2 * P * pH Lq t ^ 2)) := by
  rw [k1''_eq]
  set X := Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)
  set a := pH L0d t
  set b := pH Lq t
  set l := t * Real.log t
  have h1 : (2 * (a * X) + l * (b * X)) ^ 2 ≤ 8 * (a * X) ^ 2 + 2 * (l * (b * X)) ^ 2 := by
    nlinarith [sq_nonneg (2 * (a * X) - l * (b * X))]
  have h2 : 2 * (l * (b * X)) ^ 2 ≤ 2 * (P * (b * X) ^ 2) := by
    have : (l * (b * X)) ^ 2 = l ^ 2 * (b * X) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (b * X)]
  have := mul_le_mul_of_nonneg_left (h1.trans (by linarith : 8 * (a * X) ^ 2 + 2 * (l * (b * X)) ^ 2 ≤
    8 * (a * X) ^ 2 + 2 * (P * (b * X) ^ 2))) ht0
  calc t * (2 * (a * X) + l * (b * X)) ^ 2 ≤ t * (8 * (a * X) ^ 2 + 2 * (P * (b * X) ^ 2)) := this
    _ = X ^ 2 * (t * (8 * a ^ 2 + 2 * P * b ^ 2)) := by ring

theorem LQ1_eq (t : ℝ) : t ^ 1 * pH LQ1 t = t * (8 * pH L0d t ^ 2 + 2 * (1 - t) ^ 2 * pH Lq t ^ 2) := by
  simp only [LQ1, L0d, Lq, pH]; push_cast; ring

theorem LQ2_eq (t : ℝ) :
    t ^ 1 * pH LQ2 t = t * (8 * pH L0d t ^ 2 + 2 * (t * (t - 1)) ^ 2 * pH Lq t ^ 2) := by
  simp only [LQ2, L0d, Lq, pH]; push_cast; ring

/-- `∑_{i<8} rⁱ/i! ≤ eʳ`. -/
def expS (r : ℚ) : ℚ := ∑ i ∈ Finset.range 8, r ^ i / (Nat.factorial i : ℚ)

theorem exp_neg_le {r : ℚ} (hr : 0 ≤ r) : Real.exp (-(r : ℝ)) ≤ (((expS r)⁻¹ : ℚ) : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (r : ℝ)) (by exact_mod_cast hr) 8
  have he : ((expS r : ℚ) : ℝ) = ∑ i ∈ Finset.range 8, (r : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    simp [expS]
  have hpos : (0 : ℝ) < ((expS r : ℚ) : ℝ) := by
    rw [he, Finset.sum_range_succ']; simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ i ∈ Finset.range 7, (r : ℝ) ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) :=
      Finset.sum_nonneg fun i _ => by have : (0 : ℝ) ≤ r := by exact_mod_cast hr
                                      positivity
    linarith
  rw [Real.exp_neg, Rat.cast_inv]
  exact inv_anti₀ hpos (he ▸ h)

theorem piece_le {lo hi r : ℚ} {L : List ℚ} (hlohi : (lo : ℝ) ≤ hi) (hr : 0 ≤ r)
    (hexp : ∀ t ∈ Icc (lo : ℝ) hi, 2 * t - 1 - 2 * t ^ 2 ≤ -(r : ℝ))
    (hpt : ∀ t ∈ Icc (lo : ℝ) hi,
      t * k1'' t ^ 2 ≤ (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2)) ^ 2 * (t ^ 1 * pH L t))
    (hnn : ∀ t ∈ Icc (lo : ℝ) hi, 0 ≤ t ^ 1 * pH L t) :
    ∫ t in (lo : ℝ)..hi, t * k1'' t ^ 2 ≤ (((expS r)⁻¹ * pI lo hi L 1 : ℚ) : ℝ) := by
  have hm := exp_neg_le hr
  have hmono : ∫ t in (lo : ℝ)..hi, t * k1'' t ^ 2 ≤
      ∫ t in (lo : ℝ)..hi, (((expS r)⁻¹ : ℚ) : ℝ) * (t ^ 1 * pH L t) := by
    refine intervalIntegral.integral_mono_on hlohi ?_ ?_ fun t ht => ?_
    · exact (continuous_id.mul (continuous_k1''.pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul ((continuous_pow 1).mul (continuous_pH L))).intervalIntegrable _ _
    · refine (hpt t ht).trans (mul_le_mul_of_nonneg_right ?_ (hnn t ht))
      rw [X_sq]
      exact (Real.exp_le_exp.2 (hexp t ht)).trans hm
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_pH] at hmono
  push_cast at hmono ⊢
  exact hmono

theorem piece_0 : ∫ t in (((0 : ℚ) : ℚ) : ℝ)..(((1 / 4 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (5 / 8 : ℚ))⁻¹ * pI (0 : ℚ) (1 / 4 : ℚ) LQ1 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.2) (show (0 : ℝ) ≤ (1 - 1 / 4) - t by linarith [ht.2])])
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h1 : t ≤ 1 := le_trans ht.2 (by norm_num)
      rw [LQ1_eq]; exact k1''_pt t h0 _ (tlog_sq_le_one h0 h1)))
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ1_eq]; positivity))

theorem piece_1 : ∫ t in (((1 / 4 : ℚ) : ℚ) : ℝ)..(((1 / 2 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (1 / 2 : ℚ))⁻¹ * pI (1 / 4 : ℚ) (1 / 2 : ℚ) LQ1 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.2) (show (0 : ℝ) ≤ (1 - 1 / 2) - t by linarith [ht.2])])
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h1 : t ≤ 1 := le_trans ht.2 (by norm_num)
      rw [LQ1_eq]; exact k1''_pt t h0 _ (tlog_sq_le_one h0 h1)))
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ1_eq]; positivity))

theorem piece_2 : ∫ t in (((1 / 2 : ℚ) : ℚ) : ℝ)..(((3 / 4 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (1 / 2 : ℚ))⁻¹ * pI (1 / 2 : ℚ) (3 / 4 : ℚ) LQ1 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 1 / 2) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h1 : t ≤ 1 := le_trans ht.2 (by norm_num)
      rw [LQ1_eq]; exact k1''_pt t h0 _ (tlog_sq_le_one h0 h1)))
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ1_eq]; positivity))

theorem piece_3 : ∫ t in (((3 / 4 : ℚ) : ℚ) : ℝ)..(((1 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (5 / 8 : ℚ))⁻¹ * pI (3 / 4 : ℚ) (1 : ℚ) LQ1 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 3 / 4) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h1 : t ≤ 1 := le_trans ht.2 (by norm_num)
      rw [LQ1_eq]; exact k1''_pt t h0 _ (tlog_sq_le_one h0 h1)))
    (by push_cast; exact (fun t ht => by
      have h0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ1_eq]; positivity))

theorem piece_4 : ∫ t in (((1 : ℚ) : ℚ) : ℝ)..(((5 / 4 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (1 : ℚ))⁻¹ * pI (1 : ℚ) (5 / 4 : ℚ) LQ2 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 1 / 1) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ2_eq]; exact k1''_pt t (by linarith) _ (tlog_sq_le_two h1)))
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h0 : (0 : ℝ) ≤ t := by linarith
      rw [LQ2_eq]; positivity))

theorem piece_5 : ∫ t in (((5 / 4 : ℚ) : ℚ) : ℝ)..(((3 / 2 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (13 / 8 : ℚ))⁻¹ * pI (5 / 4 : ℚ) (3 / 2 : ℚ) LQ2 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 5 / 4) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ2_eq]; exact k1''_pt t (by linarith) _ (tlog_sq_le_two h1)))
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h0 : (0 : ℝ) ≤ t := by linarith
      rw [LQ2_eq]; positivity))

theorem piece_6 : ∫ t in (((3 / 2 : ℚ) : ℚ) : ℝ)..(((7 / 4 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (5 / 2 : ℚ))⁻¹ * pI (3 / 2 : ℚ) (7 / 4 : ℚ) LQ2 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 3 / 2) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ2_eq]; exact k1''_pt t (by linarith) _ (tlog_sq_le_two h1)))
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h0 : (0 : ℝ) ≤ t := by linarith
      rw [LQ2_eq]; positivity))

theorem piece_7 : ∫ t in (((7 / 4 : ℚ) : ℚ) : ℝ)..(((2 : ℚ) : ℚ) : ℝ), t * k1'' t ^ 2 ≤
    ((((expS (29 / 8 : ℚ))⁻¹ * pI (7 / 4 : ℚ) (2 : ℚ) LQ2 1 : ℚ)) : ℝ) :=
  piece_le (by norm_num) (by norm_num)
    (fun t ht => by
      push_cast at ht ⊢
      nlinarith [ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.1) (show (0 : ℝ) ≤ t - (1 - 7 / 4) by linarith [ht.1])])
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      rw [LQ2_eq]; exact k1''_pt t (by linarith) _ (tlog_sq_le_two h1)))
    (by push_cast; exact (fun t ht => by
      have h1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht.1
      have h0 : (0 : ℝ) ≤ t := by linarith
      rw [LQ2_eq]; positivity))

theorem pieces_sum : (expS (5 / 8 : ℚ))⁻¹ * pI (0 : ℚ) (1 / 4 : ℚ) LQ1 1 + (expS (1 / 2 : ℚ))⁻¹ * pI (1 / 4 : ℚ) (1 / 2 : ℚ) LQ1 1 + (expS (1 / 2 : ℚ))⁻¹ * pI (1 / 2 : ℚ) (3 / 4 : ℚ) LQ1 1 + (expS (5 / 8 : ℚ))⁻¹ * pI (3 / 4 : ℚ) (1 : ℚ) LQ1 1 + (expS (1 : ℚ))⁻¹ * pI (1 : ℚ) (5 / 4 : ℚ) LQ2 1 + (expS (13 / 8 : ℚ))⁻¹ * pI (5 / 4 : ℚ) (3 / 2 : ℚ) LQ2 1 + (expS (5 / 2 : ℚ))⁻¹ * pI (3 / 2 : ℚ) (7 / 4 : ℚ) LQ2 1 + (expS (29 / 8 : ℚ))⁻¹ * pI (7 / 4 : ℚ) (2 : ℚ) LQ2 1 ≤ 60 := by decide +kernel

/-- **`‖W₁''‖₂² ≤ 60`** (value `8.389`): `(a + b)² ≤ 2a² + 2b²`, `|t log t| ≤ 1 − t` resp. `t(t − 1)`,
and `e^{2t−1−2t²}` bounded on 8 pieces of `[0, 2]`. -/
theorem W1''_sq_le : ∫ u, W1'' u ^ 2 ≤ 60 := by
  rw [IF_W1''.sq.integral]
  have hc : Continuous fun t => t * k1'' t ^ 2 := continuous_id.mul (continuous_k1''.pow 2)
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => t * k1'' t ^ 2) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have s0 := intervalIntegral.integral_add_adjacent_intervals (hi (((0 : ℚ) : ℚ) : ℝ) (((1 / 4 : ℚ) : ℚ) : ℝ)) (hi (((1 / 4 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s1 := intervalIntegral.integral_add_adjacent_intervals (hi (((1 / 4 : ℚ) : ℚ) : ℝ) (((1 / 2 : ℚ) : ℚ) : ℝ)) (hi (((1 / 2 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s2 := intervalIntegral.integral_add_adjacent_intervals (hi (((1 / 2 : ℚ) : ℚ) : ℝ) (((3 / 4 : ℚ) : ℚ) : ℝ)) (hi (((3 / 4 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s3 := intervalIntegral.integral_add_adjacent_intervals (hi (((3 / 4 : ℚ) : ℚ) : ℝ) (((1 : ℚ) : ℚ) : ℝ)) (hi (((1 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s4 := intervalIntegral.integral_add_adjacent_intervals (hi (((1 : ℚ) : ℚ) : ℝ) (((5 / 4 : ℚ) : ℚ) : ℝ)) (hi (((5 / 4 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s5 := intervalIntegral.integral_add_adjacent_intervals (hi (((5 / 4 : ℚ) : ℚ) : ℝ) (((3 / 2 : ℚ) : ℚ) : ℝ)) (hi (((3 / 2 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have s6 := intervalIntegral.integral_add_adjacent_intervals (hi (((3 / 2 : ℚ) : ℚ) : ℝ) (((7 / 4 : ℚ) : ℚ) : ℝ)) (hi (((7 / 4 : ℚ) : ℚ) : ℝ) ((2 : ℚ) : ℝ))
  have p0 := piece_0
  have p1 := piece_1
  have p2 := piece_2
  have p3 := piece_3
  have p4 := piece_4
  have p5 := piece_5
  have p6 := piece_6
  have p7 := piece_7
  have hs := (Rat.cast_le (K := ℝ)).2 pieces_sum
  push_cast at hs s0 s1 s2 s3 s4 s5 s6 p0 p1 p2 p3 p4 p5 p6 p7 ⊢
  linarith

/-- The four elementary integrals (proved above and in `EtaONum.lean`):
* `∫₀² η◦² = 0.6402059973663522…` and `∫₀² η◦² log t = −0.0210947786988671…`, where
  `η◦ = P0 = (t(2 − t))³ e^{−(t−1)²/2}` ([B] gets the same values with VNODE-LP);
* `‖W₀''‖₂² = 35.790…` and `‖W₁''‖₂² = 8.389…` (bounded here by `1000` and `60`), where
  `W₀(u) = g(u) e^{3u − e^{2u}}`, `W₁ = u W₀` and `g(u) = h(eᵘ)`. -/
theorem etaO_numerics :
    (0.640205997 ≤ ∫ t in (0:ℝ)..2, P0 t ^ 2 * 1 ∧ ∫ t in (0:ℝ)..2, P0 t ^ 2 * 1 ≤ 0.640205998) ∧
    (-0.02109479 ≤ ∫ t in (0:ℝ)..2, P0 t ^ 2 * Real.log t ∧
      ∫ t in (0:ℝ)..2, P0 t ^ 2 * Real.log t ≤ -0.02109477) ∧
    ∫ u, W0'' u ^ 2 ≤ 1000 ∧ ∫ u, W1'' u ^ 2 ≤ 60 :=
  ⟨TernaryGoldbach.MajorArcs.PolyNum.integral_P0_sq, TernaryGoldbach.MajorArcs.PolyNum.integral_P0_sq_log,
    W0''_sq_le, W1''_sq_le⟩

theorem continuous_Ew : Continuous Ew := by unfold Ew; fun_prop

theorem integral_six_add {f1 f2 f3 f4 f5 f6 : ℝ → ℝ} (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) (h5 : Integrable f5) (h6 : Integrable f6) :
    ∫ u, (f1 u + f2 u + f3 u + f4 u + f5 u + f6 u) =
      (∫ u, f1 u) + (∫ u, f2 u) + (∫ u, f3 u) + (∫ u, f4 u) + (∫ u, f5 u) + ∫ u, f6 u := by
  have j2 : Integrable fun u => f1 u + f2 u := h1.add h2
  have j3 : Integrable fun u => f1 u + f2 u + f3 u := j2.add h3
  have j4 : Integrable fun u => f1 u + f2 u + f3 u + f4 u := j3.add h4
  have j5 : Integrable fun u => f1 u + f2 u + f3 u + f4 u + f5 u := j4.add h5
  rw [integral_add j5 h6, integral_add j4 h5, integral_add j3 h4, integral_add j2 h3,
    integral_add h1 h2]

/-- `∫₀^∞ η₊² log(xt) dt = ∫ (g + D)² E (log x + u) du`. -/
theorem integral_etaPlus_sq_log_eq {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t) =
      ∫ u, (gL u + Dg u) ^ 2 * Ew u * (Real.log x + u) := by
  rw [← integral_comp_exp]
  congr 1; ext u
  rw [smul_eq_mul, Real.log_mul hx.ne' (Real.exp_pos u).ne', Real.log_exp]
  have hD : gL u + Dg u = hH 200 (Real.exp u) := by unfold Dg; ring
  rw [hD, etaPlus, Ew, exp_sq_eq]; ring

/-- **[B, (9.94)]**: `∫₀^∞ η₊²(t) log(xt) dt = (0.640206 + O*(1.95·10⁻⁶)) log x − 0.021095 + O*(5.3·10⁻⁷)`
for `x ≥ 1`. The errors here are at most `2.6·10⁻⁷ log x + 3.8·10⁻⁷`: the cross terms are
`O(H⁻⁴)` by Parseval (`abs_integral_Dg_mul_le`), not `O(H^{−7/2})` as with [B]'s Cauchy–Schwarz. -/
theorem integral_etaPlus_sq_log {x : ℝ} (hx : 1 ≤ x) :
    |(∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t)) - (0.640206 * Real.log x - 0.021095)| ≤
      1.95e-6 * Real.log x + 5.3e-7 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, m0, m1⟩ := etaO_numerics
  rw [← integral_gL_mul_W0] at a1 a2
  rw [← integral_gL_mul_W1] at b1 b2
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  rw [integral_etaPlus_sq_log_eq hx0]
  -- the six pieces
  have iA : Integrable fun u => gL u * W0 u := memLp_gL.integrable_mul memLp_W0
  have iB : Integrable fun u => gL u * W1 u := memLp_gL.integrable_mul memLp_W1
  have iC : Integrable fun u => Dg u * W0 u := memLp_Dg.integrable_mul memLp_W0
  have iD : Integrable fun u => Dg u * W1 u := memLp_Dg.integrable_mul memLp_W1
  have mE : AEStronglyMeasurable (fun u => Dg u ^ 2 * Ew u) :=
    ((continuous_Dg.pow 2).mul continuous_Ew).aestronglyMeasurable
  have iE : Integrable fun u => Dg u ^ 2 * Ew u :=
    Integrable.mono' (integrable_Dg_sq.mul_const (1 / 2)) mE (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Ew_nonneg u))]
      exact mul_le_mul_of_nonneg_left (Ew_le u) (sq_nonneg _))
  have mF : AEStronglyMeasurable (fun u => Dg u ^ 2 * Ew u * u) :=
    (((continuous_Dg.pow 2).mul continuous_Ew).mul continuous_id).aestronglyMeasurable
  have hF : ∀ u, |Dg u ^ 2 * Ew u * u| ≤ Dg u ^ 2 * 0.37 := by
    intro u
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Ew_nonneg u), mul_assoc,
      mul_comm (Ew u)]
    exact mul_le_mul_of_nonneg_left (abs_mul_Ew_le u) (sq_nonneg _)
  have iF : Integrable fun u => Dg u ^ 2 * Ew u * u :=
    Integrable.mono' (integrable_Dg_sq.mul_const 0.37) mF
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hF u)
  have hexp : (fun u => (gL u + Dg u) ^ 2 * Ew u * (L + u)) = fun u =>
      L * (gL u * W0 u) + gL u * W1 u + 2 * L * (Dg u * W0 u) + 2 * (Dg u * W1 u) +
        L * (Dg u ^ 2 * Ew u) + Dg u ^ 2 * Ew u * u := by
    ext u; simp only [W0, W1]; ring
  rw [hexp, integral_six_add (iA.const_mul L) iB (iC.const_mul (2 * L)) (iD.const_mul 2)
      (iE.const_mul L) iF,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  -- bounds
  have hD2 := integral_Dg_sq_le
  have hC0 := abs_integral_Dg_mul_le hasDerivAt_W0 hasDerivAt_W0' integrable_W0 integrable_W0'
    integrable_W0'' integrable_W0''_sq memLp_W0 continuous_W0 m0 (lam := 1.6) (by norm_num)
  have hC1 := abs_integral_Dg_mul_le hasDerivAt_W1 hasDerivAt_W1' integrable_W1 integrable_W1'
    integrable_W1'' integrable_W1''_sq memLp_W1 continuous_W1 m1 (lam := 0.4) (by norm_num)
  have hQ0 : |∫ u, Dg u ^ 2 * Ew u| ≤ 368 / 200 ^ 4 / 2 := by
    rw [abs_of_nonneg (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Ew_nonneg u))]
    calc ∫ u, Dg u ^ 2 * Ew u ≤ ∫ u, Dg u ^ 2 * (1 / 2) :=
          integral_mono iE (integrable_Dg_sq.mul_const _)
            fun u => mul_le_mul_of_nonneg_left (Ew_le u) (sq_nonneg _)
      _ = (∫ u, Dg u ^ 2) / 2 := by rw [integral_mul_const]; ring
      _ ≤ 368 / 200 ^ 4 / 2 := by linarith
  have hQ1 : |∫ u, Dg u ^ 2 * Ew u * u| ≤ 0.37 * (368 / 200 ^ 4) := by
    calc |∫ u, Dg u ^ 2 * Ew u * u| ≤ ∫ u, |Dg u ^ 2 * Ew u * u| := abs_integral_le_integral_abs
      _ ≤ ∫ u, Dg u ^ 2 * 0.37 := integral_mono iF.abs (integrable_Dg_sq.mul_const _) hF
      _ = 0.37 * ∫ u, Dg u ^ 2 := by rw [integral_mul_const]; ring
      _ ≤ 0.37 * (368 / 200 ^ 4) := by linarith
  set A := ∫ u, gL u * W0 u
  set B := ∫ u, gL u * W1 u
  set C0 := ∫ u, Dg u * W0 u
  set C1 := ∫ u, Dg u * W1 u
  set Q0 := ∫ u, Dg u ^ 2 * Ew u
  set Q1 := ∫ u, Dg u ^ 2 * Ew u * u
  rw [abs_le] at hC0 hC1 hQ0 hQ1 ⊢
  norm_num at hC0 hC1 hQ0 hQ1 a1 a2 b1 b2 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hC0.1 hL0, mul_le_mul_of_nonneg_left hC0.2 hL0,
    mul_le_mul_of_nonneg_left hQ0.1 hL0, mul_le_mul_of_nonneg_left hQ0.2 hL0,
    mul_le_mul_of_nonneg_left a1 hL0, mul_le_mul_of_nonneg_left a2 hL0]

end TernaryGoldbach.MajorArcs
