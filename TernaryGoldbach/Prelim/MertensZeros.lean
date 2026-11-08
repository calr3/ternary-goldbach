import TernaryGoldbach.Prelim.MertensWindow
import TernaryGoldbach.Explicit.ZetaLowZeroFree

/-!
# The smoothed explicit formula integrated against `dy/y²`

For `φ = gsm a b δ` and `Ψ(y) = Σ Λ(n) φ(n/y)`, `M = e^{δ²/2}(e^a − e^b)`, the explicit formula
`Ψ(y) − M y = −Σ_ρ M(ρ) y^ρ − J(y)` integrates termwise over `[Y₁, Y₂]`:
`∫_{Y₁}^{Y₂} (Ψ(y) − M y)/y² dy = −Σ_ρ M(ρ) (Y₂^{ρ−1} − Y₁^{ρ−1})/(ρ − 1) − ∫ J(y)/y² dy`
(`integral_psi_gsm_zeros`: dominated convergence over the rectangles `R_{T_k}`, which do not depend
on `y`, `explicit_formula_zeta_seq`). The zeros now carry the weight `|M(ρ)|/|ρ − 1|`, of order
`1/|ρ|²`, so the sum over them converges absolutely: with RH up to `H`,
`|∫_{Y₁}^{Y₂} (Ψ(y) − M y)/y² dy| ≤ (Y₁^{−1/2} + Y₂^{−1/2}) LQW + 2 TailB/H + (2/3) Y₁^{−3/2} V/(2π)`
(`abs_integral_psi_gsm_le`). Integrating the pointwise bound for `Ψ − M y` instead would cost
`2 LineB2/√Y₁`, with the weight `1/|ρ|`.

The line zeros are counted in windows of height `6` by Jensen (`line_sum_leW`, a version of
`line_sum_leH` for any decreasing weight), and the zero-free strip `|γ| < 2.39`
(`abs_im_ge_of_zeroH`) bounds the weight of the first windows.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- **Line zeros with a decreasing weight**: `Σ m_ρ g(ρ) ≤ 2C Σ_{d<J} log(B((d + ½)h)/0.355)/log(10/r)
· W(hd)` if `g(ρ) ≤ C W(|γ|)` with `W ≥ 0` decreasing on `[0, ∞)`. -/
theorem line_sum_leW {T H h r : ℝ} (hH : 0 ≤ H) (hh : 0 < h) (hr : 0 < r) (hr10 : r < 10)
    (hhr : 1.5 ^ 2 + (h / 2) ^ 2 ≤ r ^ 2) (S : Finset ℂ) (hS : S ⊆ zerosRectD zetaF T)
    (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ H) (g : ℂ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (W : ℝ → ℝ) (hW0 : ∀ t, 0 ≤ W t) (hW : AntitoneOn W (Ici 0))
    (hg : ∀ u ∈ S, g u ≤ C * W |u.im|) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u ≤
      C * (2 * ∑ m ∈ Finset.range (JlH h H), Real.log (BPz2 (((m : ℝ) + 1 / 2) * h) / 0.355) /
        Real.log (10 / r) * W (h * (m : ℝ))) := by
  set J := JlH h H with hJdef
  set idx : ℂ → ℕ := fun u => (⌊u.im / h⌋ + J).toNat with hidx
  have hJ := lt_JlH hh hH
  set d : ℕ → ℝ := fun k => if J ≤ k then ((k - J : ℕ) : ℝ) else ((J - 1 - k : ℕ) : ℝ) with hd
  set dn : ℕ → ℕ := fun k => if J ≤ k then k - J else J - 1 - k with hdn
  set w : ℕ → ℝ := fun k => W (h * d k) with hw
  set Zw : ℕ → ℝ := fun k => Real.log (BPz2 (((dn k : ℝ) + 1 / 2) * h) / 0.355) / Real.log (10 / r)
    with hZw
  have hd0 : ∀ k, 0 ≤ d k := fun k => by simp only [hd]; split_ifs <;> positivity
  have hw0 : ∀ k, 0 ≤ w k := fun k => hW0 _
  have hmaps : ∀ u ∈ S, idx u ∈ Finset.range (2 * J) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h :=
      mem_line_window hh hJ (him u hu)
    have := (abs_le.1 (him u hu)).2
    rw [Finset.mem_range]
    have h1 : (((idx u : ℕ) : ℝ) - J) * h < J * h := by linarith [hwin.1]
    have h2 : ((idx u : ℕ) : ℝ) < 2 * J := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hh.le
      nlinarith
    exact_mod_cast h2
  have hwin_g : ∀ u ∈ S, g u ≤ C * w (idx u) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h :=
      mem_line_window hh hJ (him u hu)
    have habs : h * d (idx u) ≤ |u.im| := by
      rw [hd]; simp only
      split_ifs with hk
      · rw [Nat.cast_sub hk]
        have : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im := hwin.1
        have hp : 0 ≤ (((idx u : ℕ) : ℝ) - J) * h :=
          mul_nonneg (sub_nonneg.2 (Nat.cast_le.2 hk)) hh.le
        rw [abs_of_nonneg (by linarith)]
        linarith
      · push Not at hk
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h := hwin.2
        have hk' : ((idx u : ℕ) : ℝ) + 1 ≤ J := by exact_mod_cast hk
        have hp : 0 ≤ ((J : ℝ) - ((idx u : ℕ) : ℝ) - 1) * h := mul_nonneg (by linarith) hh.le
        rw [abs_of_nonpos (by linarith)]
        push_cast; linarith
    have hm0 : (0 : ℝ) ≤ h * d (idx u) := mul_nonneg hh.le (hd0 _)
    refine (hg u hu).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact hW hm0 (le_trans hm0 habs) habs
  have hcount : ∀ k, ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) ≤ Zw k := by
    intro k
    refine (count_line_windowC hh hr hr10 hhr hH S hS hre him k).trans ?_
    refine div_le_div_of_nonneg_right (polyDatum_zeta2.log_mono (le_of_eq ?_)) (log_ratio_pos hr hr10).le
    rw [← hJdef]
    simp only [hdn]
    split_ifs with hk
    · rw [Nat.cast_sub hk]
    · have e : (((J - 1 - k : ℕ) : ℝ) + 1 / 2) * h = -(((k : ℝ) - J + 1 / 2) * h) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e, abs_neg]
  calc ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u
      = ∑ k ∈ Finset.range (2 * J), ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range (2 * J), Zw k * (C * w k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u
            ≤ ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * (C * w k) := by
              refine Finset.sum_le_sum fun u hu => ?_
              obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              rw [← hk]; exact hwin_g u huS
          _ = (∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ)) * (C * w k) := by
              rw [Finset.sum_mul]
          _ ≤ Zw k * (C * w k) :=
              mul_le_mul_of_nonneg_right (hcount k) (mul_nonneg hC (hw0 k))
    _ = C * ∑ k ∈ Finset.range (2 * J), Zw k * w k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ C * (2 * ∑ m ∈ Finset.range J, Real.log (BPz2 (((m : ℝ) + 1 / 2) * h) / 0.355) /
          Real.log (10 / r) * W (h * (m : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hC
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : J ≤ 2 * J)]
        have hA : ∑ k ∈ Finset.range J, Zw k * w k = ∑ m ∈ Finset.range J,
            Real.log (BPz2 (((m : ℝ) + 1 / 2) * h) / 0.355) / Real.log (10 / r) *
              W (h * (m : ℝ)) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have e1 : J - 1 - (J - 1 - k) = k := by omega
          simp only [hw, hd, hZw, hdn, if_neg (show ¬ J ≤ J - 1 - k by omega), e1]
        have hB : ∑ k ∈ Finset.Ico J (2 * J), Zw k * w k = ∑ m ∈ Finset.range J,
            Real.log (BPz2 (((m : ℝ) + 1 / 2) * h) / 0.355) / Real.log (10 / r) *
              W (h * (m : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range, show 2 * J - J = J by omega]
          refine Finset.sum_congr rfl fun k _ => ?_
          have e1 : J + k - J = k := by omega
          simp only [hw, hd, hZw, hdn, if_pos (show J ≤ J + k by omega), e1]
        rw [hA, hB]; ring

/-- The weight `1/max(2.39, t)²`. -/
noncomputable def Wsq (t : ℝ) : ℝ := 1 / max 2.39 t ^ 2

theorem Wsq_nonneg (t : ℝ) : 0 ≤ Wsq t := by unfold Wsq; positivity

theorem Wsq_anti : AntitoneOn Wsq (Ici 0) := by
  intro s _ t _ hst
  unfold Wsq
  have h1 : (0 : ℝ) < max 2.39 s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ h1.le (max_le_max le_rfl hst) 2)

/-- The line-zero constant for the weight `|M(ρ)|/|ρ − 1|`. -/
noncomputable def LQW (a b δ H : ℝ) : ℝ :=
  (Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2))) *
    (2 * ∑ m ∈ Finset.range (JlH 6 H), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * Wsq (6 * (m : ℝ)))

/-- On the critical line, away from `|γ| < 2.39`: `|M(ρ)|/|ρ − 1| ≤ e^{δ²/2}(e^{a/2} + e^{b/2}) W(|γ|)`. -/
theorem norm_Mg_div_le {a b δ : ℝ} {u : ℂ} (hre : u.re = 1 / 2) (him : 2.39 ≤ |u.im|) :
    ‖Mg a b δ u‖ / ‖u - 1‖ ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2)) * Wsq |u.im| := by
  have hu : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
  have hM := norm_Mg_line_le' a b δ u.im
  rw [← hu] at hM
  have hmax1 : max (1 / 2 : ℝ) |u.im| = |u.im| := max_eq_right (by linarith)
  have hmax2 : max (2.39 : ℝ) |u.im| = |u.im| := max_eq_right him
  rw [hmax1] at hM
  have hpos : 0 < |u.im| := by linarith
  have hn1 : |u.im| ≤ ‖u - 1‖ := by
    have := Complex.abs_im_le_norm (u - 1); simpa using this
  set C := Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2))
  have hC0 : 0 ≤ C := by positivity
  unfold Wsq; rw [hmax2]
  have hMle : ‖Mg a b δ u‖ ≤ C / |u.im| := by rw [le_div_iff₀ hpos]; exact hM
  calc ‖Mg a b δ u‖ / ‖u - 1‖ ≤ (C / |u.im|) / |u.im| :=
        div_le_div₀ (by positivity) hMle hpos hn1
    _ = C * (1 / |u.im| ^ 2) := by field_simp

/-- **The zero sum of the smoothed explicit formula**, uniformly in the rectangle: for `x ≥ 1`,
`‖Σ_{ρ ∈ R_T} m_ρ M(ρ) x^ρ‖ ≤ √x LineB2 + x TailB` (the bound inside `SsumG_gsm_errH`). -/
theorem norm_zeroSum_gsm_le {a b δ x H T : ℝ} (hH : 0 < H) (hRH : RHBelow H) (hδ : 0 < δ)
    (hb : b ≤ 0) (hx : 1 ≤ x) :
    ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (Mg a b δ u * (x : ℂ) ^ u)‖ ≤
      √x * LineB2H a b δ H + x * TailBH a δ H := by
  have hx0 : 0 < x := by linarith
  set Z := zerosRectD zetaF T with hZ
  set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
  have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (Mg a b δ u * (x : ℂ) ^ u)‖ ≤
      ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0]
  refine h1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H)]
  refine add_le_add ?_ ?_
  · set S := Z.filter (fun u => |u.im| ≤ H) with hS
    have hSZ : S ⊆ Z := Finset.filter_subset _ _
    have hre : ∀ u ∈ S, u.re = 1 / 2 := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
      exact hRH u hz hr1 hr2 hu2
    have him : ∀ u ∈ S, |u.im| ≤ H := fun u hu => (Finset.mem_filter.1 hu).2
    have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
      intro u hu
      rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine line_sum_leH hH.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) S hSZ hre him
      (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _) (by positivity) (fun u hu => ?_)
    have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
      apply Complex.ext <;> simp [hre u hu]
    rw [hu']
    have := norm_Mg_line_le' a b δ u.im
    simpa using this
  · set S := Z.filter (fun u => ¬ |u.im| ≤ H) with hS
    have hSZ : S ⊆ Z := Finset.filter_subset _ _
    have him : ∀ u ∈ S, H < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
    exact tail_sum_gauss hH hδ hb hx S hSZ him

/-- `y ↦ y^s` is continuous on `(0, ∞)`. -/
theorem continuousOn_ofReal_cpow (s : ℂ) : ContinuousOn (fun y : ℝ => (y : ℂ) ^ s) (Ioi 0) :=
  fun y hy => (continuousAt_ofReal_cpow_const y s (Or.inr (ne_of_gt hy))).continuousWithinAt

/-- `∫_{Y₁}^{Y₂} y^{u−2} dy = (Y₂^{u−1} − Y₁^{u−1})/(u − 1)`, so its norm is at most
`(Y₁^{β−1} + Y₂^{β−1})/|u − 1|`. -/
theorem norm_integral_cpow_le {Y1 Y2 : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) {u : ℂ} (hu : u ≠ 1) :
    ‖∫ y in Ioc Y1 Y2, (y : ℂ) ^ u * (y : ℂ) ^ (-2 : ℂ)‖ ≤
      (Y1 ^ (u.re - 1) + Y2 ^ (u.re - 1)) / ‖u - 1‖ := by
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  have e1 : ∫ y in Ioc Y1 Y2, (y : ℂ) ^ u * (y : ℂ) ^ (-2 : ℂ) = ∫ y in Y1..Y2, (y : ℂ) ^ (u - 2) := by
    rw [intervalIntegral.integral_of_le hY12]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have hy0 : (y : ℂ) ≠ 0 := by
      have : (0 : ℝ) < y := lt_trans hY1 hy.1
      exact_mod_cast this.ne'
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hy0]
  have h0 : (0 : ℝ) ∉ [[Y1, Y2]] := by
    rw [uIcc_of_le hY12]; intro h; linarith [h.1]
  have hne : u - 2 ≠ -1 := by intro h; apply hu; linear_combination h
  rw [e1, integral_cpow (Or.inr ⟨hne, h0⟩)]
  have e2 : u - 2 + 1 = u - 1 := by ring
  rw [e2, norm_div]
  have hu1 : 0 < ‖u - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
  refine div_le_div_of_nonneg_right ?_ hu1.le
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_cpow_x hY2, norm_cpow_x hY1]
  simp only [Complex.sub_re, Complex.one_re]
  ring

end TernaryGoldbach.Explicit

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.Explicit

/-- `(Ψ(y) − M y)/y²` is integrable on `(Y₁, Y₂]` (RH up to `H`). -/
theorem integrableOn_psi_gsm_sub {a b δ H Y1 Y2 : ℝ} (hH : 0 < H) (hRH : RHBelow H) (hδ : 0 < δ)
    (hab : b ≤ a) (hb : b ≤ 0) (hY1 : 1 ≤ Y1) :
    IntegrableOn (fun y => (∑' n : ℕ, Λ n * gsm a b δ (n / y) -
        Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * y) / y ^ 2) (Ioc Y1 Y2) := by
  have hY10 : 0 < Y1 := by linarith
  set M := Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) with hM
  set Ψ : ℝ → ℝ := fun y => ∑' n : ℕ, Λ n * gsm a b δ (n / y) with hΨ
  set μ := volume.restrict (Ioc Y1 Y2) with hμ
  have hcont_rpow : ∀ q : ℝ, ContinuousOn (fun y : ℝ => y ^ q) (Icc Y1 Y2) := fun q y hy =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hy.1]))).continuousWithinAt
  have hΨmeas : AEStronglyMeasurable (fun y => Ψ y / y ^ 2) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N y => ∑ n ∈ Finset.range N, Gy a b δ n y) (fun N => ?_) ?_
    · exact (integrable_finsetSum _ fun n _ => integrableOn_Gy hY10 n).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
      have hy0 : 0 < y := lt_trans hY10 hy.1
      have hs := (summable_gsm (a := a) (b := b) hδ hab hy0).div_const (y ^ 2)
      have := hs.hasSum.tendsto_sum_nat
      simp only [hΨ, ← tsum_div_const]
      simpa [Gy] using this
  have hFmeas : AEStronglyMeasurable (fun y => (Ψ y - M * y) / y ^ 2) μ := by
    have h2 : AEStronglyMeasurable (fun y : ℝ => M * y / y ^ 2) μ :=
      (Measurable.aestronglyMeasurable (by fun_prop))
    refine (hΨmeas.sub h2).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  set eb : ℝ → ℝ := fun y => (√y * LineB2H a b δ H + y * TailBH a δ H +
    y ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)) * y ^ (-2 : ℝ) with heb
  have heb_int : Integrable eb μ := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact ContinuousOn.mul (ContinuousOn.add (by fun_prop)
      ((hcont_rpow _).mul continuousOn_const |>.div_const _)) (hcont_rpow _)
  refine Integrable.mono' heb_int hFmeas ((ae_restrict_iff' measurableSet_Ioc).2
    (Eventually.of_forall fun y hy => ?_))
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have h := tsum_gsm_leH hH hRH hδ hab hb hy1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2)]
  have e : (y ^ 2)⁻¹ = y ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hy0.le, Real.rpow_two]
  rw [div_eq_mul_inv, e]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- **The integrated explicit formula**: with RH up to `H ≥ 2.39`, for `1 ≤ Y₁ ≤ Y₂`,
`|∫_{Y₁}^{Y₂} (Ψ(y) − M y)/y² dy| ≤ (Y₁^{−1/2} + Y₂^{−1/2}) LQW + 2 TailB/H + (2/3) Y₁^{−3/2} V/(2π)`,
`Ψ(y) = Σ Λ(n) gsm(n/y)`, `M = e^{δ²/2}(e^a − e^b)`. -/
theorem abs_integral_psi_gsm_le {a b δ H Y1 Y2 : ℝ} (hH : 2.39 ≤ H) (hRH : RHBelow H) (hδ : 0 < δ)
    (hab : b ≤ a) (hb : b ≤ 0) (hY1 : 1 ≤ Y1) (hY12 : Y1 ≤ Y2) :
    |∫ y in Ioc Y1 Y2, (∑' n : ℕ, Λ n * gsm a b δ (n / y) -
        Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * y) / y ^ 2| ≤
      (Y1 ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a b δ H + 2 * TailBH a δ H / H +
        2 / 3 * Y1 ^ (-(3 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hH0 : 0 < H := by linarith
  have hY10 : 0 < Y1 := by linarith
  have hY20 : 0 < Y2 := by linarith
  have hIoc : ∀ y ∈ Ioc Y1 Y2, 1 ≤ y ∧ 0 < y := fun y hy => ⟨by linarith [hy.1], by linarith [hy.1]⟩
  set M := Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) with hM
  set Ψ : ℝ → ℝ := fun y => ∑' n : ℕ, Λ n * gsm a b δ (n / y) with hΨ
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hMel : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  set Tk := goodSeqD ldatum_zeta with hTk
  set S : ℕ → ℝ → ℂ := fun k y => ∑ u ∈ zerosRectD zetaF (Tk k),
    (multRectD zetaF (Tk k) u : ℂ) * (Mg a b δ u * (y : ℂ) ^ u) with hS
  set Jc : ℝ → ℂ := fun y => (1 / (2 * π) : ℂ) * ∫ t : ℝ, hZeta φ y (((-1 / 2 : ℝ) : ℂ) + t * I) with hJc
  set L : ℝ → ℂ := fun y => (M : ℂ) * y - (Ψ y : ℂ) - Jc y with hL
  set w : ℝ → ℂ := fun y => (y : ℂ) ^ (-2 : ℂ) with hw
  set μ := volume.restrict (Ioc Y1 Y2) with hμ
  -- the explicit formula at each `y`
  have hlim : ∀ y, 0 < y → Tendsto (fun k => S k y) atTop (𝓝 (L y)) := by
    intro y hy
    have h := explicit_formula_zeta_seq hgood hy
    rw [hMel, SsumG_one_ofReal, Mg_one] at h
    exact h
  -- `‖w(y)‖ = y^{−2}`
  have hwn : ∀ y, 0 < y → ‖w y‖ = y ^ (-2 : ℝ) := by
    intro y hy; simp only [hw]; rw [norm_cpow_x hy]; simp
  -- dominated convergence
  set bnd : ℝ → ℝ := fun y => (√y * LineB2H a b δ H + y * TailBH a δ H) * y ^ (-2 : ℝ) with hbnd
  have hcont_rpow : ∀ q : ℝ, ContinuousOn (fun y : ℝ => y ^ q) (Icc Y1 Y2) := fun q y hy =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hy.1]))).continuousWithinAt
  have hbnd_int : Integrable bnd μ := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact ContinuousOn.mul (by fun_prop) (hcont_rpow _)
  have hcontS : ∀ k, ContinuousOn (fun y => S k y * w y) (Ioi 0) := by
    intro k
    refine ContinuousOn.mul ?_ (continuousOn_ofReal_cpow _)
    exact continuousOn_finsetSum _ fun u _ => continuousOn_const.mul
      (continuousOn_const.mul (continuousOn_ofReal_cpow u))
  have hmeasS : ∀ k, AEStronglyMeasurable (fun y => S k y * w y) μ := fun k =>
    ((hcontS k).mono fun y hy => lt_trans hY10 hy.1).aestronglyMeasurable measurableSet_Ioc
  have hboundS : ∀ k, ∀ᵐ y ∂μ, ‖S k y * w y‖ ≤ bnd y := by
    intro k
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
    obtain ⟨hy1, hy0⟩ := hIoc y hy
    rw [norm_mul, hwn y hy0]
    exact mul_le_mul_of_nonneg_right (norm_zeroSum_gsm_le hH0 hRH hδ hb hy1) (by positivity)
  have hlimS : ∀ᵐ y ∂μ, Tendsto (fun k => S k y * w y) atTop (𝓝 (L y * w y)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
    exact (hlim y (hIoc y hy).2).mul_const _
  have hDCT := tendsto_integral_of_dominated_convergence bnd hmeasS hbnd_int hboundS hlimS
  -- `L w` is integrable
  have hLmeas : AEStronglyMeasurable (fun y => L y * w y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeasS hlimS
  have hLint : Integrable (fun y => L y * w y) μ := by
    refine Integrable.mono' hbnd_int hLmeas ?_
    filter_upwards [hlimS, ae_all_iff.2 hboundS] with y hy hb'
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hy) hb'
  -- the zero sums, integrated
  set Bz := (Y1 ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a b δ H + 2 * TailBH a δ H / H with hBz
  have hSk_bd : ∀ k, ‖∫ y, S k y * w y ∂μ‖ ≤ Bz := by
    intro k
    set Z := zerosRectD zetaF (Tk k) with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF (Tk k) u : ℝ) with hm
    have hint_u : ∀ u : ℂ, Integrable (fun y : ℝ => (y : ℂ) ^ u * w y) μ := fun u =>
      (ContinuousOn.integrableOn_Icc (((continuousOn_ofReal_cpow u).mul (continuousOn_ofReal_cpow _)).mono
        fun y hy => lt_of_lt_of_le hY10 hy.1)).mono_set Ioc_subset_Icc_self
    have e : (fun y => S k y * w y) = fun y : ℝ => ∑ u ∈ Z,
        ((multRectD zetaF (Tk k) u : ℂ) * Mg a b δ u) * ((y : ℂ) ^ u * w y) := by
      funext y; simp only [hS, Finset.sum_mul]; refine Finset.sum_congr rfl fun u _ => by ring
    rw [e, integral_finsetSum _ fun u _ => (hint_u u).const_mul _]
    have hzero : ∀ u ∈ Z, u ≠ 1 ∧ 0 < u.re ∧ u.re < 1 ∧ riemannZeta u = 0 := by
      intro u hu
      obtain ⟨hz, h1, h2, -⟩ := zerosRectD_zetaF_strip hu
      exact ⟨fun h => by rw [h] at h2; simp at h2, h1, h2, hz⟩
    have hterm : ∀ u ∈ Z, ‖∫ y, ((multRectD zetaF (Tk k) u : ℂ) * Mg a b δ u) * ((y : ℂ) ^ u * w y) ∂μ‖ ≤
        m u * (‖Mg a b δ u‖ * ((Y1 ^ (u.re - 1) + Y2 ^ (u.re - 1)) / ‖u - 1‖)) := by
      intro u hu
      rw [integral_const_mul, norm_mul, norm_mul, Complex.norm_natCast, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (norm_integral_cpow_le hY10 hY12 (hzero u hu).1) (norm_nonneg _)) (Nat.cast_nonneg _)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H)]
    refine add_le_add ?_ ?_
    · -- line zeros
      set SL := Z.filter (fun u => |u.im| ≤ H) with hSL
      have hSLZ : SL ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ SL, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨-, h1, h2, hz⟩ := hzero u hu1
        exact hRH u hz h1 h2 hu2
      have him : ∀ u ∈ SL, |u.im| ≤ H := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ SL, m u * (‖Mg a b δ u‖ * ((Y1 ^ (u.re - 1) + Y2 ^ (u.re - 1)) / ‖u - 1‖)) =
          (Y1 ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * (m u * (‖Mg a b δ u‖ / ‖u - 1‖)) := by
        intro u hu
        rw [hre u hu]; norm_num; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine line_sum_leW hH0.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) SL
        (hSLZ.trans le_rfl) hre him (fun u => ‖Mg a b δ u‖ / ‖u - 1‖) (by positivity) Wsq Wsq_nonneg
        Wsq_anti fun u hu => ?_
      obtain ⟨-, h1, h2, hz⟩ := hzero u (hSLZ hu)
      exact norm_Mg_div_le (hre u hu) (abs_im_ge_of_zeroH hRH hH hz h1 h2)
    · -- zeros above `H`
      set ST := Z.filter (fun u => ¬ |u.im| ≤ H) with hST
      have hSTZ : ST ⊆ Z := Finset.filter_subset _ _
      have him : ∀ u ∈ ST, H < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      have hpt : ∀ u ∈ ST, m u * (‖Mg a b δ u‖ * ((Y1 ^ (u.re - 1) + Y2 ^ (u.re - 1)) / ‖u - 1‖)) ≤
          2 / H * (m u * (‖Mg a b δ u‖ * (1 : ℝ) ^ u.re)) := by
        intro u hu
        obtain ⟨-, h1, h2, -⟩ := hzero u (hSTZ hu)
        have hY1p : Y1 ^ (u.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
        have hY2p : Y2 ^ (u.re - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
        have hn : H ≤ ‖u - 1‖ := by
          have := Complex.abs_im_le_norm (u - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
          linarith [him u hu]
        have hq : (Y1 ^ (u.re - 1) + Y2 ^ (u.re - 1)) / ‖u - 1‖ ≤ 2 / H :=
          div_le_div₀ (by norm_num) (by linarith) hH0 hn
        rw [Real.one_rpow, mul_one]
        have hm0 : 0 ≤ m u := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_left hq (mul_nonneg hm0 (norm_nonneg (Mg a b δ u)))
        nlinarith
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [← Finset.mul_sum]
      have ht := tail_sum_gauss (a := a) hH0 hδ hb le_rfl ST (hSTZ.trans le_rfl) him
      rw [one_mul] at ht
      have : 2 / H * ∑ u ∈ ST, m u * (‖Mg a b δ u‖ * (1 : ℝ) ^ u.re) ≤ 2 / H * TailBH a δ H :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      calc _ ≤ 2 / H * TailBH a δ H := this
        _ = 2 * TailBH a δ H / H := by ring
  have hL_bd : ‖∫ y, L y * w y ∂μ‖ ≤ Bz :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hDCT) hSk_bd
  -- `Ψ − M y`: measurable, and bounded on `[Y₁, Y₂]`
  have hΨmeas : AEStronglyMeasurable (fun y => Ψ y / y ^ 2) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N y => ∑ n ∈ Finset.range N, Gy a b δ n y) (fun N => ?_) ?_
    · exact (integrable_finsetSum _ fun n _ => integrableOn_Gy hY10 n).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
      have hy0 : 0 < y := lt_trans hY10 hy.1
      have hs := (summable_gsm (a := a) (b := b) hδ hab hy0).div_const (y ^ 2)
      have := hs.hasSum.tendsto_sum_nat
      simp only [hΨ, ← tsum_div_const]
      simpa [Gy] using this
  set F : ℝ → ℝ := fun y => (Ψ y - M * y) / y ^ 2 with hF
  have hFmeas : AEStronglyMeasurable F μ := by
    have h2 : AEStronglyMeasurable (fun y : ℝ => M * y / y ^ 2) μ :=
      (Measurable.aestronglyMeasurable (by fun_prop))
    refine (hΨmeas.sub h2).congr (Eventually.of_forall fun y => ?_)
    simp only [hF, Pi.sub_apply]; ring
  set eb : ℝ → ℝ := fun y => (√y * LineB2H a b δ H + y * TailBH a δ H +
    y ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)) * y ^ (-2 : ℝ) with heb
  have heb_int : Integrable eb μ := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact ContinuousOn.mul (ContinuousOn.add (by fun_prop) ((hcont_rpow _).mul continuousOn_const |>.div_const _))
      (hcont_rpow _)
  have hFint : Integrable F μ := by
    refine Integrable.mono' heb_int hFmeas ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun y hy => ?_))
    obtain ⟨hy1, hy0⟩ := hIoc y hy
    have h := tsum_gsm_leH hH0 hRH hδ hab hb hy1
    rw [Real.norm_eq_abs, hF, abs_div, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2)]
    have e : (y ^ 2)⁻¹ = y ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy0.le, Real.rpow_two]
    rw [div_eq_mul_inv, e]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  -- the identity `F + L w = −J w`
  have hFc : ∀ y ∈ Ioc Y1 Y2, ((F y : ℝ) : ℂ) = ((Ψ y - M * y : ℝ) : ℂ) * w y := by
    intro y hy
    obtain ⟨-, hy0⟩ := hIoc y hy
    simp only [hF, hw]
    rw [Complex.ofReal_div, div_eq_mul_inv]
    congr 1
    rw [Complex.cpow_neg, Complex.ofReal_pow]
    norm_cast
  have hJ : ∀ y ∈ Ioc Y1 Y2, ‖((F y : ℝ) : ℂ) + L y * w y‖ ≤ Vg a b δ / (2 * π) * y ^ (-(5 / 2) : ℝ) := by
    intro y hy
    obtain ⟨-, hy0⟩ := hIoc y hy
    have e : ((F y : ℝ) : ℂ) + L y * w y = -(Jc y * w y) := by
      rw [hFc y hy]; simp only [hL]; push_cast; ring
    rw [e, norm_neg, norm_mul, hwn y hy0]
    have hJn : ‖Jc y‖ ≤ y ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
      simp only [hJc]
      rw [norm_mul]
      have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
        rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [h1]
      have := norm_integral_hZeta_gsm hδ hab hy0
      rw [div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_right this (by positivity)
    have e2 : y ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) * y ^ (-2 : ℝ) =
        Vg a b δ / (2 * π) * y ^ (-(5 / 2) : ℝ) := by
      rw [show (-(5 / 2) : ℝ) = -(1 / 2) + -2 by norm_num, Real.rpow_add hy0]; ring
    rw [← e2]
    exact mul_le_mul_of_nonneg_right hJn (by positivity)
  have hVg : 0 ≤ Vg a b δ := by
    unfold Vg
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hJint : ‖∫ y, (((F y : ℝ) : ℂ) + L y * w y) ∂μ‖ ≤ 2 / 3 * Y1 ^ (-(3 / 2) : ℝ) * Vg a b δ / (2 * π) := by
    have hg : Integrable (fun y : ℝ => Vg a b δ / (2 * π) * y ^ (-(5 / 2) : ℝ)) μ :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.mul (hcont_rpow _))).mono_set Ioc_subset_Icc_self
    refine (norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall hJ))).trans ?_
    rw [integral_const_mul, hμ, ← intervalIntegral.integral_of_le hY12,
      integral_rpow (Or.inr ⟨by norm_num, by rw [uIcc_of_le hY12]; intro h; linarith [h.1]⟩)]
    have hY2p : 0 ≤ Y2 ^ (-(5 / 2) + 1 : ℝ) := Real.rpow_nonneg hY20.le _
    have e : (-(5 / 2) + 1 : ℝ) = -(3 / 2) := by norm_num
    rw [e] at hY2p ⊢
    have hc : 0 ≤ Vg a b δ / (2 * π) := by positivity
    have : (Y2 ^ (-(3 / 2) : ℝ) - Y1 ^ (-(3 / 2) : ℝ)) / (-(3 / 2)) ≤ 2 / 3 * Y1 ^ (-(3 / 2) : ℝ) := by
      rw [div_le_iff_of_neg (by norm_num)]; nlinarith
    calc Vg a b δ / (2 * π) * ((Y2 ^ (-(3 / 2) : ℝ) - Y1 ^ (-(3 / 2) : ℝ)) / (-(3 / 2)))
        ≤ Vg a b δ / (2 * π) * (2 / 3 * Y1 ^ (-(3 / 2) : ℝ)) := mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  -- assemble
  have hFcint : Integrable (fun y => ((F y : ℝ) : ℂ)) μ := hFint.ofReal
  have hsum : ∫ y, (((F y : ℝ) : ℂ) + L y * w y) ∂μ = (∫ y, ((F y : ℝ) : ℂ) ∂μ) + ∫ y, L y * w y ∂μ :=
    integral_add hFcint hLint
  have hcast : ((∫ y, F y ∂μ : ℝ) : ℂ) = ∫ y, ((F y : ℝ) : ℂ) ∂μ := integral_ofReal.symm
  have key : ‖((∫ y, F y ∂μ : ℝ) : ℂ)‖ ≤ 2 / 3 * Y1 ^ (-(3 / 2) : ℝ) * Vg a b δ / (2 * π) + Bz := by
    rw [hcast, show (∫ y, ((F y : ℝ) : ℂ) ∂μ) = (∫ y, (((F y : ℝ) : ℂ) + L y * w y) ∂μ) - ∫ y, L y * w y ∂μ by
      rw [hsum]; ring]
    exact (norm_sub_le _ _).trans (add_le_add hJint hL_bd)
  rw [Complex.norm_real, Real.norm_eq_abs] at key
  have e : (∫ y in Ioc Y1 Y2, (∑' n : ℕ, Λ n * gsm a b δ (n / y) -
      Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * y) / y ^ 2) = ∫ y, F y ∂μ := rfl
  rw [e]
  linarith

end TernaryGoldbach.Prelim
