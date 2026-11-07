import TernaryGoldbach.Explicit.ZetaGrowth
import TernaryGoldbach.Explicit.ZetaZeroSums

/-!
# No zeros of `ζ` with `|γ| < 2.39`

One more integration by parts in `Izeta` (`ZetaGrowth`): with `P₂(t) = ({t}² − {t})/2 ∈ [−1/8, 0]`,
`Izeta(s) = −1/(2s) − (s + 1) J(s)`, `J(s) = ∫₁^∞ P₂(t) t^{−s−2} dt` (`Izeta_eq`), so
`zetaF(s) = (s + 1)/2 − s(s² − 1) J(s)` and `|J(½ + it)| ≤ 1/12`. Since `|s| = |s − 1|` on the critical
line, `zetaF(½ + it) = 0` needs `|s|² ≥ 6`, i.e. `|t| ≥ 2.39…` (`zetaF_half_ne_zero`). With RH up to
a height `H ≥ 2.39`, every nontrivial zero has `|γ| ≥ 2.39` (`abs_im_ge_of_zeroH`).
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-- `P₂(t) = ({t}² − {t})/2`. -/
noncomputable def P2 (t : ℝ) : ℝ := (Int.fract t ^ 2 - Int.fract t) / 2

theorem P2_nonpos (t : ℝ) : P2 t ≤ 0 := by
  unfold P2
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  nlinarith

theorem neg_eighth_le_P2 (t : ℝ) : -(1 / 8) ≤ P2 t := by
  unfold P2; nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

theorem abs_P2_le (t : ℝ) : |P2 t| ≤ 1 / 8 := by
  rw [abs_le]; exact ⟨neg_eighth_le_P2 t, by linarith [P2_nonpos t]⟩

theorem measurable_P2 : Measurable P2 := by
  unfold P2; exact ((measurable_fract.pow_const 2).sub measurable_fract).div_const 2

theorem saw_eq {t : ℝ} (ht : 0 ≤ t) : saw t = -((Int.fract t : ℝ) : ℂ) := by
  rw [saw, Int.fract, ← Int.natCast_floor_eq_floor ht]; push_cast; ring

/-- `J(s) = ∫₁^∞ P₂(t) t^{−s−2} dt`. -/
noncomputable def Jzeta (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (P2 t : ℂ) * (t : ℂ) ^ (-(s + 2))

theorem integrableOn_P2_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (P2 t : ℂ) * (t : ℂ) ^ (-(s + 2))) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 2)) (by linarith) one_pos).const_mul
    (1 / 8 : ℝ)).mono' ?_ ?_
  · refine (Complex.measurable_ofReal.comp measurable_P2).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (Complex.continuousAt_ofReal_cpow_const t _
      (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht']
    have : (-(s + 2)).re = -(s.re + 2) := by simp only [Complex.neg_re, Complex.add_re, Complex.re_ofNat]
    rw [this]
    exact mul_le_mul_of_nonneg_right (abs_P2_le t) (Real.rpow_nonneg ht'.le _)

theorem norm_Jzeta_le {s : ℂ} (hs : 0 < s.re) : ‖Jzeta s‖ ≤ 1 / (8 * (s.re + 1)) := by
  unfold Jzeta
  have hb : ∀ t ∈ Ioi (1 : ℝ), ‖(P2 t : ℂ) * (t : ℂ) ^ (-(s + 2))‖ ≤ 1 / 8 * t ^ (-(s.re + 2)) := by
    intro t ht
    have ht' : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht']
    have : (-(s + 2)).re = -(s.re + 2) := by simp only [Complex.neg_re, Complex.add_re, Complex.re_ofNat]
    rw [this]
    exact mul_le_mul_of_nonneg_right (abs_P2_le t) (Real.rpow_nonneg ht'.le _)
  have hint : IntegrableOn (fun t : ℝ => 1 / 8 * t ^ (-(s.re + 2))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 2)) (by linarith) one_pos).const_mul _
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall hb))).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    show -(s.re + 2) + 1 = -(s.re + 1) by ring]
  have : 0 < s.re + 1 := by linarith
  field_simp

theorem fract_eq_sub {n : ℕ} {t : ℝ} (h1 : (n : ℝ) < t) (h2 : t < n + 1) : Int.fract t = t - n := by
  rw [Int.fract, show (⌊t⌋ : ℝ) = n by
    rw [show (n : ℝ) = ((n : ℤ) : ℝ) by push_cast; rfl]
    exact_mod_cast Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩]

/-- On `(n, n+1)` both integrands are the polynomial versions, a.e. on the interval. -/
theorem ae_fract_eq (n : ℕ) {f g : ℝ → ℂ} (h : ∀ t, (n : ℝ) < t → t < n + 1 → f t = g t) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (n : ℝ) (n + 1) → f t = g t := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (n : ℝ) + 1 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  filter_upwards [hne] with t ht hmem
  rw [uIoc_of_le (by linarith)] at hmem
  exact h t hmem.1 (lt_of_le_of_ne hmem.2 ht)

/-- **One unit interval**: `∫_n^{n+1} ({t} − ½) t^{−s−1} = (s + 1) ∫_n^{n+1} P₂(t) t^{−s−2}`. -/
theorem unit_ibp {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in (n : ℝ)..(n + 1), ((Int.fract t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (s + 1) * ∫ t in (n : ℝ)..(n + 1), (P2 t : ℂ) * (t : ℂ) ^ (-(s + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : ∀ t ∈ uIcc (n : ℝ) (n + 1), 0 < t := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht; linarith [ht.1]
  have hr : -(s + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set q : ℝ → ℝ := fun t => ((t - n) ^ 2 - (t - n)) / 2 with hq
  set F : ℝ → ℂ := fun t => (q t : ℂ) * (t : ℂ) ^ (-(s + 1)) with hF
  set F' : ℝ → ℂ := fun t => ((t - n - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) +
    (q t : ℂ) * (-(s + 1) * (t : ℂ) ^ (-(s + 1) - 1)) with hF'
  have hderiv : ∀ t ∈ uIcc (n : ℝ) (n + 1), HasDerivAt F (F' t) t := by
    intro t ht
    have h0 := (hpos t ht).ne'
    have hq' : HasDerivAt (fun t : ℝ => ((q t : ℝ) : ℂ)) ((t - n - 1 / 2 : ℝ) : ℂ) t := by
      have : HasDerivAt q (t - n - 1 / 2) t := by
        have h := (((hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul ((2 : ℝ) * n + 1))).add_const
          ((n : ℝ) ^ 2 + n)).div_const 2
        have hqe : q = fun x => (x ^ 2 - ((2 : ℝ) * n + 1) * id x + ((n : ℝ) ^ 2 + n)) / 2 := by
          funext x; simp only [hq, id]; ring
        rw [hqe]
        exact h.congr_deriv (by norm_num; ring)
      exact this.ofReal_comp
    exact hq'.mul (hasDerivAt_ofReal_cpow_const h0 hr)
  have hcont : ContinuousOn F' (uIcc (n : ℝ) (n + 1)) := by
    intro t ht
    have h0 := (hpos t ht).ne'
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) t :=
      Complex.continuousAt_ofReal_cpow_const t _ (Or.inr h0)
    have c2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-(s + 1) - 1)) t :=
      Complex.continuousAt_ofReal_cpow_const t _ (Or.inr h0)
    exact ((by fun_prop : Continuous fun t : ℝ => ((t - n - 1 / 2 : ℝ) : ℂ)).continuousAt.mul c1).add
      ((by fun_prop : Continuous fun t : ℝ => ((q t : ℝ) : ℂ)).continuousAt.mul (continuousAt_const.mul c2))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  have hF0 : F (n + 1) - F n = 0 := by simp [hF, hq]
  rw [hF0] at hFTC
  -- split `F'` and identify the two integrals
  have hA : IntervalIntegrable (fun t : ℝ => ((t - n - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) volume
      (n : ℝ) (n + 1) := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    exact (by fun_prop : Continuous fun t : ℝ => ((t - n - 1 / 2 : ℝ) : ℂ)).continuousAt.mul
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hpos t ht).ne'))
  have hB : IntervalIntegrable (fun t : ℝ => (q t : ℂ) * (t : ℂ) ^ (-(s + 2))) volume (n : ℝ) (n + 1) := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    exact (by fun_prop : Continuous fun t : ℝ => ((q t : ℝ) : ℂ)).continuousAt.mul
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hpos t ht).ne'))
  have he : ∀ t : ℝ, F' t = ((t - n - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) -
      (s + 1) * ((q t : ℂ) * (t : ℂ) ^ (-(s + 2))) := by
    intro t; simp only [hF']; rw [show -(s + 1) - 1 = -(s + 2) by ring]; ring
  simp_rw [he] at hFTC
  rw [intervalIntegral.integral_sub hA (hB.const_mul _), intervalIntegral.integral_const_mul,
    sub_eq_zero] at hFTC
  have e1 : ∫ t in (n : ℝ)..(n + 1), ((Int.fract t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in (n : ℝ)..(n + 1), ((t - n - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
    intervalIntegral.integral_congr_ae (ae_fract_eq n fun t h1 h2 => by rw [fract_eq_sub h1 h2])
  have e2 : ∫ t in (n : ℝ)..(n + 1), (P2 t : ℂ) * (t : ℂ) ^ (-(s + 2)) =
      ∫ t in (n : ℝ)..(n + 1), (q t : ℂ) * (t : ℂ) ^ (-(s + 2)) :=
    intervalIntegral.integral_congr_ae (ae_fract_eq n fun t h1 h2 => by
      rw [P2, fract_eq_sub h1 h2])
  rw [e1, e2, hFTC]

theorem integrableOn_fract_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
    (1 : ℝ)).mono' ?_ ?_
  · refine (Complex.measurable_ofReal.comp (measurable_fract.sub measurable_const)).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (Complex.continuousAt_ofReal_cpow_const t _
      (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht']
    have : (-(s + 1)).re = -(s.re + 1) := by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    rw [this]
    have h1 : |Int.fract t - 1 / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht'.le _)

/-- **`Izeta(s) = −1/(2s) − (s + 1) J(s)`**. -/
theorem Izeta_eq {s : ℂ} (hs : 0 < s.re) : Izeta s = -1 / (2 * s) - (s + 1) * Jzeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  set f : ℝ → ℂ := fun t => ((Int.fract t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) with hf
  set g : ℝ → ℂ := fun t => (P2 t : ℂ) * (t : ℂ) ^ (-(s + 2)) with hg
  have hfi := integrableOn_fract_integrand hs
  have hgi := integrableOn_P2_integrand hs
  -- `∫₁^{M+1} f = (s + 1) ∫₁^{M+1} g`
  have hfin : ∀ M : ℕ, ∫ t in (1 : ℝ)..((M : ℝ) + 1), f t = (s + 1) * ∫ t in (1 : ℝ)..((M : ℝ) + 1), g t := by
    intro M
    have hii : ∀ (F : ℝ → ℂ), IntegrableOn F (Ioi 1) → ∀ k < M,
        IntervalIntegrable F volume ((k : ℝ) + 1) (((k + 1 : ℕ) : ℝ) + 1) := by
      intro F hF k _
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
      refine hF.mono_set fun t ht => ?_
      have h1 := ht.1
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      show (1 : ℝ) < t
      linarith
    have h1 := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) + 1) (n := M)
      (f := f) (μ := volume) (hii f hfi)
    have h2 := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) + 1) (n := M)
      (f := g) (μ := volume) (hii g hgi)
    simp only [Nat.cast_zero, zero_add] at h1 h2
    rw [← h1, ← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := unit_ibp hs (n := k + 1) (by omega)
    simp only [hf, hg]
    push_cast at this ⊢
    exact this
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hf_lim := (intervalIntegral_tendsto_integral_Ioi 1 hfi tendsto_id).comp hlim
  have hg_lim := ((intervalIntegral_tendsto_integral_Ioi 1 hgi tendsto_id).comp hlim).const_mul (s + 1)
  have hK : ∫ t in Ioi (1 : ℝ), f t = (s + 1) * Jzeta s := by
    refine tendsto_nhds_unique hf_lim ?_
    refine hg_lim.congr fun M => ?_
    simp only [Function.comp, id]; exact (hfin M).symm
  -- `saw t t^{−s−1} = −½ t^{−s−1} − f(t)`
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hsplit : Izeta s = ∫ t in Ioi (1 : ℝ), (-(1 / 2 : ℂ) * (t : ℂ) ^ (-(s + 1)) - f t) := by
    unfold Izeta
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    simp only [hf]
    rw [saw_eq ht0]; push_cast; ring
  rw [hsplit, integral_sub (hpow.const_mul _) hfi, integral_const_mul, hK,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  rw [show -(s + 1) + 1 = -s by ring, Complex.ofReal_one, Complex.one_cpow]
  field_simp

/-- `zetaF(s) = (s + 1)/2 − s(s² − 1) J(s)` for `ℜs > 0`. -/
theorem zetaF_eq_J {s : ℂ} (hs : 0 < s.re) : zetaF s = (s + 1) / 2 - s * (s - 1) * (s + 1) * Jzeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rw [zetaF_eq hs, Izeta_eq hs]
  field_simp
  ring

/-- **No zeros on the critical line with `|t| < 2.39`.** -/
theorem zetaF_half_ne_zero {t : ℝ} (ht : |t| < 2.39) : zetaF ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have him : s.im = t := by simp [hsdef]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hJ := norm_Jzeta_le hs
  rw [hre] at hJ
  have hn : ‖s‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring
  have hn1 : ‖s - 1‖ = ‖s‖ := by
    have : ‖s - 1‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hsdef]; ring
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), this, hn]
  have ht2 : t ^ 2 < 2.39 ^ 2 := by
    have := sq_abs t; nlinarith [abs_nonneg t]
  have hs1 : 0 < ‖s + 1‖ := by
    have : (s + 1).re = 3 / 2 := by simp [hsdef]; norm_num
    exact lt_of_lt_of_le (by norm_num) (this ▸ Complex.re_le_norm (s + 1))
  rw [zetaF_eq_J hs]
  intro h
  have heq : (s + 1) / 2 = s * (s - 1) * (s + 1) * Jzeta s := sub_eq_zero.1 h
  have hA : ‖(s + 1) / 2‖ = ‖s + 1‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hB : ‖s * (s - 1) * (s + 1) * Jzeta s‖ ≤ ‖s‖ ^ 2 * ‖s + 1‖ * (1 / (8 * (1 / 2 + 1))) := by
    rw [norm_mul, norm_mul, norm_mul, hn1]
    have := norm_nonneg (s + 1)
    calc ‖s‖ * ‖s‖ * ‖s + 1‖ * ‖Jzeta s‖ ≤ ‖s‖ * ‖s‖ * ‖s + 1‖ * (1 / (8 * (1 / 2 + 1))) := by gcongr
      _ = _ := by ring
  rw [heq] at hA
  rw [hA, hn] at hB
  have : (1 / 4 + t ^ 2) * ‖s + 1‖ * (1 / (8 * (1 / 2 + 1))) < ‖s + 1‖ / 2 := by
    have : (1 / 4 + t ^ 2) * (1 / (8 * (1 / 2 + 1))) < 1 / 2 := by nlinarith
    nlinarith
  linarith


/-- Every zero of `ζ` in the critical strip has `|γ| ≥ 2.39`, under RH up to any `H ≥ 2.39`. -/
theorem abs_im_ge_of_zeroH {H : ℝ} (hRH : RHBelow H) (hH : 2.39 ≤ H) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : 2.39 ≤ |ρ.im| := by
  by_contra hlt
  push Not at hlt
  have hre := hRH ρ hz h0 h1 (by linarith)
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hne := zetaF_half_ne_zero hlt
  rw [← hρ] at hne
  apply hne
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  rw [zetaF_of_ne hρ1, hz, mul_zero]

end TernaryGoldbach.Explicit
