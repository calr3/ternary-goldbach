import TernaryGoldbach.Explicit.WeilRect
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Weil identity: the three parts of `ξ'/ξ` on `ℜs = 3/2`

`H̃(s) = H_T(s) + H_T(1 − s)` (`WHt`). On `ℜs = 3/2`,
`ξ'/ξ(s) = (1/s + 1/(s − 1)) + (−½ log π + ½ψ(s/2)) + ζ'/ζ(s)`, and
* `∫ ζ'/ζ(3/2 + iy) H̃(3/2 + iy) dy = 0` (`integral_logDeriv_zeta_WHt`): `ζ'/ζ = −Σ Λ(n) n^{−s}`,
  termwise, and each term vanishes by `Explicit/WeilPrime.lean` when `e^{2mℓ} < 2`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval LSeries.notation

namespace TernaryGoldbach.Explicit

open ArithmeticFunction (vonMangoldt)

/-- `H̃_T(s) = H_T(s) + H_T(1 − s)`. -/
noncomputable def WHt (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) (s : ℂ) : ℂ := WH ℓ m T₀ s + WH ℓ m T₀ (1 - s)

theorem differentiable_WHt (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) : Differentiable ℂ (WHt ℓ m T₀) :=
  (differentiable_WH ℓ m T₀).add
    ((differentiable_WH ℓ m T₀).comp ((differentiable_const 1).sub differentiable_id))

theorem norm_WHt_le {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T₀ : ℝ) (s : ℂ) :
    ‖WHt ℓ m T₀ s‖ ≤ 4 ^ m * Real.exp (2 * m * ℓ * |s.re - 1 / 2|) * (lor (s.im - T₀) + lor (s.im + T₀)) := by
  have h1 := norm_WH_le_exp hℓ0 hℓ1 hm T₀ s
  have h2 := norm_WH_le_exp hℓ0 hℓ1 hm T₀ (1 - s)
  have e1 : |(1 - s).re - 1 / 2| = |s.re - 1 / 2| := by
    rw [show (1 - s).re - 1 / 2 = -(s.re - 1 / 2) by simp; ring, abs_neg]
  have e2 : lor ((1 - s).im - T₀) = lor (s.im + T₀) := by
    rw [show (1 - s).im - T₀ = -(s.im + T₀) by simp; ring, lor_neg]
  rw [e1, e2] at h2
  calc ‖WHt ℓ m T₀ s‖ ≤ ‖WH ℓ m T₀ s‖ + ‖WH ℓ m T₀ (1 - s)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The majorant of `H̃` on the line `ℜs = c`. -/
noncomputable def WHtMaj (ℓ : ℝ) (m : ℕ) (T₀ c : ℝ) (y : ℝ) : ℝ :=
  4 ^ m * Real.exp (2 * m * ℓ * |c - 1 / 2|) * (lor (y - T₀) + lor (y + T₀))

theorem integrable_WHtMaj (ℓ : ℝ) (m : ℕ) (T₀ c : ℝ) : Integrable (WHtMaj ℓ m T₀ c) := by
  have h2 : Integrable fun y : ℝ => lor (y + T₀) := by
    simpa [sub_neg_eq_add] using integrable_lor (-T₀)
  exact ((integrable_lor T₀).add h2).const_mul _

theorem norm_WHt_line_le {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T₀ c y : ℝ) :
    ‖WHt ℓ m T₀ ((c : ℂ) + y * I)‖ ≤ WHtMaj ℓ m T₀ c y := by
  have := norm_WHt_le hℓ0 hℓ1 hm T₀ ((c : ℂ) + y * I)
  simpa [WHtMaj] using this

theorem integrable_WHt_line {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T₀ c : ℝ) :
    Integrable fun y : ℝ => WHt ℓ m T₀ ((c : ℂ) + y * I) :=
  (integrable_WHtMaj ℓ m T₀ c).mono' ((differentiable_WHt ℓ m T₀).continuous.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun y => norm_WHt_line_le hℓ0 hℓ1 hm T₀ c y)

/-! ### `ζ'/ζ`: the prime side -/

theorem logDeriv_zeta_eq_neg_LSeries {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s = -LSeries ↗vonMangoldt s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply]; ring

/-- `Σ_n ‖term Λ (3/2) n‖ < ∞`. -/
theorem summable_norm_term_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖LSeries.term ↗vonMangoldt s n‖ :=
  (summable_norm_iff (E := ℂ)).2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)

/-- **The prime side vanishes**: `∫ ζ'/ζ(3/2 + iy) H̃(3/2 + iy) dy = 0` if `e^{2mℓ} < 2`. -/
theorem integral_logDeriv_zeta_WHt {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) (T₀ : ℝ) :
    ∫ y : ℝ, logDeriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) = 0 := by
  set s : ℝ → ℂ := fun y => ((3 / 2 : ℝ) : ℂ) + y * I with hsdef
  have hre : ∀ y, (s y).re = 3 / 2 := fun y => by simp [hsdef]
  have hre1 : ∀ y, 1 < (s y).re := fun y => by rw [hre]; norm_num
  set W : ℝ → ℂ := fun y => WHt ℓ m T₀ (s y) with hW
  set F : ℕ → ℝ → ℂ := fun n y => -(LSeries.term ↗vonMangoldt (s y) n * W y) with hF
  -- the integrand is `Σ' n, F n`
  have hpt : ∀ y, logDeriv riemannZeta (s y) * W y = ∑' n, F n y := by
    intro y
    rw [logDeriv_zeta_eq_neg_LSeries (hre1 y), LSeries, neg_mul, ← tsum_mul_right, ← tsum_neg]
  -- each term vanishes
  have hterm : ∀ n, ∫ y, F n y = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hΛ : LSeries.term ↗vonMangoldt = fun s n => LSeries.term ↗vonMangoldt s n := rfl
      have : ∀ y, F n y = 0 := by
        intro y
        interval_cases n
        · simp [hF]
        · simp [hF]
      simp [this]
    · have hn0 : n ≠ 0 := by omega
      have hnR : Real.exp (2 * m * ℓ) < (n : ℝ) := h2.trans_le (by exact_mod_cast hn)
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hF' : ∀ y, F n y = -((vonMangoldt n : ℂ) *
          (WH ℓ m T₀ (s y) * ((n : ℝ) : ℂ) ^ (-s y) + WH ℓ m T₀ (1 - s y) * ((n : ℝ) : ℂ) ^ (-s y))) := by
        intro y
        simp only [hF, hW, WHt]
        rw [LSeries.term_of_ne_zero hn0, Complex.ofReal_natCast, Complex.cpow_neg]
        ring
      simp_rw [hF']
      have i1 : Integrable fun y : ℝ => WH ℓ m T₀ (s y) * ((n : ℝ) : ℂ) ^ (-s y) := by
        refine Integrable.mono' ((integrable_lor T₀).const_mul (4 ^ m * Real.exp (2 * m * ℓ * |3 / 2 - 1 / 2|) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)))) ?_ (ae_of_all _ fun y => ?_)
        · exact ((differentiable_WH ℓ m T₀).continuous.comp (by fun_prop)).mul
            (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn'.ne'))) |>.aestronglyMeasurable
        · rw [norm_mul, norm_ofReal_cpow_neg hn', hre]
          have h := norm_WH_le_exp hℓ0 hℓ1 hm T₀ (s y)
          rw [hre] at h
          have : (s y).im = y := by simp [hsdef]
          rw [this] at h
          calc ‖WH ℓ m T₀ (s y)‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              4 ^ m * Real.exp (2 * m * ℓ * |3 / 2 - 1 / 2|) * lor (y - T₀) * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right h (by positivity)
            _ = _ := by ring
      have i2 : Integrable fun y : ℝ => WH ℓ m T₀ (1 - s y) * ((n : ℝ) : ℂ) ^ (-s y) := by
        refine Integrable.mono' ((integrable_lor (-T₀)).const_mul (4 ^ m * Real.exp (2 * m * ℓ * |3 / 2 - 1 / 2|) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)))) ?_ (ae_of_all _ fun y => ?_)
        · exact ((differentiable_WH ℓ m T₀).continuous.comp (by fun_prop)).mul
            (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn'.ne'))) |>.aestronglyMeasurable
        · rw [norm_mul, norm_ofReal_cpow_neg hn', hre]
          have h := norm_WH_le_exp hℓ0 hℓ1 hm T₀ (1 - s y)
          have e1 : |(1 - s y).re - 1 / 2| = |3 / 2 - 1 / 2| := by
            have h1 : (1 - s y).re = 1 - 3 / 2 := by simp [hsdef]
            rw [h1]; norm_num
          have e2 : (1 - s y).im - T₀ = -(y - -T₀) := by simp [hsdef]; ring
          rw [e1, e2, lor_neg] at h
          calc ‖WH ℓ m T₀ (1 - s y)‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              4 ^ m * Real.exp (2 * m * ℓ * |3 / 2 - 1 / 2|) * lor (y - -T₀) * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right h (by positivity)
            _ = _ := by ring
      rw [integral_neg, integral_const_mul, integral_add i1 i2]
      have z1 := integral_WH_cpow_eq_zero hℓ0 hℓ1 hm T₀ hnR (3 / 2)
      have z2 := integral_WH_one_sub_cpow_eq_zero hℓ0 hℓ1 hm T₀ hnR (3 / 2)
      simp only [hsdef] at z1 z2 ⊢
      rw [z1, z2]; simp
  -- integrability and summability of the terms
  have hnorm : ∀ n y, ‖F n y‖ = ‖LSeries.term ↗vonMangoldt (3 / 2 : ℂ) n‖ * ‖W y‖ := by
    intro n y
    rw [hF, norm_neg, norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq]
    congr 2
    rw [hre]; norm_num
  have hWi : Integrable W := integrable_WHt_line hℓ0 hℓ1 hm T₀ (3 / 2)
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    refine (hWi.norm.const_mul ‖LSeries.term ↗vonMangoldt (3 / 2 : ℂ) n‖).mono' ?_
      (ae_of_all _ fun y => (hnorm n y).le)
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [hF, LSeries.term_zero, zero_mul, neg_zero]; exact aestronglyMeasurable_const
    · have : F n = fun y => -((vonMangoldt n : ℂ) / (n : ℂ) ^ (s y) * W y) := by
        funext y; simp only [hF]; rw [LSeries.term_of_ne_zero hn0]
      rw [this]
      have hW : Continuous W := (differentiable_WHt ℓ m T₀).continuous.comp (by fun_prop)
      have hc : Continuous fun y : ℝ => (n : ℂ) ^ (s y) :=
        Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn0))
      refine (((continuous_const.div hc fun y => ?_).mul hW).neg).aestronglyMeasurable
      exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hn0))
  have hsum : Summable fun n => ∫ y, ‖F n y‖ := by
    simp_rw [hnorm, integral_const_mul]
    exact (summable_norm_term_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num)).mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFi hsum
  calc ∫ y : ℝ, logDeriv riemannZeta (s y) * W y = ∫ y, ∑' n, F n y := integral_congr_ae (ae_of_all _ hpt)
    _ = ∑' n, ∫ y, F n y := hswap.symm
    _ = 0 := by simp [hterm]

/-! ### Stronger decay of `H` (`m ≥ 2`) and tools for the line shifts -/

theorem tendsto_lor_atTop (τ : ℝ) : Tendsto (fun Y : ℝ => lor (Y - τ)) atTop (𝓝 0) := by
  unfold lor
  refine tendsto_const_nhds.div_atTop ?_
  exact tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).comp
    (tendsto_atTop_add_const_right _ _ tendsto_id))

theorem tendsto_lor_atBot (τ : ℝ) : Tendsto (fun Y : ℝ => lor (Y - τ)) atBot (𝓝 0) := by
  have h := (tendsto_lor_atTop (-τ)).comp tendsto_neg_atBot_atTop
  refine h.congr fun Y => ?_
  simp only [Function.comp]
  rw [show -Y - -τ = -(Y - τ) by ring, lor_neg]

theorem lor_le_two (u : ℝ) : lor u ≤ 2 := by
  unfold lor; rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg u]

/-- `(1 + |t|) L(t − τ)² ≤ (3 + 2|τ|) L(t − τ)`. -/
theorem one_add_abs_mul_lor_sq_le (τ t : ℝ) :
    (1 + |t|) * lor (t - τ) ^ 2 ≤ (3 + 2 * |τ|) * lor (t - τ) := by
  set u := t - τ with hu
  have hl0 := (lor_pos u).le
  have hl2 := lor_le_two u
  have h1 : |u| * lor u ^ 2 ≤ lor u := by
    have : |u| * lor u ≤ 1 := by
      unfold lor
      rw [← mul_div_assoc, div_le_one (by positivity)]
      nlinarith [sq_abs u, abs_nonneg u, sq_nonneg (|u| - 1)]
    calc |u| * lor u ^ 2 = (|u| * lor u) * lor u := by ring
      _ ≤ 1 * lor u := mul_le_mul_of_nonneg_right this hl0
      _ = lor u := one_mul _
  have ht : |t| ≤ |u| + |τ| := by
    have := abs_add_le u τ; rwa [show u + τ = t by rw [hu]; ring] at this
  calc (1 + |t|) * lor u ^ 2 ≤ (1 + |τ|) * lor u ^ 2 + |u| * lor u ^ 2 := by nlinarith [sq_nonneg (lor u)]
    _ ≤ (1 + |τ|) * (2 * lor u) + lor u := by
        gcongr
        nlinarith
    _ = (3 + 2 * |τ|) * lor u := by ring

/-- `|H_T(s)| ≤ 4^m e^{2mℓ|σ−½|} L(t − T)²` for `m ≥ 2`. -/
theorem norm_WH_le_lor_sq {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m) (T : ℝ) (s : ℂ) :
    ‖WH ℓ m T s‖ ≤ 4 ^ m * Real.exp (2 * m * ℓ * |s.re - 1 / 2|) * lor (s.im - T) ^ 2 := by
  set E := 2 * Real.exp (ℓ * |s.re - 1 / 2|) with hE
  have hE1 : 1 ≤ E := by
    have : 1 ≤ Real.exp (ℓ * |s.re - 1 / 2|) := Real.one_le_exp (by positivity)
    linarith
  have hEm : E ^ (2 * m) = 4 ^ m * Real.exp (2 * m * ℓ * |s.re - 1 / 2|) := by
    rw [hE, mul_pow, ← Real.exp_nat_mul, pow_mul]; norm_num; ring_nf
  rw [← hEm]
  have hEm0 : 0 ≤ E ^ (2 * m) := by positivity
  rcases le_or_gt |s.im - T| 1 with hu | hu
  · have h := norm_WH_le hℓ0.le m T s
    have h2 : ((2 * ℓ * Real.exp (ℓ * |s.re - 1 / 2|)) ^ m) ^ 2 ≤ E ^ (2 * m) := by
      rw [← pow_mul, mul_comm m 2]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have : 0 ≤ Real.exp (ℓ * |s.re - 1 / 2|) := (Real.exp_pos _).le
      nlinarith
    have hl : 1 ≤ lor (s.im - T) ^ 2 := one_le_pow₀ (one_le_lor hu)
    calc ‖WH ℓ m T s‖ ≤ E ^ (2 * m) := h.trans h2
      _ = E ^ (2 * m) * 1 := (mul_one _).symm
      _ ≤ E ^ (2 * m) * lor (s.im - T) ^ 2 := mul_le_mul_of_nonneg_left hl hEm0
  · have hne : s.im ≠ T := by intro h; rw [h, sub_self, abs_zero] at hu; linarith
    have h := norm_WH_le_div hℓ0 m T hne
    set u := s.im - T with hudef
    have hpos : 0 < |u| := by linarith
    have hu4 : 1 / u ^ 4 ≤ lor u ^ 2 := by
      have h1 := inv_sq_le_lor hu.le
      have : 1 / u ^ 4 = (1 / u ^ 2) ^ 2 := by rw [div_pow, one_pow, ← pow_mul]
      rw [this]
      exact pow_le_pow_left₀ (by positivity) h1 2
    have h2 : ((E / |u|) ^ m) ^ 2 ≤ E ^ (2 * m) * (1 / u ^ 4) := by
      rw [← pow_mul, div_pow, mul_comm m 2, div_eq_mul_one_div (E ^ (2 * m))]
      refine mul_le_mul_of_nonneg_left ?_ hEm0
      have hu4' : u ^ 4 = |u| ^ 4 := by
        rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
      rw [hu4']
      refine one_div_le_one_div_of_le (by positivity) ?_
      calc |u| ^ 4 = |u| ^ 4 * 1 := (mul_one _).symm
        _ ≤ |u| ^ 4 * |u| ^ (2 * m - 4) := mul_le_mul_of_nonneg_left (one_le_pow₀ hu.le) (by positivity)
        _ = |u| ^ (2 * m) := by rw [← pow_add]; congr 1; omega
    calc ‖WH ℓ m T s‖ ≤ ((E / |u|) ^ m) ^ 2 := h
      _ ≤ E ^ (2 * m) * (1 / u ^ 4) := h2
      _ ≤ E ^ (2 * m) * lor u ^ 2 := mul_le_mul_of_nonneg_left hu4 hEm0

/-- **Limits of rectangle integrals**: if `∮ F = C` on `[a, b] × [−Y, Y]` for all large `Y`, `F` is
integrable on `ℜs = a, b` and `‖F(σ + iY)‖ ≤ M(Y) → 0` eventually, then
`i(∫ F(b + it) − ∫ F(a + it)) = C`. -/
theorem rectInt_limit {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) {C : ℂ}
    (hC : ∀ᶠ Y in atTop, rectInt F ((a : ℂ) + ((-Y : ℝ) : ℂ) * I) ((b : ℂ) + (Y : ℂ) * I) = C)
    (hia : Integrable fun t : ℝ => F (a + t * I)) (hib : Integrable fun t : ℝ => F (b + t * I))
    {M : ℝ → ℝ} (hMt : Tendsto M atTop (𝓝 0)) (hMb : Tendsto M atBot (𝓝 0))
    (hMt' : ∀ᶠ Y : ℝ in atTop, ∀ σ ∈ Icc a b, ‖F (σ + Y * I)‖ ≤ M Y)
    (hMb' : ∀ᶠ Y : ℝ in atBot, ∀ σ ∈ Icc a b, ‖F (σ + Y * I)‖ ≤ M Y) :
    I * ((∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I)) = C := by
  have hE : ∀ Y : ℝ, rectInt F ((a : ℂ) + ((-Y : ℝ) : ℂ) * I) ((b : ℂ) + (Y : ℂ) * I) =
      ((∫ x : ℝ in a..b, F (x + (-Y : ℝ) * I)) - ∫ x : ℝ in a..b, F (x + (Y : ℝ) * I)) +
      I * (∫ y : ℝ in (-Y)..Y, F (b + y * I)) - I * (∫ y : ℝ in (-Y)..Y, F (a + y * I)) := by
    intro Y
    unfold rectInt
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add, smul_eq_mul]
  have hhor : ∀ g : ℝ → ℝ, Tendsto (fun Y => M (g Y)) atTop (𝓝 0) →
      (∀ᶠ Y in atTop, ∀ σ ∈ Icc a b, ‖F (σ + (g Y : ℝ) * I)‖ ≤ M (g Y)) →
      Tendsto (fun Y : ℝ => ∫ x : ℝ in a..b, F (x + (g Y : ℝ) * I)) atTop (𝓝 0) := by
    intro g hg hgb
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hg.mul_const (b - a))
    filter_upwards [hgb] with Y hY
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun x : ℝ => F (x + (g Y : ℝ) * I)) (C := M (g Y)) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hY x ⟨hx.1.le, hx.2⟩)
    rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  have h1 := hhor (fun Y => -Y) (hMb.comp tendsto_neg_atTop_atBot)
    (tendsto_neg_atTop_atBot.eventually hMb')
  have h2 := hhor id hMt hMt'
  have h3 := intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h4 := intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((h1.sub h2).add (h3.const_mul I)).sub (h4.const_mul I)
  have hlimC : Tendsto (fun Y : ℝ => ((∫ x : ℝ in a..b, F (x + (-Y : ℝ) * I)) -
      ∫ x : ℝ in a..b, F (x + (Y : ℝ) * I)) + I * (∫ y : ℝ in (-Y)..Y, F (b + y * I)) -
      I * (∫ y : ℝ in (-Y)..Y, F (a + y * I))) atTop (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hC] with Y hY
    rw [← hY, hE]
  have heq := tendsto_nhds_unique hlim hlimC
  simp only [sub_self, zero_add] at heq
  rw [mul_sub]; exact heq

end TernaryGoldbach.Explicit
