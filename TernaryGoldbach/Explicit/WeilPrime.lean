import TernaryGoldbach.Explicit.WeilTest
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The prime side of the Weil explicit formula vanishes

* `integral_vertical_eq`: vertical line integrals of an entire function that decays uniformly on
  horizontal segments do not depend on the line (Cauchy on rectangles).
* `norm_WH_le_lorentz`: `|H_T(s)| ≤ (2e^{ℓ|σ − ½|})^{2m} · 2/(1 + (t − T)²)` (`ℓ ≤ 1`, `m ≥ 1`).
* `integral_cpow_eq_zero_of_bound`: if `|G(s)| ≤ A e^{κ|σ − ½|} · 2/(1 + (t − τ)²)` and `n > e^κ`, then
  `∫ G(c + it) n^{−(c + it)} dt = 0` for every `c` (move the line to `ℜs → ∞`).
* `integral_WH_cpow_eq_zero`, `integral_WH_one_sub_cpow_eq_zero`: the case `G = H_T`, `G = H_T(1 − ·)`,
  `κ = 2mℓ`; for `2mℓ < log 2` this covers every `n ≥ 2`.
-/

open Complex MeasureTheory Filter Set
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-! ### Moving a vertical line -/

/-- **Vertical line integrals are independent of the line** for `F` holomorphic on the closed strip
`a ≤ ℜs ≤ b` with `‖F(σ + iY)‖ ≤ M(Y)` there, `M → 0` at `±∞`. -/
theorem integral_vertical_eq_strip {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ s : ℂ, s.re ∈ Icc a b → DifferentiableAt ℂ F s)
    (hia : Integrable fun t : ℝ => F (a + t * I)) (hib : Integrable fun t : ℝ => F (b + t * I))
    {M : ℝ → ℝ} (hMt : Tendsto M atTop (𝓝 0)) (hMb : Tendsto M atBot (𝓝 0))
    (hM : ∀ σ ∈ Icc a b, ∀ Y : ℝ, ‖F (σ + Y * I)‖ ≤ M Y) :
    ∫ t : ℝ, F (a + t * I) = ∫ t : ℝ, F (b + t * I) := by
  have key : ∀ Y : ℝ, ((∫ x : ℝ in a..b, F (x + (-Y : ℝ) * I)) - ∫ x : ℝ in a..b, F (x + (Y : ℝ) * I)) +
      I * (∫ y : ℝ in (-Y)..Y, F (b + y * I)) - I * (∫ y : ℝ in (-Y)..Y, F (a + y * I)) = 0 := by
    intro Y
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) + ((-Y : ℝ) : ℂ) * I) ((b : ℂ) + (Y : ℂ) * I) (fun u hu => by
        refine (hF u ?_).differentiableWithinAt
        have := (Complex.mem_reProdIm.1 hu).1
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at this
        rwa [Set.uIcc_of_le hab] at this)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add, smul_eq_mul] at h
    exact h
  -- the horizontal sides tend to `0`
  have hhor : ∀ g : ℝ → ℝ, Tendsto (fun Y => M (g Y)) atTop (𝓝 0) →
      Tendsto (fun Y : ℝ => ∫ x : ℝ in a..b, F (x + (g Y : ℝ) * I)) atTop (𝓝 0) := by
    intro g hg
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun Y => ?_) (by simpa using hg.mul_const (b - a))
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun x : ℝ => F (x + (g Y : ℝ) * I)) (C := M (g Y)) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hM x ⟨hx.1.le, hx.2⟩ (g Y))
    rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  have h1 := hhor (fun Y => -Y) (hMb.comp tendsto_neg_atTop_atBot)
  have h2 := hhor id hMt
  have h3 := intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h4 := intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((h1.sub h2).add (h3.const_mul I)).sub (h4.const_mul I)
  have hlim0 : Tendsto (fun Y : ℝ => ((∫ x : ℝ in a..b, F (x + (-Y : ℝ) * I)) -
      ∫ x : ℝ in a..b, F (x + (Y : ℝ) * I)) + I * (∫ y : ℝ in (-Y)..Y, F (b + y * I)) -
      I * (∫ y : ℝ in (-Y)..Y, F (a + y * I))) atTop (𝓝 0) := by
    simp_rw [key]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hlim0
  simp only [sub_self, zero_add] at heq
  have : I * ((∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I)) = 0 := by rw [mul_sub]; exact heq
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.1 h).symm

/-- `integral_vertical_eq_strip` for an entire `F`. -/
theorem integral_vertical_eq {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b : ℝ} (hab : a ≤ b)
    (hia : Integrable fun t : ℝ => F (a + t * I)) (hib : Integrable fun t : ℝ => F (b + t * I))
    {M : ℝ → ℝ} (hMt : Tendsto M atTop (𝓝 0)) (hMb : Tendsto M atBot (𝓝 0))
    (hM : ∀ σ ∈ Icc a b, ∀ Y : ℝ, ‖F (σ + Y * I)‖ ≤ M Y) :
    ∫ t : ℝ, F (a + t * I) = ∫ t : ℝ, F (b + t * I) :=
  integral_vertical_eq_strip hab (fun s _ => hF s) hia hib hMt hMb hM

/-! ### A Lorentzian majorant for `H_T` -/

/-- `L(u) = 2/(1 + u²)`. -/
noncomputable def lor (u : ℝ) : ℝ := 2 / (1 + u ^ 2)

theorem lor_pos (u : ℝ) : 0 < lor u := by unfold lor; positivity

theorem integrable_lor (τ : ℝ) : Integrable fun t : ℝ => lor (t - τ) := by
  have h := (integrable_inv_one_add_sq.const_mul 2).comp_sub_right τ
  refine h.congr (ae_of_all _ fun t => ?_)
  simp [lor, div_eq_mul_inv]

theorem integral_lor (τ : ℝ) : ∫ t : ℝ, lor (t - τ) = 2 * π := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ => lor t) τ
  rw [h]
  simp only [lor, div_eq_mul_inv]
  rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem one_le_lor {u : ℝ} (hu : |u| ≤ 1) : 1 ≤ lor u := by
  unfold lor
  rw [le_div_iff₀ (by positivity)]
  have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
  linarith

theorem inv_sq_le_lor {u : ℝ} (hu : 1 ≤ |u|) : 1 / u ^ 2 ≤ lor u := by
  have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
  unfold lor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- `|H_T(s)| ≤ (2e^{ℓ|σ − ½|})^{2m} · 2/(1 + (t − T)²)` for `0 < ℓ ≤ 1`, `m ≥ 1`. -/
theorem norm_WH_le_lorentz {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T : ℝ) (s : ℂ) :
    ‖WH ℓ m T s‖ ≤ (2 * Real.exp (ℓ * |s.re - 1 / 2|)) ^ (2 * m) * lor (s.im - T) := by
  set E := 2 * Real.exp (ℓ * |s.re - 1 / 2|) with hE
  have hE1 : 1 ≤ E := by
    have : 1 ≤ Real.exp (ℓ * |s.re - 1 / 2|) := Real.one_le_exp (by positivity)
    linarith
  have hEm : 0 ≤ E ^ (2 * m) := by positivity
  rcases le_or_gt |s.im - T| 1 with hu | hu
  · have h := norm_WH_le hℓ0.le m T s
    have h2 : ((2 * ℓ * Real.exp (ℓ * |s.re - 1 / 2|)) ^ m) ^ 2 ≤ E ^ (2 * m) := by
      rw [← pow_mul, mul_comm m 2]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [hE]
      have : 0 ≤ Real.exp (ℓ * |s.re - 1 / 2|) := (Real.exp_pos _).le
      nlinarith
    calc ‖WH ℓ m T s‖ ≤ E ^ (2 * m) := h.trans h2
      _ = E ^ (2 * m) * 1 := (mul_one _).symm
      _ ≤ E ^ (2 * m) * lor (s.im - T) := mul_le_mul_of_nonneg_left (one_le_lor hu) hEm
  · have hne : s.im ≠ T := by intro h; rw [h, sub_self, abs_zero] at hu; linarith
    have h := norm_WH_le_div hℓ0 m T hne
    have hpos : 0 < |s.im - T| := by linarith
    have h2 : ((E / |s.im - T|) ^ m) ^ 2 ≤ E ^ (2 * m) * (1 / (s.im - T) ^ 2) := by
      rw [← pow_mul, div_pow, mul_comm m 2, div_eq_mul_one_div (E ^ (2 * m))]
      refine mul_le_mul_of_nonneg_left ?_ hEm
      rw [← sq_abs (s.im - T)]
      refine one_div_le_one_div_of_le (by positivity) ?_
      calc |s.im - T| ^ 2 = |s.im - T| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |s.im - T| ^ 2 * |s.im - T| ^ (2 * m - 2) :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ hu.le) (by positivity)
        _ = |s.im - T| ^ (2 * m) := by rw [← pow_add]; congr 1; omega
    calc ‖WH ℓ m T s‖ ≤ ((E / |s.im - T|) ^ m) ^ 2 := h
      _ ≤ E ^ (2 * m) * (1 / (s.im - T) ^ 2) := h2
      _ ≤ E ^ (2 * m) * lor (s.im - T) := mul_le_mul_of_nonneg_left (inv_sq_le_lor hu.le) hEm

/-! ### The prime side -/

theorem norm_ofReal_cpow_neg {n : ℝ} (hn : 0 < n) (s : ℂ) : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]; simp

/-- **Prime side**: if `|G(s)| ≤ A e^{κ|σ − ½|} · L(t − τ)` with `G` entire and `n > e^κ`, then
`∫ G(c + it) n^{−(c + it)} dt = 0` for every `c`. -/
theorem integral_cpow_eq_zero_of_bound {G : ℂ → ℂ} (hG : Differentiable ℂ G) {A κ τ : ℝ}
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hbd : ∀ s : ℂ, ‖G s‖ ≤ A * Real.exp (κ * |s.re - 1 / 2|) * lor (s.im - τ))
    {n : ℝ} (hn : Real.exp κ < n) (c : ℝ) :
    ∫ t : ℝ, G (c + t * I) * (n : ℂ) ^ (-((c : ℂ) + t * I)) = 0 := by
  have hn0 : 0 < n := (Real.exp_pos κ).trans hn
  have hn1 : 1 < n := lt_of_le_of_lt (Real.one_le_exp hκ) hn
  set F : ℂ → ℂ := fun s => G s * (n : ℂ) ^ (-s) with hFdef
  have hFd : Differentiable ℂ F := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    exact hG.mul fun s => ((differentiableAt_id.neg).const_cpow (Or.inl hn'))
  -- the pointwise bound on the line `ℜs = σ`
  have hpt : ∀ σ t : ℝ, ‖F (σ + t * I)‖ ≤ A * Real.exp (κ * |σ - 1 / 2|) * n ^ (-σ) * lor (t - τ) := by
    intro σ t
    have h1 := hbd (σ + t * I)
    have h2 := norm_ofReal_cpow_neg hn0 (σ + t * I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add] at h1 h2
    rw [hFdef, norm_mul, h2]
    calc ‖G (σ + t * I)‖ * n ^ (-σ) ≤ A * Real.exp (κ * |σ - 1 / 2|) * lor (t - τ) * n ^ (-σ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hint : ∀ σ : ℝ, Integrable fun t : ℝ => F (σ + t * I) := by
    intro σ
    refine ((integrable_lor τ).const_mul (A * Real.exp (κ * |σ - 1 / 2|) * n ^ (-σ))).mono'
      ((hFd.continuous.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    exact hpt σ t
  -- the line integral does not depend on `σ ≥ c`
  have hind : ∀ σ : ℝ, c ≤ σ → ∫ t : ℝ, F (c + t * I) = ∫ t : ℝ, F (σ + t * I) := by
    intro σ hσ
    set C : ℝ := A * (Real.exp (κ * (|c - 1 / 2| + |σ - 1 / 2|))) * (n ^ (-c) + n ^ (-σ)) with hC
    refine integral_vertical_eq hFd hσ (hint c) (hint σ) (M := fun Y => C * lor (Y - τ)) ?_ ?_ ?_
    · have : Tendsto (fun Y : ℝ => lor (Y - τ)) atTop (𝓝 0) := by
        unfold lor
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).comp
          (tendsto_atTop_add_const_right _ _ tendsto_id))
      simpa using this.const_mul C
    · have : Tendsto (fun Y : ℝ => lor (Y - τ)) atBot (𝓝 0) := by
        unfold lor
        refine tendsto_const_nhds.div_atTop ?_
        refine tendsto_atTop_add_const_left _ _ ?_
        have := (tendsto_pow_atTop (two_ne_zero)).comp
          (tendsto_neg_atBot_atTop.comp (tendsto_atBot_add_const_right _ (-τ) tendsto_id))
        refine this.congr fun Y => ?_
        simp only [Function.comp, id]; ring
      simpa using this.const_mul C
    · intro x hx Y
      refine (hpt x Y).trans (mul_le_mul_of_nonneg_right ?_ (lor_pos _).le)
      have he : Real.exp (κ * |x - 1 / 2|) ≤ Real.exp (κ * (|c - 1 / 2| + |σ - 1 / 2|)) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hκ)
        rcases le_total x (1 / 2) with h | h
        · rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)]
          have := neg_le_abs (c - 1 / 2); linarith [abs_nonneg (σ - 1 / 2), hx.1]
        · rw [abs_of_nonneg (by linarith : 0 ≤ x - 1 / 2)]
          have := le_abs_self (σ - 1 / 2); linarith [abs_nonneg (c - 1 / 2), hx.2]
      have hnx : n ^ (-x) ≤ n ^ (-c) + n ^ (-σ) := by
        have : n ^ (-x) ≤ n ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith [hx.1])
        linarith [Real.rpow_nonneg hn0.le (-σ)]
      calc A * Real.exp (κ * |x - 1 / 2|) * n ^ (-x) ≤
          A * Real.exp (κ * (|c - 1 / 2| + |σ - 1 / 2|)) * (n ^ (-c) + n ^ (-σ)) := by
            gcongr
        _ = C := rfl
  -- and it tends to `0`
  have hbound : ∀ σ : ℝ, 1 / 2 ≤ σ → ‖∫ t : ℝ, F (σ + t * I)‖ ≤
      A * Real.exp (-(κ / 2)) * (Real.exp κ / n) ^ σ * (2 * π) := by
    intro σ hσ
    refine (norm_integral_le_of_norm_le ((integrable_lor τ).const_mul
      (A * Real.exp (κ * |σ - 1 / 2|) * n ^ (-σ))) (ae_of_all _ fun t => hpt σ t)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_lor, abs_of_nonneg (by linarith : 0 ≤ σ - 1 / 2),
      Real.div_rpow (Real.exp_pos κ).le hn0.le, ← Real.exp_mul, Real.rpow_neg hn0.le]
    rw [show κ * (σ - 1 / 2) = κ * σ + -(κ / 2) by ring, Real.exp_add]
    field_simp
  have hr : Real.exp κ / n < 1 := (div_lt_one hn0).2 hn
  have hr0 : 0 ≤ Real.exp κ / n := by positivity
  have htend : Tendsto (fun σ : ℝ => A * Real.exp (-(κ / 2)) * (Real.exp κ / n) ^ σ * (2 * π))
      atTop (𝓝 0) := by
    have := (tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hr).const_mul (A * Real.exp (-(κ / 2)))
    simpa using this.mul_const (2 * π)
  -- conclude
  have hle : ‖∫ t : ℝ, F (c + t * I)‖ ≤ 0 := by
    refine ge_of_tendsto htend (eventually_atTop.2 ⟨max c (1 / 2), fun σ hσ => ?_⟩)
    rw [hind σ (le_trans (le_max_left _ _) hσ)]
    exact hbound σ (le_trans (le_max_right _ _) hσ)
  exact norm_le_zero_iff.1 hle

theorem lor_neg (u : ℝ) : lor (-u) = lor u := by simp [lor]

/-- The bound of `integral_cpow_eq_zero_of_bound` for `H_T`: `A = 4^m`, `κ = 2mℓ`, `τ = T`. -/
theorem norm_WH_le_exp {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T : ℝ) (s : ℂ) :
    ‖WH ℓ m T s‖ ≤ 4 ^ m * Real.exp ((2 * m * ℓ) * |s.re - 1 / 2|) * lor (s.im - T) := by
  refine (norm_WH_le_lorentz hℓ0 hℓ1 hm T s).trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul, pow_mul]
  norm_num
  left; ring_nf

/-- **The prime side vanishes for `H_T`**: `∫ H_T(c + it) n^{−(c+it)} dt = 0` if `n > e^{2mℓ}`. -/
theorem integral_WH_cpow_eq_zero {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T : ℝ)
    {n : ℝ} (hn : Real.exp (2 * m * ℓ) < n) (c : ℝ) :
    ∫ t : ℝ, WH ℓ m T (c + t * I) * (n : ℂ) ^ (-((c : ℂ) + t * I)) = 0 :=
  integral_cpow_eq_zero_of_bound (differentiable_WH ℓ m T) (by positivity) (by positivity)
    (norm_WH_le_exp hℓ0 hℓ1 hm T) hn c

/-- **The prime side vanishes for `H_T(1 − ·)`**. -/
theorem integral_WH_one_sub_cpow_eq_zero {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m)
    (T : ℝ) {n : ℝ} (hn : Real.exp (2 * m * ℓ) < n) (c : ℝ) :
    ∫ t : ℝ, WH ℓ m T (1 - (c + t * I)) * (n : ℂ) ^ (-((c : ℂ) + t * I)) = 0 := by
  refine integral_cpow_eq_zero_of_bound (G := fun s => WH ℓ m T (1 - s))
    ((differentiable_WH ℓ m T).comp ((differentiable_const _).sub differentiable_id))
    (A := 4 ^ m) (τ := -T) (by positivity) (by positivity) (fun s => ?_) hn c
  have h := norm_WH_le_exp hℓ0 hℓ1 hm T (1 - s)
  have h1 : |(1 - s).re - 1 / 2| = |s.re - 1 / 2| := by
    rw [show (1 - s).re - 1 / 2 = -(s.re - 1 / 2) by simp; ring, abs_neg]
  have h2 : lor ((1 - s).im - T) = lor (s.im - -T) := by
    rw [show (1 - s).im - T = -(s.im - -T) by simp; ring, lor_neg]
  rwa [h1, h2] at h

end TernaryGoldbach.Explicit
