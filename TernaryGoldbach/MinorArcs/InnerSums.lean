import TernaryGoldbach.MinorArcs.FourierSums
import TernaryGoldbach.Helfgott.Eta2

/-!
# The inner sums of the Type I estimates [B, §4.2]

* `norm_fourier_comp_affine`: `‖𝓕[h(λ· + μ)](t)‖ = λ⁻¹ ‖𝓕h(t/λ)‖`.
* `eta2_fourier_bound'`: **trusted fact** `|η̂₂''|_∞ ≤ c₀ = 31.521` [B, (B.6)] (a rigorous
  computation in [B]; `sorry` here).
* `Todd`: `T_{m,∘}(α) = ∑_{n odd} e(αmn) η₂(mn/x)` [B, (4.35)], and `norm_Todd_le`: the three
  bounds of [B, (4.36)], from [B, (2.2)] and [B, Lemma 2.3.1] (`MinorArcs/FourierSums.lean`).

Everything here except `eta2_fourier_bound'` is proved.
-/

open Complex MeasureTheory Real FourierTransform

namespace TernaryGoldbach

/-- `∫ g(λv + μ) dv = λ⁻¹ ∫ g` for `λ > 0`. -/
theorem integral_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    {lam : ℝ} (hlam : 0 < lam) (μ : ℝ) : ∫ v, g (lam * v + μ) = lam⁻¹ • ∫ w, g w := by
  rw [Measure.integral_comp_mul_left (fun v => g (v + μ)) lam, integral_add_right_eq_self,
    abs_of_pos (inv_pos.2 hlam)]

/-- Fourier transform of `h(λu + μ)`: `‖𝓕 g(t)‖ = λ⁻¹ ‖𝓕 h(t/λ)‖`. -/
theorem norm_fourier_comp_affine (h : ℝ → ℂ) {lam : ℝ} (hlam : 0 < lam) (μ t : ℝ) :
    ‖𝓕 (fun u => h (lam * u + μ)) t‖ = lam⁻¹ * ‖𝓕 h (t / lam)‖ := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  have : ∀ v, e (-(v * t)) * h (lam * v + μ) =
      e (μ * t / lam) * (fun w => e (-(w * (t / lam))) * h w) (lam * v + μ) := by
    intro v; simp only
    rw [← mul_assoc, ← e_add]; congr 2; field_simp; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_affine (fun w => e (-(w * (t / lam))) * h w) hlam, norm_mul, norm_e, one_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hlam)]


namespace MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The constant `c₀ = 31.521 ≥ |η̂₂''|_∞` [B, (B.6), §6.1]. -/
def c₀ : ℝ := 31.521

/-- `|η₂'|₁ = 8 log 2` [B, (6.1)]; it is the total variation of `η₂` (`eVariationOn_eta2`). -/
noncomputable def eta2'L1 : ℝ := 8 * Real.log 2

theorem eta2'L1_pos : 0 < eta2'L1 := by
  unfold eta2'L1; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- **Trusted fact** [B, (B.6), Lemma B.2.3]: `|η̂₂''|_∞ ≤ 31.521`, written as
`(2πt)² |η̂₂(t)| ≤ c₀` (`η̂''(t) = (2πit)² η̂(t)`).  In [B] this is a rigorous computation
(interval arithmetic); it is not formalized here. -/
theorem eta2_fourier_bound' (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ ≤ c₀ := by
  sorry

/-- `T_{m,∘}(α) = ∑_{n odd} e(αmn) η₂(mn/x)` [B, (4.35)], with `n = 2r + 1`. -/
noncomputable def Todd (α x : ℝ) (m : ℕ) : ℂ :=
  ∑' r : ℤ, e (α * m * (2 * r + 1)) * (eta2 (m * (2 * r + 1) / x) : ℂ)

/-- The function `r ↦ η₂(m(2r+1)/x) = η₂((2m/x) r + m/x)`. -/
noncomputable def fodd (x : ℝ) (m : ℕ) (u : ℝ) : ℂ := (eta2 (2 * m / x * u + m / x) : ℂ)

theorem Todd_eq (α x : ℝ) (m : ℕ) :
    Todd α x m = e (α * m) * ∑' r : ℤ, fodd x m r * e (2 * α * m * r) := by
  rw [Todd, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  simp only [fodd]
  rw [show (2 * m / x * (r : ℝ) + m / x) = m * (2 * r + 1) / x by ring,
    show α * m * (2 * r + 1) = α * m + 2 * α * m * r by ring, e_add]
  ring

section
variable {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m)
include hx hm

theorem lam_pos : 0 < 2 * (m : ℝ) / x := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

omit hx hm in
theorem continuous_fodd : Continuous (fodd x m) :=
  continuous_ofReal.comp (Helfgott.continuous_eta2.comp (by fun_prop))

theorem hasCompactSupport_fodd : HasCompactSupport (fodd x m) := by
  have h1 : HasCompactSupport (fun u => (eta2 u : ℂ)) :=
    Helfgott.hasCompactSupport_eta2.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have h2 := (h1.comp_homeomorph (Homeomorph.addRight (m / x : ℝ))).comp_homeomorph
    (Homeomorph.mulLeft₀ (2 * m / x : ℝ) (lam_pos hx hm).ne')
  convert h2 using 1
  funext u; simp [fodd, Function.comp]

theorem variation_fodd : eVariationOn (fodd x m) Set.univ ≤ ENNReal.ofReal eta2'L1 := by
  have h1 : eVariationOn (fodd x m) Set.univ ≤
      eVariationOn (fun u => (eta2 u : ℂ)) Set.univ := by
    have := eVariationOn.comp_le_of_monotoneOn (fun u => (eta2 u : ℂ)) (s := Set.univ)
      (t := Set.univ) (fun u => 2 * m / x * u + m / x)
      (fun a _ b _ hab => by have := lam_pos hx hm; simp only; nlinarith) (Set.mapsTo_univ _ _)
    exact this
  have h2 : eVariationOn (fun u => (eta2 u : ℂ)) Set.univ ≤ 1 * eVariationOn eta2 Set.univ :=
    LipschitzOnWith.comp_eVariationOn_le (f := fun t : ℝ => (t : ℂ)) (t := Set.univ)
      (Complex.isometry_ofReal.lipschitzWith.lipschitzOnWith) (Set.mapsTo_univ _ _)
  rw [one_mul, Helfgott.eVariationOn_eta2] at h2
  exact h1.trans h2

theorem integral_norm_fodd : ∫ u, ‖fodd x m u‖ = x / (2 * m) := by
  simp only [fodd, Complex.norm_real, Real.norm_eq_abs]
  rw [integral_comp_affine (fun t => |eta2 t|) (lam_pos hx hm), Helfgott.integral_abs_eta2]
  simp

theorem fourier_bound_fodd (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (fodd x m) t‖ ≤ 2 * m / x * c₀ := by
  have hl := lam_pos hx hm
  have h := eta2_fourier_bound' (t / (2 * m / x))
  have e1 : 𝓕 (fodd x m) t = 𝓕 (fun u => (eta2 (2 * m / x * u + m / x) : ℂ)) t := rfl
  rw [e1, norm_fourier_comp_affine (fun u => (eta2 u : ℂ)) hl]
  have : (2 * π * t) ^ 2 * ((2 * m / x)⁻¹ * ‖𝓕 (fun u => (eta2 u : ℂ)) (t / (2 * m / x))‖) =
      2 * m / x * ((2 * π * (t / (2 * m / x))) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) (t / (2 * m / x))‖) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h hl.le

/-- **[B, (4.36)]**: `|T_{m,∘}(α)| ≤ min(x/2m + |η'|₁/2, (|η'|₁/2)/|sin 2πmα|,
(m/x)(c₀/2)/sin² 2πmα)`, for `η = η₂`. -/
theorem norm_Todd_le (α : ℝ) :
    ‖Todd α x m‖ ≤ x / (2 * m) + eta2'L1 / 2 ∧
    (Real.sin (2 * π * m * α) ≠ 0 →
      ‖Todd α x m‖ ≤ eta2'L1 / 2 / |Real.sin (2 * π * m * α)| ∧
      ‖Todd α x m‖ ≤ m / x * (c₀ / 2) / Real.sin (2 * π * m * α) ^ 2) := by
  have hsin : π * (2 * α * m) = 2 * π * m * α := by ring
  rw [Todd_eq, norm_mul, norm_e, one_mul]
  refine ⟨?_, fun hs => ⟨?_, ?_⟩⟩
  · obtain ⟨hsumm, hle⟩ := tsum_norm_le_variation (continuous_fodd)
      (hasCompactSupport_fodd hx hm) eta2'L1_pos.le (variation_fodd hx hm)
    rw [integral_norm_fodd hx hm] at hle
    refine le_trans ?_ hle
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun r => ?_))
    · exact hsumm.congr fun r => by rw [norm_mul, norm_e, mul_one]
    · rw [norm_mul, norm_e, mul_one]
  · have := norm_tsum_le_variation (hasCompactSupport_fodd hx hm) eta2'L1_pos.le
      (variation_fodd hx hm) (α := 2 * α * m) (by rwa [hsin])
    rw [hsin] at this
    refine this.trans (le_of_eq ?_); ring
  · have := norm_tsum_le_of_fourier_bound (continuous_fodd) (hasCompactSupport_fodd hx hm)
      (fourier_bound_fodd hx hm) (α := 2 * α * m) (by rwa [hsin])
    rw [hsin] at this
    refine this.trans (le_of_eq ?_); ring

end

end MinorArcs

end TernaryGoldbach
