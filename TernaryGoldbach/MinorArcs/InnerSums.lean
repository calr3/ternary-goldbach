import TernaryGoldbach.MinorArcs.FourierSums
import TernaryGoldbach.Helfgott.Eta2
import TernaryGoldbach.MinorArcs.Eta2Fourier

/-!
# The inner sums of the Type I estimates [H, §4.2]

* `norm_fourier_comp_affine`: `‖𝓕[h(λ· + μ)](t)‖ = λ⁻¹ ‖𝓕h(t/λ)‖`.
* `eta2_fourier_bound'`: `|η̂₂''|_∞ ≤ c₀ = 31.521` [H, (B.6)]. The analytic part (`|t| ≥ 655`) is
  proved in `Eta2Fourier.lean`; `0 ≤ t ≤ 655` is the numerical axiom `eta2DD_small`.
* `Todd`: `T_{m,∘}(α) = ∑_{n odd} e(αmn) η₂(mn/x)` [H, (4.35)], and `norm_Todd_le`: the three
  bounds of [H, (4.36)], from [H, (2.2)] and [H, Lemma 2.3.1] (`MinorArcs/FourierSums.lean`).
* `Todd_main`: the main term [H, (4.33)–(4.34)]: for `q ∣ m` (`m/q` odd) and `|δ|m/x ≤ 1/2`,
  `T_{m,∘}(α) = κ'((x/2m) η̂₂(-δ/2) + O*((m/x)(c₀/2π²)(π² - 4)))`, `κ' = e((a + k₀q)/2) = ±1`,
  by Poisson summation.

Everything here except `eta2DD_small` is proved.
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


/-- `𝓕[h(λ· + μ)](t) = λ⁻¹ e(μt/λ) 𝓕h(t/λ)` for `λ > 0`. -/
theorem fourier_comp_affine (h : ℝ → ℂ) {lam : ℝ} (hlam : 0 < lam) (μ t : ℝ) :
    𝓕 (fun u => h (lam * u + μ)) t = (lam⁻¹ : ℂ) * (e (μ * t / lam) * 𝓕 h (t / lam)) := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  have : ∀ v, e (-(v * t)) * h (lam * v + μ) =
      e (μ * t / lam) * (fun w => e (-(w * (t / lam))) * h w) (lam * v + μ) := by
    intro v; simp only
    rw [← mul_assoc, ← e_add]; congr 2; field_simp; ring
  simp_rw [this]
  rw [integral_const_mul, integral_comp_affine (fun w => e (-(w * (t / lam))) * h w) hlam,
    Complex.real_smul]
  push_cast; ring

namespace MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The constant `c₀ = 31.521 ≥ |η̂₂''|_∞` [H, (B.6), §6.1]. -/
def c₀ : ℝ := 31.521

/-- `|η₂'|₁ = 8 log 2` [H, (6.1)]; it is the total variation of `η₂` (`eVariationOn_eta2`). -/
noncomputable def eta2'L1 : ℝ := 8 * Real.log 2

theorem eta2'L1_pos : 0 < eta2'L1 := by
  unfold eta2'L1; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- **Numerical axiom** (our computation, `scripts/rigorous/eta2_fourier_rig.py`, ball arithmetic;
maximum `31.52065` at `t ≈ 17.415`): [H, (B.6)] on `0 ≤ t ≤ 655`, in the explicit form
`eta2DD t = 16 e(−t/2) − 16 e(−t/4) − 4 e(−t) + 4 ∫_{1/4}^{1/2} e(−ut)/u² du − 4 ∫_{1/2}^1 e(−ut)/u² du`,
which equals `(2πt)² η̂₂(t)` (`eta2DD_eq`). -/
axiom eta2DD_small {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 655) : ‖eta2DD t‖ ≤ 31.521

theorem norm_fourier_eta2_neg (t : ℝ) :
    ‖𝓕 (fun u => (eta2 u : ℂ)) (-t)‖ = ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  have : (fun v => e (-(v * -t)) * (eta2 v : ℂ)) =
      fun v => (starRingEnd ℂ) (e (-(v * t)) * (eta2 v : ℂ)) := by
    funext v; rw [map_mul, conj_e, Complex.conj_ofReal, mul_neg, neg_neg]
  rw [this, integral_conj, Complex.norm_conj]

/-- **[H, Lemma B.1.2, (B.6)]**: `|η̂₂''|_∞ ≤ 31.521`, written as `(2πt)² |η̂₂(t)| ≤ c₀`
(`η̂''(t) = (2πit)² η̂(t)`). For `|t| ≥ 655` this is `norm_eta2DD_large`; for `|t| ≤ 655` it is the
computation `eta2DD_small`. -/
theorem eta2_fourier_bound' (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ ≤ c₀ := by
  wlog ht : 0 ≤ t generalizing t
  · have h := this (-t) (by linarith)
    rwa [norm_fourier_eta2_neg, show (2 * π * -t) ^ 2 = (2 * π * t) ^ 2 by ring] at h
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0; unfold c₀; norm_num
  have hn : (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ = ‖eta2DD t‖ := by
    rw [← eta2DD_eq hpos.ne', norm_mul]
    congr 1
    rw [show ((2 * π * t) ^ 2 : ℂ) = (((2 * π * t) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn]; unfold c₀
  rcases le_or_gt t 655 with h | h
  · exact eta2DD_small ht h
  · exact norm_eta2DD_large (by rw [abs_of_pos hpos]; linarith)

/-- `T_{m,∘}(α) = ∑_{n odd} e(αmn) η₂(mn/x)` [H, (4.35)], with `n = 2r + 1`. -/
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

/-- **[H, (4.36)]**: `|T_{m,∘}(α)| ≤ min(x/2m + |η'|₁/2, (|η'|₁/2)/|sin 2πmα|,
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

/-- `η̂₂` as a function `ℝ → ℂ`. -/
noncomputable def eta2hat (t : ℝ) : ℂ := 𝓕 (fun u => (eta2 u : ℂ)) t

theorem norm_eta2hat_le_one (t : ℝ) : ‖eta2hat t‖ ≤ 1 := by
  rw [eta2hat, fourier_eq_integral_e]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact Helfgott.integral_abs_eta2

theorem norm_eta2hat_le (t : ℝ) (ht : t ≠ 0) : ‖eta2hat t‖ ≤ c₀ / (2 * π * t) ^ 2 := by
  have h := eta2_fourier_bound' t
  rw [le_div_iff₀ (by positivity)]; rw [mul_comm]; exact h


/-- The phase in [H, proof of Lemma 4.2.2]: if `2α = a/q + δ/x + k₀` and `m = qm'` with `m'` odd,
then `e(αm(2r+1)) = κ' e((δm/2x)(2r+1))` with `κ' = e((a + k₀q)/2)` independent of `m'`, `r`. -/
theorem e_phase {α x δ : ℝ} {a k₀ : ℤ} {q m' : ℕ} (hx : 0 < x) (hq : 1 ≤ q) (hm' : Odd m')
    (h2α : 2 * α = a / q + δ / x + k₀) (r : ℤ) :
    e (α * ((q * m' : ℕ) : ℝ) * (2 * r + 1)) =
      e ((a + k₀ * q) / 2) * e (δ * ((q * m' : ℕ) : ℝ) / (2 * x) * (2 * r + 1)) := by
  obtain ⟨j, rfl⟩ := hm'
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hα : α = (a / q + δ / x + k₀) / 2 := by linarith
  have : α * ((q * (2 * j + 1) : ℕ) : ℝ) * (2 * r + 1) =
      (a + k₀ * q) / 2 + δ * ((q * (2 * j + 1) : ℕ) : ℝ) / (2 * x) * (2 * r + 1) +
        (((a + k₀ * q) * (2 * j * r + j + r) : ℤ) : ℝ) := by
    rw [hα]; push_cast; field_simp; ring
  rw [this, e_add, e_add, e_intCast, mul_one]

/-- **The main term of [H, (4.33)–(4.34)]**: for `m = qm'` with `m'` odd and `|δ|m/x ≤ 1/2`,
`T_{m,∘}(α) = κ'((x/2m) η̂₂(-δ/2) + E)` with `|E| ≤ (m/x)(c₀/2π²)(π² - 4)`. -/
theorem Todd_main {α x δ : ℝ} {a k₀ : ℤ} {q m' : ℕ} (hx : 0 < x) (hq : 1 ≤ q) (hm' : Odd m')
    (h2α : 2 * α = a / q + δ / x + k₀) (hr : |δ * (q * m' : ℕ) / x| ≤ 1 / 2) :
    ∃ E : ℂ, Todd α x (q * m') = e ((a + k₀ * q) / 2) *
        ((x / (2 * (q * m' : ℕ)) : ℝ) * eta2hat (-(δ / 2)) + E) ∧
      ‖E‖ ≤ (q * m' : ℕ) / x * (c₀ / (2 * π ^ 2)) * (π ^ 2 - 4) := by
  set m : ℕ := q * m' with hmdef
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by
    obtain ⟨j, rfl⟩ := hm'; omega))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  set β : ℝ := δ * m / (2 * x)
  set ρ : ℝ := δ * m / x
  set h : ℝ → ℂ := fun u => e (β * (2 * u + 1)) * (eta2 (m * (2 * u + 1) / x) : ℂ)
  -- Step A: the phase.
  have hA : Todd α x m = e ((a + k₀ * q) / 2) * ∑' r : ℤ, h r := by
    rw [Todd, ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    simp only [h, hmdef]; rw [e_phase hx hq hm' h2α r]; ring
  -- Step C: the Fourier transform of `h`.
  set G : ℝ → ℂ := fun v => (eta2 (m / x * v + 0) : ℂ) * e (β * v)
  have hhG : h = fun u => G (2 * u + 1) := by
    funext u; simp only [h, G]; rw [show (m : ℝ) / x * (2 * u + 1) + 0 = m * (2 * u + 1) / x by ring]
    ring
  have hlam : (0 : ℝ) < m / x := by positivity
  have hF : ∀ k : ℤ, 𝓕 h k =
      (x / (2 * m) : ℝ) * (e (k / 2) * eta2hat (k * x / (2 * m) - δ / 2)) := by
    intro k
    rw [hhG, fourier_comp_affine G two_pos 1 k]
    simp only [G]
    rw [fourier_mul_e (fun v => (eta2 (m / x * v + 0) : ℂ)) β,
      fourier_comp_affine (fun u => (eta2 u : ℂ)) hlam 0, zero_mul, zero_div, e_zero, one_mul]
    have : ((k : ℝ) / 2 - β) / (m / x) = k * x / (2 * m) - δ / 2 := by
      simp only [β]; field_simp
    rw [this, eta2hat]
    push_cast
    field_simp
  -- Step D: bounds on the non-zero frequencies.
  set C : ℝ := m / x * (c₀ / (2 * π ^ 2))
  have hρ : |ρ| ≤ 1 / 2 := by simpa [ρ, hmdef] using hr
  have hkρ : ∀ k : ℤ, k ≠ 0 → (k : ℝ) - ρ ≠ 0 := by
    intro k hk h0
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have : (k : ℝ) = ρ := by linarith
    rw [this] at hk1; linarith
  have hbound : ∀ k : ℤ, k ≠ 0 → ‖𝓕 h k‖ ≤ C * (1 / ((k : ℝ) - ρ) ^ 2) := by
    intro k hk
    rw [hF k, norm_mul, norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have ht : (k : ℝ) * x / (2 * m) - δ / 2 = x / (2 * m) * ((k : ℝ) - ρ) := by
      simp only [ρ]; field_simp
    have hne : (k : ℝ) * x / (2 * m) - δ / 2 ≠ 0 := by
      rw [ht]; exact mul_ne_zero (by positivity) (hkρ k hk)
    refine (mul_le_mul_of_nonneg_left (norm_eta2hat_le _ hne) (by positivity)).trans
      (le_of_eq ?_)
    rw [ht]; simp only [C]
    have := hkρ k hk
    field_simp
  obtain ⟨hs, hsle⟩ := tsum_inv_sq_sub_le hρ
  have hsummF : Summable fun k : ℤ => 𝓕 h k := by
    refine Summable.of_norm_bounded (g := fun k : ℤ => (if k = 0 then ‖𝓕 h 0‖ else 0) +
      C * (if k = 0 then 0 else 1 / ((k : ℝ) - ρ) ^ 2)) ?_ ?_
    · exact (summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])).add
        (hs.mul_left C)
    · intro k
      by_cases hk : k = 0
      · subst hk; simp
      · simp only [hk, ite_false, zero_add]; exact hbound k hk
  -- Step B: Poisson summation.
  have hcont : Continuous h := by
    simp only [h]
    exact (continuous_e.comp (by fun_prop)).mul
      (continuous_ofReal.comp (Helfgott.continuous_eta2.comp (by fun_prop)))
  have hcs : HasCompactSupport h := by
    have h1 : HasCompactSupport (fun u => (eta2 u : ℂ)) :=
      Helfgott.hasCompactSupport_eta2.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have h2 := (h1.comp_homeomorph (Homeomorph.addRight (m / x : ℝ))).comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * m / x : ℝ) (by positivity))
    have h3 : HasCompactSupport fun u : ℝ => (eta2 (m * (2 * u + 1) / x) : ℂ) := by
      convert h2 using 1; funext u; simp only [Function.comp]
      congr 2; simp; ring
    simp only [h]; exact h3.mul_left
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont one_lt_two
    (isBigO_of_hasCompactSupport hcs 2) hsummF 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  -- Step F: separate the zero frequency.
  refine ⟨∑' k : ℤ, if k = 0 then 0 else 𝓕 h k, ?_, ?_⟩
  · rw [hA, hP, hsummF.tsum_eq_add_tsum_ite 0, hF 0]
    congr 2
    simp only [Int.cast_zero, zero_div, e_zero, one_mul, zero_mul, zero_sub]
  · have hsn : Summable fun k : ℤ => ‖if k = 0 then (0 : ℂ) else 𝓕 h k‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left C)
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, ite_false]; exact hbound k hk
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    refine (hsn.tsum_le_tsum (fun k => ?_) (hs.mul_left C)).trans ?_
    · by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, ite_false]; exact hbound k hk
    · rw [tsum_mul_left]
      have hC : 0 ≤ C := by simp only [C]; unfold c₀; positivity
      exact mul_le_mul_of_nonneg_left hsle hC

end MinorArcs

end TernaryGoldbach
