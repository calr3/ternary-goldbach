import TernaryGoldbach.MinorArcs.InnerSums

/-!
# Inner sums for a general smoothing function

The results of `MinorArcs/InnerSums.lean` (the bounds [H, (4.36)] on `T_{m,∘}` and the Poisson
main term [H, (4.33)–(4.34)]) for any continuous, compactly supported `g : ℝ → ℝ` with
`|g|₁ ≤ N`, total variation `≤ V` and `(2πt)² |ĝ(t)| ≤ K` (`SmoothData g N V K`).
Lemma 4.2.3 applies them to `g = η_(x/m)`, `η_(ρ)(t) = log(ρt) η₂(t)` [H, (4.38)].

Proved, with no `sorry`.
-/

open Complex MeasureTheory Real FourierTransform

namespace TernaryGoldbach.MinorArcs

/-- The hypotheses on a smoothing function in [H, Ch. 4]. -/
structure SmoothData (g : ℝ → ℝ) (N V K : ℝ) : Prop where
  cont : Continuous g
  supp : HasCompactSupport g
  l1 : ∫ t, |g t| ≤ N
  V0 : 0 ≤ V
  var : eVariationOn g Set.univ ≤ ENNReal.ofReal V
  four : ∀ t, (2 * π * t) ^ 2 * ‖𝓕 (fun u => (g u : ℂ)) t‖ ≤ K

/-- `T_{m,∘}(α)` for the smoothing `g`: `∑_{n odd} e(αmn) g(mn/x)`. -/
noncomputable def ToddG (g : ℝ → ℝ) (α x : ℝ) (m : ℕ) : ℂ :=
  ∑' r : ℤ, e (α * m * (2 * r + 1)) * (g (m * (2 * r + 1) / x) : ℂ)

noncomputable def foddG (g : ℝ → ℝ) (x : ℝ) (m : ℕ) (u : ℝ) : ℂ := (g (2 * m / x * u + m / x) : ℂ)

/-- `ĝ` as a function `ℝ → ℂ`. -/
noncomputable def ghat (g : ℝ → ℝ) (t : ℝ) : ℂ := 𝓕 (fun u => (g u : ℂ)) t

namespace SmoothData

variable {g : ℝ → ℝ} {N V K : ℝ} (hg : SmoothData g N V K)
include hg

theorem K_nonneg : 0 ≤ K := le_trans (by positivity) (hg.four 1)

theorem norm_ghat_le (t : ℝ) (ht : t ≠ 0) : ‖ghat g t‖ ≤ K / (2 * π * t) ^ 2 := by
  have h := hg.four t
  rw [le_div_iff₀ (by positivity)]; rw [mul_comm]; exact h

theorem norm_ghat_le_l1 (t : ℝ) : ‖ghat g t‖ ≤ N := by
  rw [ghat, fourier_eq_integral_e]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_ |>.trans hg.l1)
  simp_rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]

omit hg in
theorem ToddG_eq (α x : ℝ) (m : ℕ) :
    ToddG g α x m = e (α * m) * ∑' r : ℤ, foddG g x m r * e (2 * α * m * r) := by
  rw [ToddG, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  simp only [foddG]
  rw [show (2 * m / x * (r : ℝ) + m / x) = m * (2 * r + 1) / x by ring,
    show α * m * (2 * r + 1) = α * m + 2 * α * m * r by ring, e_add]
  ring

variable {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m)
include hx hm

omit hx hm in
theorem continuous_foddG : Continuous (foddG g x m) :=
  continuous_ofReal.comp (hg.cont.comp (by fun_prop))

theorem hasCompactSupport_foddG : HasCompactSupport (foddG g x m) := by
  have h1 : HasCompactSupport (fun u => (g u : ℂ)) :=
    hg.supp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have h2 := (h1.comp_homeomorph (Homeomorph.addRight (m / x : ℝ))).comp_homeomorph
    (Homeomorph.mulLeft₀ (2 * m / x : ℝ) (lam_pos hx hm).ne')
  convert h2 using 1
  funext u; simp [foddG, Function.comp]

theorem variation_foddG : eVariationOn (foddG g x m) Set.univ ≤ ENNReal.ofReal V := by
  have h1 : eVariationOn (foddG g x m) Set.univ ≤
      eVariationOn (fun u => (g u : ℂ)) Set.univ :=
    eVariationOn.comp_le_of_monotoneOn (fun u => (g u : ℂ)) (s := Set.univ)
      (t := Set.univ) (fun u => 2 * m / x * u + m / x)
      (fun a _ b _ hab => by have := lam_pos hx hm; simp only; nlinarith) (Set.mapsTo_univ _ _)
  have h2 : eVariationOn (fun u => (g u : ℂ)) Set.univ ≤ 1 * eVariationOn g Set.univ :=
    LipschitzOnWith.comp_eVariationOn_le (f := fun t : ℝ => (t : ℂ)) (t := Set.univ)
      (Complex.isometry_ofReal.lipschitzWith.lipschitzOnWith) (Set.mapsTo_univ _ _)
  rw [one_mul] at h2
  exact h1.trans (h2.trans hg.var)

theorem integral_norm_foddG : ∫ u, ‖foddG g x m u‖ ≤ x / (2 * m) * N := by
  simp only [foddG, Complex.norm_real, Real.norm_eq_abs]
  rw [integral_comp_affine (fun t => |g t|) (lam_pos hx hm), smul_eq_mul]
  have : (2 * (m : ℝ) / x)⁻¹ = x / (2 * m) := by rw [inv_div]
  rw [this]
  exact mul_le_mul_of_nonneg_left hg.l1 (by have := lam_pos hx hm; positivity)

theorem fourier_bound_foddG (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (foddG g x m) t‖ ≤ 2 * m / x * K := by
  have hl := lam_pos hx hm
  have h := hg.four (t / (2 * m / x))
  have e1 : 𝓕 (foddG g x m) t = 𝓕 (fun u => (g (2 * m / x * u + m / x) : ℂ)) t := rfl
  rw [e1, norm_fourier_comp_affine (fun u => (g u : ℂ)) hl]
  have : (2 * π * t) ^ 2 * ((2 * m / x)⁻¹ * ‖𝓕 (fun u => (g u : ℂ)) (t / (2 * m / x))‖) =
      2 * m / x * ((2 * π * (t / (2 * m / x))) ^ 2 * ‖𝓕 (fun u => (g u : ℂ)) (t / (2 * m / x))‖) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h hl.le

/-- **[H, (4.36)]** for the smoothing `g`. -/
theorem norm_ToddG_le (α : ℝ) :
    ‖ToddG g α x m‖ ≤ x / (2 * m) * N + V / 2 ∧
    (Real.sin (2 * π * m * α) ≠ 0 →
      ‖ToddG g α x m‖ ≤ V / 2 / |Real.sin (2 * π * m * α)| ∧
      ‖ToddG g α x m‖ ≤ m / x * (K / 2) / Real.sin (2 * π * m * α) ^ 2) := by
  have hsin : π * (2 * α * m) = 2 * π * m * α := by ring
  rw [ToddG_eq, norm_mul, norm_e, one_mul]
  refine ⟨?_, fun hs => ⟨?_, ?_⟩⟩
  · obtain ⟨hsumm, hle⟩ := tsum_norm_le_variation hg.continuous_foddG
      (hg.hasCompactSupport_foddG hx hm) hg.V0 (hg.variation_foddG hx hm)
    have h2 := hg.integral_norm_foddG hx hm
    refine le_trans ?_ (hle.trans (by linarith))
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun r => ?_))
    · exact hsumm.congr fun r => by rw [norm_mul, norm_e, mul_one]
    · rw [norm_mul, norm_e, mul_one]
  · have := norm_tsum_le_variation (hg.hasCompactSupport_foddG hx hm) hg.V0
      (hg.variation_foddG hx hm) (α := 2 * α * m) (by rwa [hsin])
    rw [hsin] at this
    refine this.trans (le_of_eq ?_); ring
  · have := norm_tsum_le_of_fourier_bound hg.continuous_foddG
      (hg.hasCompactSupport_foddG hx hm) (hg.fourier_bound_foddG hx hm) (α := 2 * α * m)
      (by rwa [hsin])
    rw [hsin] at this
    refine this.trans (le_of_eq ?_); ring

end SmoothData

/-- **The main term of [H, (4.33)–(4.34)]**: for `m = qm'` with `m'` odd and `|δ|m/x ≤ 1/2`,
`T_{m,∘}(α) = κ'((x/2m) ĝ(-δ/2) + E)` with `|E| ≤ (m/x)(K/2π²)(π² - 4)`. -/
theorem ToddG_main {g : ℝ → ℝ} {N V K : ℝ} (hg : SmoothData g N V K) {α x δ : ℝ} {a k₀ : ℤ} {q m' : ℕ} (hx : 0 < x) (hq : 1 ≤ q) (hm' : Odd m')
    (h2α : 2 * α = a / q + δ / x + k₀) (hr : |δ * (q * m' : ℕ) / x| ≤ 1 / 2) :
    ∃ E : ℂ, ToddG g α x (q * m') = e ((a + k₀ * q) / 2) *
        ((x / (2 * (q * m' : ℕ)) : ℝ) * ghat g (-(δ / 2)) + E) ∧
      ‖E‖ ≤ (q * m' : ℕ) / x * (K / (2 * π ^ 2)) * (π ^ 2 - 4) := by
  set m : ℕ := q * m' with hmdef
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by
    obtain ⟨j, rfl⟩ := hm'; omega))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  set β : ℝ := δ * m / (2 * x)
  set ρ : ℝ := δ * m / x
  set h : ℝ → ℂ := fun u => e (β * (2 * u + 1)) * (g (m * (2 * u + 1) / x) : ℂ)
  -- Step A: the phase.
  have hA : ToddG g α x m = e ((a + k₀ * q) / 2) * ∑' r : ℤ, h r := by
    rw [ToddG, ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    simp only [h, hmdef]; rw [e_phase hx hq hm' h2α r]; ring
  -- Step C: the Fourier transform of `h`.
  set G : ℝ → ℂ := fun v => (g (m / x * v + 0) : ℂ) * e (β * v)
  have hhG : h = fun u => G (2 * u + 1) := by
    funext u; simp only [h, G]; rw [show (m : ℝ) / x * (2 * u + 1) + 0 = m * (2 * u + 1) / x by ring]
    ring
  have hlam : (0 : ℝ) < m / x := by positivity
  have hF : ∀ k : ℤ, 𝓕 h k =
      (x / (2 * m) : ℝ) * (e (k / 2) * ghat g (k * x / (2 * m) - δ / 2)) := by
    intro k
    rw [hhG, fourier_comp_affine G two_pos 1 k]
    simp only [G]
    rw [fourier_mul_e (fun v => (g (m / x * v + 0) : ℂ)) β,
      fourier_comp_affine (fun u => (g u : ℂ)) hlam 0, zero_mul, zero_div, e_zero, one_mul]
    have : ((k : ℝ) / 2 - β) / (m / x) = k * x / (2 * m) - δ / 2 := by
      simp only [β]; field_simp
    rw [this, ghat]
    push_cast
    field_simp
  -- Step D: bounds on the non-zero frequencies.
  set C : ℝ := m / x * (K / (2 * π ^ 2))
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
    refine (mul_le_mul_of_nonneg_left (hg.norm_ghat_le _ hne) (by positivity)).trans
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
      (continuous_ofReal.comp (hg.cont.comp (by fun_prop)))
  have hcs : HasCompactSupport h := by
    have h1 : HasCompactSupport (fun u => (g u : ℂ)) :=
      hg.supp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have h2 := (h1.comp_homeomorph (Homeomorph.addRight (m / x : ℝ))).comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * m / x : ℝ) (by positivity))
    have h3 : HasCompactSupport fun u : ℝ => (g (m * (2 * u + 1) / x) : ℂ) := by
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
      have hC : 0 ≤ C := by simp only [C]; have := hg.K_nonneg; positivity
      exact mul_le_mul_of_nonneg_left hsle hC

end TernaryGoldbach.MinorArcs
