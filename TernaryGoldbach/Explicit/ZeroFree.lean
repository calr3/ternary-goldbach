import TernaryGoldbach.Explicit.XiPartial

/-!
# Stechkin's inequality for `ξ'/ξ`

For `s = σ + it`, `s₁ = σ₁ + it` with `1 < σ < σ₁` and `(σ − ½)² + (σ₁ − ½)² ≥ 3/2`, put `κ = (σ − ½)/(σ₁ − ½)`.
Pairing each zero `ρ` with `1 − ρ̄`, `Re ξ'/ξ(s) = ½ lim Σ_ρ Φ_s(ρ)` with
`Φ_s(ρ) = Re 1/(s − ρ) + Re 1/(s − (1 − ρ̄))`, and `Φ_s(ρ) ≥ κ Φ_{s₁}(ρ)` for every `ρ` in the critical strip
(an elementary inequality; [Stechkin 1970]). Hence `Re ξ'/ξ(s) − κ Re ξ'/ξ(s₁) ≥ Φ_s(ρ₀) − κ Φ_{s₁}(ρ₀)` for any
zero `ρ₀` off the critical line, and `≥ 0` in general.
-/

open Complex Set Metric Filter
open scoped Real Interval Topology ComplexConjugate

namespace TernaryGoldbach.Explicit

/-- `(d−b)/((d−b)²+τ²) + (d+b)/((d+b)²+τ²) = 2d(d²+τ²−b²)/((d²+τ²−b²)² + 4b²τ²)`. -/
theorem pair_frac_eq {d b τ : ℝ} (h1 : 0 < d - b) (h2 : 0 < d + b) :
    (d - b) / ((d - b) ^ 2 + τ ^ 2) + (d + b) / ((d + b) ^ 2 + τ ^ 2) =
      2 * d * (d ^ 2 + τ ^ 2 - b ^ 2) / ((d ^ 2 + τ ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 2 * τ ^ 2) := by
  have a1 : 0 < (d - b) ^ 2 + τ ^ 2 := by positivity
  have a2 : 0 < (d + b) ^ 2 + τ ^ 2 := by positivity
  have a3 : (d ^ 2 + τ ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 2 * τ ^ 2 = ((d - b) ^ 2 + τ ^ 2) * ((d + b) ^ 2 + τ ^ 2) := by
    ring
  rw [a3, div_add_div _ _ a1.ne' a2.ne']
  congr 1; ring

/-- **Stechkin's lemma** (elementary form). -/
theorem stechkin_alg {c c1 b τ : ℝ} (hc : 1 / 2 < c) (hcc : c < c1) (hb : |b| ≤ 1 / 2)
    (h32 : 3 / 2 ≤ c ^ 2 + c1 ^ 2) :
    c / c1 * ((c1 - b) / ((c1 - b) ^ 2 + τ ^ 2) + (c1 + b) / ((c1 + b) ^ 2 + τ ^ 2)) ≤
      (c - b) / ((c - b) ^ 2 + τ ^ 2) + (c + b) / ((c + b) ^ 2 + τ ^ 2) := by
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  have hc1 : 0 < c1 := by linarith
  rw [pair_frac_eq (by linarith) (by linarith), pair_frac_eq (by linarith) (by linarith)]
  set Y := c ^ 2 + τ ^ 2 - b ^ 2 with hY
  set Y1 := c1 ^ 2 + τ ^ 2 - b ^ 2 with hY1
  set m := 4 * b ^ 2 * τ ^ 2 with hm
  have hb2' : b ^ 2 ≤ 1 / 4 := by nlinarith
  have hcb : 0 ≤ c ^ 2 - b ^ 2 := by nlinarith
  have hc1b : 0 ≤ c1 ^ 2 - b ^ 2 := by nlinarith
  have hYp : 0 ≤ Y := by rw [hY]; nlinarith [sq_nonneg τ]
  have hY1p : 0 < Y1 := by rw [hY1]; nlinarith [sq_nonneg τ]
  have hm0 : 0 ≤ m := by positivity
  have hD : 0 < Y ^ 2 + m := by
    rcases eq_or_lt_of_le hYp with h | h
    · rw [← h]
      have : c ^ 2 - b ^ 2 = 0 ∧ τ ^ 2 = 0 := by
        constructor <;> nlinarith [sq_nonneg τ]
      nlinarith
    · positivity
  have hD1 : 0 < Y1 ^ 2 + m := by positivity
  have e : c / c1 * (2 * c1 * Y1 / (Y1 ^ 2 + m)) = 2 * c * Y1 / (Y1 ^ 2 + m) := by
    field_simp
  rw [e, div_le_div_iff₀ hD1 hD]
  have h1 : 0 ≤ Y1 - Y := by rw [hY, hY1]; nlinarith
  have h2 : 0 ≤ Y * Y1 - m := by
    have : Y * Y1 - m = (c ^ 2 - b ^ 2) * (c1 ^ 2 - b ^ 2) + τ ^ 2 * (c ^ 2 + c1 ^ 2 - 6 * b ^ 2) + (τ ^ 2) ^ 2 := by
      rw [hY, hY1, hm]; ring
    rw [this]
    have : 0 ≤ c ^ 2 + c1 ^ 2 - 6 * b ^ 2 := by nlinarith
    positivity
  have h3 : 0 ≤ 2 * c * ((Y1 - Y) * (Y * Y1 - m)) := by
    have : 0 ≤ c := by linarith
    positivity
  nlinarith

/-- `Φ_s(u) = Re 1/(s − u) + Re 1/(s − (1 − ū))`. -/
noncomputable def Phi (s u : ℂ) : ℝ := ((s - u)⁻¹).re + ((s - (1 - conj u))⁻¹).re

theorem Phi_eq (s u : ℂ) :
    Phi s u = ((s.re - 1 / 2) - (u.re - 1 / 2)) / (((s.re - 1 / 2) - (u.re - 1 / 2)) ^ 2 + (s.im - u.im) ^ 2) +
      ((s.re - 1 / 2) + (u.re - 1 / 2)) / (((s.re - 1 / 2) + (u.re - 1 / 2)) ^ 2 + (s.im - u.im) ^ 2) := by
  unfold Phi
  rw [Complex.inv_re, Complex.inv_re, Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, sub_im, one_re, one_im, conj_re, conj_im]
  ring

theorem Phi_one_sub_conj (s u : ℂ) : Phi s (1 - conj u) = Phi s u := by
  unfold Phi
  rw [map_sub, map_one, Complex.conj_conj, sub_sub_cancel, add_comm]

theorem Phi_nonneg {s u : ℂ} (hs : 1 < s.re) (hu1 : 0 < u.re) (hu2 : u.re < 1) : 0 ≤ Phi s u := by
  rw [Phi_eq]
  have a : 0 < (s.re - 1 / 2) - (u.re - 1 / 2) := by linarith
  have b : 0 < (s.re - 1 / 2) + (u.re - 1 / 2) := by linarith
  positivity

theorem Phi_stechkin {s s1 u : ℂ} (hs : 1 < s.re) (hss : s.re < s1.re) (him : s1.im = s.im)
    (h32 : 3 / 2 ≤ (s.re - 1 / 2) ^ 2 + (s1.re - 1 / 2) ^ 2) (hu1 : 0 < u.re) (hu2 : u.re < 1) :
    (s.re - 1 / 2) / (s1.re - 1 / 2) * Phi s1 u ≤ Phi s u := by
  rw [Phi_eq, Phi_eq, him]
  exact stechkin_alg (by linarith) (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩) h32

/-- Zeros of `ξ` lie in the open critical strip. -/
theorem xiF_zero_re {u : ℂ} (hu : xiF u = 0) : 0 < u.re ∧ u.re < 1 := by
  constructor
  · by_contra h; exact xiF_ne_zero_of_re_nonpos (not_lt.1 h) hu
  · by_contra h; exact xiF_ne_zero_of_one_le_re (not_lt.1 h) hu

theorem xiF_zero_one_sub_conj {u : ℂ} (hu : xiF u = 0) : xiF (1 - conj u) = 0 := by
  rw [xiF_one_sub, xiF_conj, hu, map_zero]

theorem re_inv_conj_shift (s u : ℂ) : ((u - (1 - conj s))⁻¹).re = ((s - (1 - conj u))⁻¹).re := by
  have : u - (1 - conj s) = conj (s - (1 - conj u)) := by
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  rw [this, ← map_inv₀, Complex.conj_re]

/-- **Pairing**: on an approximating square, `|Σ_u m_u Φ_s(u) − 2 Re ξ'/ξ(s)| ≤ 2ε`. -/
theorem pair_approx {T M ε : ℝ}
    (happrox : ∀ s : ℂ, ‖s - 1 / 2‖ ≤ M → xiF s ≠ 0 →
      ‖logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹‖ ≤ ε)
    {s : ℂ} (hs : 1 < s.re) (hsM : ‖s - 1 / 2‖ ≤ M) :
    |∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u - 2 * (logDeriv xiF s).re| ≤ 2 * ε := by
  have hξ : xiF s ≠ 0 := xiF_ne_zero_of_one_le_re hs.le
  set p := 1 - conj s with hp
  have hpM : ‖p - 1 / 2‖ ≤ M := by
    have : p - 1 / 2 = -conj (s - 1 / 2) := by
      rw [hp, map_sub]; simp only [map_div₀, map_one, map_ofNat]; ring
    rw [this, norm_neg, Complex.norm_conj]; exact hsM
  have hξp : xiF p ≠ 0 := by
    rw [hp, xiF_one_sub, xiF_conj]; exact (map_ne_zero _).2 hξ
  have h1 := happrox s hsM hξ
  have h2 := happrox p hpM hξp
  have r1 : (logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹).re =
      (logDeriv xiF s).re - ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - u)⁻¹).re := by
    rw [Complex.add_re, Complex.re_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show u - s = -(s - u) by ring, inv_neg, mul_neg, Complex.neg_re]
    simp [Complex.mul_re]
  have r2 : (logDeriv xiF p + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - p)⁻¹).re =
      -(logDeriv xiF s).re + ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - (1 - conj u))⁻¹).re := by
    rw [Complex.add_re, Complex.re_sum, hp, logDeriv_xiF_one_sub, logDeriv_xiF_conj, Complex.neg_re,
      Complex.conj_re]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← re_inv_conj_shift s u]
    simp [Complex.mul_re]
  have a1 : |(logDeriv xiF s).re - ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - u)⁻¹).re| ≤ ε := by
    rw [← r1]; exact (Complex.abs_re_le_norm _).trans h1
  have a2 : |-(logDeriv xiF s).re + ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - (1 - conj u))⁻¹).re| ≤ ε := by
    rw [← r2]; exact (Complex.abs_re_le_norm _).trans h2
  have e : ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u =
      ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - u)⁻¹).re +
        ∑ u ∈ sqZeros T, (mult T u : ℝ) * ((s - (1 - conj u))⁻¹).re := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Phi]; ring
  rw [e]
  have := abs_le.1 a1
  have := abs_le.1 a2
  rw [abs_le]; constructor <;> linarith

/-- **`Re ξ'/ξ(s) ≥ 0`** for `ℜs > 1`. -/
theorem re_logDeriv_xiF_nonneg {s : ℂ} (hs : 1 < s.re) : 0 ≤ (logDeriv xiF s).re := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨T, -, happrox, -, hzero⟩ := xi_partial_approx (norm_nonneg (s - 1 / 2)) (half_pos hε)
  have hp := pair_approx happrox hs le_rfl
  have hnn : 0 ≤ ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u := by
    refine Finset.sum_nonneg fun u hu => ?_
    have := xiF_zero_re (hzero u hu)
    exact mul_nonneg (Nat.cast_nonneg _) (Phi_nonneg hs this.1 this.2)
  have := (abs_le.1 hp).2
  linarith

/-- **Stechkin's inequality for `ξ'/ξ`** (a zero `ρ₀` off the critical line contributes `Φ_s(ρ₀) − κΦ_{s₁}(ρ₀)`). -/
theorem stechkin_xi {s s1 : ℂ} (hs : 1 < s.re) (hss : s.re < s1.re) (him : s1.im = s.im)
    (h32 : 3 / 2 ≤ (s.re - 1 / 2) ^ 2 + (s1.re - 1 / 2) ^ 2) {ρ : ℂ} (hρ : xiF ρ = 0) (hρre : ρ.re ≠ 1 / 2) :
    Phi s ρ - (s.re - 1 / 2) / (s1.re - 1 / 2) * Phi s1 ρ ≤
      (logDeriv xiF s).re - (s.re - 1 / 2) / (s1.re - 1 / 2) * (logDeriv xiF s1).re := by
  set κ := (s.re - 1 / 2) / (s1.re - 1 / 2) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hs1 : 1 < s1.re := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set M := max (max ‖s - 1 / 2‖ ‖s1 - 1 / 2‖) ‖ρ - 1 / 2‖ with hM
  have hM0 : 0 ≤ M := le_max_of_le_right (norm_nonneg _)
  set ε' := ε / (2 * (1 + κ)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T, -, happrox, hmem, hzero⟩ := xi_partial_approx hM0 hε'0
  have hp := pair_approx happrox hs (le_max_of_le_left (le_max_left _ _))
  have hp1 := pair_approx happrox hs1 (le_max_of_le_left (le_max_right _ _))
  set ρ' := 1 - conj ρ with hρ'
  have hρ'z : xiF ρ' = 0 := xiF_zero_one_sub_conj hρ
  have hρ'M : ‖ρ' - 1 / 2‖ ≤ M := by
    have : ρ' - 1 / 2 = -conj (ρ - 1 / 2) := by
      rw [hρ', map_sub]; simp only [map_div₀, map_one, map_ofNat]; ring
    rw [this, norm_neg, Complex.norm_conj]; exact le_max_right _ _
  obtain ⟨hρZ, hρm⟩ := hmem ρ hρ (le_max_right _ _)
  obtain ⟨hρ'Z, hρ'm⟩ := hmem ρ' hρ'z hρ'M
  have hne : ρ ≠ ρ' := by
    intro h
    have := congrArg Complex.re h
    rw [hρ'] at this; simp at this
    exact hρre (by linarith)
  -- the termwise inequality
  set F : ℂ → ℝ := fun u => (mult T u : ℝ) * (Phi s u - κ * Phi s1 u) with hF
  have hF0 : ∀ u ∈ sqZeros T, 0 ≤ F u := by
    intro u hu
    have := xiF_zero_re (hzero u hu)
    have := Phi_stechkin hs hss him h32 this.1 this.2
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsub : ({ρ, ρ'} : Finset ℂ) ⊆ sqZeros T := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hρZ
    · exact hρ'Z
  have hsum : F ρ + F ρ' ≤ ∑ u ∈ sqZeros T, F u := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun u hu _ => hF0 u hu
  have hρs := xiF_zero_re hρ
  have hq0 : 0 ≤ Phi s ρ - κ * Phi s1 ρ := by
    have := Phi_stechkin hs hss him h32 hρs.1 hρs.2; linarith
  have hFρ : Phi s ρ - κ * Phi s1 ρ ≤ F ρ := by
    have : (1:ℝ) ≤ mult T ρ := by exact_mod_cast hρm
    rw [hF]; nlinarith
  have hFρ' : Phi s ρ - κ * Phi s1 ρ ≤ F ρ' := by
    have : (1:ℝ) ≤ mult T ρ' := by exact_mod_cast hρ'm
    rw [hF]
    simp only
    rw [hρ', Phi_one_sub_conj, Phi_one_sub_conj]
    nlinarith
  have hsplit : ∑ u ∈ sqZeros T, F u = ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u -
      κ * ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s1 u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hF]; ring
  have a := (abs_le.1 hp).2
  have b := (abs_le.1 hp1).1
  have hκε : 2 * ε' + κ * (2 * ε') = ε := by rw [hε']; field_simp
  set S := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u
  set S1 := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s1 u
  have hk := mul_nonneg hκ0 (by linarith : 0 ≤ S1 - 2 * (logDeriv xiF s1).re + 2 * ε')
  linarith

end TernaryGoldbach.Explicit
