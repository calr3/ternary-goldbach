import TernaryGoldbach.Helfgott.Defs
import TernaryGoldbach.MinorArcs.TypeI

/-!
# Major arcs and the Dirichlet parameter `r_α` [B, §13.2]

If `2α = a/q + δ/y (mod 1)` (`Approx2 α y δ a q _`) with `q ≤ r` and `|δ| q < δ₀ r`, then
`α ∈ 𝔐_{δ₀,r}` at scale `y` (`mem_majorArcs_of_approx`).  The odd/even radii of (10.5) are
exactly what makes this work in every parity case: `α = m/(2q) + δ/(2y)` with `m = a + kq`, and
either `m` is even and `q` odd (`α` is near `(m/2)/q`, odd denominator `q ≤ r`) or `m/(2q)` is
reduced (even denominator `2q ≤ 2r`).

Contrapositive (`le_rAlpha_of_not_mem`): **off `𝔐_{δ₀,r}` at scale `y`,
`r_α = max(1, |δ|/δ₀) q ≥ r`**.  This is the ℓ∞ step of [B, Thm 13.2.1] ("Let `α ∉ 𝔐_{8,r}`,
where `y` is used instead of `x` …"), and it holds only for the arcs at the scale `y` of the
approximation.  See NOTES "Ch. 13: scale erratum".

Proved, with no `sorry`.
-/

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)

theorem mem_majorArcs_of_approx {α y δ δ₀ r Q : ℝ} {a : ℤ} {q : ℕ} (hy : 0 < y)
    (h : Approx2 α y δ a q Q) (hqr : (q : ℝ) ≤ r) (hδ : |δ| * q < δ₀ * r) :
    α ∈ majorArcs δ₀ r y := by
  obtain ⟨hq1, hcop, ⟨k, hk⟩, -, -⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set m : ℤ := a + k * q with hm
  have hcopm : IsCoprime m (q : ℤ) := by
    simpa [hm] using hcop.add_mul_right_left k
  have hα : α = m / (2 * q) + δ / (2 * y) := by
    have : α = (a / q + δ / y + k) / 2 := by linarith
    rw [this, hm]; push_cast
    field_simp; ring
  -- `|δ/(2y)| < δ₀ r/(2 q y)`
  have hrad : |δ / (2 * y)| < δ₀ * r / (2 * q * y) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * y), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have hmem : ∀ (c ρ : ℝ), |α - c| < ρ → α ∈ Set.Ioo (c - ρ) (c + ρ) := fun c ρ h => by
    rw [abs_lt] at h; constructor <;> linarith
  by_cases hpar : Odd q ∧ Even m
  · obtain ⟨hqo, b, hb⟩ := hpar
    left
    refine Set.mem_iUnion₂.2 ⟨q, ⟨hq1, hqr, hqo⟩, Set.mem_iUnion₂.2 ⟨b, ?_, hmem _ _ ?_⟩⟩
    · have : IsCoprime (2 * b) (q : ℤ) := by rw [two_mul, ← hb]; exact hcopm
      exact this.of_mul_left_right
    · rw [hα, show (m : ℝ) = 2 * b by rw [hb]; push_cast; ring]
      convert hrad using 2; field_simp; ring
  · right
    have hmo : Odd m := by
      rcases Nat.even_or_odd q with hqe | hqo
      · obtain ⟨j, hj⟩ := hqe
        refine Int.not_even_iff_odd.1 fun hme => ?_
        have h2 : (2 : ℤ) ∣ m := hme.two_dvd
        have h2q : (2 : ℤ) ∣ (q : ℤ) := ⟨j, by rw [hj]; push_cast; ring⟩
        have := Int.isUnit_iff.1 (hcopm.isUnit_of_dvd' h2 h2q)
        omega
      · exact Int.not_even_iff_odd.1 fun hme => hpar ⟨hqo, hme⟩
    have hcop2 : IsCoprime m ((2 * q : ℕ) : ℤ) := by
      push_cast; exact (Int.isCoprime_two_right.mpr hmo).mul_right hcopm
    refine Set.mem_iUnion₂.2 ⟨2 * q, ⟨by omega, by push_cast; linarith, even_two_mul q⟩,
      Set.mem_iUnion₂.2 ⟨m, hcop2, hmem _ _ ?_⟩⟩
    rw [hα]; push_cast
    convert hrad using 2; field_simp; ring

/-- **Off the arcs, `r_α ≥ r`**: if `α ∉ 𝔐_{δ₀,r}` at scale `y` and `2α = a/q + δ/y (mod 1)`,
then `r ≤ max(1, |δ|/δ₀) q`. -/
theorem le_rAlpha_of_not_mem {α y δ δ₀ r Q : ℝ} {a : ℤ} {q : ℕ} (hy : 0 < y) (hδ₀ : 0 < δ₀)
    (h : Approx2 α y δ a q Q) (hα : α ∉ majorArcs δ₀ r y) :
    r ≤ max 1 (|δ| / δ₀) * q := by
  by_contra hlt
  push Not at hlt
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (q : ℝ) < r := lt_of_le_of_lt (by nlinarith [le_max_left 1 (|δ| / δ₀)]) hlt
  have h2 : |δ| / δ₀ * q < r := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hq0) hlt
  refine hα (mem_majorArcs_of_approx hy h h1.le ?_)
  rw [div_mul_eq_mul_div, div_lt_iff₀ hδ₀] at h2
  linarith

/-- The arcs grow with the level. -/
theorem majorArcs_mono {δ₀ x : ℝ} (hδ₀ : 0 ≤ δ₀) (hx : 0 < x) :
    Monotone fun r : ℝ => majorArcs δ₀ r x := by
  intro r r' hrr' α hα
  simp only [majorArcs, Set.mem_union, Set.mem_iUnion] at hα ⊢
  rcases hα with ⟨q, ⟨hq1, hqr, hqo⟩, b, hb, hαI⟩ | ⟨q, ⟨hq1, hqr, hqe⟩, b, hb, hαI⟩
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have : δ₀ * r / (2 * q * x) ≤ δ₀ * r' / (2 * q * x) := by gcongr
    exact Or.inl ⟨q, ⟨hq1, hqr.trans hrr', hqo⟩, b, hb, ⟨by linarith [hαI.1], by linarith [hαI.2]⟩⟩
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have : δ₀ * r / (q * x) ≤ δ₀ * r' / (q * x) := by gcongr
    exact Or.inr ⟨q, ⟨hq1, by linarith, hqe⟩, b, hb, ⟨by linarith [hαI.1], by linarith [hαI.2]⟩⟩

/-- The arcs grow with `δ₀` and with the level. -/
theorem majorArcs_subset {δ₀ δ₀' r r' x : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ₀') (hr0 : 0 ≤ r)
    (hrr' : r ≤ r') (hx : 0 < x) : majorArcs δ₀ r x ⊆ majorArcs δ₀' r' x := by
  intro α hα
  simp only [majorArcs, Set.mem_union, Set.mem_iUnion] at hα ⊢
  rcases hα with ⟨q, ⟨hq1, hqr, hqo⟩, b, hb, hαI⟩ | ⟨q, ⟨hq1, hqr, hqe⟩, b, hb, hαI⟩
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have : δ₀ * r / (2 * q * x) ≤ δ₀' * r' / (2 * q * x) := by gcongr; linarith
    exact Or.inl ⟨q, ⟨hq1, hqr.trans hrr', hqo⟩, b, hb, ⟨by linarith [hαI.1], by linarith [hαI.2]⟩⟩
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have : δ₀ * r / (q * x) ≤ δ₀' * r' / (q * x) := by gcongr; linarith
    exact Or.inr ⟨q, ⟨hq1, by linarith, hqe⟩, b, hb, ⟨by linarith [hαI.1], by linarith [hαI.2]⟩⟩

/-- Rescaling: `𝔐_{δ₀,r}(x/c) = 𝔐_{cδ₀,r}(x)`. -/
theorem majorArcs_div (δ₀ r x c : ℝ) :
    majorArcs δ₀ r (x / c) = majorArcs (δ₀ * c) r x := by
  have e1 : ∀ q : ℝ, δ₀ * r / (2 * q * (x / c)) = δ₀ * c * r / (2 * q * x) := fun q => by
    rw [mul_div_assoc', div_div_eq_mul_div]; ring
  have e2 : ∀ q : ℝ, δ₀ * r / (q * (x / c)) = δ₀ * c * r / (q * x) := fun q => by
    rw [mul_div_assoc', div_div_eq_mul_div]; ring
  simp only [majorArcs, e1, e2]

end TernaryGoldbach.MinorArcs
