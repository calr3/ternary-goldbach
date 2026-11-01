import TernaryGoldbach.Explicit.ZeroFree
import TernaryGoldbach.Explicit.Digamma

/-!
# A zero-free region for `ζ`: `β ≤ 1 − 1/(11 log|γ|)` for `|γ| ≥ 10⁹`

The classical argument with Stechkin's refinement: the non-negative trigonometric polynomial
`18 + 30 cos θ + 17 cos 2θ + 6 cos 3θ + cos 4θ = 8(½ + (3/2) cos θ + cos²θ)²` applied to
`−ℜ ζ'/ζ(σ + ijt) = Σ Λ(n) n^{−σ} cos(jt log n)`, and for `j ≥ 1` the inequality
`Re ξ'/ξ(s) − κ Re ξ'/ξ(s₁) ≥ Φ_s(ρ) − κ Φ_{s₁}(ρ)` (`stechkin_xi`) with `σ₁ = 1.6181`, which replaces
the coefficient `½` of `log t` by `(1 − κ)/2`, `κ ≈ 1/√5`.
-/

open Complex Set Metric Filter MeasureTheory
open scoped Real Interval Topology ComplexConjugate ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-! ## Digamma bounds -/

theorem digamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- `ψ(z) = ψ(z + 2) − 1/z − 1/(z + 1)` for `ℜz > 0`. -/
theorem digamma_eq_add_two {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
  have h1 := Complex.digamma_apply_add_one z (digamma_ne_neg_nat hz)
  have h2 := Complex.digamma_apply_add_one (z + 1) (digamma_ne_neg_nat (by simp; linarith))
  rw [show z + 2 = z + 1 + 1 by ring, h2, h1]; ring

/-- `ψ(x) ≤ log(x + 2) − 1/x − 1/(x + 1)` for real `x > 0`. -/
theorem re_digamma_real_le {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re ≤ Real.log (x + 2) - 1 / x - 1 / (x + 1) := by
  rw [digamma_eq_add_two (by simpa using hx)]
  have h := re_digamma_le (σ := x + 2) (t := 0) (by linarith)
  simp only [ofReal_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, Real.log_one, mul_zero] at h
  have e : ((x + 2 : ℝ) : ℂ) = (x : ℂ) + 2 := by push_cast; ring
  rw [e] at h
  have e1 : ((x : ℂ)⁻¹).re = 1 / x := by rw [← ofReal_inv, ofReal_re, one_div]
  have e2 : (((x : ℂ) + 1)⁻¹).re = 1 / (x + 1) := by
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_inv, ofReal_re, one_div]
  rw [Complex.sub_re, Complex.sub_re, e1, e2]
  linarith

theorem integral_one_add_rpow_neg {A : ℝ} (hA : 1 < A) :
    ∫ u in Ioi (0:ℝ), (1 + u) ^ (-A) = 1 / (A - 1) := by
  rw [setIntegral_Ioi_one_add (fun y : ℝ => y ^ (-A)), integral_Ioi_rpow_of_lt (by linarith) one_pos,
    Real.one_rpow, show -A + 1 = -(A - 1) by ring, div_neg, neg_div, neg_neg]

/-- `Re ψ(A + iy) − Re ψ(B + iy) ≤ (B − A)/(A − 1)` for `1 < A ≤ B`. -/
theorem re_digamma_sub_le_of_gt_one {A B y : ℝ} (hA : 1 < A) (hAB : A ≤ B) :
    (Complex.digamma ((A : ℂ) + y * I)).re - (Complex.digamma ((B : ℂ) + y * I)).re ≤ (B - A) / (A - 1) := by
  have hsA : 1 / 2 < ((A : ℂ) + y * I).re := by simp; linarith
  have hsB : 1 / 2 < ((B : ℂ) + y * I).re := by simp; linarith
  rw [digamma_eq_integral hsA, digamma_eq_integral hsB]
  have hiA := integrableOn_digG hsA
  have hiB := integrableOn_digG hsB
  rw [show (∫ u : ℝ in Ioi 0, ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-((A : ℂ) + y * I))) / u).re =
      RCLike.re (∫ u : ℝ in Ioi 0, digG ((A : ℂ) + y * I) u) from rfl, ← integral_re hiA,
    show (∫ u : ℝ in Ioi 0, ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-((B : ℂ) + y * I))) / u).re =
      RCLike.re (∫ u : ℝ in Ioi 0, digG ((B : ℂ) + y * I) u) from rfl, ← integral_re hiB,
    ← integral_sub hiA.re hiB.re]
  have hmaj : IntegrableOn (fun u : ℝ => (B - A) * (1 + u) ^ (-A)) (Ioi 0) :=
    (integrableOn_one_add_rpow hA).const_mul _
  have hpt : ∀ u ∈ Ioi (0:ℝ), RCLike.re (digG ((A : ℂ) + y * I) u) - RCLike.re (digG ((B : ℂ) + y * I) u) ≤
      (B - A) * (1 + u) ^ (-A) := by
    intro u (hu : 0 < u)
    rw [show RCLike.re (digG ((A : ℂ) + y * I) u) = (digG ((A : ℂ) + y * I) u).re from rfl,
      show RCLike.re (digG ((B : ℂ) + y * I) u) = (digG ((B : ℂ) + y * I) u).re from rfl, re_digG hu,
      re_digG hu]
    have h1u : (0:ℝ) < 1 + u := by linarith
    set c := Real.cos (y * Real.log (1 + u))
    have hc1 : -1 ≤ c := Real.neg_one_le_cos _
    have hsplit : (1 + u) ^ (-B) = (1 + u) ^ (-A) * (1 + u) ^ (-(B - A)) := by
      rw [← Real.rpow_add h1u]; ring_nf
    have hpA : 0 < (1 + u) ^ (-A) := Real.rpow_pos_of_pos h1u _
    have hd : 1 - (B - A) * u ≤ (1 + u) ^ (-(B - A)) := by
      rw [Real.rpow_def_of_pos h1u]
      have := Real.add_one_le_exp (Real.log (1 + u) * (-(B - A)))
      have hl : Real.log (1 + u) ≤ u := by
        have := Real.log_le_sub_one_of_pos h1u; linarith
      nlinarith
    have hd1 : (1 + u) ^ (-(B - A)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have e : (Real.exp (-u) - (1 + u) ^ (-A) * c) / u - (Real.exp (-u) - (1 + u) ^ (-B) * c) / u =
        ((1 + u) ^ (-A) * (1 + u) ^ (-(B - A)) - (1 + u) ^ (-A)) * c / u := by
      rw [hsplit]; field_simp; ring
    rw [e, div_le_iff₀ hu]
    have hX : (1 + u) ^ (-A) * (1 + u) ^ (-(B - A)) - (1 + u) ^ (-A) ≤ 0 := by nlinarith
    have hX2 : -((1 + u) ^ (-A) * (1 + u) ^ (-(B - A)) - (1 + u) ^ (-A)) ≤ (B - A) * (1 + u) ^ (-A) * u := by
      nlinarith
    nlinarith
  refine (setIntegral_mono_on (hiA.re.sub hiB.re) hmaj measurableSet_Ioi hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_one_add_rpow_neg hA]; ring

/-- `Re ψ(a + iy) − Re ψ(b + iy) ≤ (b − a)/(a + 1) + b/(b² + y²) + (b+1)/((b+1)² + y²)` for `0 < a ≤ b`. -/
theorem re_digamma_sub_le {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Complex.digamma ((a : ℂ) + y * I)).re - (Complex.digamma ((b : ℂ) + y * I)).re ≤
      (b - a) / (a + 1) + b / (b ^ 2 + y ^ 2) + (b + 1) / ((b + 1) ^ 2 + y ^ 2) := by
  have hb : 0 < b := by linarith
  rw [digamma_eq_add_two (z := (a : ℂ) + y * I) (by simpa using ha),
    digamma_eq_add_two (z := (b : ℂ) + y * I) (by simpa using hb)]
  have e2 : ∀ x : ℝ, (x : ℂ) + y * I + 2 = ((x + 2 : ℝ) : ℂ) + y * I := fun x => by push_cast; ring
  rw [e2 a, e2 b]
  have hmain := re_digamma_sub_le_of_gt_one (y := y) (show 1 < a + 2 by linarith) (show a + 2 ≤ b + 2 by linarith)
  have hinv : ∀ x : ℝ, (((x : ℂ) + y * I)⁻¹).re = x / (x ^ 2 + y ^ 2) := by
    intro x; rw [Complex.inv_re, Complex.normSq_apply]; simp; ring
  have hinv1 : ∀ x : ℝ, (((x : ℂ) + y * I + 1)⁻¹).re = (x + 1) / ((x + 1) ^ 2 + y ^ 2) := by
    intro x; rw [show (x : ℂ) + y * I + 1 = ((x + 1 : ℝ) : ℂ) + y * I by push_cast; ring, hinv]
  simp only [Complex.sub_re]
  rw [hinv, hinv, hinv1, hinv1]
  have p1 : 0 ≤ a / (a ^ 2 + y ^ 2) := by positivity
  have p2 : 0 ≤ (a + 1) / ((a + 1) ^ 2 + y ^ 2) := by positivity
  have : b + 2 - (a + 2) = b - a := by ring
  rw [this, show a + 2 - 1 = a + 1 by ring] at hmain
  linarith

end TernaryGoldbach.Explicit
