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

/-! ## The Dirichlet series `−ζ'/ζ = Σ Λ(n) n^{−s}` -/

/-- The real part of the terms of `Σ Λ(n) n^{−s}`. -/
theorem re_term_vM (σ τ : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I) n).re =
      if n = 0 then 0 else Λ n * Real.exp (-σ * Real.log n) * Real.cos (τ * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, if_neg hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log, Complex.re_ofReal_mul]
  have e : (Real.log n : ℂ) * -((σ : ℂ) + τ * I) = ((-σ * Real.log n : ℝ) : ℂ) + ((-τ * Real.log n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e, Complex.exp_re]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  rw [show -τ * Real.log n = -(τ * Real.log n) by ring, Real.cos_neg]
  ring

theorem hasSum_re_vM {σ : ℝ} (hσ : 1 < σ) (τ : ℝ) :
    HasSum (fun n : ℕ => if n = 0 then 0 else Λ n * Real.exp (-σ * Real.log n) * Real.cos (τ * Real.log n))
      (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I)).re := by
  have hs : 1 < ((σ : ℂ) + τ * I).re := by simpa using hσ
  have h := Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  convert h using 1 <;> first | rfl | (funext n; rw [re_term_vM])

/-- `18 + 30 cos θ + 17 cos 2θ + 6 cos 3θ + cos 4θ ≥ 0`. -/
theorem trig_poly_nonneg (θ : ℝ) :
    0 ≤ 18 + 30 * Real.cos θ + 17 * Real.cos (2 * θ) + 6 * Real.cos (3 * θ) + Real.cos (4 * θ) := by
  have h2 := Real.cos_two_mul θ
  have h3 := Real.cos_three_mul θ
  have h4 : Real.cos (4 * θ) = 2 * Real.cos (2 * θ) ^ 2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul]
  rw [h4, h2, h3]
  nlinarith [sq_nonneg (1 / 2 + 3 / 2 * Real.cos θ + Real.cos θ ^ 2)]

/-- **Positivity**: `Σ_j a_j ℜ(−ζ'/ζ)(σ + ijt) ≥ 0` for `(a_j) = (18, 30, 17, 6, 1)`. -/
theorem vM_positivity {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 18 * (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((0 * t : ℝ) : ℂ) * I)).re +
      30 * (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((1 * t : ℝ) : ℂ) * I)).re +
      17 * (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re +
      6 * (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * I)).re +
      (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((4 * t : ℝ) : ℂ) * I)).re := by
  have H := (((((hasSum_re_vM hσ (0 * t)).mul_left 18).add ((hasSum_re_vM hσ (1 * t)).mul_left 30)).add
    ((hasSum_re_vM hσ (2 * t)).mul_left 17)).add ((hasSum_re_vM hσ (3 * t)).mul_left 6)).add
    (hasSum_re_vM hσ (4 * t))
  refine H.nonneg fun n => ?_
  split_ifs with hn
  · simp
  · have hΛ : 0 ≤ Λ n * Real.exp (-σ * Real.log n) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
    have := mul_nonneg hΛ (trig_poly_nonneg (t * Real.log n))
    rw [show (0:ℝ) * t * Real.log n = 0 by ring, show (1:ℝ) * t * Real.log n = t * Real.log n by ring,
      show (2:ℝ) * t * Real.log n = 2 * (t * Real.log n) by ring,
      show (3:ℝ) * t * Real.log n = 3 * (t * Real.log n) by ring,
      show (4:ℝ) * t * Real.log n = 4 * (t * Real.log n) by ring, Real.cos_zero]
    nlinarith [this]

/-- `ℜ(−ζ'/ζ)(σ + iτ) ≤ −ζ'/ζ(σ)`. -/
theorem re_vM_le {σ : ℝ} (hσ : 1 < σ) (τ : ℝ) :
    (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I)).re ≤
      (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re := by
  refine hasSum_le (fun n => ?_) (hasSum_re_vM hσ τ) (hasSum_re_vM hσ 0)
  split_ifs
  · exact le_rfl
  · simp only [zero_mul, Real.cos_zero, mul_one]
    have hΛ : 0 ≤ Λ n * Real.exp (-σ * Real.log n) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
    nlinarith [Real.cos_le_one (τ * Real.log n)]

/-- `ℜ(−ζ'/ζ)(s) = −ℜ ξ'/ξ(s) + ℜ 1/s + ℜ 1/(s−1) − ½ log π + ½ ℜ ψ(s/2)` for `ℜs > 1`. -/
theorem re_vM_eq {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => (Λ n : ℂ)) s).re = -(logDeriv xiF s).re + (1 / s).re + (1 / (s - 1)).re -
      1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [logDeriv_xiF (by linarith) hs1 (xiF_ne_zero_of_one_le_re hs.le), logDeriv_zetaF_eq hs1 hz,
    logDeriv_apply]
  have hl : (Complex.log (π : ℂ)).re = Real.log π := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  rw [hL]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, hl]
  norm_num
  rw [neg_div, Complex.neg_re]
  ring

end TernaryGoldbach.Explicit
