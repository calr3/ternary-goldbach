import TernaryGoldbach.Explicit.ZeroFree
import TernaryGoldbach.Explicit.Digamma

/-!
# A zero-free region for `ζ`: `β ≤ 1 − 1/(11 log|γ|)` for `|γ| ≥ 10⁸`

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

/-! ## Assembling the zero-free region -/

/-- Stechkin's inequality without a distinguished zero. -/
theorem stechkin_xi_nonneg {s s1 : ℂ} (hs : 1 < s.re) (hss : s.re < s1.re) (him : s1.im = s.im)
    (h32 : 3 / 2 ≤ (s.re - 1 / 2) ^ 2 + (s1.re - 1 / 2) ^ 2) :
    0 ≤ (logDeriv xiF s).re - (s.re - 1 / 2) / (s1.re - 1 / 2) * (logDeriv xiF s1).re := by
  set κ := (s.re - 1 / 2) / (s1.re - 1 / 2) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hs1 : 1 < s1.re := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set M := max ‖s - 1 / 2‖ ‖s1 - 1 / 2‖ with hM
  have hM0 : 0 ≤ M := le_max_of_le_right (norm_nonneg _)
  set ε' := ε / (2 * (1 + κ)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T, -, happrox, -, hzero⟩ := xi_partial_approx hM0 hε'0
  have hp := pair_approx happrox hs (le_max_left _ _)
  have hp1 := pair_approx happrox hs1 (le_max_right _ _)
  set S := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u
  set S1 := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s1 u
  have hF : 0 ≤ S - κ * S1 := by
    have : S - κ * S1 = ∑ u ∈ sqZeros T, (mult T u : ℝ) * (Phi s u - κ * Phi s1 u) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [this]
    refine Finset.sum_nonneg fun u hu => ?_
    have := xiF_zero_re (hzero u hu)
    have := Phi_stechkin hs hss him h32 this.1 this.2
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have a := (abs_le.1 hp).2
  have b := (abs_le.1 hp1).1
  have hκε : 2 * ε' + κ * (2 * ε') = ε := by rw [hε']; field_simp
  have hk := mul_nonneg hκ0 (by linarith : 0 ≤ S1 + 2 * ε' - 2 * (logDeriv xiF s1).re)
  nlinarith

theorem log_pi_ge : 1.1447 ≤ Real.log π := by
  rw [Real.le_log_iff_exp_le Real.pi_pos]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.1447) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 1.1447 = Real.exp 1 * Real.exp 0.1447 := by rw [← Real.exp_add]; norm_num
  have hπ := Real.pi_gt_d6
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.1447]

theorem log_le_of_le_exp' {x c : ℝ} (hx : 0 < x) (h : x ≤ Real.exp c) : Real.log x ≤ c :=
  (Real.log_le_iff_le_exp hx).2 h

theorem log280905_le : Real.log 2.80905 ≤ 1.0329 := by
  refine log_le_of_le_exp' (by norm_num) ?_
  have h := exp_split_ge' 1 (u := 0.0329) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log2_le' : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; linarith

theorem log3_le' : Real.log 3 ≤ 1.0987 := by
  refine log_le_of_le_exp' (by norm_num) ?_
  have h := exp_split_ge' 1 (u := 0.0987) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log2585_le : Real.log 2.5085 ≤ 0.9197 := by
  refine log_le_of_le_exp' (by norm_num) ?_
  have h := exp_split_ge' 0 (u := 0.9197) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_1e8_ge : 18.4 ≤ Real.log 1e8 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 18.4 = Real.exp 1 ^ 18 * Real.exp 0.4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h3 := Real.exp_bound' (x := 0.4) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h3
  rw [h2]
  calc Real.exp 1 ^ 18 * Real.exp 0.4 ≤ 2.7182818286 ^ 18 * 1.4919 :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 18) (by linarith) (Real.exp_pos _).le
          (by positivity)
    _ ≤ 1e8 := by norm_num

theorem vM_real_le {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      1 / σ + 1 / (σ - 1) - 1 / 2 * Real.log π + 1 / 2 * (Real.log (σ / 2 + 2) - 2 / σ - 1 / (σ / 2 + 1)) := by
  have hs : 1 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I).re := by simpa using hσ
  rw [re_vM_eq hs]
  have hX := re_logDeriv_xiF_nonneg hs
  have e0 : (σ : ℂ) + ((0 : ℝ) : ℂ) * I = ((σ : ℝ) : ℂ) := by simp
  rw [e0] at hX ⊢
  have e1 : (1 / (σ : ℂ)).re = 1 / σ := by rw [← ofReal_one, ← ofReal_div, ofReal_re]
  have e2 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  have e3 : (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3]
  have hψ := re_digamma_real_le (x := σ / 2) (by linarith)
  have : 1 / (σ / 2) = 2 / σ := by field_simp
  rw [this] at hψ
  linarith

/-- The terms `j ≥ 1`: `ℜ(−ζ'/ζ)(σ + iτ) ≤ 2/τ² + (1−κ)(½ log τ + 0.36 − ½ log π) + ½κ(0.20604 + 11/τ²)
+ κ E₁ − Z` where `Z ≤ Re ξ'/ξ(s) − κ Re ξ'/ξ(s₁)`, `s₁ = 1.6181 + iτ`. -/
theorem vM_term_le {σ τ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 1.02) (hτ : 10 ≤ τ) {Z : ℝ}
    (hZ : Z ≤ (logDeriv xiF ((σ : ℂ) + τ * I)).re -
      (σ - 1 / 2) / (1.6181 - 1 / 2) * (logDeriv xiF ((1.6181 : ℝ) + τ * I)).re) :
    (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I)).re ≤
      2 / τ ^ 2 + (1 - (σ - 1 / 2) / (1.6181 - 1 / 2)) * (1 / 2 * Real.log τ + 0.36 - 1 / 2 * Real.log π) +
        1 / 2 * ((σ - 1 / 2) / (1.6181 - 1 / 2)) * (0.20604 + 11 / τ ^ 2) +
        (σ - 1 / 2) / (1.6181 - 1 / 2) *
          (1 / 1.6181 + 1 / (1.6181 - 1) - 1 / 2 * Real.log π +
            1 / 2 * (Real.log (1.6181 / 2 + 2) - 2 / 1.6181 - 1 / (1.6181 / 2 + 1))) - Z := by
  set κ := (σ - 1 / 2) / (1.6181 - 1 / 2) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by norm_num)
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by norm_num)]; linarith
  have hs : 1 < ((σ : ℂ) + τ * I).re := by simpa using hσ1
  have hs1 : 1 < (((1.6181 : ℝ) : ℂ) + τ * I).re := by simp; norm_num
  have hL := re_vM_eq hs
  have hL1 := re_vM_eq hs1
  -- `ℜ(−ζ'/ζ)(s₁) ≤ E₁`
  have hE1 := (re_vM_le (σ := 1.6181) (by norm_num) τ).trans (vM_real_le (by norm_num))
  -- small terms
  have hτ0 : 0 < τ := by linarith
  have r1 : (1 / ((σ : ℂ) + τ * I)).re ≤ 1.02 / τ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1.02 - σ) (sq_nonneg τ), sq_nonneg σ]
  have r2 : (1 / ((σ : ℂ) + τ * I - 1)).re ≤ 0.02 / τ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 0.02 - (σ - 1)) (sq_nonneg τ), sq_nonneg (σ - 1)]
  have r3 : 0 ≤ (1 / (((1.6181 : ℝ) : ℂ) + τ * I)).re := by
    rw [one_div, Complex.inv_re]; apply div_nonneg _ (Complex.normSq_nonneg _); simp; norm_num
  have r4 : 0 ≤ (1 / (((1.6181 : ℝ) : ℂ) + τ * I - 1)).re := by
    rw [one_div, Complex.inv_re]; apply div_nonneg _ (Complex.normSq_nonneg _); simp; norm_num
  -- digamma
  have ed : ((σ : ℂ) + τ * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have ed1 : (((1.6181 : ℝ) : ℂ) + τ * I) / 2 = ((1.6181 / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hψ1 := half_re_digamma_half_le hσ1 (by linarith) (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at hψ1
  have hD := re_digamma_sub_le (a := σ / 2) (b := 1.6181 / 2) (y := τ / 2) (by linarith) (by linarith)
  rw [← ed, ← ed1] at hD
  have hD1 : (1.6181 / 2 - σ / 2) / (σ / 2 + 1) ≤ 0.20604 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hD2 : 1.6181 / 2 / ((1.6181 / 2) ^ 2 + (τ / 2) ^ 2) + (1.6181 / 2 + 1) / ((1.6181 / 2 + 1) ^ 2 + (τ / 2) ^ 2)
      ≤ 11 / τ ^ 2 := by
    have a1 : 1.6181 / 2 / ((1.6181 / 2) ^ 2 + (τ / 2) ^ 2) ≤ 1.6181 / 2 / ((τ / 2) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have a2 : (1.6181 / 2 + 1) / ((1.6181 / 2 + 1) ^ 2 + (τ / 2) ^ 2) ≤ (1.6181 / 2 + 1) / ((τ / 2) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have e : 1.6181 / 2 / ((τ / 2) ^ 2) + (1.6181 / 2 + 1) / ((τ / 2) ^ 2) = 10.4724 / τ ^ 2 := by
      field_simp; ring
    have : 10.4724 / τ ^ 2 ≤ 11 / τ ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  -- combine
  set X := (logDeriv xiF ((σ : ℂ) + τ * I)).re
  set X1 := (logDeriv xiF (((1.6181 : ℝ) : ℂ) + τ * I)).re
  set P := (Complex.digamma (((σ : ℂ) + τ * I) / 2)).re
  set P1 := (Complex.digamma ((((1.6181 : ℝ) : ℂ) + τ * I) / 2)).re
  set E1 := 1 / 1.6181 + 1 / (1.6181 - 1) - 1 / 2 * Real.log π +
      1 / 2 * (Real.log (1.6181 / 2 + 2) - 2 / 1.6181 - 1 / (1.6181 / 2 + 1))
  set L1 := (LSeries (fun n => (Λ n : ℂ)) (((1.6181 : ℝ) : ℂ) + τ * I)).re
  have hZ' : Z ≤ X - κ * X1 := hZ
  have hPP : P - P1 ≤ 0.20604 + 11 / τ ^ 2 := by linarith
  have k1 : κ * L1 ≤ κ * E1 := mul_le_mul_of_nonneg_left hE1 hκ0
  have k2 : κ * (P - P1) ≤ κ * (0.20604 + 11 / τ ^ 2) := mul_le_mul_of_nonneg_left hPP hκ0
  have k3 : (1 - κ) * (1 / 2 * P) ≤ (1 - κ) * (1 / 2 * Real.log τ + 0.36) :=
    mul_le_mul_of_nonneg_left hψ1 (by linarith)
  have k4 : 0 ≤ κ * ((1 / (((1.6181 : ℝ) : ℂ) + τ * I)).re + (1 / (((1.6181 : ℝ) : ℂ) + τ * I - 1)).re) :=
    mul_nonneg hκ0 (by linarith)
  have hsplit : (1.02 / τ ^ 2) + 0.02 / τ ^ 2 ≤ 2 / τ ^ 2 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rw [hL]
  rw [hL1] at k1
  linear_combination hZ' + k1 + (1 / 2 : ℝ) * k2 + k3 + k4 + r1 + r2 + hsplit

theorem stech_wrap {σ τ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 1.02) :
    0 ≤ (logDeriv xiF ((σ : ℂ) + τ * I)).re -
      (σ - 1 / 2) / (1.6181 - 1 / 2) * (logDeriv xiF ((1.6181 : ℝ) + τ * I)).re := by
  have e1 : ((σ : ℂ) + τ * I).re = σ := by simp
  have e2 : (((1.6181 : ℝ) : ℂ) + τ * I).re = 1.6181 := by simp
  have h := stechkin_xi_nonneg (s := (σ : ℂ) + τ * I) (s1 := ((1.6181 : ℝ) : ℂ) + τ * I)
    (by rw [e1]; exact hσ1) (by rw [e1, e2]; linarith) (by simp) (by rw [e1, e2]; nlinarith)
  rw [e1, e2] at h; exact h

theorem stech_wrap_rho {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 1.02) {ρ : ℂ} (hρ : xiF ρ = 0)
    (hρre : ρ.re ≠ 1 / 2) :
    (1 / (σ - ρ.re) + 1 / (σ + ρ.re - 1)) -
        (σ - 1 / 2) / (1.6181 - 1 / 2) * (1 / (1.6181 - ρ.re) + 1 / (1.6181 + ρ.re - 1)) ≤
      (logDeriv xiF ((σ : ℂ) + ρ.im * I)).re -
        (σ - 1 / 2) / (1.6181 - 1 / 2) * (logDeriv xiF ((1.6181 : ℝ) + ρ.im * I)).re := by
  have e1 : ((σ : ℂ) + ρ.im * I).re = σ := by simp
  have e2 : (((1.6181 : ℝ) : ℂ) + ρ.im * I).re = 1.6181 := by simp
  have h := stechkin_xi (s := (σ : ℂ) + ρ.im * I) (s1 := ((1.6181 : ℝ) : ℂ) + ρ.im * I)
    (by rw [e1]; exact hσ1) (by rw [e1, e2]; linarith) (by simp) (by rw [e1, e2]; nlinarith) hρ hρre
  rw [e1, e2, Phi_eq, Phi_eq] at h
  have hz := xiF_zero_re hρ
  have i1 : ((σ : ℂ) + ρ.im * I).im - ρ.im = 0 := by simp
  have i2 : (((1.6181 : ℝ) : ℂ) + ρ.im * I).im - ρ.im = 0 := by simp
  rw [e1, e2, i1, i2] at h
  have f : ∀ x : ℝ, x ≠ 0 → x / (x ^ 2 + 0 ^ 2) = 1 / x := fun x hx => by
    rw [show x ^ 2 + 0 ^ 2 = x * x by ring]; field_simp
  rw [f _ (by linarith), f _ (by linarith), f _ (by linarith), f _ (by linarith)] at h
  have g1 : σ - 1 / 2 - (ρ.re - 1 / 2) = σ - ρ.re := by ring
  have g2 : σ - 1 / 2 + (ρ.re - 1 / 2) = σ + ρ.re - 1 := by ring
  have g3 : 1.6181 - 1 / 2 - (ρ.re - 1 / 2) = 1.6181 - ρ.re := by ring
  have g4 : 1.6181 - 1 / 2 + (ρ.re - 1 / 2) = 1.6181 + ρ.re - 1 := by ring
  rw [g1, g2, g3, g4] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **Zero-free region** (Stechkin-type, `R = 11`): every zero `ρ = β + iγ` of `ξ` with `γ ≥ 10⁸` has
`β ≤ 1 − 1/(11 log γ)`. -/
theorem zero_free_pos {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1e8 ≤ ρ.im) :
    ρ.re ≤ 1 - 1 / (11 * Real.log ρ.im) := by
  obtain ⟨t, htdef⟩ : ∃ t, t = ρ.im := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log t := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β, β = ρ.re := ⟨_, rfl⟩
  rw [← htdef] at ht ⊢
  rw [← hLdef, ← hβdef]
  have ht0 : 0 < t := by linarith
  have hL : 18.4 ≤ L := hLdef ▸ log_1e8_ge.trans (Real.log_le_log (by norm_num) ht)
  have hL0 : 0 < L := by linarith
  by_contra hβ
  push Not at hβ
  have hz := xiF_zero_re hρ
  have hβ1 : β < 1 := hβdef ▸ hz.2
  have h11 : 1 / (11 * L) ≤ 0.05 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hβ95 : 0.95 ≤ β := by linarith
  have hβh : ρ.re ≠ 1 / 2 := by intro h; rw [← hβdef] at h; linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 1 + 0.31 / L := ⟨_, rfl⟩
  have hσL0 : 0 < 0.31 / L := by positivity
  have hσ1 : 1 < σ := by linarith
  have hσL : 0.31 / L ≤ 0.01685 := by rw [div_le_iff₀ hL0]; linarith
  have hσ2 : σ ≤ 1.01685 := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = (σ - 1 / 2) / (1.6181 - 1 / 2) := ⟨_, rfl⟩
  have hκl : 0.4471 ≤ κ := by rw [hκ, le_div_iff₀ (by norm_num)]; norm_num; linarith
  have hκu : κ ≤ 0.46226 := by rw [hκ, div_le_iff₀ (by norm_num)]; norm_num; linarith
  -- numerical constants
  have lπ := log_pi_ge
  have lπu := log_pi_le
  have l2 := log2_le'
  have l2' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have l3 := log3_le'
  have l3' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  have l2508 := log2585_le
  -- tiny terms
  have tt : ∀ j : ℝ, 1 ≤ j → 2 / (j * t) ^ 2 + 1 / 2 * κ * (0.20604 + 11 / (j * t) ^ 2) ≤ 1 / 2 * κ * 0.20604 + 1e-15 := by
    intro j hj
    have hjt : 1 * 1e8 ≤ j * t := mul_le_mul hj ht (by norm_num) (by linarith)
    have hsq : (1e8 : ℝ) ^ 2 ≤ (j * t) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hsq' : (1e16 : ℝ) ≤ (j * t) ^ 2 := by norm_num at hsq ⊢; linarith
    have a : 2 / (j * t) ^ 2 ≤ 2 / 1e16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq'
    have b : 11 / (j * t) ^ 2 ≤ 11 / 1e16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq'
    have c : κ * (11 / (j * t) ^ 2) ≤ 1 * (11 / 1e16) :=
      mul_le_mul (by linarith) b (by positivity) (by norm_num)
    have e : 2 / (j * t) ^ 2 + 1 / 2 * κ * (0.20604 + 11 / (j * t) ^ 2) =
        1 / 2 * κ * 0.20604 + (2 / (j * t) ^ 2 + 1 / 2 * (κ * (11 / (j * t) ^ 2))) := by ring
    rw [e]
    norm_num at a c ⊢
    linarith
  have t1 := tt 1 le_rfl
  have t2 := tt 2 (by norm_num)
  have t3 := tt 3 (by norm_num)
  have t4 := tt 4 (by norm_num)
  rw [one_mul] at t1
  -- the zero term
  have hsb : 0 < σ - β := by linarith
  have hsb' : σ - β ≤ 0.40091 / L := by
    have h1 : σ - β < 0.31 / L + 1 / (11 * L) := by linarith only [hβ, hσ]
    have e : 0.31 / L + 1 / (11 * L) = (0.31 + 1 / 11) / L := by field_simp
    have e2 : (0.31 + 1 / 11) / L ≤ 0.40091 / L := div_le_div_of_nonneg_right (by norm_num) hL0.le
    linarith
  have hZ1 : 2.4943 * L ≤ 1 / (σ - β) := by
    rw [le_div_iff₀ hsb]; rw [le_div_iff₀ hL0] at hsb'; linarith only [hsb']
  have hZ2 : 1 / σ ≤ 1 / (σ + β - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hZ3 : 1 / (1.6181 - β) ≤ 1 / 0.6181 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hZ4 : 1 / (1.6181 + β - 1) ≤ 1 / 1.5681 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hσinv : 0.9834 ≤ 1 / σ := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσinv2 : 1.9668 ≤ 2 / σ := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσinv3 : 0.6629 ≤ 1 / (σ / 2 + 1) := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσ1L : 1 / (σ - 1) = 100 / 31 * L := by rw [hσ]; field_simp; ring
  have hlogσ : Real.log (σ / 2 + 2) ≤ 0.9197 := (Real.log_le_log (by linarith) (by linarith)).trans l2508
  have hσinv1 : 1 / σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- products with `κ`
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = 1 / 1.6181 + 1 / (1.6181 - 1) - 1 / 2 * Real.log π +
      1 / 2 * (Real.log (1.6181 / 2 + 2) - 2 / 1.6181 - 1 / (1.6181 / 2 + 1)) := ⟨_, rfl⟩
  have hE1u : E1 ≤ 1.2857 := by
    have := log280905_le
    rw [hE1, show (1.6181 : ℝ) / 2 + 2 = 2.80905 by norm_num]; norm_num; linarith
  have hE1l : 0 ≤ E1 := by
    rw [hE1, show (1.6181 : ℝ) / 2 + 2 = 2.80905 by norm_num]
    have : 0 ≤ Real.log 2.80905 := Real.log_nonneg (by norm_num)
    norm_num; linarith
  have pE : κ * E1 ≤ 0.5944 := by
    calc κ * E1 ≤ 0.46226 * E1 := mul_le_mul_of_nonneg_right hκu hE1l
      _ ≤ 0.46226 * 1.2857 := by gcongr
      _ ≤ 0.5944 := by norm_num
  have pW : ∀ X : ℝ, 0 ≤ X → (1 - κ) * X ≤ 0.5529 * X := fun X hX =>
    mul_le_mul_of_nonneg_right (by linarith) hX
  have pW1 := pW (1 / 2 * L + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW2 := pW (1 / 2 * (Real.log 2 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW3 := pW (1 / 2 * (Real.log 3 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW4 := pW (1 / 2 * (2 * Real.log 2 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pZ : κ * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) ≤ 1.0427 := by
    have : 0 ≤ 1 / (1.6181 - β) + 1 / (1.6181 + β - 1) := by
      have : 0 < 1.6181 - β := by linarith
      have : 0 < 1.6181 + β - 1 := by linarith
      positivity
    calc κ * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) ≤ 0.46226 * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) :=
          mul_le_mul_of_nonneg_right hκu this
      _ ≤ 0.46226 * (1 / 0.6181 + 1 / 1.5681) := by gcongr
      _ ≤ 1.0427 := by norm_num
  -- the positivity and the five terms
  have hP := vM_positivity hσ1 t
  rw [show (0:ℝ) * t = 0 by ring, show (1:ℝ) * t = t by ring] at hP
  have h0 := vM_real_le hσ1
  rw [hσ1L] at h0
  have Z1 := stech_wrap_rho hσ1 (by linarith) hρ hβh
  rw [← htdef, ← hβdef] at Z1
  have h1 := vM_term_le hσ1 (by linarith) (show (10:ℝ) ≤ t by linarith) Z1
  have h2 := vM_term_le (τ := 2 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 2 * t) hσ1 (by linarith))
  have h3 := vM_term_le (τ := 3 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 3 * t) hσ1 (by linarith))
  have h4 := vM_term_le (τ := 4 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 4 * t) hσ1 (by linarith))
  rw [← hκ, ← hE1] at h1 h2 h3 h4
  have lt2 : Real.log (2 * t) = Real.log 2 + L := by rw [Real.log_mul (by norm_num) ht0.ne', hLdef]
  have lt3 : Real.log (3 * t) = Real.log 3 + L := by rw [Real.log_mul (by norm_num) ht0.ne', hLdef]
  have lt4 : Real.log (4 * t) = 2 * Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) ht0.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hLdef]; push_cast; ring
  rw [← hLdef] at h1
  rw [lt2] at h2
  rw [lt3] at h3
  rw [lt4] at h4
  linarith only [hP, h0, h1, h2, h3, h4, t1, t2, t3, t4, hZ1, hZ2, hσinv, hσinv1, hσinv2, hσinv3, hlogσ,
    lπ, l2, l3, pE, pW1, pW2, pW3, pW4, pZ, hκu, hκl, hL]

/-- **Zero-free region**: every zero `ρ = β + iγ` of `ξ` (equivalently a nontrivial zero of `ζ`) with
`|γ| ≥ 10⁸` has `β ≤ 1 − 1/(11 log|γ|)`. -/
theorem zero_free {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1e8 ≤ |ρ.im|) :
    ρ.re ≤ 1 - 1 / (11 * Real.log |ρ.im|) := by
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at ht ⊢; exact zero_free_pos hρ ht
  · have hc : xiF (conj ρ) = 0 := by rw [xiF_conj, hρ, map_zero]
    have := zero_free_pos hc (by simpa [abs_of_neg h] using ht)
    simpa [abs_of_neg h] using this

end TernaryGoldbach.Explicit
