import TernaryGoldbach.MinorArcs.Eta2DDExpand

/-!
# `‖η̂₂''(t)‖ ≤ 32` for `0 ≤ t ≤ 2`: Taylor polynomials and a kernel-checked grid

Put `x = 2πt`. Then `e(−ut) = exp(−iux)`, and expanding each exponential in `eta2DD` to `N = 50`
terms (`Complex.exp_bound'`) gives

`eta2DD(x/2π) = P(x) + O*(120 |x|^N/N!)`,  `P(x) = ∑_{j<N} β_j (−ix)^j/j!`

for `|x| ≤ 12.6` (`norm_eta2DD_sub_P`). Here
`β_j = 16·2^{−j} − 16·4^{−j} − 4 + 4∫_{1/4}^{1/2} u^{j−2} du − 4∫_{1/2}^1 u^{j−2} du`
is rational (`β₀ = β₁ = 0`: the logarithms of `j = 1` cancel). `eta2DD(x/2π)` is `24`-Lipschitz in
`x` (`norm_eta2DD_sub_le`). The kernel evaluates `P` exactly over `ℚ` at the centres of a bisection
of `[0, 12.6]` (`chkC`).
-/

open Real Complex MeasureTheory Finset

namespace TernaryGoldbach.MinorArcs

/-- `e(−u · x/2π) = exp(−iux)`. -/
theorem e_eq_cexp (u x : ℝ) : e (-(u * (x / (2 * π)))) = cexp (-I * ((u * x : ℝ) : ℂ)) := by
  unfold e; congr 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast; field_simp

/-! ## Lipschitz bound -/

theorem norm_five_le (A B C D F : ℂ) : ‖A - B - C + D - F‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ := by
  have := norm_sub_le (A - B - C + D) F
  have := norm_add_le (A - B - C) D
  have := norm_sub_le (A - B) C
  have := norm_sub_le A B
  linarith

theorem norm_cexp_sub_le (y y' : ℝ) :
    ‖cexp (-I * (y : ℂ)) - cexp (-I * (y' : ℂ))‖ ≤ |y - y'| := by
  have h : cexp (-I * (y : ℂ)) - cexp (-I * (y' : ℂ)) =
      cexp (-I * (y' : ℂ)) * (cexp (I * ((-(y - y') : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h, norm_mul]
  have h1 : ‖cexp (-I * (y' : ℂ))‖ = 1 := by
    rw [show -I * (y' : ℂ) = ((-y' : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_neg]

theorem norm_Jq_sub_le {a b x x' : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖Jq a b (x / (2 * π)) - Jq a b (x' / (2 * π))‖ ≤ |x - x'| / a * (b - a) := by
  have hpos : ∀ u ∈ Set.uIcc a b, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  have hint : ∀ y : ℝ, IntervalIntegrable (fun u => e (-(u * y)) * (((u ^ 2)⁻¹ : ℝ) : ℂ)) volume a b :=
    fun y => ((continuous_E y).continuousOn.mul
      (continuous_ofReal.comp_continuousOn (by
        simpa using continuousOn_inv_pow ha hab 1 2))).intervalIntegrable
  unfold Jq
  rw [← intervalIntegral.integral_sub (hint _) (hint _)]
  have hb : |b - a| = b - a := abs_of_nonneg (by linarith)
  rw [← hb]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
  have hu' : u ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hu
  have hu0 := hpos u hu'
  have hau : a ≤ u := by rw [Set.uIcc_of_le hab] at hu'; exact hu'.1
  rw [← sub_mul, norm_mul, e_eq_cexp, e_eq_cexp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h1 := norm_cexp_sub_le (u * x) (u * x')
  rw [show u * x - u * x' = u * (x - x') by ring, abs_mul, abs_of_pos hu0] at h1
  calc ‖cexp (-I * ((u * x : ℝ) : ℂ)) - cexp (-I * ((u * x' : ℝ) : ℂ))‖ * (u ^ 2)⁻¹
      ≤ u * |x - x'| * (u ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = |x - x'| / u := by field_simp
    _ ≤ |x - x'| / a := div_le_div_of_nonneg_left (abs_nonneg _) ha hau

theorem norm_e_sub_le (u x x' : ℝ) (hu : 0 ≤ u) :
    ‖e (-(u * (x / (2 * π)))) - e (-(u * (x' / (2 * π))))‖ ≤ u * |x - x'| := by
  rw [e_eq_cexp, e_eq_cexp]
  refine (norm_cexp_sub_le _ _).trans (le_of_eq ?_)
  rw [show u * x - u * x' = u * (x - x') by ring, abs_mul, abs_of_nonneg hu]

/-- **`eta2DD(x/2π)` is `24`-Lipschitz in `x`.** -/
theorem norm_eta2DD_sub_le (x x' : ℝ) :
    ‖eta2DD (x / (2 * π)) - eta2DD (x' / (2 * π))‖ ≤ 24 * |x - x'| := by
  have h1 := norm_e_sub_le (1 / 2) x x' (by norm_num)
  have h2 := norm_e_sub_le (1 / 4) x x' (by norm_num)
  have h3 := norm_e_sub_le 1 x x' (by norm_num)
  have h4 := norm_Jq_sub_le (a := 1 / 4) (b := 1 / 2) (x := x) (x' := x') (by norm_num) (by norm_num)
  have h5 := norm_Jq_sub_le (a := 1 / 2) (b := 1) (x := x) (x' := x') (by norm_num) (by norm_num)
  have hE : eta2DD (x / (2 * π)) - eta2DD (x' / (2 * π)) =
      16 * (e (-(1 / 2 * (x / (2 * π)))) - e (-(1 / 2 * (x' / (2 * π))))) -
      16 * (e (-(1 / 4 * (x / (2 * π)))) - e (-(1 / 4 * (x' / (2 * π))))) -
      4 * (e (-(1 * (x / (2 * π)))) - e (-(1 * (x' / (2 * π))))) +
      4 * (Jq (1 / 4) (1 / 2) (x / (2 * π)) - Jq (1 / 4) (1 / 2) (x' / (2 * π))) -
      4 * (Jq (1 / 2) 1 (x / (2 * π)) - Jq (1 / 2) 1 (x' / (2 * π))) := by
    unfold eta2DD; ring
  rw [hE]
  have n4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  have n16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  have hd := abs_nonneg (x - x')
  refine (norm_five_le _ _ _ _ _).trans ?_
  simp only [norm_mul, n4, n16]
  norm_num at h4 h5
  nlinarith

/-! ## Taylor expansion -/

/-- `T_N(y) = ∑_{j<N} (−iy)^j/j!`. -/
noncomputable def TN (N : ℕ) (y : ℝ) : ℂ := ∑ j ∈ range N, (-I * y) ^ j / j.factorial

theorem norm_cexp_sub_TN {N : ℕ} {y : ℝ} (hy : |y| / (N + 1) ≤ 1 / 2) :
    ‖cexp (-I * (y : ℂ)) - TN N y‖ ≤ |y| ^ N / N.factorial * 2 := by
  have hn : ‖-I * (y : ℂ)‖ = |y| := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := Complex.exp_bound' (x := -I * (y : ℂ)) (n := N) (by rw [hn]; push_cast; exact hy)
  rw [hn] at h
  exact h

/-- `∫_a^b u^j/u² du`. -/
noncomputable def mom (a b : ℝ) (j : ℕ) : ℝ := ∫ u in a..b, u ^ j * (u ^ 2)⁻¹

/-- `β_j`. -/
noncomputable def βR (j : ℕ) : ℝ :=
  16 * (1 / 2) ^ j - 16 * (1 / 4) ^ j - 4 + 4 * mom (1 / 4) (1 / 2) j - 4 * mom (1 / 2) 1 j

/-- `P(x) = ∑_{j<N} β_j (−ix)^j/j!`. -/
noncomputable def PN (N : ℕ) (x : ℝ) : ℂ := ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (βR j : ℂ)

/-- `J(a, b)` against the Taylor polynomial: `∫_a^b T_N(ux)/u² du = ∑_j (−ix)^j/j! · mom(a, b, j)`. -/
theorem integral_TN {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (x : ℝ) :
    ∫ u in a..b, TN N (u * x) * (((u ^ 2)⁻¹ : ℝ) : ℂ) =
      ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (mom a b j : ℂ) := by
  have hc : ∀ j : ℕ, ContinuousOn (fun u : ℝ => u ^ j * (u ^ 2)⁻¹) (Set.uIcc a b) := fun j =>
    (continuous_pow j).continuousOn.mul (by simpa using continuousOn_inv_pow ha hab 1 2)
  have e1 : ∀ u : ℝ, TN N (u * x) * (((u ^ 2)⁻¹ : ℝ) : ℂ) =
      ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (((u ^ j * (u ^ 2)⁻¹ : ℝ)) : ℂ) := by
    intro u
    rw [TN, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; rw [mul_pow, mul_pow, mul_pow]; ring
  simp_rw [e1]
  rw [intervalIntegral.integral_finsetSum
    (f := fun (j : ℕ) (u : ℝ) => (-I * (x : ℂ)) ^ j / (j.factorial : ℂ) * (((u ^ j * (u ^ 2)⁻¹ : ℝ)) : ℂ))
    fun j _ => (continuousOn_const.mul (continuous_ofReal.comp_continuousOn (hc j))).intervalIntegrable]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, mom]

theorem norm_Jq_sub_TN {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) {N : ℕ} {x : ℝ}
    (hx : |x| / (N + 1) ≤ 1 / 2) :
    ‖Jq a b (x / (2 * π)) - ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (mom a b j : ℂ)‖ ≤
      |x| ^ N / N.factorial * 2 * (a ^ 2)⁻¹ * (b - a) := by
  have hpos : ∀ u ∈ Set.uIcc a b, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  have hci : ContinuousOn (fun u : ℝ => (((u ^ 2)⁻¹ : ℝ) : ℂ)) (Set.uIcc a b) :=
    continuous_ofReal.comp_continuousOn (by simpa using continuousOn_inv_pow ha hab 1 2)
  have hJ : Jq a b (x / (2 * π)) = ∫ u in a..b, cexp (-I * ((u * x : ℝ) : ℂ)) * (((u ^ 2)⁻¹ : ℝ) : ℂ) := by
    unfold Jq; congr 1; ext u; rw [e_eq_cexp]
  have hTc : Continuous fun u : ℝ => TN N (u * x) := by unfold TN; fun_prop
  rw [hJ, ← integral_TN ha hab N x, ← intervalIntegral.integral_sub
    (f := fun u : ℝ => cexp (-I * ((u * x : ℝ) : ℂ)) * (((u ^ 2)⁻¹ : ℝ) : ℂ))
    (g := fun u : ℝ => TN N (u * x) * (((u ^ 2)⁻¹ : ℝ) : ℂ))
    ((Continuous.continuousOn (by fun_prop)).mul hci |>.intervalIntegrable)
    (hTc.continuousOn.mul hci |>.intervalIntegrable)]
  have hb : |b - a| = b - a := abs_of_nonneg (by linarith)
  rw [← hb]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
  have hu' : u ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hu
  have hu0 := hpos u hu'
  have hu1 : u ≤ 1 := by rw [Set.uIcc_of_le hab] at hu'; exact hu'.2.trans hb1
  have hau : a ≤ u := by rw [Set.uIcc_of_le hab] at hu'; exact hu'.1
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hux : |u * x| ≤ |x| := by
    rw [abs_mul, abs_of_pos hu0]; exact mul_le_of_le_one_left (abs_nonneg _) hu1
  have h1 := norm_cexp_sub_TN (N := N) (y := u * x) ((div_le_div_of_nonneg_right hux (by positivity)).trans hx)
  have h2 : |u * x| ^ N / N.factorial * 2 ≤ |x| ^ N / N.factorial * 2 := by
    gcongr
  have h3 : (u ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hau 2)
  exact mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)

/-- **`eta2DD(x/2π) = P_N(x) + O*(120 |x|^N/N!)`** for `|x|/(N + 1) ≤ 1/2`. -/
theorem norm_eta2DD_sub_P {N : ℕ} {x : ℝ} (hx : |x| / (N + 1) ≤ 1 / 2) :
    ‖eta2DD (x / (2 * π)) - PN N x‖ ≤ 120 * (|x| ^ N / N.factorial) := by
  have hy : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |u * x| / (N + 1) ≤ 1 / 2 := fun u h0 h1 => by
    refine le_trans ?_ hx
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
  have hT : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖e (-(u * (x / (2 * π)))) - TN N (u * x)‖ ≤ |x| ^ N / N.factorial * 2 := by
    intro u h0 h1
    rw [e_eq_cexp]
    refine (norm_cexp_sub_TN (hy u h0 h1)).trans ?_
    have : |u * x| ≤ |x| := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
    gcongr
  have e1 := hT (1 / 2) (by norm_num) (by norm_num)
  have e2 := hT (1 / 4) (by norm_num) (by norm_num)
  have e3 := hT 1 (by norm_num) le_rfl
  have j1 := norm_Jq_sub_TN (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) hx
  have j2 := norm_Jq_sub_TN (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) le_rfl hx
  set S1 := ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (mom (1 / 4) (1 / 2) j : ℂ)
  set S2 := ∑ j ∈ range N, (-I * x) ^ j / j.factorial * (mom (1 / 2) 1 j : ℂ)
  have hP : PN N x = 16 * TN N (1 / 2 * x) - 16 * TN N (1 / 4 * x) - 4 * TN N (1 * x) +
      4 * S1 - 4 * S2 := by
    simp only [PN, TN, S1, S2, βR, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
    ring
  have hE : eta2DD (x / (2 * π)) - PN N x =
      16 * (e (-(1 / 2 * (x / (2 * π)))) - TN N (1 / 2 * x)) -
      16 * (e (-(1 / 4 * (x / (2 * π)))) - TN N (1 / 4 * x)) -
      4 * (e (-(1 * (x / (2 * π)))) - TN N (1 * x)) +
      4 * (Jq (1 / 4) (1 / 2) (x / (2 * π)) - S1) - 4 * (Jq (1 / 2) 1 (x / (2 * π)) - S2) := by
    rw [hP]; unfold eta2DD; ring
  rw [hE]
  have n4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  have n16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  have hX : 0 ≤ |x| ^ N / N.factorial := by positivity
  refine (norm_five_le _ _ _ _ _).trans ?_
  simp only [norm_mul, n4, n16]
  norm_num at j1 j2
  nlinarith

/-! ## `β_j` is rational -/

/-- `β_j` over `ℚ`. -/
def βq : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | k + 2 => 16 / 2 ^ (k + 2) - 16 / 4 ^ (k + 2) - 4 +
      4 * ((1 / 2) ^ (k + 1) - (1 / 4) ^ (k + 1)) / (k + 1) - 4 * (1 - (1 / 2) ^ (k + 1)) / (k + 1)

theorem mom_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : mom a b 0 = a⁻¹ - b⁻¹ := by
  unfold mom
  have hpos : ∀ u ∈ Set.uIcc a b, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun v : ℝ => -v⁻¹) (u ^ 0 * (u ^ 2)⁻¹) u := by
    intro u hu
    have := (hasDerivAt_inv (hpos u hu).ne').neg
    convert this using 1; simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_const.mul (by simpa using continuousOn_inv_pow ha hab 1 2)).intervalIntegrable)]
  ring

theorem mom_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : mom a b 1 = Real.log (b / a) := by
  unfold mom
  have hpos : ∀ u ∈ Set.uIcc a b, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  rw [intervalIntegral.integral_congr (g := fun u : ℝ => u⁻¹) fun u hu => by
    have := (hpos u hu).ne'
    simp only; field_simp]
  exact integral_inv_of_pos ha (ha.trans_le hab)

theorem mom_add_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    mom a b (k + 2) = (b ^ (k + 1) - a ^ (k + 1)) / (k + 1) := by
  unfold mom
  have hpos : ∀ u ∈ Set.uIcc a b, 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  rw [intervalIntegral.integral_congr (g := fun u : ℝ => u ^ k) fun u hu => by
    have := (hpos u hu).ne'
    simp only; field_simp; ring]
  rw [integral_pow]

theorem βR_eq (j : ℕ) : βR j = βq j := by
  match j with
  | 0 => simp only [βR, βq, mom_zero (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num),
            mom_zero (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)]; norm_num
  | 1 =>
    simp only [βR, βq, mom_one (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num),
      mom_one (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)]
    rw [show (1 / 2 : ℝ) / (1 / 4) = 2 by norm_num, show (1 : ℝ) / (1 / 2) = 2 by norm_num]
    norm_num
  | k + 2 =>
    simp only [βR, βq, mom_add_two (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num),
      mom_add_two (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)]
    push_cast
    simp only [one_div_pow, one_pow]
    field_simp

/-! ## The kernel check -/

/-- `γ_j = β_j/j!`. -/
def γq (j : ℕ) : ℚ := βq j / j.factorial

def smulQ (c : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (c * p.1, c * p.2)

/-- `s + ∑_{i<k} γ_{j+i} p y^i` with `y = −ix`, by a walk. -/
def serAux (x : ℚ) : ℕ → ℕ → ℚ × ℚ → ℚ × ℚ → ℚ × ℚ
  | 0, _, s, _ => s
  | k + 1, j, s, p => serAux x k (j + 1) (cadd s (smulQ (γq j) p)) (cmul p (0, -x))

theorem toC_smulQ (c : ℚ) (p : ℚ × ℚ) : toC (smulQ c p) = (c : ℂ) * toC p := by
  apply Complex.ext <;> simp [toC, smulQ]

theorem serAux_spec (x : ℚ) : ∀ (k j : ℕ) (s p : ℚ × ℚ),
    toC (serAux x k j s p) = toC s + ∑ i ∈ range k, (γq (j + i) : ℂ) * toC p * (-I * (x : ℝ)) ^ i
  | 0, j, s, p => by simp [serAux]
  | k + 1, j, s, p => by
    rw [serAux, serAux_spec x k, toC_cadd, toC_smulQ, toC_cmul, Finset.sum_range_succ']
    have hy : toC ((0 : ℚ), -x) = -I * ((x : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [toC]
    rw [hy]
    simp only [add_zero, pow_zero, mul_one]
    have : ∀ i ∈ range k, (γq (j + 1 + i) : ℂ) * (toC p * (-I * ((x : ℝ) : ℂ))) *
        (-I * ((x : ℝ) : ℂ)) ^ i = (γq (j + (i + 1)) : ℂ) * toC p * (-I * ((x : ℝ) : ℂ)) ^ (i + 1) := by
      intro i _; rw [show j + 1 + i = j + (i + 1) by ring]; ring
    rw [Finset.sum_congr rfl this]
    ring

/-- `P_N(x)` over `ℚ`. -/
def PQ (N : ℕ) (x : ℚ) : ℚ × ℚ := serAux x N 0 (0, 0) (1, 0)

theorem toC_PQ (N : ℕ) (x : ℚ) : toC (PQ N x) = PN N x := by
  rw [PQ, serAux_spec]
  have h0 : toC ((0 : ℚ), (0 : ℚ)) = 0 := by apply Complex.ext <;> simp [toC]
  have h1 : toC ((1 : ℚ), (0 : ℚ)) = 1 := by apply Complex.ext <;> simp [toC]
  rw [h0, h1, zero_add, PN]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add, γq, βR_eq]; push_cast; ring

/-- The order of the Taylor polynomials and the end of the range. -/
def Nc : ℕ := 50
def Xc : ℚ := 63 / 5

/-- `120 X^N/N!`. -/
def errC : ℚ := 120 * Xc ^ Nc / Nc.factorial

def cellC (x0 x1 : ℚ) : Bool :=
  let F := PQ Nc ((x0 + x1) / 2)
  let M := 32 - 12 * (x1 - x0) - errC
  decide (0 ≤ M) && decide (F.1 ^ 2 + F.2 ^ 2 ≤ M ^ 2)

def chkC : ℕ → ℚ → ℚ → Bool
  | 0, x0, x1 => cellC x0 x1
  | n + 1, x0, x1 => cellC x0 x1 || (chkC n x0 ((x0 + x1) / 2) && chkC n ((x0 + x1) / 2) x1)

def GoodC (x0 x1 : ℚ) : Prop :=
  ∀ x : ℝ, (x0 : ℝ) ≤ x → x ≤ x1 → ‖eta2DD (x / (2 * π))‖ ≤ 32

theorem cellC_sound {x0 x1 : ℚ} (h0 : 0 ≤ x0) (h1 : x1 ≤ Xc) (h : cellC x0 x1 = true) :
    GoodC x0 x1 := by
  intro x hx0 hx1
  simp only [cellC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hF⟩ := h
  set xc : ℚ := (x0 + x1) / 2
  set F := PQ Nc xc
  set M : ℚ := 32 - 12 * (x1 - x0) - errC
  have hx01 : (x0 : ℝ) ≤ x1 := hx0.trans hx1
  have hxc0 : (0 : ℝ) ≤ xc := by
    have : (0 : ℝ) ≤ x0 := by exact_mod_cast h0
    simp only [xc]; push_cast; linarith
  have hxcX : (xc : ℝ) ≤ Xc := by
    have : (x1 : ℝ) ≤ Xc := by exact_mod_cast h1
    simp only [xc]; push_cast; linarith
  -- Taylor at the centre
  have hcond : |(xc : ℝ)| / (Nc + 1) ≤ 1 / 2 := by
    rw [abs_of_nonneg hxc0, div_le_iff₀ (by positivity)]
    simp only [Nc, Xc] at hxcX ⊢; push_cast at hxcX ⊢; linarith
  have hT := norm_eta2DD_sub_P hcond
  have hPc : ‖PN Nc xc‖ ≤ M := by
    rw [← toC_PQ]
    have h1 := norm_sq_toC F
    have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
    have hF' : ((F.1 ^ 2 + F.2 ^ 2 : ℚ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hF
    exact (sq_le_sq₀ (norm_nonneg _) hM').1 (h1 ▸ hF')
  have herr : 120 * (|(xc : ℝ)| ^ Nc / Nc.factorial) ≤ errC := by
    rw [abs_of_nonneg hxc0]
    have : (xc : ℝ) ^ Nc ≤ (Xc : ℝ) ^ Nc := pow_le_pow_left₀ hxc0 hxcX Nc
    simp only [errC]; push_cast
    have hf : (0 : ℝ) < Nc.factorial := by exact_mod_cast Nat.factorial_pos _
    rw [mul_div_assoc]
    gcongr
  have hL := norm_eta2DD_sub_le x xc
  have hd : |x - (xc : ℝ)| ≤ ((x1 : ℝ) - x0) / 2 := by
    simp only [xc]; push_cast; rw [abs_le]; constructor <;> linarith
  have hMdef : (M : ℝ) = 32 - 12 * ((x1 : ℝ) - x0) - errC := by simp only [M]; push_cast; ring
  have := norm_sub_norm_le (eta2DD (x / (2 * π))) (eta2DD ((xc : ℝ) / (2 * π)))
  have := norm_sub_norm_le (eta2DD ((xc : ℝ) / (2 * π))) (PN Nc xc)
  linarith

theorem chkC_sound : ∀ (n : ℕ) (x0 x1 : ℚ), 0 ≤ x0 → x1 ≤ Xc → chkC n x0 x1 = true → GoodC x0 x1
  | 0, x0, x1, h0, h1, h => cellC_sound h0 h1 h
  | n + 1, x0, x1, h0, h1, h => by
    simp only [chkC, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact cellC_sound h0 h1 h
    · intro x hx0 hx1
      have hx01 : x0 ≤ x1 := by exact_mod_cast hx0.trans hx1
      rcases le_total x (((x0 + x1) / 2 : ℚ) : ℝ) with hx | hx
      · exact chkC_sound n _ _ h0 (by linarith) ha x hx0 hx
      · exact chkC_sound n _ _ (by linarith) h1 hb x hx hx1

end TernaryGoldbach.MinorArcs
