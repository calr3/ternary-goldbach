import TernaryGoldbach.CircleMethod

/-!
# Exponential sums via Fourier analysis [B, §2.3]

* `hasSum_inv_sq_sub`: `∑_{n ∈ ℤ} 1/(n - s)² = π²/sin²(πs)` for `s ∉ ℤ` (via Parseval for `e(sx)`
  on `[0, 1]`, rather than by differentiating the cotangent series as in [B, (2.4)]).
* `tsum_inv_sq_sub_le`: `∑_{n ≠ 0} 1/(n - r)² ≤ π² - 4` for `|r| ≤ 1/2` [B, (4.12)].
* `norm_tsum_le_of_fourier_bound`: **[B, Lemma 2.3.1]**, by Poisson summation (Mathlib's
  `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`).
* `norm_tsum_le_variation`, `tsum_norm_le_variation`: the two bounds of [B, (2.2)], with `|f'|₁`
  replaced by the total variation of `f` (which equals `|f'|₁` for piecewise `C¹` `f`).

Proved, with no `sorry`.
-/

open Complex MeasureTheory intervalIntegral Real

namespace TernaryGoldbach

theorem e_eq_cos_sin (t : ℝ) : e t = Real.cos (2 * π * t) + Real.sin (2 * π * t) * I := by
  rw [e, show (2 * (π : ℂ) * I * t) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

theorem norm_e_sub_one_sq (s : ℝ) : ‖e s - 1‖ ^ 2 = 4 * Real.sin (π * s) ^ 2 := by
  rw [e_eq_cos_sin, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
  have h2 : 2 * π * s = 2 * (π * s) := by ring
  rw [h2, Real.cos_two_mul, Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

theorem e_intCast (n : ℤ) : e n = 1 := by
  rw [e, show (2 * (π : ℂ) * I * (n : ℝ)) = n * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- Fourier coefficients of `x ↦ e(sx)` on `[0, 1]`. -/
theorem fourierCoeffOn_e_mul {s : ℝ} (n : ℤ) (hs : s ≠ n) :
    fourierCoeffOn zero_lt_one (fun x => e (s * x)) n = (e s - 1) / (2 * π * I * (s - n)) := by
  have hc : (2 * π * I * ((s : ℂ) - n)) ≠ 0 := by
    have : ((s : ℂ) - n) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hs
    simp [Real.pi_ne_zero, I_ne_zero, this]
  rw [fourierCoeffOn_eq_integral]
  have : ∀ x : ℝ, fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • e (s * x) =
      cexp (2 * π * I * (s - n) * x) := by
    intro x
    rw [fourier_coe_apply, e, smul_eq_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [this]
  rw [integral_exp_mul_complex hc]
  have he : cexp (2 * π * I * (s - n) * (1 : ℝ)) = e s := by
    rw [show (2 * (π : ℂ) * I * (s - n) * ((1 : ℝ) : ℂ)) = 2 * π * I * ((s - n : ℝ) : ℂ) by
      push_cast; ring, ← e, sub_eq_add_neg, e_add, show (-(n : ℝ)) = ((-n : ℤ) : ℝ) by push_cast; ring,
      e_intCast, mul_one]
  rw [he]; simp

/-- `∑_{n ∈ ℤ} 1/(n - s)² = π²/sin²(πs)` for `s ∉ ℤ`, via Parseval for `e(sx)` on `[0, 1]`. -/
theorem hasSum_inv_sq_sub {s : ℝ} (hs : Real.sin (π * s) ≠ 0) :
    HasSum (fun n : ℤ => 1 / ((n : ℝ) - s) ^ 2) (π ^ 2 / Real.sin (π * s) ^ 2) := by
  have hsn : ∀ n : ℤ, s ≠ n := by
    intro n h; apply hs; rw [h, mul_comm]; exact Real.sin_int_mul_pi n
  have hL2 : MemLp (fun x : ℝ => e (s * x)) 2 (volume.restrict (Set.Ioc 0 1)) :=
    MemLp.of_bound ((continuous_e.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
      1 (ae_of_all _ fun x => by simp [norm_e])
  have h := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  simp only [norm_e, one_pow, intervalIntegral.integral_const, sub_zero, inv_one,
    smul_eq_mul, mul_one] at h
  have hterm : ∀ n : ℤ, ‖fourierCoeffOn zero_lt_one (fun x => e (s * x)) n‖ ^ 2 =
      Real.sin (π * s) ^ 2 / π ^ 2 * (1 / ((n : ℝ) - s) ^ 2) := by
    intro n
    have hne : (s : ℝ) - n ≠ 0 := sub_ne_zero.2 (hsn n)
    rw [fourierCoeffOn_e_mul n (hsn n), norm_div, div_pow, norm_e_sub_one_sq]
    have : ‖(2 * π * I * ((s : ℂ) - n))‖ = 2 * π * |s - n| := by
      have h1 : ((s : ℂ) - n) = ((s - n : ℝ) : ℂ) := by push_cast; ring
      rw [h1, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat, mul_one]
    rw [this]
    have : (n - s) ^ 2 = |s - n| ^ 2 := by rw [sq_abs]; ring
    rw [this]
    have := abs_pos.2 hne
    field_simp
    ring
  simp_rw [hterm] at h
  have hk : Real.sin (π * s) ^ 2 / π ^ 2 ≠ 0 := by positivity
  have := h.mul_left (π ^ 2 / Real.sin (π * s) ^ 2)
  convert this using 1
  · funext n; rw [← mul_assoc, div_mul_div_comm, mul_comm (π ^ 2), div_self (by positivity), one_mul]
  · ring


/-! ## Pairing `n` with `-n` -/

/-- If `f, g ≥ 0` on `ℤ` and `f(n) + f(-n) ≤ g(n) + g(-n)` for `n ∈ ℕ`, then `∑ f ≤ ∑ g`. -/
theorem summable_tsum_le_of_pair {f g : ℤ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hfg : ∀ n : ℕ, f n + f (-n) ≤ g n + g (-n)) (hg : Summable g) :
    Summable f ∧ ∑' n, f n ≤ ∑' n, g n := by
  have hG : Summable fun n : ℤ => g n + g (-n) := hg.add (hg.comp_injective neg_injective)
  have hle : ∀ n : ℤ, f n ≤ g n + g (-n) := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · linarith [hfg m, hf0 (-(m : ℤ))]
    · have := hfg m; rw [neg_neg]; linarith [hf0 (m : ℤ)]
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hle hG
  refine ⟨hf, ?_⟩
  have h1 := hf.hasSum.nat_add_neg
  have h2 := hg.hasSum.nat_add_neg
  have h3 := hasSum_le hfg h1 h2
  have hf00 : f 0 ≤ g 0 := by have := hfg 0; simp at this; linarith
  -- `h3 : ∑f + f 0 ≤ ∑g + g 0`; we need the version without the `0` terms.
  have h1' := (hf.hasSum.nat_add_neg).tsum_eq
  have hsplit : ∀ {h : ℤ → ℝ}, Summable h → ∑' n : ℕ, (h n + h (-n)) = ∑' n, h n + h 0 :=
    fun hh => hh.hasSum.nat_add_neg.tsum_eq
  -- Separate the `n = 0` terms.
  have hfs : Summable fun n : ℕ => f (n + 1 : ℕ) + f (-((n + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).2 h1.summable
  have hgs : Summable fun n : ℕ => g (n + 1 : ℕ) + g (-((n + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).2 h2.summable
  have ef := h1.summable.tsum_eq_zero_add
  have eg := h2.summable.tsum_eq_zero_add
  simp only [Nat.cast_zero, neg_zero] at ef eg
  rw [hsplit hf] at ef; rw [hsplit hg] at eg
  have : ∑' n : ℕ, (f (n + 1 : ℕ) + f (-((n + 1 : ℕ) : ℤ))) ≤
      ∑' n : ℕ, (g (n + 1 : ℕ) + g (-((n + 1 : ℕ) : ℤ))) :=
    hfs.tsum_le_tsum (fun n => hfg (n + 1)) hgs
  push_cast at ef eg this
  linarith

/-- `1/(n-r)² + 1/(n+r)²` increases with `|r| ≤ 1/2`, for `n ≥ 1`. -/
theorem pair_le_half {n r : ℝ} (hn : 1 ≤ n) (hr : |r| ≤ 1 / 2) :
    1 / (n - r) ^ 2 + 1 / (n + r) ^ 2 ≤ 1 / (n - 1 / 2) ^ 2 + 1 / (n + 1 / 2) ^ 2 := by
  have hr2 : r ^ 2 ≤ 1 / 4 := by
    have := sq_abs r ▸ pow_le_pow_left₀ (abs_nonneg r) hr 2; linarith
  have h1 : 0 < n - r := by linarith [neg_abs_le r, le_abs_self r]
  have h2 : 0 < n + r := by linarith [neg_abs_le r, le_abs_self r]
  have h3 : 0 < n - 1 / 2 := by linarith
  have h4 : 0 < n + 1 / 2 := by linarith
  have E : ∀ t, 0 < n - t → 0 < n + t →
      1 / (n - t) ^ 2 + 1 / (n + t) ^ 2 = 2 * (n ^ 2 + t ^ 2) / (n ^ 2 - t ^ 2) ^ 2 := by
    intro t ht1 ht2
    have : n ^ 2 - t ^ 2 = (n - t) * (n + t) := by ring
    rw [this]; field_simp; ring
  have e1 := E r h1 h2
  have e2 := E (1 / 2) h3 h4
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num] at e2
  rw [e1, e2]
  have ha : 0 < n ^ 2 - r ^ 2 := by nlinarith
  have hb : 0 < n ^ 2 - 1 / 4 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `(N+a)(N-b)² ≤ (N+b)(N-a)²` with `a = r² ≤ b = 1/4`, `N = n² ≥ 1`.
  have hN : 1 ≤ n ^ 2 := by nlinarith
  have key : (n ^ 2 + 1 / 4) * (n ^ 2 - r ^ 2) ^ 2 - (n ^ 2 + r ^ 2) * (n ^ 2 - 1 / 4) ^ 2 =
      (1 / 4 - r ^ 2) * (3 * (n ^ 2) ^ 2 - n ^ 2 * (r ^ 2 + 1 / 4) - r ^ 2 / 4) := by ring
  have : 0 ≤ (1 / 4 - r ^ 2) * (3 * (n ^ 2) ^ 2 - n ^ 2 * (r ^ 2 + 1 / 4) - r ^ 2 / 4) := by
    apply mul_nonneg (by linarith); nlinarith [sq_nonneg r]
  nlinarith

/-- `∑_{n ≠ 0} 1/(n - 1/2)² = π² - 4`. -/
theorem hasSum_inv_sq_sub_half :
    HasSum (fun n : ℤ => if n = 0 then 0 else 1 / ((n : ℝ) - 1 / 2) ^ 2) (π ^ 2 - 4) := by
  have h := hasSum_inv_sq_sub (s := 1 / 2) (by rw [mul_one_div, Real.sin_pi_div_two]; norm_num)
  rw [mul_one_div, Real.sin_pi_div_two, one_pow, div_one] at h
  have := h.update 0 0
  convert this using 1
  · funext n; by_cases hn : n = 0 <;> simp [hn, Function.update]
  · norm_num; ring

/-- **[B, (4.12)]**: for `|r| ≤ 1/2`, `∑_{n ≠ 0} 1/(n - r)² ≤ π² - 4` (and the sum converges). -/
theorem tsum_inv_sq_sub_le {r : ℝ} (hr : |r| ≤ 1 / 2) :
    Summable (fun n : ℤ => if n = 0 then 0 else 1 / ((n : ℝ) - r) ^ 2) ∧
      ∑' n : ℤ, (if n = 0 then 0 else 1 / ((n : ℝ) - r) ^ 2) ≤ π ^ 2 - 4 := by
  rw [← hasSum_inv_sq_sub_half.tsum_eq]
  refine summable_tsum_le_of_pair (fun n => by split_ifs <;> positivity) (fun n => ?_) hasSum_inv_sq_sub_half.summable
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [hn', neg_eq_zero, ite_false, Int.cast_neg, Int.cast_natCast]
  have e1 : (-(n : ℝ) - r) ^ 2 = (n + r) ^ 2 := by ring
  have e2 : (-(n : ℝ) - 1 / 2) ^ 2 = (n + 1 / 2) ^ 2 := by ring
  rw [e1, e2]
  exact pair_le_half hn1 hr


/-! ## Poisson summation and [B, Lemma 2.3.1] -/

open FourierTransform Filter Asymptotics

theorem fourierChar_eq_e (x : ℝ) : (Real.fourierChar x : ℂ) = e x := by
  rw [Real.fourierChar_apply, e]; congr 1; push_cast; ring

/-- `𝓕 f(ξ) = ∫ e(-vξ) f(v) dv`. -/
theorem fourier_eq_integral_e (f : ℝ → ℂ) (ξ : ℝ) : 𝓕 f ξ = ∫ v, e (-(v * ξ)) * f v := by
  rw [Real.fourier_real_eq]
  simp_rw [Circle.smul_def, fourierChar_eq_e, smul_eq_mul]

/-- Twisting by `e(αu)` translates the Fourier transform. -/
theorem fourier_mul_e (f : ℝ → ℂ) (α ξ : ℝ) :
    𝓕 (fun u => f u * e (α * u)) ξ = 𝓕 f (ξ - α) := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  congr 1; funext v
  rw [mul_comm (f v), ← mul_assoc, ← e_add]; congr 2; ring

theorem isBigO_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) (b : ℝ) :
    f =O[cocompact ℝ] (|·| ^ (-b)) := by
  refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [hf.isCompact.compl_mem_cocompact] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- **[B, Lemma 2.3.1]**, with `|f̂''|_∞ ≤ K` written as `(2πt)² |f̂(t)| ≤ K` (this is how the
bound on `η̂₂''` is stated, `eta2_fourier_bound`): for `f` continuous and compactly supported,
`|∑ₙ f(n) e(αn)| ≤ K / (4 sin²(πα))`. -/
theorem norm_tsum_le_of_fourier_bound {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    {K : ℝ} (hK : ∀ t, (2 * π * t) ^ 2 * ‖𝓕 f t‖ ≤ K) {α : ℝ} (hα : Real.sin (π * α) ≠ 0) :
    ‖∑' n : ℤ, f n * e (α * n)‖ ≤ K / (4 * Real.sin (π * α) ^ 2) := by
  set g : ℝ → ℂ := fun u => f u * e (α * u)
  have hg : Continuous g := hf.mul (continuous_e.comp (continuous_const.mul continuous_id))
  have hgs : HasCompactSupport g := hfs.mul_right
  have hαn : ∀ n : ℤ, (n : ℝ) - α ≠ 0 := by
    intro n h; apply hα
    rw [show α = n by linarith, mul_comm]; exact Real.sin_int_mul_pi n
  -- Pointwise bound on the Fourier side.
  have hpt : ∀ n : ℤ, ‖𝓕 g n‖ ≤ K / (4 * π ^ 2) * (1 / ((n : ℝ) - α) ^ 2) := by
    intro n
    rw [fourier_mul_e]
    have h := hK (n - α)
    have hpos : 0 < (2 * π * ((n : ℝ) - α)) ^ 2 := by
      have := hαn n; positivity
    rw [show K / (4 * π ^ 2) * (1 / ((n : ℝ) - α) ^ 2) = K / (2 * π * ((n : ℝ) - α)) ^ 2 by
      field_simp; ring]
    rw [le_div_iff₀ hpos]; linarith
  have hsum := hasSum_inv_sq_sub hα
  have hsumm : Summable fun n : ℤ => ‖𝓕 g n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.summable.mul_left _)
  -- Poisson summation at `x = 0`.
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hg one_lt_two
    (isBigO_of_hasCompactSupport hgs 2) hsumm.of_norm 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  change ‖∑' n : ℤ, g n‖ ≤ _
  rw [hP]
  calc ‖∑' n : ℤ, 𝓕 g n‖ ≤ ∑' n : ℤ, ‖𝓕 g n‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℤ, K / (4 * π ^ 2) * (1 / ((n : ℝ) - α) ^ 2) :=
        hsumm.tsum_le_tsum hpt (hsum.summable.mul_left _)
    _ = K / (4 * π ^ 2) * (π ^ 2 / Real.sin (π * α) ^ 2) := by rw [tsum_mul_left, hsum.tsum_eq]
    _ = _ := by field_simp

open Finset

/-- Abel summation: `∑_{i<L} fᵢ (cᵢ₊₁ - cᵢ) = ∑_{i<L} (fᵢ - fᵢ₊₁) cᵢ₊₁ + f_L c_L - f₀ c₀`. -/
theorem sum_range_by_parts' (f c : ℕ → ℂ) (L : ℕ) :
    ∑ i ∈ range L, f i * (c (i + 1) - c i) =
      ∑ i ∈ range L, (f i - f (i + 1)) * c (i + 1) + f L * c L - f 0 * c 0 := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- A compactly supported `f` vanishes at all integers outside `[-N, N]`, for some `N`. -/
theorem exists_nat_vanish {f : ℝ → ℂ} (hfs : HasCompactSupport f) :
    ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ |x| → f x = 0 := by
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  refine ⟨⌈R⌉₊ + 1, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have := Nat.le_ceil R
  push_cast at hx; linarith

/-- For `f` vanishing at integers outside `[-N, N]`, `∑_{n ∈ ℤ} F(n)` is a finite sum. -/
theorem tsum_int_eq_sum_range {F : ℤ → ℂ} {N : ℕ} (hF : ∀ n : ℤ, (N : ℤ) < |n| → F n = 0) :
    ∑' n : ℤ, F n = ∑ i ∈ range (2 * N + 1), F (-N + i) := by
  rw [tsum_eq_sum (s := (range (2 * N + 1)).image fun i : ℕ => (-N + i : ℤ))]
  · rw [sum_image]; intro i _ j _ h; simpa using h
  · intro n hn
    apply hF
    simp only [mem_image, mem_range, not_exists, not_and] at hn
    by_contra hle; push Not at hle
    rw [abs_le] at hle
    exact hn (n + N).toNat (by omega) (by omega)

theorem norm_e_sub_one {s : ℝ} : ‖e s - 1‖ = 2 * |Real.sin (π * s)| := by
  have h := norm_e_sub_one_sq s
  rw [show 4 * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by rw [mul_pow, sq_abs]; ring] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- **[B, (2.2)], second bound**: `|∑ₙ f(n) e(αn)| ≤ V(f) / (2|sin πα|)`, `V(f)` the total
variation of `f` (`= |f'|₁` for piecewise `C¹` `f`). Proved by summation by parts. -/
theorem norm_tsum_le_variation {f : ℝ → ℂ} (hfs : HasCompactSupport f) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : eVariationOn f Set.univ ≤ ENNReal.ofReal V) {α : ℝ} (hα : Real.sin (π * α) ≠ 0) :
    ‖∑' n : ℤ, f n * e (α * n)‖ ≤ V / (2 * |Real.sin (π * α)|) := by
  obtain ⟨N, hN⟩ := exists_nat_vanish hfs
  have hF : ∀ n : ℤ, (N : ℤ) < |n| → f n * e (α * n) = 0 := by
    intro n hn
    rw [hN n (by rw [← Int.cast_abs]; exact_mod_cast hn.le), zero_mul]
  rw [tsum_int_eq_sum_range hF]
  set L := 2 * N + 1
  set w := e α
  have hw : w - 1 ≠ 0 := by
    intro h; have := congrArg norm h
    rw [norm_e_sub_one, norm_zero] at this
    exact hα (abs_eq_zero.1 (by linarith))
  set c : ℕ → ℂ := fun i => e (α * ((-N + i : ℤ) : ℝ)) / (w - 1)
  set g : ℕ → ℂ := fun i => f ((-N + i : ℤ) : ℝ)
  have hc : ∀ i : ℕ, e (α * ((-N + i : ℤ) : ℝ)) = c (i + 1) - c i := by
    intro i
    simp only [c]
    rw [← sub_div, eq_div_iff hw]
    have : α * ((-N + (i + 1 : ℕ) : ℤ) : ℝ) = α * ((-N + i : ℤ) : ℝ) + α := by push_cast; ring
    rw [this, e_add]; ring
  have hsum : ∑ i ∈ range L, f ((-N + i : ℤ) : ℝ) * e (α * ((-N + i : ℤ) : ℝ)) =
      ∑ i ∈ range L, (g i - g (i + 1)) * c (i + 1) := by
    simp_rw [hc]
    rw [sum_range_by_parts' g c L]
    have h0 : g 0 = 0 := hN _ (by push_cast; simp)
    have hL : g L = 0 := hN _ (by
      simp only [L]; push_cast
      rw [show (-(N : ℝ) + (2 * N + 1)) = N + 1 by ring, abs_of_pos (by positivity)]; linarith)
    rw [h0, hL]; simp
  rw [hsum]
  have hcn : ∀ i, ‖c i‖ = 1 / (2 * |Real.sin (π * α)|) := by
    intro i; simp only [c]; rw [norm_div, norm_e, norm_e_sub_one]
  have hvar : ∑ i ∈ range L, ‖g i - g (i + 1)‖ ≤ V := by
    have h := eVariationOn.sum_le (f := f) (s := Set.univ) (n := L)
      (u := fun i => ((-N + i : ℤ) : ℝ)) (fun i j hij => by simp; exact_mod_cast hij)
      (fun _ => Set.mem_univ _)
    have h' := h.trans hV
    simp_rw [edist_dist] at h'
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg),
      ENNReal.ofReal_le_ofReal_iff hV0] at h'
    refine le_trans (le_of_eq ?_) h'
    refine sum_congr rfl fun i _ => ?_
    rw [dist_eq_norm, ← norm_neg]; simp only [g]; congr 1; ring
  calc ‖∑ i ∈ range L, (g i - g (i + 1)) * c (i + 1)‖
      ≤ ∑ i ∈ range L, ‖(g i - g (i + 1)) * c (i + 1)‖ := norm_sum_le _ _
    _ = (∑ i ∈ range L, ‖g i - g (i + 1)‖) * (1 / (2 * |Real.sin (π * α)|)) := by
        rw [sum_mul]; refine sum_congr rfl fun i _ => ?_; rw [norm_mul, hcn]
    _ ≤ V * (1 / (2 * |Real.sin (π * α)|)) := by gcongr
    _ = _ := by ring


/-! ## [B, (2.2)], first bound -/

theorem variation_ne_top {f : ℝ → ℂ} {V : ℝ} (hV : eVariationOn f Set.univ ≤ ENNReal.ofReal V)
    (s : Set ℝ) : eVariationOn f s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((eVariationOn.mono f (Set.subset_univ s)).trans hV)

/-- `‖f(n)‖ ≤ ∫_{n-1/2}^{n+1/2} ‖f‖ + V(f, [n-1/2, n+1/2]) / 2`. -/
theorem norm_le_integral_add_variation {f : ℝ → ℂ} (hf : Continuous f) (n : ℝ)
    (hW : eVariationOn f (Set.Icc (n - 1 / 2) (n + 1 / 2)) ≠ ⊤) :
    ‖f n‖ ≤ (∫ t in (n - 1 / 2)..(n + 1 / 2), ‖f t‖) +
      (eVariationOn f (Set.Icc (n - 1 / 2) (n + 1 / 2))).toReal / 2 := by
  set W := (eVariationOn f (Set.Icc (n - 1 / 2) (n + 1 / 2))).toReal
  have hsplit := eVariationOn.Icc_add_Icc f (s := Set.univ) (a := n - 1 / 2) (b := n)
    (c := n + 1 / 2) (by linarith) (by linarith) (Set.mem_univ _)
  simp only [Set.univ_inter] at hsplit
  have hL : eVariationOn f (Set.Icc (n - 1 / 2) n) ≠ ⊤ :=
    ne_top_of_le_ne_top hW (eVariationOn.mono f (Set.Icc_subset_Icc le_rfl (by linarith)))
  have hR : eVariationOn f (Set.Icc n (n + 1 / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hW (eVariationOn.mono f (Set.Icc_subset_Icc (by linarith) le_rfl))
  have hWsum : (eVariationOn f (Set.Icc (n - 1 / 2) n)).toReal +
      (eVariationOn f (Set.Icc n (n + 1 / 2))).toReal = W := by
    rw [← ENNReal.toReal_add hL hR, hsplit]
  have hdist : ∀ {s : Set ℝ} {x y : ℝ}, eVariationOn f s ≠ ⊤ → x ∈ s → y ∈ s →
      ‖f x - f y‖ ≤ (eVariationOn f s).toReal := by
    intro s x y hs hx hy
    have := eVariationOn.edist_le f hx hy
    rw [edist_dist, ← ENNReal.ofReal_toReal hs, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
      dist_eq_norm] at this
    exact this
  -- Pointwise in `τ ∈ [0, 1/2]`.
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖f n‖ ≤ (‖f (n - τ)‖ + ‖f (n + τ)‖) / 2 + W / 2 := by
    intro τ hτ
    have h1 := hdist hL (x := n) (y := n - τ) ⟨by linarith [hτ.2], le_rfl⟩
      ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have h2 := hdist hR (x := n) (y := n + τ) ⟨le_rfl, by linarith [hτ.2]⟩
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have t1 : ‖f n‖ ≤ ‖f (n - τ)‖ + ‖f n - f (n - τ)‖ := by
      have := norm_add_le (f (n - τ)) (f n - f (n - τ)); simpa using this
    have t2 : ‖f n‖ ≤ ‖f (n + τ)‖ + ‖f n - f (n + τ)‖ := by
      have := norm_add_le (f (n + τ)) (f n - f (n + τ)); simpa using this
    linarith
  have hcont : Continuous fun t => ‖f t‖ := hf.norm
  have hint : ∫ _ in (0 : ℝ)..(1 / 2), ‖f n‖ ≤
      ∫ τ in (0 : ℝ)..(1 / 2), ((‖f (n - τ)‖ + ‖f (n + τ)‖) / 2 + W / 2) :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
  have i1 : IntervalIntegrable (fun τ => ‖f (n - τ)‖) volume 0 (1 / 2) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun τ => ‖f (n + τ)‖) volume 0 (1 / 2) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add ((i1.add i2).div_const 2)
    intervalIntegrable_const, intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_add i1 i2] at hint
  have e1 : ∫ τ in (0 : ℝ)..(1 / 2), ‖f (n - τ)‖ = ∫ t in (n - 1 / 2)..n, ‖f t‖ := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => ‖f t‖), sub_zero]
  have e2 : ∫ τ in (0 : ℝ)..(1 / 2), ‖f (n + τ)‖ = ∫ t in n..(n + 1 / 2), ‖f t‖ := by
    rw [intervalIntegral.integral_comp_add_left (fun t => ‖f t‖), add_zero]
  have e3 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := n - 1 / 2) (b := n) (c := n + 1 / 2) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)
  rw [e1, e2, e3] at hint
  simp only [sub_zero, smul_eq_mul] at hint
  linarith

/-- **[B, (2.2)], first bound**: `∑ₙ ‖f(n)‖ ≤ |f|₁ + V(f)/2`, hence `|∑ₙ f(n) e(αn)|` is at most
the same. -/
theorem tsum_norm_le_variation {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    {V : ℝ} (hV0 : 0 ≤ V) (hV : eVariationOn f Set.univ ≤ ENNReal.ofReal V) :
    Summable (fun n : ℤ => ‖f n‖) ∧ ∑' n : ℤ, ‖f n‖ ≤ (∫ t, ‖f t‖) + V / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_vanish hfs
  have hF : ∀ n : ℤ, (N : ℤ) < |n| → ‖f n‖ = 0 := by
    intro n hn
    rw [hN n (by rw [← Int.cast_abs]; exact_mod_cast hn.le), norm_zero]
  have hsumm : Summable (fun n : ℤ => ‖f n‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro n hn; apply hF
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rw [lt_abs]; omega
  refine ⟨hsumm, ?_⟩
  have hfin : ∑' n : ℤ, ‖f n‖ = ∑ i ∈ range (2 * N + 1), ‖f ((-N + i : ℤ) : ℝ)‖ := by
    have := tsum_int_eq_sum_range (F := fun n => (‖f n‖ : ℂ)) (N := N)
      (fun n hn => by simp [hF n hn])
    rw [← Complex.ofReal_tsum] at this
    exact_mod_cast this
  rw [hfin]
  set L := 2 * N + 1
  set a : ℕ → ℝ := fun i => ((-N + i : ℤ) : ℝ) - 1 / 2
  have ha : ∀ i : ℕ, ((-N + i : ℤ) : ℝ) = a i + 1 / 2 := fun i => by simp only [a]; ring
  have ha1 : ∀ i : ℕ, a (i + 1) = ((-N + i : ℤ) : ℝ) + 1 / 2 := fun i => by
    simp only [a]; push_cast; ring
  have hcont : Continuous fun t => ‖f t‖ := hf.norm
  have hpt : ∀ i ∈ range L, ‖f ((-N + i : ℤ) : ℝ)‖ ≤ (∫ t in a i..a (i + 1), ‖f t‖) +
      (eVariationOn f (Set.Icc (a i) (a (i + 1)))).toReal / 2 := by
    intro i _
    have := norm_le_integral_add_variation hf ((-N + i : ℤ) : ℝ) (variation_ne_top hV _)
    rwa [← ha1 i, show ((-N + i : ℤ) : ℝ) - 1 / 2 = a i by rw [ha i]; ring] at this
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hcont.intervalIntegrable _ _), ← sum_div]
  have hmono : ∀ i, a i ≤ a (i + 1) := fun i => by rw [ha1 i, ha i]; linarith
  -- Variations over adjacent intervals add up.
  have hvsum : ∀ m, ∑ i ∈ range m, eVariationOn f (Set.Icc (a i) (a (i + 1))) =
      eVariationOn f (Set.Icc (a 0) (a m)) := by
    intro m
    induction m with
    | zero => simp [Set.Icc_self, eVariationOn.subsingleton]
    | succ m ih =>
      rw [sum_range_succ, ih]
      have hm : a 0 ≤ a m := by
        have : Monotone a := monotone_nat_of_le_succ hmono
        exact this (Nat.zero_le m)
      have := eVariationOn.Icc_add_Icc f (s := Set.univ) hm (hmono m) (Set.mem_univ _)
      simpa only [Set.univ_inter] using this
  have hvle : ∑ i ∈ range L, (eVariationOn f (Set.Icc (a i) (a (i + 1)))).toReal ≤ V := by
    rw [← ENNReal.toReal_sum (fun i _ => variation_ne_top hV _), hvsum]
    exact ENNReal.toReal_le_of_le_ofReal hV0
      ((eVariationOn.mono f (Set.subset_univ _)).trans hV)
  have hileq : ∫ t in a 0..a L, ‖f t‖ ≤ ∫ t, ‖f t‖ := by
    have hle : a 0 ≤ a L := (monotone_nat_of_le_succ hmono) (Nat.zero_le L)
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral (hcont.integrable_of_hasCompactSupport hfs.norm)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  linarith

end TernaryGoldbach
