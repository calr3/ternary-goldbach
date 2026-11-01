import TernaryGoldbach.Explicit.Xi
import TernaryGoldbach.Explicit.RectResidue2
import TernaryGoldbach.MajorArcs.Cor713

/-!
# The Hadamard-type inequality `Re ξ'/ξ(s) ≥ Σ_{ρ ∈ S} Re 1/(s − ρ)` (`ℜs > 1`)

Without the product theorem: on squares `R_k` symmetric about `ℜs = 1/2` at good heights,
`∮ ξ'/ξ(w) (w−s)^{-1} = ½ ∮ ξ'/ξ(w) [(w−s)^{-1} − (w−(1−s))^{-1}]` (symmetry `w ↦ 1 − w`), and the kernel is
`O(|w|^{-2})` while `|ξ'/ξ| ≪ log² T` on `∂R_k` (polynomial `B''_ζ`, good heights, digamma bounds). So
`ξ'/ξ(s) = lim Σ_{ρ ∈ R_k} m_ρ/(s − ρ)`, and all terms have positive real part for `ℜs > 1`.
-/

open Complex Set Metric Filter
open scoped Real Interval Topology

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.MajorArcs (log9201_le log22_le log1375_le neg_log0355_le)

/-! ## A datum for `zetaF` with the polynomial bound `B''_ζ` -/

theorem BPz2_le (T : ℝ) : BPz2 T ≤ 9201 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 := by
  unfold BPz2
  set a := |T| with ha
  have ha0 : 0 ≤ a := abs_nonneg T
  set b := 1.25 * (a + 11) with hb
  have hb1 : 13.75 ≤ b := by rw [hb]; linarith
  have hb0 : 0 ≤ b := by linarith
  have h1 : 20 * (a + 22) ^ 2 ≤ b ^ 7 := by
    have h2 : (a + 22) ^ 2 ≤ 4 * b ^ 2 := by rw [hb]; nlinarith
    have h3 : 80 * b ^ 2 ≤ b ^ 7 := by
      have : (13.75 : ℝ) ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ (by norm_num) hb1 5
      have : (80 : ℝ) ≤ b ^ 5 := le_trans (by norm_num) this
      nlinarith [sq_nonneg b]
    nlinarith
  have h4 : 20 * (a + 22) ^ 3 * b ^ 2 ≤ (a + 22) * b ^ 9 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (a + 22) * b ^ 2)
    nlinarith
  linarith

theorem log_le_log_add (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) : Real.log (a + x) ≤ Real.log a + x / a := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (a + x) / a by positivity)
  rw [Real.log_div (by positivity) ha.ne'] at h
  have : (a + x) / a - 1 = x / a := by field_simp; ring
  linarith

/-- `log(B''_ζ(T)/0.355) ≤ 10.24 + log(|T|+22) + 9 log(1.25(|T|+11))`. -/
theorem log_BPz2_le' (T : ℝ) :
    Real.log (BPz2 T / 0.355) ≤ 10.24 + Real.log (|T| + 22) + 9 * Real.log (1.25 * (|T| + 11)) := by
  have hB0 : 0 < BPz2 T := by unfold BPz2; positivity
  have hpos : (0:ℝ) < 9201 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 := by positivity
  refine (Real.log_le_log (div_pos hB0 (by norm_num)) (div_le_div_of_nonneg_right (BPz2_le T)
    (by norm_num))).trans ?_
  rw [Real.log_div hpos.ne' (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have := log9201_le
  have := neg_log0355_le
  push_cast
  linarith

theorem log_BPz2_lin (T : ℝ) : Real.log (BPz2 T / 0.355) ≤ 0 + 37 + 2.6 * |T| := by
  have h := log_BPz2_le' T
  have h1 := log_le_log_add 22 |T| (by norm_num) (abs_nonneg T)
  rw [add_comm] at h1
  have h2 : Real.log (1.25 * (|T| + 11)) ≤ Real.log 13.75 + |T| / 11 := by
    have := log_le_log_add 13.75 (1.25 * |T|) (by norm_num) (by positivity)
    rw [show (1.25 : ℝ) * (|T| + 11) = 13.75 + 1.25 * |T| by ring]
    refine this.trans (le_of_eq ?_); ring
  have := log22_le
  have := log1375_le
  have hT := abs_nonneg T
  linarith

theorem zetaF_center_lt2 (T : ℝ) : ‖zetaF (2 + T * I)‖ < BPz2 T := by
  have hne : (2 : ℂ) + T * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [zetaF_of_ne hne, norm_mul]
  have h1 : ‖(2 : ℂ) + T * I - 1‖ ≤ 1 + |T| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp; norm_num
  have h2 := norm_zeta_two_le (s := 2 + T * I) (by simp)
  have hpi := Real.pi_lt_d4
  have h3 : π ^ 2 / 6 ≤ 1.65 := by nlinarith [Real.pi_pos]
  have hT0 := abs_nonneg T
  have h4 : (1 + |T|) * 1.65 < BPz2 T := by
    unfold BPz2
    have : (1 + |T|) * 1.65 < 9200 * (|T| + 22) * 1 := by nlinarith
    have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ 9 := one_le_pow₀ (by linarith)
    have : 9200 * (|T| + 22) * 1 ≤ 9200 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    have : 0 ≤ 20 * (|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ 2 := by positivity
    linarith
  calc ‖(2 : ℂ) + T * I - 1‖ * ‖riemannZeta (2 + T * I)‖ ≤ (1 + |T|) * 1.65 :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
    _ < _ := h4

/-- `zetaF` with the polynomial bound. -/
theorem ldatum_zeta2 : LDatum zetaF BPz2 0 (C3 + 2) where
  diff := differentiable_zetaF
  center_ge := zetaF_center_ge
  center_lt := zetaF_center_lt2
  bound := fun T w hw => norm_zetaF_le_BPz2 T hw
  B_ge := polyDatum_zeta2.B_ge
  B_mono := polyDatum_zeta2.B_mono
  logB_lin := log_BPz2_lin
  D_nonneg := le_rfl
  nz_strip := fun s h1 h2 => zetaF_ne_zero_strip h1 h2
  nz_right := fun s h => zetaF_ne_zero_right h
  right_bound := norm_logDeriv_zetaF_right

/-- `HkD B''_ζ k ≤ 11.4 P² + 7.7 P`, `P = 10.24 + 10 log(1.25(k + 23))`. -/
theorem HkD_BPz2_le (k : ℕ) :
    HkD BPz2 k ≤ 11.4 * (10.24 + 10 * Real.log (1.25 * (k + 23))) ^ 2 +
      7.7 * (10.24 + 10 * Real.log (1.25 * (k + 23))) := by
  unfold HkD
  set P := Real.log (BPz2 ((k : ℝ) + 1) / 0.355) with hP
  have hP0 : 0 ≤ P := (polyDatum_zeta2.log_pos _).le
  have hPle : P ≤ 10.24 + 10 * Real.log (1.25 * (k + 23)) := by
    have h := log_BPz2_le' ((k : ℝ) + 1)
    rw [abs_of_nonneg (by positivity)] at h
    have h1 : Real.log ((k : ℝ) + 1 + 22) ≤ Real.log (1.25 * (k + 23)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (1.25 * ((k : ℝ) + 1 + 11)) ≤ Real.log (1.25 * (k + 23)) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hl1 : 0.51 ≤ Real.log (10 / 6) := by
    have := log_ratio_pos (r := 6) (by norm_num) (by norm_num)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_bound' (x := 0.51) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  have hl2 := Real.log_two_gt_d9
  have hX : (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8 ≤ 11.4 * P + 7.7 := by
    have e1 : 2 * P / Real.log (10 / 6) ≤ 2 * P / 0.51 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl1
    have e2 : (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 ≤ (2 * (2 * P / 0.51) + 2) / 0.6931 := by
      have h0 : 0 ≤ 2 * (2 * P / Real.log (10 / 6)) + 2 := by
        have : 0 ≤ 2 * P / Real.log (10 / 6) := div_nonneg (by positivity) (by linarith)
        linarith
      calc (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2
          ≤ (2 * (2 * P / 0.51) + 2) / Real.log 2 := by gcongr
        _ ≤ (2 * (2 * P / 0.51) + 2) / 0.6931 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have e3 : (2 * (2 * P / 0.51) + 2) / 0.6931 ≤ 11.4 * P + 2.9 := by
      rw [div_le_iff₀ (by norm_num)]
      have : 2 * (2 * P / 0.51) = (4 / 0.51) * P := by ring
      rw [this]; nlinarith
    linarith
  calc P * ((2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8) ≤ P * (11.4 * P + 7.7) :=
        mul_le_mul_of_nonneg_left hX hP0
    _ ≤ (10.24 + 10 * Real.log (1.25 * (k + 23))) * (11.4 * (10.24 + 10 * Real.log (1.25 * (k + 23))) + 7.7) := by
        have : 0 ≤ Real.log (1.25 * ((k : ℝ) + 23)) := Real.log_nonneg (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
        gcongr
    _ = _ := by ring

/-! ## Rectangles symmetric about `ℜs = 1/2` -/

/-- The square `[1/2 − A, 1/2 + A] × [−T, T]`. -/
noncomputable def sqZ (A T : ℝ) : ℂ := ((1 / 2 - A : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I
noncomputable def sqW (A T : ℝ) : ℂ := ((1 / 2 + A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I

@[simp] theorem sqZ_re (A T : ℝ) : (sqZ A T).re = 1 / 2 - A := by simp [sqZ]
@[simp] theorem sqZ_im (A T : ℝ) : (sqZ A T).im = -T := by simp [sqZ]
@[simp] theorem sqW_re (A T : ℝ) : (sqW A T).re = 1 / 2 + A := by simp [sqW]
@[simp] theorem sqW_im (A T : ℝ) : (sqW A T).im = T := by simp [sqW]

/-- **Symmetry**: `∮ G(1 − w) dw = −∮ G(w) dw` on the symmetric square. -/
theorem rectInt_one_sub (G : ℂ → ℂ) (A T : ℝ) :
    rectInt (fun w => G (1 - w)) (sqZ A T) (sqW A T) = -rectInt G (sqZ A T) (sqW A T) := by
  unfold rectInt
  simp only [sqZ_re, sqZ_im, sqW_re, sqW_im]
  have e1 : (∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (1 - (x + ((-T : ℝ) : ℂ) * I))) =
      ∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (x + (T : ℂ) * I) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => G (x + (T : ℂ) * I))
      (a := 1 / 2 - A) (b := 1 / 2 + A) 1
    rw [show (1 : ℝ) - (1 / 2 + A) = 1 / 2 - A by ring, show (1 : ℝ) - (1 / 2 - A) = 1 / 2 + A by ring]
      at this
    rw [← this]
    congr 1; ext x; congr 1; push_cast; ring
  have e2 : (∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (1 - (x + ((T : ℝ) : ℂ) * I))) =
      ∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (x + ((-T : ℝ) : ℂ) * I) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => G (x + ((-T : ℝ) : ℂ) * I))
      (a := 1 / 2 - A) (b := 1 / 2 + A) 1
    rw [show (1 : ℝ) - (1 / 2 + A) = 1 / 2 - A by ring, show (1 : ℝ) - (1 / 2 - A) = 1 / 2 + A by ring]
      at this
    rw [← this]
    congr 1; ext x; congr 1; push_cast; ring
  have e3 : (∫ y : ℝ in (-T)..T, G (1 - (((1 / 2 + A : ℝ) : ℂ) + y * I))) =
      ∫ y : ℝ in (-T)..T, G (((1 / 2 - A : ℝ) : ℂ) + y * I) := by
    have := intervalIntegral.integral_comp_neg (fun y : ℝ => G (((1 / 2 - A : ℝ) : ℂ) + y * I))
      (a := -T) (b := T)
    rw [neg_neg] at this
    rw [← this]
    congr 1; ext y; congr 1; push_cast; ring
  have e4 : (∫ y : ℝ in (-T)..T, G (1 - (((1 / 2 - A : ℝ) : ℂ) + y * I))) =
      ∫ y : ℝ in (-T)..T, G (((1 / 2 + A : ℝ) : ℂ) + y * I) := by
    have := intervalIntegral.integral_comp_neg (fun y : ℝ => G (((1 / 2 + A : ℝ) : ℂ) + y * I))
      (a := -T) (b := T)
    rw [neg_neg] at this
    rw [← this]
    congr 1; ext y; congr 1; push_cast; ring
  rw [e1, e2, e3, e4]
  ring

/-- `‖∮ G‖ ≤ 2((w.re − z.re) + (w.im − z.im)) M` if `‖G‖ ≤ M` on the boundary. -/
theorem norm_rectInt_le {G : ℂ → ℂ} {z w : ℂ} (hzw1 : z.re ≤ w.re) (hzw2 : z.im ≤ w.im) {M : ℝ}
    (h1 : ∀ x ∈ Icc z.re w.re, ‖G (x + z.im * I)‖ ≤ M) (h2 : ∀ x ∈ Icc z.re w.re, ‖G (x + w.im * I)‖ ≤ M)
    (h3 : ∀ y ∈ Icc z.im w.im, ‖G (w.re + y * I)‖ ≤ M) (h4 : ∀ y ∈ Icc z.im w.im, ‖G (z.re + y * I)‖ ≤ M) :
    ‖rectInt G z w‖ ≤ 2 * ((w.re - z.re) + (w.im - z.im)) * M := by
  have b : ∀ (f : ℝ → ℂ) (a b : ℝ), a ≤ b → (∀ x ∈ Icc a b, ‖f x‖ ≤ M) →
      ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
    intro f a b hab hf
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := M) (f := f) (a := a) (b := b)
      (fun x hx => by rw [Set.uIoc_of_le hab] at hx; exact hf x (Ioc_subset_Icc_self hx))
    rwa [abs_of_nonneg (by linarith)] at this
  have i1 := b _ _ _ hzw1 h1
  have i2 := b _ _ _ hzw1 h2
  have i3 := b _ _ _ hzw2 h3
  have i4 := b _ _ _ hzw2 h4
  unfold rectInt
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  calc ‖(∫ x : ℝ in z.re..w.re, G (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, G (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, G (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, G (z.re + y * I))‖
      ≤ ‖∫ x : ℝ in z.re..w.re, G (x + z.im * I)‖ + ‖∫ x : ℝ in z.re..w.re, G (x + w.im * I)‖ +
        ‖∫ y : ℝ in z.im..w.im, G (w.re + y * I)‖ + ‖∫ y : ℝ in z.im..w.im, G (z.re + y * I)‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
        · rw [norm_smul, hI, one_mul]
        · rw [norm_smul, hI, one_mul]
    _ ≤ M * (w.re - z.re) + M * (w.re - z.re) + M * (w.im - z.im) + M * (w.im - z.im) := by linarith
    _ = _ := by ring

end TernaryGoldbach.Explicit
