import TernaryGoldbach.Explicit.WeilArch

/-!
# An explicit majorant `Φ⁺ ≥ Φ + Off`

`Φ(t) = Re H̃_t(1) + (1/2π) ∫ Re A(½ + iy) (B(y − t)² + B(y + t)²) dy` (`WPhi_eq`), and with
`A_N ≥ Re A` (`archF_line_re_le`), evenness, and a split at `|y − t| = R`:
`Φ(t) + Off ≤ Φ⁺(t) = P(t) + (1/π)[A_N(|t| + R) B_R + (c_N + ½ log(1 + |t|)) I₀ + I₁] + Off`
(`WPhi_le_PhiUp`), where `B_R = ∫_{−R}^{R} B²`, `P(t) = 2(2ℓ)^{2m} e^{mℓ}/max(1, ℓ|t|)^{2m}` (the poles),
`c_N = ½(log(N + ¼) − log π)`, and `I₀ = ∫_{|u|>R} (2/|u|)^{2m}`, `I₁ = ∫_{|u|>R} √|u| (2/|u|)^{2m}`.
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

variable {ℓ : ℝ} {m : ℕ}

/-! ### The pieces of `Φ⁺` -/

noncomputable def KRB (ℓ : ℝ) (m : ℕ) (R : ℝ) : ℝ := ∫ u in (-R)..R, Bsq ℓ m u

noncomputable def cN (N : ℕ) : ℝ := 1 / 2 * (Real.log (N + 1 / 4) - Real.log π)

/-- The tail integrands, as functions on `ℝ`. -/
noncomputable def tail0 (m : ℕ) (R : ℝ) (u : ℝ) : ℝ := if R < |u| then (2 / |u|) ^ (2 * m) else 0
noncomputable def tail1 (m : ℕ) (R : ℝ) (u : ℝ) : ℝ := if R < |u| then √|u| * (2 / |u|) ^ (2 * m) else 0

noncomputable def I0 (m : ℕ) (R : ℝ) : ℝ := ∫ u, tail0 m R u
noncomputable def I1 (m : ℕ) (R : ℝ) : ℝ := ∫ u, tail1 m R u

noncomputable def polarUp (ℓ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  2 * ((2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ)) / max 1 (ℓ * |t|) ^ (2 * m)

noncomputable def PhiUp (ℓ : ℝ) (m N : ℕ) (R t : ℝ) : ℝ :=
  polarUp ℓ m t + (1 / π) * (aN N (|t| + R) * KRB ℓ m R +
    (cN N + 1 / 2 * Real.log (1 + |t|)) * I0 m R + I1 m R) + OffC ℓ m

theorem continuous_PhiUp (ℓ : ℝ) (m N : ℕ) (R : ℝ) : Continuous (PhiUp ℓ m N R) := by
  unfold PhiUp polarUp
  have hmax : Continuous fun t : ℝ => max 1 (ℓ * |t|) ^ (2 * m) :=
    (continuous_const.max (continuous_const.mul continuous_abs)).pow _
  have hlog : Continuous fun t : ℝ => Real.log (1 + |t|) :=
    Continuous.log (by fun_prop) fun t => by positivity
  refine ((continuous_const.div hmax fun t => ?_).add (continuous_const.mul ?_)).add continuous_const
  · exact (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _).ne'
  · exact (((continuous_aN N).comp (continuous_abs.add continuous_const)).mul continuous_const).add
      ((continuous_const.add (continuous_const.mul hlog)).mul continuous_const) |>.add continuous_const

theorem cN_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ cN N := by
  unfold cN
  have : π ≤ (N : ℝ) + 1 / 4 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.pi_lt_d2]
  have := Real.log_le_log Real.pi_pos this
  linarith

/-! ### Pointwise bounds -/

theorem Bsq_le_norm_sq (ℓ : ℝ) (m : ℕ) (u : ℝ) : Bsq ℓ m u ≤ ‖WB ℓ m (u : ℂ)‖ ^ 2 := by
  unfold Bsq
  calc (WB ℓ m (u : ℂ)).re ^ 2 = |(WB ℓ m (u : ℂ)).re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖WB ℓ m (u : ℂ)‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

theorem Bsq_le_tail (hℓ0 : 0 < ℓ) (m : ℕ) {u : ℝ} (hu : u ≠ 0) : Bsq ℓ m u ≤ (2 / |u|) ^ (2 * m) := by
  have hz : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have h := norm_WB_le_div hℓ0 m hz
  simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs] at h
  calc Bsq ℓ m u ≤ ‖WB ℓ m (u : ℂ)‖ ^ 2 := Bsq_le_norm_sq ℓ m u
    _ ≤ ((2 / |u|) ^ m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = (2 / |u|) ^ (2 * m) := by rw [← pow_mul, mul_comm]

theorem log_one_add_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * √x := by
  have h1 : 1 + x ≤ (1 + √x) ^ 2 := by nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have h3 : Real.log (1 + √x) ≤ √x := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + √x); linarith
  push_cast at h2
  linarith

/-- `A_N(y) ≤ c_N + ½ log(1 + |y|)` (`N ≥ 2`). -/
theorem aN_le_log {N : ℕ} (hN : 2 ≤ N) (y : ℝ) : aN N y ≤ cN N + 1 / 2 * Real.log (1 + |y|) := by
  unfold aN cN psiN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 ≤ ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (y / 2) ^ 2) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hNc : 1 / 4 ≤ ((N : ℝ) - 3 / 4) ^ 2 := by nlinarith
  have hq : (y / 2) ^ 2 / ((N : ℝ) - 3 / 4) ^ 2 ≤ y ^ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hNc (sq_nonneg y)]
  have h1 : Real.log (1 + (y / 2) ^ 2 / ((N : ℝ) - 3 / 4) ^ 2) ≤ Real.log (1 + y ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have h2 : Real.log (1 + y ^ 2) ≤ 2 * Real.log (1 + |y|) := by
    have h := Real.log_le_log (by positivity) (show 1 + y ^ 2 ≤ (1 + |y|) ^ 2 by
      nlinarith [abs_nonneg y, sq_abs y])
    rw [Real.log_pow] at h; push_cast at h; exact h
  nlinarith

/-- `|A_N(y)| ≤ A₀ + |y|`. -/
noncomputable def AN0 (N : ℕ) : ℝ :=
  1 / 2 * Real.log π + 1 / 2 * (|Real.log (N + 1 / 4)| + ∑ k ∈ range N, 1 / ((k : ℝ) + 1 / 4))

theorem abs_aN_le {N : ℕ} (hN : 2 ≤ N) (y : ℝ) : |aN N y| ≤ AN0 N + |y| := by
  have hup := aN_le_log hN y
  have hcN : cN N ≤ 1 / 2 * |Real.log (N + 1 / 4)| + 1 / 2 * Real.log π := by
    unfold cN
    have := le_abs_self (Real.log (N + 1 / 4))
    have : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hlog : 1 / 2 * Real.log (1 + |y|) ≤ |y| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |y|)
    linarith [abs_nonneg y]
  have hs0 : 0 ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1 / 4) := Finset.sum_nonneg fun k _ => by positivity
  have hlow : -(AN0 N + |y|) ≤ aN N y := by
    unfold aN psiN AN0
    have hs : ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (y / 2) ^ 2) ≤
        ∑ k ∈ range N, 1 / ((k : ℝ) + 1 / 4) := Finset.sum_le_sum fun k _ => by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (y / 2), sq_nonneg ((k : ℝ) + 1 / 4)]
    have hl : 0 ≤ Real.log (1 + (y / 2) ^ 2 / ((N : ℝ) - 3 / 4) ^ 2) := Real.log_nonneg (by
      have : 0 ≤ (y / 2) ^ 2 / ((N : ℝ) - 3 / 4) ^ 2 := by positivity
      linarith)
    have := neg_abs_le (Real.log ((N : ℝ) + 1 / 4))
    nlinarith [abs_nonneg y]
  rw [abs_le]; constructor
  · linarith
  · unfold AN0; linarith

/-! ### Integrability -/

theorem inv_pow_le_lor_sq {u : ℝ} (hu : 1 ≤ |u|) {m : ℕ} (hm : 2 ≤ m) :
    (2 / |u|) ^ (2 * m) ≤ 4 ^ m * lor u ^ 2 := by
  have hu0 : 0 < |u| := by linarith
  have h1 : (2 / |u|) ^ (2 * m) = 4 ^ m * (1 / |u| ^ 2) ^ m := by
    rw [mul_comm 2 m, pow_mul', div_pow, show (2 : ℝ) ^ 2 / |u| ^ 2 = 4 * (1 / |u| ^ 2) by ring, mul_pow]
  have h2 : (1 / |u| ^ 2) ^ m ≤ (1 / |u| ^ 2) ^ 2 :=
    pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; nlinarith) hm
  have h3 : (1 / |u| ^ 2) ^ 2 ≤ lor u ^ 2 := by
    have := inv_sq_le_lor hu
    rw [sq_abs]
    exact pow_le_pow_left₀ (by positivity) this 2
  rw [h1]; gcongr; exact h2.trans h3

theorem measurable_tail0 (m : ℕ) (R : ℝ) : Measurable (tail0 m R) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) (by fun_prop) measurable_const

theorem measurable_tail1 (m : ℕ) (R : ℝ) : Measurable (tail1 m R) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs)
    ((Real.continuous_sqrt.measurable.comp measurable_abs).mul (by fun_prop)) measurable_const

theorem tail0_nonneg (m : ℕ) (R u : ℝ) : 0 ≤ tail0 m R u := by
  unfold tail0; split_ifs <;> positivity

theorem tail1_nonneg (m : ℕ) (R u : ℝ) : 0 ≤ tail1 m R u := by
  unfold tail1; split_ifs <;> positivity

theorem integrable_lor_sq : Integrable fun u : ℝ => lor u ^ 2 := by
  have h := (integrable_lor 0).const_mul 2
  have hc : Continuous fun u : ℝ => lor u ^ 2 := by
    unfold lor; exact (continuous_const.div (by fun_prop) fun u => by positivity).pow 2
  refine h.mono' hc.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sub_zero, sq]
  exact mul_le_mul_of_nonneg_right (lor_le_two u) (lor_pos u).le

theorem integrable_tail0 {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 1 ≤ R) : Integrable (tail0 m R) := by
  refine (integrable_lor_sq.const_mul (4 ^ m)).mono' (measurable_tail0 m R).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tail0_nonneg m R u)]
  unfold tail0
  split_ifs with h
  · exact inv_pow_le_lor_sq (by linarith) hm
  · positivity

theorem integrable_tail1 {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 1 ≤ R) : Integrable (tail1 m R) := by
  refine ((integrable_lor 0).const_mul (4 ^ m * 3)).mono' (measurable_tail1 m R).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tail1_nonneg m R u)]
  unfold tail1
  split_ifs with h
  · have hu : 1 ≤ |u| := by linarith
    have hs : √|u| ≤ 1 + |u| := by
      have := Real.sqrt_le_sqrt (show |u| ≤ |u| ^ 2 by nlinarith)
      rw [Real.sqrt_sq (abs_nonneg u)] at this; linarith
    have h1 := inv_pow_le_lor_sq hu hm
    have h2 := one_add_abs_mul_lor_sq_le 0 u
    simp only [sub_zero, abs_zero, mul_zero, add_zero] at h2
    calc √|u| * (2 / |u|) ^ (2 * m) ≤ (1 + |u|) * (4 ^ m * lor u ^ 2) :=
          mul_le_mul hs h1 (by positivity) (by positivity)
      _ = 4 ^ m * ((1 + |u|) * lor u ^ 2) := by ring
      _ ≤ 4 ^ m * (3 * lor u) := by gcongr
      _ = 4 ^ m * 3 * lor (u - 0) := by rw [sub_zero]; ring
  · have := (lor_pos (u - 0)).le; positivity

/-! ### The bound -/

theorem AN0_nonneg (N : ℕ) : 0 ≤ AN0 N := by
  unfold AN0
  have := Real.log_nonneg (show (1 : ℝ) ≤ π by linarith [Real.pi_gt_three])
  have : 0 ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1 / 4) := Finset.sum_nonneg fun k _ => by positivity
  have := abs_nonneg (Real.log ((N : ℝ) + 1 / 4))
  positivity

theorem Bsq_le_WHt_line (ℓ : ℝ) (m : ℕ) (t y : ℝ) :
    Bsq ℓ m (y - t) ≤ ‖WHt ℓ m t (((1 / 2 : ℝ) : ℂ) + y * I)‖ := by
  rw [WHt_line, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (Bsq_nonneg ℓ m (y - t)) (Bsq_nonneg ℓ m (y + t)))]
  linarith [Bsq_nonneg ℓ m (y + t)]

theorem integrable_aN_Bsq (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    Integrable fun y : ℝ => aN N y * Bsq ℓ m (y - t) := by
  have hc : Continuous fun y : ℝ => aN N y * Bsq ℓ m (y - t) :=
    (continuous_aN N).mul ((continuous_Bsq ℓ m).comp (continuous_id.sub continuous_const))
  refine (integrable_LMaj t (4 ^ m * Real.exp (2 * m * ℓ) * (AN0 N + 1) * (3 + 2 * |t|))).mono'
    hc.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have h := mul_norm_WHt_le hℓ0 hℓ1 hm t (AN0_nonneg N) zero_le_one (σ := 1 / 2) (by norm_num) y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Bsq_nonneg ℓ m (y - t))]
  calc |aN N y| * Bsq ℓ m (y - t) ≤ (AN0 N + 1 * |y|) * ‖WHt ℓ m t (((1 / 2 : ℝ) : ℂ) + y * I)‖ :=
        mul_le_mul (by rw [one_mul]; exact abs_aN_le hN y) (Bsq_le_WHt_line ℓ m t y)
          (Bsq_nonneg ℓ m (y - t)) (by linarith [AN0_nonneg N, abs_nonneg y])
    _ ≤ _ := h

/-- `∫ A_N(y) B(y − t)² dy ≤ A_N(|t| + R) B_R + (c_N + ½ log(1 + |t|)) I₀ + I₁`. -/
theorem integral_aN_Bsq_le (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) {N : ℕ} (hN : 3 ≤ N)
    {R : ℝ} (hR : 1 ≤ R) (t : ℝ) :
    ∫ y, aN N y * Bsq ℓ m (y - t) ≤ aN N (|t| + R) * KRB ℓ m R +
      (cN N + 1 / 2 * Real.log (1 + |t|)) * I0 m R + I1 m R := by
  set W := Icc (t - R) (t + R) with hW
  set c := cN N + 1 / 2 * Real.log (1 + |t|) with hc
  have hc0 : 0 ≤ c := by
    have := cN_nonneg hN
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + |t| by linarith [abs_nonneg t])
    positivity
  have hind : Integrable (W.indicator fun y => Bsq ℓ m (y - t)) :=
    (((continuous_Bsq ℓ m).comp (continuous_id.sub continuous_const)).integrableOn_Icc).integrable_indicator
      measurableSet_Icc
  have ht0 : Integrable fun y => tail0 m R (y - t) := (integrable_tail0 hm hR).comp_sub_right t
  have ht1 : Integrable fun y => tail1 m R (y - t) := (integrable_tail1 hm hR).comp_sub_right t
  have hpt : ∀ y, aN N y * Bsq ℓ m (y - t) ≤
      aN N (|t| + R) * W.indicator (fun y => Bsq ℓ m (y - t)) y + c * tail0 m R (y - t) + tail1 m R (y - t) := by
    intro y
    by_cases hy : y ∈ W
    · have hu : |y - t| ≤ R := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      rw [Set.indicator_of_mem hy]
      have h0 : tail0 m R (y - t) = 0 := by unfold tail0; rw [if_neg (not_lt.2 hu)]
      have h1 : tail1 m R (y - t) = 0 := by unfold tail1; rw [if_neg (not_lt.2 hu)]
      rw [h0, h1, mul_zero, add_zero, add_zero]
      refine mul_le_mul_of_nonneg_right (aN_mono (by omega) ?_) (Bsq_nonneg ℓ m (y - t))
      have := abs_sub_abs_le_abs_sub y t
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |t| + R)]; linarith
    · have hu : R < |y - t| := by
        by_contra h
        push Not at h
        exact hy ⟨by linarith [(abs_le.1 h).1], by linarith [(abs_le.1 h).2]⟩
      rw [Set.indicator_of_notMem hy, mul_zero, zero_add]
      have h0 : tail0 m R (y - t) = (2 / |y - t|) ^ (2 * m) := by unfold tail0; rw [if_pos hu]
      have h1 : tail1 m R (y - t) = √|y - t| * (2 / |y - t|) ^ (2 * m) := by unfold tail1; rw [if_pos hu]
      rw [h0, h1]
      have hyt : y - t ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
      have hB := Bsq_le_tail hℓ0 m hyt
      have hB0 := Bsq_nonneg ℓ m (y - t)
      have hP : 0 ≤ (2 / |y - t|) ^ (2 * m) := by positivity
      -- `A_N(y) ≤ c + √|y − t|`
      have ha : aN N y ≤ c + √|y - t| := by
        have h1 := aN_le_log (N := N) (by omega) y
        have h2 : Real.log (1 + |y|) ≤ Real.log (1 + |t|) + Real.log (1 + |y - t|) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          refine Real.log_le_log (by positivity) ?_
          have := abs_sub_abs_le_abs_sub y t
          nlinarith [abs_nonneg t, abs_nonneg (y - t)]
        have h3 := log_one_add_le_sqrt (abs_nonneg (y - t))
        rw [hc]; linarith
      have hs : 0 ≤ c + √|y - t| := by positivity
      rcases le_total (aN N y) 0 with hneg | hpos
      · have : aN N y * Bsq ℓ m (y - t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hB0
        have : 0 ≤ c * (2 / |y - t|) ^ (2 * m) + √|y - t| * (2 / |y - t|) ^ (2 * m) := by positivity
        linarith
      · calc aN N y * Bsq ℓ m (y - t) ≤ (c + √|y - t|) * (2 / |y - t|) ^ (2 * m) :=
            mul_le_mul ha hB hB0 hs
          _ = c * (2 / |y - t|) ^ (2 * m) + √|y - t| * (2 / |y - t|) ^ (2 * m) := by ring
  have i1 : Integrable fun y => aN N (|t| + R) * W.indicator (fun y => Bsq ℓ m (y - t)) y :=
    hind.const_mul _
  have i2 : Integrable fun y => c * tail0 m R (y - t) := ht0.const_mul c
  have i12 : Integrable fun y => aN N (|t| + R) * W.indicator (fun y => Bsq ℓ m (y - t)) y +
      c * tail0 m R (y - t) := i1.add i2
  have i123 : Integrable fun y => aN N (|t| + R) * W.indicator (fun y => Bsq ℓ m (y - t)) y +
      c * tail0 m R (y - t) + tail1 m R (y - t) := i12.add ht1
  have hmono := integral_mono (integrable_aN_Bsq hℓ0 hℓ1 hm (by omega) t) i123 hpt
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add i12 ht1, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun u => Bsq ℓ m u),
    integral_sub_right_eq_self (fun u => tail0 m R u) t, integral_sub_right_eq_self (fun u => tail1 m R u) t]
  rw [show t - R - t = -R by ring, show t + R - t = R by ring]
  rfl

/-- The poles: `Re H̃_t(1) ≤ P(t)`. -/
theorem WHt_one_re_le (hℓ0 : 0 < ℓ) (m : ℕ) (t : ℝ) : (WHt ℓ m t 1).re ≤ polarUp ℓ m t := by
  have hb : ∀ s : ℂ, s.im = 0 → |s.re - 1 / 2| = 1 / 2 →
      ‖WH ℓ m t s‖ ≤ (2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ) / max 1 (ℓ * |t|) ^ (2 * m) := by
    intro s hs0 hs1
    have hE : ((2 * ℓ * Real.exp (ℓ * (1 / 2))) ^ m) ^ 2 = (2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ) := by
      rw [← pow_mul, mul_pow, ← Real.exp_nat_mul, mul_comm m 2]
      congr 2; push_cast; ring
    rcases le_or_gt (ℓ * |t|) 1 with ht | ht
    · rw [max_eq_left ht, one_pow, div_one, ← hE]
      have := norm_WH_le hℓ0.le m t s
      rwa [hs1] at this
    · have htne : s.im ≠ t := by
        intro h; rw [← h, hs0, abs_zero, mul_zero] at ht; linarith
      have h := norm_WH_le_div hℓ0 m t htne
      rw [hs1, hs0, zero_sub, abs_neg] at h
      rw [max_eq_right ht.le]
      have ht0 : 0 < |t| := by
        rcases eq_or_ne t 0 with h0 | h0
        · rw [h0, abs_zero, mul_zero] at ht; linarith
        · exact abs_pos.2 h0
      refine h.trans (le_of_eq ?_)
      have he : Real.exp (ℓ * (1 / 2)) ^ (2 * m) = Real.exp (m * ℓ) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hl : 0 < ℓ * |t| := by positivity
      rw [← pow_mul, mul_comm m 2, div_pow, mul_pow, he, mul_pow (2 : ℝ) ℓ, mul_pow ℓ |t|]
      field_simp
  have h1 := hb 1 (by simp) (by norm_num)
  have h0 := hb 0 (by simp) (by norm_num)
  unfold WHt
  rw [sub_self]
  calc (WH ℓ m t 1 + WH ℓ m t 0).re ≤ ‖WH ℓ m t 1 + WH ℓ m t 0‖ := Complex.re_le_norm _
    _ ≤ ‖WH ℓ m t 1‖ + ‖WH ℓ m t 0‖ := norm_add_le _ _
    _ ≤ _ := by
        unfold polarUp
        have e : 2 * ((2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ)) / max 1 (ℓ * |t|) ^ (2 * m) =
            (2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ) / max 1 (ℓ * |t|) ^ (2 * m) +
            (2 * ℓ) ^ (2 * m) * Real.exp (m * ℓ) / max 1 (ℓ * |t|) ^ (2 * m) := by ring
        rw [e]; linarith

/-! ### Assembly -/

theorem WPhi_eq (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (t : ℝ) :
    WPhi ℓ m t = (WHt ℓ m t 1).re + (1 / (2 * π)) *
      ∫ y : ℝ, (archF (((1 / 2 : ℝ) : ℂ) + y * I)).re * (Bsq ℓ m (y - t) + Bsq ℓ m (y + t)) := by
  have hint := integrable_archF_WHt hℓ0 hℓ1 hm t (c := 1 / 2) ⟨le_rfl, by norm_num⟩
  have hr := integral_re hint
  simp only [RCLike.re_to_complex] at hr
  unfold WPhi
  rw [Complex.add_re, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, ← hr]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [WHt_line, Complex.re_mul_ofReal]

theorem integral_aN_Bsq_add (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ∫ y : ℝ, aN N y * (Bsq ℓ m (y - t) + Bsq ℓ m (y + t)) = 2 * ∫ y : ℝ, aN N y * Bsq ℓ m (y - t) := by
  have i1 := integrable_aN_Bsq hℓ0 hℓ1 hm hN t
  have i2 : Integrable fun y : ℝ => aN N y * Bsq ℓ m (y + t) := by
    simpa [sub_neg_eq_add] using integrable_aN_Bsq hℓ0 hℓ1 hm hN (-t)
  have hsym : ∫ y : ℝ, aN N y * Bsq ℓ m (y + t) = ∫ y : ℝ, aN N y * Bsq ℓ m (y - t) := by
    rw [← integral_neg_eq_self (fun y : ℝ => aN N y * Bsq ℓ m (y + t)) volume]
    congr 1; funext y
    rw [aN_neg, show -y + t = -(y - t) by ring, Bsq_neg]
  simp_rw [mul_add]
  rw [integral_add i1 i2, hsym]; ring

/-- **`Φ(t) + Off ≤ Φ⁺(t)`**. -/
theorem WPhi_le_PhiUp (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) {N : ℕ} (hN : 3 ≤ N)
    {R : ℝ} (hR : 1 ≤ R) (t : ℝ) : WPhi ℓ m t + OffC ℓ m ≤ PhiUp ℓ m N R t := by
  rw [WPhi_eq hℓ0 hℓ1 hm t]
  have hint := (integrable_archF_WHt hℓ0 hℓ1 hm t (c := 1 / 2) ⟨le_rfl, by norm_num⟩).re
  simp only [RCLike.re_to_complex] at hint
  have hre : (fun y : ℝ => Complex.re (archF (((1 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m t (((1 / 2 : ℝ) : ℂ) + y * I))) =
      fun y : ℝ => (archF (((1 / 2 : ℝ) : ℂ) + y * I)).re * (Bsq ℓ m (y - t) + Bsq ℓ m (y + t)) := by
    funext y; rw [WHt_line]; exact Complex.re_mul_ofReal _ _
  rw [hre] at hint
  have i2 : Integrable fun y : ℝ => aN N y * (Bsq ℓ m (y - t) + Bsq ℓ m (y + t)) := by
    have i1 := integrable_aN_Bsq hℓ0 hℓ1 hm (N := N) (by omega) t
    have i2 : Integrable fun y : ℝ => aN N y * Bsq ℓ m (y + t) := by
      simpa [sub_neg_eq_add] using integrable_aN_Bsq hℓ0 hℓ1 hm (N := N) (by omega) (-t)
    exact (i1.add i2).congr (Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
  have hmono := integral_mono hint i2 fun y => mul_le_mul_of_nonneg_right
    (archF_line_re_le (by omega) y) (add_nonneg (Bsq_nonneg ℓ m _) (Bsq_nonneg ℓ m _))
  rw [integral_aN_Bsq_add hℓ0 hℓ1 hm (by omega) t] at hmono
  have hA := integral_aN_Bsq_le hℓ0 hℓ1 hm hN hR t
  have hP := WHt_one_re_le hℓ0 m t
  unfold PhiUp
  have hπ : 0 < π := Real.pi_pos
  have : (1 / (2 * π)) * (2 * ∫ y : ℝ, aN N y * Bsq ℓ m (y - t)) =
      (1 / π) * ∫ y : ℝ, aN N y * Bsq ℓ m (y - t) := by field_simp
  have h1 : (1 / (2 * π)) * ∫ y : ℝ, (archF (((1 / 2 : ℝ) : ℂ) + y * I)).re * (Bsq ℓ m (y - t) + Bsq ℓ m (y + t)) ≤
      (1 / π) * (aN N (|t| + R) * KRB ℓ m R + (cN N + 1 / 2 * Real.log (1 + |t|)) * I0 m R + I1 m R) := by
    calc _ ≤ (1 / (2 * π)) * (2 * ∫ y : ℝ, aN N y * Bsq ℓ m (y - t)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (1 / π) * ∫ y : ℝ, aN N y * Bsq ℓ m (y - t) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

end TernaryGoldbach.Explicit
