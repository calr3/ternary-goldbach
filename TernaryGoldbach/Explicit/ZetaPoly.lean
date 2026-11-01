import TernaryGoldbach.Explicit.ZetaExplicit
import TernaryGoldbach.Explicit.ZeroSumGen
import TernaryGoldbach.Explicit.LGrowthPoly

/-!
# Polynomial growth of `(s − 1)ζ(s)`, and its zeros in the rectangle

With the rotation bound for `Γ(1 − w)` (angle `π/2 − 1/(|t|+1)`, as in `LGrowthPoly`) the factor
`e^{π|t|/2}` from `sin(πw/2)` cancels: `|zetaF| ≤ B'_ζ(T) = 5.61·10⁵ (|T|+22)³ (1.25(|T|+11))⁹` on
`|w − (2 + iT)| ≤ 10`. The zeros of `zetaF` in the rectangle `(−1/2, 3/2) × (−T, T)` lie in `0 < ℜs < 1`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- **Polynomial growth on the left**: for `−8 ≤ ℜw ≤ 1/4`,
`|zetaF(w)| ≤ 2·40320·1.18·(π/2)·e · (1.25(|ℑw|+1))⁹ |w − 1| (|1 − w| + |1 − w||w|/(1 − ℜw))`. -/
theorem norm_zetaF_left_poly {w : ℂ} (h1 : -8 ≤ w.re) (h2 : w.re ≤ 1 / 4) :
    ‖zetaF w‖ ≤ 2 * 40320 * 1.18 * (π / 2) * Real.exp 1 * (1.25 * (|w.im| + 1)) ^ (9 : ℝ) *
      ‖w - 1‖ * (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re)) := by
  have hpi := Real.pi_gt_three
  have hR0 : 0 < 1 - w.re := by linarith
  have hP1 : (1:ℝ) ≤ (1.25 * (|w.im| + 1)) ^ (9 : ℝ) :=
    Real.one_le_rpow (by nlinarith [abs_nonneg w.im]) (by norm_num)
  by_cases hw0 : w = 0
  · subst hw0
    have h0 : zetaF 0 = 1 / 2 := by
      rw [zetaF_of_ne (by norm_num), riemannZeta_zero]; norm_num
    rw [h0]
    simp only [zero_sub, norm_neg, norm_one, Complex.zero_im, abs_zero, sub_zero, norm_zero,
      Complex.zero_re, mul_zero, zero_div, add_zero, mul_one, zero_add]
    norm_num
    have he := Real.exp_one_gt_d9
    nlinarith
  rw [zetaF_left_eq hw0 h2]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  obtain ⟨hφ0, hφ, -, hφt⟩ := angle_facts w.im
  set φ := π / 2 - 1 / (|w.im| + 1) with hφdef
  have hcp : ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ ≤ 1 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    simp; linarith
  have hre1 : (1 - w).re = 1 - w.re := by simp
  have him1 : |(1 - w).im| = |w.im| := by simp
  have hG : ‖Complex.Gamma (1 - w)‖ ≤ Real.exp (-(φ * |w.im|)) * 40320 * (1.25 * (|w.im| + 1)) ^ (9 : ℝ) := by
    have h := norm_Gamma_le_rot (a := 1 - w) (by rw [hre1]; linarith) hφ0 hφ
    rw [hre1, him1] at h
    refine h.trans ?_
    have hΓ := Gamma_le_40320 (x := 1 - w.re) (by linarith) (by linarith)
    have hc := cos_rpow_neg_le w.im (a := 1 - w.re) (by linarith)
    have hc' : (1.25 * (|w.im| + 1)) ^ (1 - w.re) ≤ (1.25 * (|w.im| + 1)) ^ (9 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg w.im]) (by linarith)
    have hcp0 : 0 ≤ (Real.cos φ) ^ (-(1 - w.re)) :=
      Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by positivity) (angle_facts w.im).2.2.1)) _
    have he := Real.exp_pos (-(φ * |w.im|))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΓ he.le) (hc.trans hc') hcp0 (by positivity)
  have hsin : ‖Complex.sin (π * w / 2)‖ ≤ 1.18 * (π / 2 * ‖w‖) * Real.exp (π * |w.im| / 2) := by
    refine (norm_sin_le_mul _).trans (le_of_eq ?_)
    have hn : ‖(π : ℂ) * w / 2‖ = π / 2 * ‖w‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; ring
    have him : ((π : ℂ) * w / 2).im = π * w.im / 2 := by simp
    rw [hn, him, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  have hZ : ‖zetaF (1 - w)‖ ≤ ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) := by
    have := norm_zetaF_le (s := 1 - w) (by rw [hre1]; linarith)
    rwa [hre1, show (1 - w - 1) = -w by ring, norm_neg] at this
  have hexp : Real.exp (-(φ * |w.im|)) * Real.exp (π * |w.im| / 2) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (π / 2 - φ) * |w.im| ≤ 1 := hφt
    nlinarith
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_div, norm_neg, Complex.norm_ofNat]
  have hZ0 : 0 ≤ ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) := by positivity
  have hP0 : 0 ≤ (1.25 * (|w.im| + 1)) ^ (9 : ℝ) := by positivity
  have hsw : ‖Complex.sin (π * w / 2)‖ / ‖w‖ ≤ 1.18 * (π / 2) * Real.exp (π * |w.im| / 2) := by
    rw [div_le_iff₀ hwn]
    calc ‖Complex.sin (π * w / 2)‖ ≤ 1.18 * (π / 2 * ‖w‖) * Real.exp (π * |w.im| / 2) := hsin
      _ = _ := by ring
  calc ‖w - 1‖ * (2 * ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ * ‖Complex.Gamma (1 - w)‖ *
        ‖Complex.sin (π * w / 2)‖ * (‖zetaF (1 - w)‖ / ‖w‖))
      = ‖w - 1‖ * (2 * ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ * ‖Complex.Gamma (1 - w)‖ *
          (‖Complex.sin (π * w / 2)‖ / ‖w‖) * ‖zetaF (1 - w)‖) := by ring
    _ ≤ ‖w - 1‖ * (2 * 1 * (Real.exp (-(φ * |w.im|)) * 40320 * (1.25 * (|w.im| + 1)) ^ (9 : ℝ)) *
          (1.18 * (π / 2) * Real.exp (π * |w.im| / 2)) *
          (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re))) := by gcongr
    _ = 2 * 40320 * 1.18 * (π / 2) * (Real.exp (-(φ * |w.im|)) * Real.exp (π * |w.im| / 2)) *
          (1.25 * (|w.im| + 1)) ^ (9 : ℝ) * ‖w - 1‖ * (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re)) := by ring
    _ ≤ 2 * 40320 * 1.18 * (π / 2) * Real.exp 1 *
          (1.25 * (|w.im| + 1)) ^ (9 : ℝ) * ‖w - 1‖ * (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re)) := by
        gcongr

/-- `B'_ζ(T) = 5.61·10⁵ (|T|+22)³ (1.25(|T|+11))⁹`. -/
noncomputable def BPz (T : ℝ) : ℝ := 5.61e5 * (|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ (9 : ℝ)

theorem BPz_ge (T : ℝ) : 5.61e5 * (|T| + 22) ^ 3 ≤ BPz T := by
  unfold BPz
  have : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ (9 : ℝ) := Real.one_le_rpow (by nlinarith [abs_nonneg T]) (by norm_num)
  have h0 : 0 ≤ 5.61e5 * (|T| + 22) ^ 3 := by positivity
  nlinarith

theorem norm_zetaF_le_BPz (T : ℝ) {w : ℂ} (hw : w ∈ closedBall (2 + T * I) 10) :
    ‖zetaF w‖ ≤ BPz T := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - (2 + T * I))
  have him := Complex.abs_im_le_norm (w - (2 + T * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im,
    Complex.add_im, Complex.im_ofNat, Complex.mul_im, zero_add, add_zero] at hre him
  have hwim1 : |w.im| ≤ |T| + 10 := by
    have := abs_sub_abs_le_abs_sub w.im T; linarith [abs_sub_comm w.im T]
  have hre1 : -8 ≤ w.re := by linarith [neg_abs_le (w.re - 2)]
  have hre2 : w.re ≤ 12 := by linarith [le_abs_self (w.re - 2)]
  have hT0 := abs_nonneg T
  have hwn : ‖w‖ ≤ |T| + 22 := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    have : |w.re| ≤ 12 := abs_le.2 ⟨by linarith, hre2⟩
    linarith
  have hw1 : ‖w - 1‖ ≤ |T| + 22 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have : |(w - 1).re| ≤ 11 := by simp; rw [abs_le]; constructor <;> linarith
    have h2 : |(w - 1).im| = |w.im| := by simp
    linarith
  have h1w : ‖1 - w‖ ≤ |T| + 22 := by rw [norm_sub_rev]; exact hw1
  have hB := BPz_ge T
  rcases le_total w.re (1 / 4) with h | h
  · refine (norm_zetaF_left_poly hre1 h).trans ?_
    have hR : 3 / 4 ≤ 1 - w.re := by linarith
    have hX : ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) ≤ 1.38 * (|T| + 22) ^ 2 := by
      have h3 : ‖1 - w‖ * ‖w‖ / (1 - w.re) ≤ (|T| + 22) * (|T| + 22) / (3 / 4) := by
        apply div_le_div₀ (by positivity) (mul_le_mul h1w hwn (norm_nonneg _) (by positivity))
          (by norm_num) hR
      nlinarith
    have hP : (1.25 * (|w.im| + 1)) ^ (9 : ℝ) ≤ (1.25 * (|T| + 11)) ^ (9 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hpi := Real.pi_lt_d4
    have he := Real.exp_one_lt_d9
    calc 2 * 40320 * 1.18 * (π / 2) * Real.exp 1 * (1.25 * (|w.im| + 1)) ^ (9 : ℝ) *
          ‖w - 1‖ * (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re))
        ≤ 2 * 40320 * 1.18 * (3.1416 / 2) * 2.7182818286 * (1.25 * (|T| + 11)) ^ (9 : ℝ) *
          (|T| + 22) * (1.38 * (|T| + 22) ^ 2) := by gcongr
      _ ≤ BPz T := by
          unfold BPz
          have hx : 0 ≤ (|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ (9 : ℝ) := by positivity
          have : (2 * 40320 * 1.18 * (3.1416 / 2) * 2.7182818286 * 1.38 : ℝ) ≤ 5.61e5 := by norm_num
          calc 2 * 40320 * 1.18 * (3.1416 / 2) * 2.7182818286 * (1.25 * (|T| + 11)) ^ (9 : ℝ) *
                (|T| + 22) * (1.38 * (|T| + 22) ^ 2)
              = (2 * 40320 * 1.18 * (3.1416 / 2) * 2.7182818286 * 1.38) *
                ((|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ (9 : ℝ)) := by ring
            _ ≤ 5.61e5 * ((|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ (9 : ℝ)) :=
                mul_le_mul_of_nonneg_right this hx
            _ = _ := by ring
  · refine (norm_zetaF_le (by linarith)).trans ?_
    have h3 : ‖w‖ * ‖w - 1‖ / w.re ≤ (|T| + 22) * (|T| + 22) / (1 / 4) :=
      div_le_div₀ (by positivity) (mul_le_mul hwn hw1 (norm_nonneg _) (by positivity)) (by norm_num) h
    have : ‖w‖ + ‖w‖ * ‖w - 1‖ / w.re ≤ 5 * (|T| + 22) ^ 2 := by nlinarith
    refine this.trans ?_
    have : 5 * (|T| + 22) ^ 2 ≤ 5.61e5 * (|T| + 22) ^ 3 := by
      have h22 : (22:ℝ) ≤ |T| + 22 := by linarith
      nlinarith [sq_nonneg (|T| + 22)]
    linarith

theorem polyDatum_zeta : PolyDatum zetaF BPz 12 where
  diff := differentiable_zetaF
  center_ge := zetaF_center_ge
  bound := fun T w hw => norm_zetaF_le_BPz T hw
  B_ge := fun T => by
    have := BPz_ge T
    have : (1:ℝ) ≤ 5.61e5 * (|T| + 22) ^ 3 := by
      have : (22:ℝ) ^ 3 ≤ (|T| + 22) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith [abs_nonneg T]) 3
      nlinarith
    linarith
  B_mono := fun T T' h => by
    unfold BPz
    have h1 : (|T| + 22) ^ 3 ≤ (|T'| + 22) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h2 : (1.25 * (|T| + 11)) ^ (9 : ℝ) ≤ (1.25 * (|T'| + 11)) ^ (9 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by positivity)
  growth := fun T0 m hT0 hm => by
    have e : ∀ c : ℝ, 0 ≤ c → Real.log (BPz c / 0.355) = Real.log 5.61e5 + 3 * Real.log (c + 22) +
        9 * Real.log (1.25 * (c + 11)) - Real.log 0.355 := by
      intro c hc
      unfold BPz
      rw [abs_of_nonneg hc, Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        Real.log_rpow (by positivity)]
      push_cast; ring
    rw [e _ (by linarith), e _ hT0.le]
    have h1 : Real.log (T0 + m + 22) - Real.log (T0 + 22) ≤ m / T0 := by
      rw [← Real.log_div (by linarith) (by linarith)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) hT0]; nlinarith
    have h2 : Real.log (1.25 * (T0 + m + 11)) - Real.log (1.25 * (T0 + 11)) ≤ m / T0 := by
      rw [← Real.log_div (by positivity) (by positivity)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hT0]; nlinarith
    have : 12 * m / T0 = 3 * (m / T0) + 9 * (m / T0) := by ring
    linarith
  κ_nonneg := by norm_num

/-! ## Zeros of `zetaF` in the rectangle -/

theorem zetaF_ne_zero_re_zero {s : ℂ} (h0 : s.re = 0) : zetaF s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst hs0; rw [zetaF_of_ne (by norm_num), riemannZeta_zero]; norm_num
  rw [zetaF_left_eq hs0 (by rw [h0]; norm_num)]
  have hs1 : s ≠ 1 := by intro h; rw [h] at h0; simp at h0
  have hre1 : (1 - s).re = 1 := by simp [h0]
  have h1s : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  refine mul_ne_zero (sub_ne_zero.2 hs1) (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    two_ne_zero ?_) ?_) ?_) (div_ne_zero ?_ (neg_ne_zero.2 hs0)))
  · rw [Complex.cpow_ne_zero_iff]; left
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    rw [hre1] at this; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    apply hs0
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs : s = 2 * (k : ℂ) := by
      have : (π : ℂ) * (s - 2 * k) = 0 := by linear_combination 2 * hk
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hπ
      · linear_combination h
    have hk0 : k = 0 := by
      have := congrArg Complex.re hs
      simp [h0] at this
      exact_mod_cast this
    rw [hs, hk0]; simp
  · rw [zetaF_of_ne h1s]
    refine mul_ne_zero (by rw [show 1 - s - 1 = -s by ring]; exact neg_ne_zero.2 hs0) ?_
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hre1])

theorem zetaF_ne_zero_one_le {s : ℂ} (h : 1 ≤ s.re) : zetaF s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; rw [zetaF_one]; exact one_ne_zero
  rw [zetaF_of_ne hs1]
  exact mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re h)

/-- The zeros of `zetaF` in the rectangle lie in `0 < ℜs < 1`. -/
theorem zerosRectD_zetaF_cases {T : ℝ} {u : ℂ} (hu : u ∈ zerosRectD zetaF T) :
    zetaF u = 0 ∧ (u = 0 ∨ (0 < u.re ∧ u.re < 1)) := by
  rw [zerosRectD, Finset.mem_filter] at hu
  obtain ⟨hu, h1, h2, -, -⟩ := hu
  simp only [zT_re, wT_re] at h1 h2
  have hL := eq_zero_of_mem_zerosIn differentiable_zetaF hu
  refine ⟨hL, Or.inr ⟨?_, ?_⟩⟩
  · by_contra h
    push Not at h
    rcases lt_or_eq_of_le h with h' | h'
    · exact zetaF_ne_zero_strip (by linarith) h' hL
    · exact zetaF_ne_zero_re_zero h' hL
  · by_contra h
    push Not at h
    exact zetaF_ne_zero_one_le h hL

end TernaryGoldbach.Explicit
