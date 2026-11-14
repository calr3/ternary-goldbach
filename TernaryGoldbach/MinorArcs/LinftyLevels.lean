import TernaryGoldbach.MinorArcs.Prop1123b
import TernaryGoldbach.MinorArcs.PhiIntegrals

/-!
# The ℓ∞ input of the repaired Thm 13.2.1, level by level

For `α ∉ 𝔐_{8,n}(y)`, `y = x/κ`, `670 ≤ n ≤ y^{1/3}/6`:
`|S_{η_*}(α, x)| ≤ y · ĝ(y, n)` with the closed form
`ĝ(y, n) = 1.398 · max(g_y(n), h(y)) + 17 (670/n)³/3`, `h(z) = 0.276 z^{-1/6} (log z)^{3/2} + 1234 z^{-1/3} log z`
(`norm_S_etaStar_le_ghat`).  From `prop_11_2_3'` with `w₀ = 670/n`, `w₁ = ∞`, and the majorant
`G(w) = max(g_y(n), h(y)) · max(1, 1/w)`:
* `g_{wy}(wn) ≤ g_y(n)/w` for `w ≤ 1` and `g_{wy}(n) ≤ g_y(n)` for `w ≥ 1` (`gx_scale_le`);
* `h(wy) ≤ h(y) max(1, 1/w)` (`hfun_scale_le`);
* `∫_{w₀}^∞ max(1, 1/w) φ ≤ 1.398`, `∫_0^{w₀} φ ≤ w₀³/3`.
-/

open Real Set MeasureTheory

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 etaStar S phi κ majorArcs)

/-! ## Monotonicity of `Ϝ`, `L_t`, and of `g` in the scale -/

theorem Fs_monotoneOn : MonotoneOn Fs (Ici 6) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 6) ?_ ?_ ?_
  · intro s hs
    exact (Fs_hasDerivAt (by linarith [hs.out])).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact (Fs_hasDerivAt (by linarith [hs.out])).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs6 : 6 < s := hs
    rw [(Fs_hasDerivAt (by linarith)).deriv]
    have hl : 1.79 ≤ Real.log s := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have : rexp 1.79 ≤ 6 := by
        have h := Real.exp_bound' (x := 0.79) (by norm_num) (by norm_num) (n := 6) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at h
        have e : rexp 1.79 = rexp 1 * rexp 0.79 := by rw [← Real.exp_add]; norm_num
        rw [e]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 0.79]
      linarith
    have hs0 : 0 < s := by linarith
    have hg := one_half_le_exp_gamma
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hs0]
    have : 2.50637 ≤ rexp eulerMascheroniConstant * Real.log s ^ 2 := by nlinarith
    nlinarith

theorem Fr_monotoneOn : MonotoneOn Fr (Ici 670) := by
  intro a ha b hb hab
  have ha0 : 0 < a := by linarith [ha.out]
  have h6 : ∀ r ∈ Ici (670 : ℝ), (6 : ℝ) ≤ Real.log r := fun r hr => by
    rw [Real.le_log_iff_exp_le (by linarith [hr.out])]; exact exp_six_le.trans hr
  rw [Fr_eq_Fs, Fr_eq_Fs]
  exact Fs_monotoneOn (h6 a ha) (h6 b hb) (Real.log_le_log ha0 hab)

theorem Fr_pos {r : ℝ} (hr : 670 ≤ r) : 0 < Fr r := by
  have h6 : (6 : ℝ) ≤ Real.log r := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact exp_six_le.trans hr
  rw [Fr_eq_Fs]; linarith [Fs_ge (s := Real.log r) (by linarith)]

theorem Lg_monotoneOn : MonotoneOn Lg (Ici 1340) := by
  intro a ha b hb hab
  have ha' : (670 : ℝ) ≤ a / 2 := by linarith [ha.out]
  have hb' : (670 : ℝ) ≤ b / 2 := by linarith [hb.out]
  have hF := Fr_monotoneOn (show a / 2 ∈ Ici (670 : ℝ) from ha')
    (show b / 2 ∈ Ici (670 : ℝ) from hb') (by linarith)
  have hFa := Fr_pos ha'
  have hl := Real.log_le_log (by linarith [ha.out]) hab
  have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith [ha.out])
  unfold Lg
  have : Fr (a / 2) * (13 / 4 * Real.log a + 7.82) ≤ Fr (b / 2) * (13 / 4 * Real.log b + 7.82) :=
    mul_le_mul hF (by linarith) (by positivity) (by linarith)
  linarith

/-- `R_{z,t}` decreases in `z` and increases in `t` (in the range where both logarithms are
positive): `R z' t' ≤ R z t` if `t' ≤ t` and `9z^{1/3}/(2.004 t) ≤ 9z'^{1/3}/(2.004 t')`. -/
theorem R_le_R {z z' t t' : ℝ} (ht' : 1 ≤ 4 * t') (htt : t' ≤ t)
    (hb : 1 < 9 * z ^ (1 / 3 : ℝ) / (2.004 * t))
    (hbb : 9 * z ^ (1 / 3 : ℝ) / (2.004 * t) ≤ 9 * z' ^ (1 / 3 : ℝ) / (2.004 * t')) :
    R z' t' ≤ R z t := by
  unfold R
  have ht0 : 0 < t' := by linarith
  have hu := Real.log_le_log (by linarith) (show 4 * t' ≤ 4 * t by linarith)
  have hu0 : 0 ≤ Real.log (4 * t') := Real.log_nonneg ht'
  have hv0 : 0 < Real.log (9 * z ^ (1 / 3 : ℝ) / (2.004 * t)) := Real.log_pos hb
  have hv := Real.log_le_log (by linarith) hbb
  have hq : Real.log (4 * t') / (2 * Real.log (9 * z' ^ (1 / 3 : ℝ) / (2.004 * t'))) ≤
      Real.log (4 * t) / (2 * Real.log (9 * z ^ (1 / 3 : ℝ) / (2.004 * t))) := by
    apply div_le_div₀ (hu0.trans hu) hu (by positivity) (by linarith)
  have hq0 : 0 ≤ Real.log (4 * t') / (2 * Real.log (9 * z' ^ (1 / 3 : ℝ) / (2.004 * t'))) :=
    div_nonneg hu0 (by linarith)
  have := Real.log_le_log (by linarith) (add_le_add_right hq 1)
  linarith

/-- **Scaling of `g`**: for `w ≤ 1`, `g_{wy}(wn) ≤ g_y(n)/w`. -/
theorem gx_scale_le_of_le_one {y n w : ℝ} (hy : 0 < y) (hw : 0 < w) (hw1 : w ≤ 1)
    (hn : 670 ≤ w * n) (hny : n ≤ y ^ (1 / 3 : ℝ) / 6) :
    gx (w * y) (w * n) ≤ gx y n / w := by
  have hn0 : 0 < n := by nlinarith
  have hn670 : 670 ≤ n := by nlinarith
  have hw13 : w ≤ w ^ (1 / 3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hw hw1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  have hY : 0 < y ^ (1 / 3 : ℝ) := by positivity
  have hwy : (w * y) ^ (1 / 3 : ℝ) = w ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) :=
    Real.mul_rpow hw.le hy.le
  -- `R`
  have hR : R (w * y) (2 * (w * n)) ≤ R y (2 * n) := by
    refine R_le_R (by nlinarith) (by nlinarith) ?_ ?_
    · rw [one_lt_div (by positivity)]; nlinarith
    · rw [hwy, div_le_div_iff₀ (by positivity) (by positivity)]
      have : y ^ (1 / 3 : ℝ) * (2.004 * (2 * (w * n))) ≤
          w ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * (2.004 * (2 * n)) := by
        have := mul_le_mul_of_nonneg_left hw13 (by positivity : (0:ℝ) ≤ y ^ (1 / 3 : ℝ) * 4.008 * n)
        nlinarith
      nlinarith
  have hR0 : 0 ≤ R (w * y) (2 * (w * n)) := R_nonneg (by nlinarith) (by
    rw [hwy]
    have := mul_le_mul_of_nonneg_left hw13 (by positivity : (0:ℝ) ≤ y ^ (1 / 3 : ℝ))
    nlinarith)
  have hl : Real.log (2 * (w * n)) ≤ Real.log (2 * n) := Real.log_le_log (by nlinarith) (by nlinarith)
  have hl0 : 0 ≤ Real.log (2 * (w * n)) := Real.log_nonneg (by nlinarith)
  have hF : Fr (w * n) ≤ Fr n :=
    Fr_monotoneOn (show w * n ∈ Ici (670 : ℝ) from hn) (show n ∈ Ici (670 : ℝ) from hn670) (by nlinarith)
  have hF0 := Fr_pos hn
  have hnum : (R (w * y) (2 * (w * n)) * Real.log (2 * (w * n)) + 0.8764) * √(Fr (w * n)) + 2.511 ≤
      (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511 := by
    have h1 : R (w * y) (2 * (w * n)) * Real.log (2 * (w * n)) ≤ R y (2 * n) * Real.log (2 * n) :=
      mul_le_mul hR hl hl0 (hR0.trans hR)
    have h2 := Real.sqrt_le_sqrt hF
    have := mul_le_mul (add_le_add_right h1 0.8764) h2 (Real.sqrt_nonneg _) (by
      have := mul_nonneg (hR0.trans hR) (hl0.trans hl); linarith)
    linarith
  have hnum0 : 0 ≤ (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511 := by
    have := mul_nonneg (hR0.trans hR) (hl0.trans hl); positivity
  have hsq : √(2 * (w * n)) = √w * √(2 * n) := by
    rw [show 2 * (w * n) = w * (2 * n) by ring, Real.sqrt_mul hw.le]
  have hsw : w ≤ √w := by
    rw [Real.le_sqrt hw.le hw.le]; nlinarith
  have hA : ((R (w * y) (2 * (w * n)) * Real.log (2 * (w * n)) + 0.8764) * √(Fr (w * n)) + 2.511) /
      √(2 * (w * n)) ≤ ((R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511) / √(2 * n) / w := by
    rw [div_div, hsq]
    calc _ ≤ ((R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511) / (√w * √(2 * n)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left hnum0 (by positivity)
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hsw (Real.sqrt_nonneg _)
  have hL : Lg (2 * (w * n)) / (w * n) ≤ Lg (2 * n) / n / w := by
    rw [div_div, mul_comm n w]
    exact div_le_div_of_nonneg_right (Lg_monotoneOn (show 2 * (w * n) ∈ Ici (1340 : ℝ) by
      simp only [mem_Ici]; linarith) (show 2 * n ∈ Ici (1340 : ℝ) by simp only [mem_Ici]; linarith)
      (by nlinarith)) (by positivity)
  have hC : 3.8 * (w * y) ^ (-1 / 6 : ℝ) ≤ 3.8 * y ^ (-1 / 6 : ℝ) / w := by
    have h1 : w ^ (-1 / 6 : ℝ) ≤ w⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hw hw1 (by norm_num)
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 3.8 * y ^ (-1 / 6 : ℝ))
    calc 3.8 * (w * y) ^ (-1 / 6 : ℝ) = 3.8 * y ^ (-1 / 6 : ℝ) * w ^ (-1 / 6 : ℝ) := by
          rw [Real.mul_rpow hw.le hy.le]; ring
      _ ≤ 3.8 * y ^ (-1 / 6 : ℝ) * w⁻¹ := this
      _ = 3.8 * y ^ (-1 / 6 : ℝ) / w := by ring
  have e : gx y n / w = ((R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511) / √(2 * n) / w +
      Lg (2 * n) / n / w + 3.8 * y ^ (-1 / 6 : ℝ) / w := by unfold gx; ring
  rw [e]
  unfold gx
  linarith

/-- **Scaling of `g`**: for `w ≥ 1`, `g_{wy}(n) ≤ g_y(n)`. -/
theorem gx_scale_le_of_one_le {y n w : ℝ} (hy : 0 < y) (hw : 1 ≤ w)
    (hn : 670 ≤ n) (hny : n ≤ y ^ (1 / 3 : ℝ) / 6) :
    gx (w * y) n ≤ gx y n := by
  have hw0 : 0 < w := by linarith
  have hY : 0 < y ^ (1 / 3 : ℝ) := by positivity
  have hYw : y ^ (1 / 3 : ℝ) ≤ (w * y) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hy.le (by nlinarith) (by norm_num)
  have hR : R (w * y) (2 * n) ≤ R y (2 * n) := by
    refine R_le_R (by linarith) le_rfl ?_ ?_
    · rw [one_lt_div (by positivity)]; nlinarith
    · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hR0 : 0 ≤ R (w * y) (2 * n) := R_nonneg (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hF0 := Fr_pos hn
  have hA : (R (w * y) (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) ≤
      (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
  have hC : (w * y) ^ (-1 / 6 : ℝ) ≤ y ^ (-1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hy (by nlinarith) (by norm_num)
  unfold gx
  have := div_le_div_of_nonneg_right (show (R (w * y) (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511 ≤
    (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.511 by linarith) (Real.sqrt_nonneg (2 * n))
  have := mul_le_mul_of_nonneg_left hC (show (0:ℝ) ≤ 3.8 by norm_num)
  linarith

/-- Both cases: `g_{wy}(min(1, w) n) ≤ g_y(n) · max(1, 1/w)`. -/
theorem gx_scale_le {y n w : ℝ} (hy : 0 < y) (hw : 0 < w) (hn : 670 ≤ min 1 w * n)
    (hny : n ≤ y ^ (1 / 3 : ℝ) / 6) :
    gx (w * y) (min 1 w * n) ≤ gx y n * max 1 (1 / w) := by
  rcases le_total w 1 with h | h
  · rw [min_eq_right h] at hn ⊢
    rw [max_eq_right (by rw [le_div_iff₀ hw]; linarith), ← div_eq_mul_one_div]
    exact gx_scale_le_of_le_one hy hw h hn hny
  · rw [min_eq_left h, one_mul] at hn ⊢
    rw [max_eq_left (by rw [div_le_iff₀ hw]; linarith), mul_one]
    exact gx_scale_le_of_one_le hy h hn hny

/-! ## The second-case function `h` -/

/-- `h(z) = 0.276 z^{-1/6} (log z)^{3/2} + 1234 z^{-1/3} log z`: the second case of Thm 3.1.1,
divided by `z`. -/
noncomputable def hfun (z : ℝ) : ℝ :=
  0.276 * z ^ (-1 / 6 : ℝ) * Real.log z ^ (3 / 2 : ℝ) + 1234 * z ^ (-1 / 3 : ℝ) * Real.log z

theorem hfun_mul_self {z : ℝ} (hz : 0 < z) :
    0.276 * z ^ (5 / 6 : ℝ) * Real.log z ^ (3 / 2 : ℝ) + 1234 * z ^ (2 / 3 : ℝ) * Real.log z =
      hfun z * z := by
  unfold hfun
  have e1 : z ^ (5 / 6 : ℝ) = z ^ (-1 / 6 : ℝ) * z := by
    rw [← Real.rpow_add_one hz.ne']; norm_num
  have e2 : z ^ (2 / 3 : ℝ) = z ^ (-1 / 3 : ℝ) * z := by
    rw [← Real.rpow_add_one hz.ne']; norm_num
  rw [e1, e2]; ring

theorem hfun_antitone {z₁ z₂ : ℝ} (h9 : rexp 9 ≤ z₁) (h12 : z₁ ≤ z₂) : hfun z₂ ≤ hfun z₁ := by
  have hz₁ : 0 < z₁ := lt_of_lt_of_le (Real.exp_pos 9) h9
  have hz₂ : 0 < z₂ := by linarith
  have hs₁ : 9 ≤ Real.log z₁ := by rw [Real.le_log_iff_exp_le hz₁]; exact h9
  have hs12 := Real.log_le_log hz₁ h12
  have hrp : ∀ z : ℝ, 0 < z → ∀ p : ℝ, z ^ p = rexp (p * Real.log z) := fun z hz p => by
    rw [Real.rpow_def_of_pos hz, mul_comm]
  -- first term
  have hA := antitoneOn_mul_exp_neg (Q := fun s => s ^ (3 / 2 : ℝ))
    (Q' := fun s => 3 / 2 * s ^ (1 / 2 : ℝ)) (s₁ := 9) (s₂ := Real.log z₂) (p := 1 / 6)
    (fun s hs => by
      have := Real.hasDerivAt_rpow_const (x := s) (p := 3 / 2) (Or.inl (by linarith [hs.1]))
      convert this using 2; norm_num)
    (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have e : s ^ (3 / 2 : ℝ) = s * s ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hs0.le (by norm_num)]; norm_num
      rw [e]
      have : 0 ≤ s ^ (1 / 2 : ℝ) := by positivity
      nlinarith [hs.1])
  have hB := antitoneOn_mul_exp_neg (Q := fun s => s) (Q' := fun _ => 1) (s₁ := 9)
    (s₂ := Real.log z₂) (p := 1 / 3) (fun s _ => hasDerivAt_id s) (fun s hs => by
      linarith [hs.1])
  have m1 : Real.log z₁ ∈ Icc 9 (Real.log z₂) := ⟨hs₁, hs12⟩
  have m2 : Real.log z₂ ∈ Icc 9 (Real.log z₂) := ⟨hs₁.trans hs12, le_rfl⟩
  have h1 := hA m1 m2 hs12
  have h2 := hB m1 m2 hs12
  simp only at h1 h2
  unfold hfun
  rw [hrp z₁ hz₁, hrp z₂ hz₂, hrp z₁ hz₁ (-1 / 3), hrp z₂ hz₂ (-1 / 3)]
  have e1 : ∀ s : ℝ, rexp (-1 / 6 * s) = rexp (-(1 / 6) * s) := fun s => by ring_nf
  have e2 : ∀ s : ℝ, rexp (-1 / 3 * s) = rexp (-(1 / 3) * s) := fun s => by ring_nf
  rw [e1, e1, e2, e2]
  nlinarith

theorem hfun_nonneg {z : ℝ} (hz : 1 ≤ z) : 0 ≤ hfun z := by
  unfold hfun
  have := Real.log_nonneg hz
  positivity

/-- `h(wy) ≤ h(y) max(1, 1/w)` for `wy ≥ e⁹`, `y ≥ e⁹`. -/
theorem hfun_scale_le {y w : ℝ} (hy : rexp 9 ≤ y) (hw : 0 < w) (hwy : rexp 9 ≤ w * y) :
    hfun (w * y) ≤ hfun y * max 1 (1 / w) := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 9) hy
  rcases le_total 1 w with h | h
  · rw [max_eq_left (by rw [div_le_iff₀ hw]; linarith), mul_one]
    exact hfun_antitone hy (by nlinarith)
  · rw [max_eq_right (by rw [le_div_iff₀ hw]; linarith)]
    have hwy0 : 0 < w * y := by positivity
    have hl : Real.log (w * y) ≤ Real.log y := Real.log_le_log hwy0 (by nlinarith)
    have hl0 : 0 ≤ Real.log (w * y) := Real.log_nonneg (by
      have := Real.add_one_le_exp 9; linarith)
    have h6 : (w * y) ^ (-1 / 6 : ℝ) ≤ y ^ (-1 / 6 : ℝ) * (1 / w) := by
      rw [Real.mul_rpow hw.le hy0.le, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hw h (by norm_num)
    have h3 : (w * y) ^ (-1 / 3 : ℝ) ≤ y ^ (-1 / 3 : ℝ) * (1 / w) := by
      rw [Real.mul_rpow hw.le hy0.le, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hw h (by norm_num)
    have hp : Real.log (w * y) ^ (3 / 2 : ℝ) ≤ Real.log y ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hl0 hl (by norm_num)
    have hp0 : 0 ≤ Real.log (w * y) ^ (3 / 2 : ℝ) := by positivity
    unfold hfun
    have t1 : 0.276 * (w * y) ^ (-1 / 6 : ℝ) * Real.log (w * y) ^ (3 / 2 : ℝ) ≤
        0.276 * (y ^ (-1 / 6 : ℝ) * (1 / w)) * Real.log y ^ (3 / 2 : ℝ) := by
      gcongr
    have t2 : 1234 * (w * y) ^ (-1 / 3 : ℝ) * Real.log (w * y) ≤
        1234 * (y ^ (-1 / 3 : ℝ) * (1 / w)) * Real.log y := by
      gcongr
    nlinarith

/-! ## The integration step with `w₁ = ∞`, and the per-level bound -/

theorem norm_S_etaStar_le_of_pointwise_Ici {α x w₀ : ℝ} {G : ℝ → ℝ} (hx : 0 < x) (hw₀ : 0 < w₀)
    (hpw : ∀ w ∈ Ici w₀, ‖S eta2 (w * (x / κ)) α‖ ≤ G w * (w * (x / κ)))
    (hGi : IntegrableOn (fun w => G w * phi w) (Ici w₀)) :
    ‖S etaStar x α‖ ≤ x / κ * ((∫ w in Ici w₀, G w * phi w) + 17 * ∫ w in Ioo 0 w₀, phi w) := by
  have hκ : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
  set y := x / κ with hy_def
  have hy0 : 0 < y := div_pos hx hκ
  set B : ℝ → ℝ := fun w =>
    (Ioo 0 w₀).indicator (fun w => 17 * y * phi w) w +
      (Ici w₀).indicator (fun w => y * (G w * phi w)) w with hB
  have hφi : IntegrableOn (fun w => 17 * y * phi w) univ :=
    (integrable_phi.const_mul (17 * y)).integrableOn
  have I1 : Integrable ((Ioo 0 w₀).indicator (fun w => 17 * y * phi w)) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioo).restrict
  have I2 : Integrable ((Ici w₀).indicator (fun w => y * (G w * phi w))) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hGi.const_mul y) measurableSet_Ici).restrict
  have hBi : Integrable B (volume.restrict (Ioi 0)) := I1.add I2
  have hpt : ∀ w ∈ Ioi (0 : ℝ), ‖S eta2 (w * y) α‖ * (phi w / w) ≤ B w := by
    intro w (hw : 0 < w)
    have hφw : 0 ≤ phi w / w := div_nonneg (phi_nonneg w) hw.le
    rcases lt_or_ge w w₀ with h1 | h1
    · have : B w = 17 * y * phi w := by
        simp only [hB, indicator, mem_Ioo, mem_Ici, hw, h1, true_and, ite_true]
        rw [ite_eq_right (by intro h'; linarith)]; ring
      rw [this]
      have := norm_S_eta2_le_trivial (mul_pos hw hy0) α
      calc ‖S eta2 (w * y) α‖ * (phi w / w) ≤ 17 * (w * y) * (phi w / w) :=
            mul_le_mul_of_nonneg_right this hφw
        _ = 17 * y * phi w := by field_simp
    · have hBw : B w = y * (G w * phi w) := by
        simp only [hB, indicator, mem_Ioo, mem_Ici]
        rw [ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_left h1]; ring
      rw [hBw]
      calc ‖S eta2 (w * y) α‖ * (phi w / w) ≤ G w * (w * y) * (phi w / w) :=
            mul_le_mul_of_nonneg_right (hpw w h1) hφw
        _ = y * (G w * phi w) := by field_simp
  refine (norm_S_etaStar_le hx α).trans ?_
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun w => ‖S eta2 (w * y) α‖ * (phi w / w) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w (hw : 0 < w) =>
      mul_nonneg (norm_nonneg _) (div_nonneg (phi_nonneg w) hw.le))
  refine (integral_mono_of_nonneg hf0 hBi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))).trans (le_of_eq ?_)
  simp only [hB]
  rw [integral_add I1 I2, setIntegral_indicator measurableSet_Ioo,
    setIntegral_indicator measurableSet_Ici,
    inter_eq_right.2 Ioo_subset_Ioi_self,
    (inter_eq_right (s := Ioi (0:ℝ)) (t := Ici w₀)).2 (Ici_subset_Ioi.2 hw₀),
    integral_const_mul, integral_const_mul]
  ring

/-- `ĝ(y, n) = 1.398 max(g_y(n), h(y)) + 17 (670/n)³/3`. -/
noncomputable def ghatY (y n : ℝ) : ℝ := 1.398 * max (gx y n) (hfun y) + 17 * (670 / n) ^ 3 / 3

theorem exp_nine_le_y {y : ℝ} (hy : 1e25 ≤ y) : rexp 9 ≤ y := exp_nine_le.trans (by linarith)

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.RamareMoebius] in
/-- **The ℓ∞ input at level `n`**: for `y = x/κ ≥ 10²⁵`, `670 ≤ n ≤ y^{1/3}/6` and
`α ∉ 𝔐_{8,n}(y)`: `|S_{η_*}(α, x)| ≤ y ĝ(y, n)`. -/
theorem norm_S_etaStar_le_ghat {x n α : ℝ} (hx : 0 < x) (hy : 1e25 ≤ x / κ)
    (hn : 670 ≤ n) (hny : n ≤ (x / κ) ^ (1 / 3 : ℝ) / 6) (hny' : 2.16e20 * n ≤ 670 * (x / κ))
    (hα : α ∉ majorArcs 8 n (x / κ)) :
    ‖S etaStar x α‖ ≤ x / κ * ghatY (x / κ) n := by
  have hκ : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
  set y := x / κ with hy_def
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < n := by linarith
  set w₀ := 670 / n with hw₀_def
  have hw₀ : 0 < w₀ := by positivity
  have hw₀1 : w₀ ≤ 1 := by rw [hw₀_def, div_le_one hn0]; exact hn
  have hw₀n : w₀ * n = 670 := by rw [hw₀_def]; field_simp
  -- `n ≤ y^{1/3}/6` makes `w₀ y` huge
  have hw₀y : 2.16e20 ≤ w₀ * y := by
    rw [hw₀_def, div_mul_eq_mul_div, le_div_iff₀ hn0]; linarith
  set M := max (gx y n) (hfun y) with hM
  set G : ℝ → ℝ := fun w => M * max 1 (1 / w) with hG
  have hGi : IntegrableOn (fun w => G w * phi w) (Ici w₀) := by
    refine (integrable_phi.const_mul (|M| * max 1 (1 / w₀))).integrableOn.mono' ?_ ?_
    · exact ((measurable_const.mul (measurable_const.max (measurable_const.div measurable_id))).mul
        (by unfold phi; fun_prop)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun w (hw : w₀ ≤ w) => ?_)
      have hw0 : 0 < w := lt_of_lt_of_le hw₀ hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (phi_nonneg w),
        abs_of_nonneg (le_max_of_le_left zero_le_one : (0:ℝ) ≤ max 1 (1 / w))]
      have : max 1 (1 / w) ≤ max 1 (1 / w₀) := max_le_max le_rfl (one_div_le_one_div_of_le hw₀ hw)
      have := mul_le_mul_of_nonneg_left this (abs_nonneg M)
      nlinarith [phi_nonneg w]
  have hpw : ∀ w ∈ Ici w₀, ‖S eta2 (w * y) α‖ ≤ G w * (w * y) := by
    intro w (hw : w₀ ≤ w)
    have hw0 : 0 < w := lt_of_lt_of_le hw₀ hw
    have hlow : 670 ≤ min 1 w * n := by
      have : w₀ ≤ min 1 w := le_min hw₀1 hw
      nlinarith
    have hz : 2.16e20 ≤ w * y := hw₀y.trans (mul_le_mul_of_nonneg_right hw hy0.le)
    refine norm_S_eta2_le_of_not_mem hy0 hα hw0 hz hlow (fun _ => ?_) ?_
    · exact (gx_scale_le hy0 hw0 hlow hny).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_of_le_left zero_le_one))
    · rw [hfun_mul_self (by linarith)]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      exact (hfun_scale_le (exp_nine_le_y hy) hw0 (exp_nine_le.trans (by linarith))).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_max_of_le_left zero_le_one))
  have key := norm_S_etaStar_le_of_pointwise_Ici hx hw₀ hpw hGi
  have hM0 : 0 ≤ M := (hfun_nonneg (by linarith)).trans (le_max_right _ _)
  have hint : ∫ w in Ici w₀, G w * phi w ≤ 1.398 * M := by
    have : ∫ w in Ici w₀, G w * phi w = M * ∫ w in Ici w₀, max 1 (1 / w) * phi w := by
      rw [← integral_const_mul]; congr 1; ext w; simp only [hG]; ring
    rw [this]
    have := integral_max_inv_phi_le hw₀ hw₀1
    nlinarith
  have hI2 := integral_phi_Ioo_le hw₀.le
  refine key.trans ?_
  unfold ghatY
  rw [← hM, ← hw₀_def]
  gcongr
  linarith

end TernaryGoldbach.MinorArcs
