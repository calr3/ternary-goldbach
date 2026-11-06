import TernaryGoldbach.Explicit.WeilLines

/-!
# The Weil explicit formula

For `0 < ℓ ≤ 1`, `m ≥ 2`, `e^{2mℓ} < 2` and any `T₀`, along good heights `T_k ∈ [k, k+1]`
(`goodT`):
`2π Σ_{ρ ∈ R_{T_k}} m_ρ H_{T₀}(ρ) → 2π H̃(1) + ∫ A(½ + iy) H̃(½ + iy) dy`,
where `R_T = [−1/2, 3/2] × [−T, T]`, `H̃ = H_{T₀} + H_{T₀}(1 − ·)` and `A(s) = −½ log π + ½ψ(s/2)`
(`weil_formula`). The prime side is `0` (`2mℓ < log 2`); this is the classical
`Σ_γ h(γ) = h(i/2) + h(−i/2) − g(0) log π + (1/2π) ∫ h(r) Re ψ(¼ + ir/2) dr` (`scripts/weil_check.py`).
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

variable {ℓ : ℝ} {m : ℕ}

/-! ### Good heights -/

/-- A good height in `[k, k+1]` (`good_heightD`). -/
noncomputable def goodT (k : ℕ) : ℝ := Classical.choose (good_heightD ldatum_zeta2 k)

theorem goodT_mem (k : ℕ) : goodT k ∈ Icc (k : ℝ) (k + 1) :=
  (Classical.choose_spec (good_heightD ldatum_zeta2 k)).1

theorem goodT_good (k : ℕ) : GoodH k (goodT k) :=
  (Classical.choose_spec (good_heightD ldatum_zeta2 k)).2

theorem tendsto_goodT : Tendsto goodT atTop atTop :=
  tendsto_atTop_mono (fun k => (goodT_mem k).1) tendsto_natCast_atTop_atTop

/-- `MX(k) L(T_k ± T₀) → 0`. -/
theorem tendsto_MX_lor (T₀ : ℝ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    Tendsto (fun k : ℕ => MX k * lor (sgn * goodT k - T₀)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 23) ^ 2 / (1 * ((k : ℝ) + 23) + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 23 tendsto_natCast_atTop_atTop)
  have hlim2 : Tendsto (fun k : ℕ => 8 * ((C3 + 14) / ((k : ℝ) + 23) +
      2700 * (Real.log ((k : ℝ) + 23) ^ 2 / (1 * ((k : ℝ) + 23) + 0)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (C3 + 14) / ((k : ℝ) + 23)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 23 tendsto_natCast_atTop_atTop)
    simpa using (h1.add (hlim.const_mul 2700)).const_mul 8
  refine squeeze_zero' (Eventually.of_forall fun k => mul_nonneg (MX_nonneg k) (lor_pos _).le) ?_ hlim2
  filter_upwards [eventually_ge_atTop (⌈2 * |T₀| + 46⌉₊)] with k hk
  have hk' : 2 * |T₀| + 46 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hT := goodT_mem k
  have hk0 : (0 : ℝ) < k + 23 := by positivity
  -- `|sgn T_k − T₀| ≥ (k + 23)/2`
  have hu : ((k : ℝ) + 23) / 2 ≤ |sgn * goodT k - T₀| := by
    have hT0 := abs_nonneg T₀
    rcases hsgn with rfl | rfl
    · rw [one_mul]
      calc ((k : ℝ) + 23) / 2 ≤ goodT k - T₀ := by linarith [hT.1, le_abs_self T₀]
        _ ≤ |goodT k - T₀| := le_abs_self _
    · calc ((k : ℝ) + 23) / 2 ≤ -(-1 * goodT k - T₀) := by linarith [hT.1, neg_abs_le T₀]
        _ ≤ |-1 * goodT k - T₀| := neg_le_abs _
  have hlor : lor (sgn * goodT k - T₀) ≤ 8 / ((k : ℝ) + 23) := by
    unfold lor
    rw [div_le_div_iff₀ (by positivity) hk0]
    have hsq : (((k : ℝ) + 23) / 2) ^ 2 ≤ (sgn * goodT k - T₀) ^ 2 := by
      rw [← sq_abs (sgn * goodT k - T₀)]; exact pow_le_pow_left₀ (by positivity) hu 2
    nlinarith
  have hMX := MX_le k
  have hMX0 := MX_nonneg k
  calc MX k * lor (sgn * goodT k - T₀) ≤ ((C3 + 14) + 2700 * Real.log ((k : ℝ) + 23) ^ 2) *
      (8 / ((k : ℝ) + 23)) := mul_le_mul hMX hlor (lor_pos _).le (by linarith)
    _ = 8 * ((C3 + 14) / ((k : ℝ) + 23) + 2700 * (Real.log ((k : ℝ) + 23) ^ 2 / (1 * ((k : ℝ) + 23) + 0))) := by
        rw [one_mul, add_zero]; field_simp

/-! ### The integral on `ℜs = 3/2` -/

theorem continuous_logDeriv_zeta_line : Continuous fun y : ℝ => logDeriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + y * I
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp [s] at this; norm_num at this
  have hU : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
    (differentiableAt_riemannZeta hw).differentiableWithinAt
  have ha : AnalyticAt ℂ riemannZeta s := hd.analyticAt (hU.mem_nhds hs1)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp [s]; norm_num)
  have hc : ContinuousAt (logDeriv riemannZeta) s := by
    have : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
      funext w; rw [logDeriv_apply]
    rw [this]
    exact ha.deriv.continuousAt.div ha.continuousAt hz
  exact hc.comp (f := fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + y * I) (by fun_prop)

theorem integrable_logDeriv_zeta_WHt (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 1 ≤ m) (T₀ : ℝ) :
    Integrable fun y : ℝ => logDeriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) *
      WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) := by
  refine ((integrable_WHt_line hℓ0 hℓ1 hm T₀ (3 / 2)).norm.const_mul C3).mono'
    ((continuous_logDeriv_zeta_line.mul ((differentiable_WHt ℓ m T₀).continuous.comp
      (by fun_prop))).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_logDeriv_zeta_le (by simp)) (norm_nonneg _)

/-- `ξ'/ξ · H̃ = (polar) + (archimedean) + (prime)` on `ℜs = 3/2`. -/
theorem logDeriv_xiF_WHt_eq (ℓ : ℝ) (m : ℕ) (T₀ y : ℝ) :
    logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) =
      WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) +
      archF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) +
      logDeriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + y * I with hs
  have hre : s.re = 3 / 2 := by simp [hs]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hre; norm_num at hre
  have hs1 : s ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
  have hξ : xiF s ≠ 0 := xiF_ne_zero_of_one_le_re (by rw [hre]; norm_num)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; norm_num)
  rw [logDeriv_xiF (by rw [hre]; norm_num) hs1 hξ, logDeriv_zetaF_eq hs1 hz, WP_eq hs0 hs1]
  unfold archF
  ring

theorem integrable_logDeriv_xiF_WHt (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (T₀ : ℝ) :
    Integrable fun y : ℝ => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) := by
  rw [show (fun y : ℝ => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I)) =
    fun y => _ from funext (logDeriv_xiF_WHt_eq ℓ m T₀)]
  exact ((integrable_WP_three_halves hℓ0 hℓ1 hm T₀).add
    (integrable_archF_WHt hℓ0 hℓ1 hm T₀ ⟨by norm_num, le_rfl⟩)).add
    (integrable_logDeriv_zeta_WHt hℓ0 hℓ1 (by omega) T₀)

/-- `∫ ξ'/ξ(3/2 + iy) H̃(3/2 + iy) dy = 2π H̃(1) + ∫ A(½ + iy) H̃(½ + iy) dy`. -/
theorem integral_logDeriv_xiF_WHt (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) (T₀ : ℝ) :
    ∫ y : ℝ, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) =
      2 * π * WHt ℓ m T₀ 1 + ∫ y : ℝ, archF (((1 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I) := by
  simp only [logDeriv_xiF_WHt_eq]
  have iA := integrable_WP_three_halves hℓ0 hℓ1 hm T₀
  have iB := integrable_archF_WHt hℓ0 hℓ1 hm T₀ (c := 3 / 2) ⟨by norm_num, le_rfl⟩
  have iC := integrable_logDeriv_zeta_WHt (m := m) hℓ0 hℓ1 (by omega) T₀
  have iAB : Integrable (fun y : ℝ => WP ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I) +
      archF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I)) := iA.add iB
  rw [integral_add iAB iC, integral_add iA iB, J1_eq hℓ0 hℓ1 hm T₀, J2_shift hℓ0 hℓ1 hm T₀,
    integral_logDeriv_zeta_WHt hℓ0 hℓ1 (by omega) h2 T₀]
  ring

/-! ### The limit -/

/-- **The Weil explicit formula** (as a limit over the rectangles `R_{T_k}`). -/
theorem weil_formula (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 2 ≤ m) (h2 : Real.exp (2 * m * ℓ) < 2) (T₀ : ℝ) :
    Tendsto (fun k : ℕ => 2 * π * ∑ u ∈ rectZerosXi (goodT k), (mult (goodT k) u : ℂ) * WH ℓ m T₀ u)
      atTop (𝓝 (2 * π * WHt ℓ m T₀ 1 +
        ∫ y : ℝ, archF (((1 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I))) := by
  have hm1 : 1 ≤ m := by omega
  set f : ℝ → ℂ := fun y => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((3 / 2 : ℝ) : ℂ) + y * I)
    with hf
  set E : ℕ → ℂ := fun k => -I * ((∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2),
      logDeriv xiF (x + ((-goodT k : ℝ) : ℂ) * I) * WH ℓ m T₀ (x + ((-goodT k : ℝ) : ℂ) * I)) -
      ∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), logDeriv xiF (x + (goodT k : ℂ) * I) * WH ℓ m T₀ (x + (goodT k : ℂ) * I))
    with hE
  -- the rectangle identity, for `k ≥ 8`
  have hid : ∀ᶠ k : ℕ in atTop, 2 * π * ∑ u ∈ rectZerosXi (goodT k), (mult (goodT k) u : ℂ) * WH ℓ m T₀ u =
      (∫ y : ℝ in (-goodT k)..(goodT k), f y) + E k := by
    filter_upwards [eventually_ge_atTop 8] with k hk
    have h := weil_rect hk (goodT_mem k) (goodT_good k) (differentiable_WH ℓ m T₀)
    simp only [hE, hf, WHt]
    rw [← h]; ring
  -- the horizontal sides tend to `0`
  have hE0 : Tendsto E atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ᶠ k : ℕ in atTop, ‖E k‖ ≤ 2 * (4 ^ m * Real.exp (2 * m * ℓ)) *
        (MX k * lor (-1 * goodT k - T₀) + MX k * lor (1 * goodT k - T₀)) := by
      filter_upwards [eventually_ge_atTop 8] with k hk
      have hT := goodT_mem k
      have hk8 : (8 : ℝ) ≤ k := by exact_mod_cast hk
      have hb1 := norm_horiz_le hℓ0 hℓ1 hm1 T₀ hk hT (goodT_good k) (y := -goodT k)
        (by rw [abs_neg, abs_of_pos (by linarith [hT.1])])
      have hb2 := norm_horiz_le hℓ0 hℓ1 hm1 T₀ hk hT (goodT_good k) (y := goodT k)
        (abs_of_pos (by linarith [hT.1]))
      simp only [hE, norm_mul, norm_neg, Complex.norm_I, one_mul]
      refine (norm_sub_le _ _).trans ?_
      simp only [neg_one_mul]
      nlinarith [hb1, hb2]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ?_
    have h1 := tendsto_MX_lor T₀ (-1) (Or.inr rfl)
    have h3 := tendsto_MX_lor T₀ 1 (Or.inl rfl)
    simpa using (h1.add h3).const_mul (2 * (4 ^ m * Real.exp (2 * m * ℓ)))
  -- the vertical integral converges
  have hint : Tendsto (fun k : ℕ => ∫ y : ℝ in (-goodT k)..(goodT k), f y) atTop (𝓝 (∫ y, f y)) :=
    intervalIntegral_tendsto_integral (integrable_logDeriv_xiF_WHt hℓ0 hℓ1 hm T₀)
      (tendsto_neg_atTop_atBot.comp tendsto_goodT) tendsto_goodT
  have hlim := hint.add hE0
  rw [add_zero, integral_logDeriv_xiF_WHt hℓ0 hℓ1 hm h2 T₀] at hlim
  exact hlim.congr' (hid.mono fun k hk => hk.symm)

end TernaryGoldbach.Explicit
