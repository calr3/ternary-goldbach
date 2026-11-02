import TernaryGoldbach.Explicit.GaussSmooth
import TernaryGoldbach.Explicit.ZetaPoly
import TernaryGoldbach.Explicit.ZeroFreeRegion
import TernaryGoldbach.Explicit.XiPartial

/-!
# Sums over the zeros of `ζ` for the Gaussian smoothing

* zeros with `|γ| ≤ H = 3·10¹²` lie on the critical line ([Platt–Trudgian 2021], numerical axiom);
  they are counted in windows of width `3.48` (`count_line_windowG`) and weighted by `1/max(1, |γ|)`;
* zeros with `|γ| > H` are weighted by the Gaussian factor `e^{−δ²γ²/2}` (geometric windows,
  `count_tail_windowG`, `sum_geom_windows`).
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology

namespace TernaryGoldbach.Explicit

/-- **Numerical axiom** ([Platt–Trudgian 2021], *The Riemann hypothesis is true up to 3·10¹²*,
Bull. LMS 53 (2021), arXiv:2004.09765): every zero of `ζ` in the critical strip with `|ℑρ| ≤ 3·10¹²`
lies on the critical line. [PT21] state it for `0 < ℑρ ≤ 3·10¹²`. Zeros with `ℑρ < 0` are the
conjugates of those (`ζ(s̄) = conj ζ(s)`), and there are none with `ℑρ = 0`, since `ζ(σ) < 0` for
`0 < σ < 1` (classical). -/
axiom rh_upto : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 3e12 → ρ.re = 1 / 2

theorem zetaF_zero_ne_zero : zetaF 0 ≠ 0 := by
  rw [zetaF_of_ne (by norm_num), riemannZeta_zero]; norm_num

/-- The zeros in the rectangles are nontrivial zeros of `ζ` and zeros of `ξ`. -/
theorem zerosRectD_zetaF_strip {T : ℝ} {u : ℂ} (hu : u ∈ zerosRectD zetaF T) :
    riemannZeta u = 0 ∧ 0 < u.re ∧ u.re < 1 ∧ xiF u = 0 := by
  obtain ⟨h0, hc⟩ := zerosRectD_zetaF_cases hu
  rcases hc with h | ⟨h1, h2⟩
  · exact absurd (h ▸ h0) zetaF_zero_ne_zero
  have hu1 : u ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hz : riemannZeta u = 0 := by
    rw [zetaF_of_ne hu1] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hu1
    · exact h
  exact ⟨hz, h1, h2, (xiF_eq_zero_iff h1 h2).2 hz⟩

/-! ## `|M(ρ)|` at zeros -/

theorem norm_intExp_line_le {a b : ℝ} (hab : b ≤ a) (y : ℝ) :
    ‖∫ w in b..a, cexp ((((1 / 2 : ℝ) : ℂ) + y * I) * w)‖ ≤ 2 * Real.exp (a / 2) := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  have e : ∀ w : ℝ, ‖cexp ((((1 / 2 : ℝ) : ℂ) + y * I) * w)‖ = Real.exp (w / 2) := by
    intro w; rw [Complex.norm_exp]; congr 1; simp; ring
  simp_rw [e]
  have h := intervalIntegral.integral_comp_div (f := Real.exp) (a := b) (b := a) (by norm_num : (2:ℝ) ≠ 0)
  rw [h, integral_exp, smul_eq_mul]
  have := Real.exp_pos (b / 2)
  linarith

/-- On the critical line: `‖M(½ + iγ)‖ ≤ 2e^{δ²/2 + |a|}/max(1, |γ|)`. -/
theorem norm_Mg_line_le {a b δ : ℝ} (hab : b ≤ a) (hb : b ≤ 0) (y : ℝ) :
    ‖Mg a b δ (((1 / 2 : ℝ) : ℂ) + y * I)‖ * max 1 |y| ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * I with hs
  have hg : ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ ≤ Real.exp (δ ^ 2 / 2) := by
    rw [norm_cexp_gauss]; apply Real.exp_le_exp.2
    simp only [hs, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add]
    nlinarith [sq_nonneg δ, sq_nonneg y, sq_nonneg (δ * y)]
  rw [Mg, norm_mul, Real.exp_add]
  rcases le_total |y| 1 with hy | hy
  · rw [max_eq_left hy, mul_one]
    have h1 := norm_intExp_line_le hab y
    have h2 : 2 * Real.exp (a / 2) ≤ 2 * Real.exp |a| := by
      have := le_abs_self a; gcongr; linarith [abs_nonneg a]
    calc ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ * ‖∫ w in b..a, cexp (s * w)‖ ≤
        Real.exp (δ ^ 2 / 2) * (2 * Real.exp |a|) := mul_le_mul hg (h1.trans h2) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [max_eq_right hy]
    have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hs] at this
    have h1 := norm_intExp_le' (a := a) (b := b) hs0
    have hsn : |y| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; simpa [hs] using this
    have hsre : s.re = 1 / 2 := by simp [hs]
    rw [hsre] at h1
    have h2 : Real.exp (a * (1 / 2)) + Real.exp (b * (1 / 2)) ≤ 2 * Real.exp |a| := by
      have : Real.exp (a * (1 / 2)) ≤ Real.exp |a| := Real.exp_le_exp.2 (by cases abs_cases a <;> linarith)
      have : Real.exp (b * (1 / 2)) ≤ Real.exp |a| := Real.exp_le_exp.2 (by cases abs_cases a <;> nlinarith)
      linarith
    have hy0 : 0 < |y| := by linarith
    have h3 : ‖∫ w in b..a, cexp (s * w)‖ * |y| ≤ 2 * Real.exp |a| := by
      calc ‖∫ w in b..a, cexp (s * w)‖ * |y| ≤ (Real.exp (a * (1 / 2)) + Real.exp (b * (1 / 2))) / ‖s‖ * ‖s‖ :=
            mul_le_mul h1 hsn hy0.le (by positivity)
        _ = Real.exp (a * (1 / 2)) + Real.exp (b * (1 / 2)) := by
            field_simp [(norm_pos_iff.2 hs0).ne']
        _ ≤ _ := h2
    calc ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ * ‖∫ w in b..a, cexp (s * w)‖ * |y| =
        ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ * (‖∫ w in b..a, cexp (s * w)‖ * |y|) := by ring
      _ ≤ Real.exp (δ ^ 2 / 2) * (2 * Real.exp |a|) := mul_le_mul hg h3 (by positivity) (by positivity)
      _ = _ := by ring

/-- In the strip, with the Gaussian factor: `‖M(ρ)‖ ≤ 2e^{δ²/2 + |a|} e^{−δ²γ²/2}/|γ|`. -/
theorem norm_Mg_strip_le {a b δ : ℝ} (hb : b ≤ 0) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (him : s.im ≠ 0) :
    ‖Mg a b δ s‖ * |s.im| ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * s.im ^ 2 / 2)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  rw [Mg, norm_mul, norm_cexp_gauss]
  have hI := norm_intExp_le' (a := a) (b := b) hs0
  have hsn : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : Real.exp (a * s.re) + Real.exp (b * s.re) ≤ 2 * Real.exp |a| := by
    have : Real.exp (a * s.re) ≤ Real.exp |a| := Real.exp_le_exp.2 (by
      cases abs_cases a <;> nlinarith)
    have : Real.exp (b * s.re) ≤ Real.exp |a| := Real.exp_le_exp.2 (by nlinarith [abs_nonneg a])
    linarith
  have h3 : ‖∫ w in b..a, cexp (s * w)‖ * |s.im| ≤ 2 * Real.exp |a| := by
    calc ‖∫ w in b..a, cexp (s * w)‖ * |s.im| ≤ (Real.exp (a * s.re) + Real.exp (b * s.re)) / ‖s‖ * ‖s‖ :=
          mul_le_mul hI hsn (abs_nonneg _) (by positivity)
      _ = Real.exp (a * s.re) + Real.exp (b * s.re) := by field_simp [(norm_pos_iff.2 hs0).ne']
      _ ≤ _ := h2
  have hg : Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) ≤ Real.exp (δ ^ 2 / 2) * Real.exp (-(δ ^ 2 * s.im ^ 2 / 2)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : s.re ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg δ]
  calc Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) * ‖∫ w in b..a, cexp (s * w)‖ * |s.im|
      = Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) * (‖∫ w in b..a, cexp (s * w)‖ * |s.im|) := by ring
    _ ≤ (Real.exp (δ ^ 2 / 2) * Real.exp (-(δ ^ 2 * s.im ^ 2 / 2))) * (2 * Real.exp |a|) :=
        mul_le_mul hg h3 (by positivity) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-! ## Zeros on the critical line, by windows -/

theorem sum_inv_one_add_le (J : ℕ) :
    ∑ m ∈ Finset.range J, 1 / (1 + 3.48 * (m : ℝ)) ≤ 1 + (1 + Real.log J) / 3.48 := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp; positivity
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h1 : ∑ m ∈ Finset.range n, 1 / (1 + 3.48 * ((m + 1 : ℕ) : ℝ)) ≤
      (1 / 3.48) * ∑ m ∈ Finset.range n, ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [inv_eq_one_div]; field_simp; nlinarith
  have h2 : ∑ m ∈ Finset.range n, ((m + 1 : ℕ) : ℝ)⁻¹ = (harmonic n : ℝ) := by
    simp [harmonic]
  have h3 := harmonic_le_one_add_log n
  have h4 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  simp only [Nat.cast_zero, mul_zero, add_zero, div_one]
  rw [h2] at h1
  have : (1 / 3.48 : ℝ) * (harmonic n : ℝ) ≤ (1 + Real.log ((n + 1 : ℕ) : ℝ)) / 3.48 := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith

/-- **Line zeros**: `Σ m_ρ g(ρ) ≤ ZL · C · 4(1 + (1 + log J)/3.48)` if `g(ρ) max(1, |γ|) ≤ C`. -/
theorem line_sum_le {T H : ℝ} (hH : 0 ≤ H) (S : Finset ℂ) (hS : S ⊆ zerosRectD zetaF T)
    (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ H) (g : ℂ → ℝ) (hg0 : ∀ u ∈ S, 0 ≤ g u)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ u ∈ S, g u * max 1 |u.im| ≤ C) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u ≤
      ZLg BPz2 H * C * (4 * (1 + (1 + Real.log (Jl H)) / 3.48)) := by
  set J := Jl H with hJdef
  set idx : ℂ → ℕ := fun u => (⌊u.im / 3.48⌋ + J).toNat with hidx
  have hJ := lt_Jl hH
  have hZL0 : 0 ≤ ZLg BPz2 H :=
    div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le
  set d : ℕ → ℝ := fun k => if J ≤ k then ((k - J : ℕ) : ℝ) else ((J - 1 - k : ℕ) : ℝ) with hd
  set w : ℕ → ℝ := fun k => 2 / (1 + 3.48 * d k) with hw
  have hd0 : ∀ k, 0 ≤ d k := fun k => by simp only [hd]; split_ifs <;> positivity
  have hmaps : ∀ u ∈ S, idx u ∈ Finset.range (2 * J) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * 3.48 ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * 3.48 :=
      mem_line_window (h := 3.48) (by norm_num) hJ (him u hu)
    have := (abs_le.1 (him u hu)).2
    rw [Finset.mem_range]
    have h1 : (((idx u : ℕ) : ℝ) - J) * 3.48 < J * 3.48 := by linarith [hwin.1]
    have h2 : ((idx u : ℕ) : ℝ) < 2 * J := by nlinarith
    exact_mod_cast h2
  have hwin_g : ∀ u ∈ S, g u ≤ C * w (idx u) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * 3.48 ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * 3.48 :=
      mem_line_window (h := 3.48) (by norm_num) hJ (him u hu)
    have habs : 3.48 * d (idx u) ≤ |u.im| := by
      rw [hd]; simp only
      split_ifs with hk
      · rw [Nat.cast_sub hk]
        have : (((idx u : ℕ) : ℝ) - J) * 3.48 ≤ u.im := hwin.1
        rw [abs_of_nonneg (by nlinarith [(Nat.cast_le.2 hk : (J : ℝ) ≤ idx u)])]
        linarith
      · push Not at hk
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * 3.48 := hwin.2
        have hk' : ((idx u : ℕ) : ℝ) + 1 ≤ J := by exact_mod_cast hk
        rw [abs_of_nonpos (by nlinarith)]
        push_cast; linarith
    have hm : (1 + 3.48 * d (idx u)) / 2 ≤ max 1 |u.im| := by
      have := le_max_left 1 |u.im|; have := le_max_right 1 |u.im|; linarith
    have hmpos : 0 < max 1 |u.im| := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hgu : g u ≤ C / max 1 |u.im| := by rw [le_div_iff₀ hmpos]; exact hg u hu
    refine hgu.trans ?_
    rw [hw]; simp only
    rw [div_le_iff₀ hmpos, mul_comm C, div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [le_div_iff₀ (by linarith [hd0 (idx u)])]
    nlinarith
  calc ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u
      = ∑ k ∈ Finset.range (2 * J), ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range (2 * J), ZLg BPz2 H * (C * w k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hcount := count_line_windowG polyDatum_zeta2 hH S hS hre him k
        calc ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u
            ≤ ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * (C * w k) := by
              refine Finset.sum_le_sum fun u hu => ?_
              obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              rw [← hk]; exact hwin_g u huS
          _ = (∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ)) * (C * w k) := by
              rw [Finset.sum_mul]
          _ ≤ ZLg BPz2 H * (C * w k) := by
              refine mul_le_mul_of_nonneg_right hcount ?_
              exact mul_nonneg hC (div_nonneg (by norm_num) (by linarith [hd0 k]))
    _ = ZLg BPz2 H * C * ∑ k ∈ Finset.range (2 * J), w k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ZLg BPz2 H * C * (4 * (1 + (1 + Real.log J) / 3.48)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hZL0 hC)
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : J ≤ 2 * J)]
        have hA : ∑ k ∈ Finset.range J, w k = ∑ m ∈ Finset.range J, 2 / (1 + 3.48 * (m : ℝ)) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          simp only [hw, hd]
          rw [if_neg (by omega), show J - 1 - (J - 1 - k) = k by omega]
        have hB : ∑ k ∈ Finset.Ico J (2 * J), w k = ∑ m ∈ Finset.range J, 2 / (1 + 3.48 * (m : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range, show 2 * J - J = J by omega]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hw, hd]
          rw [if_pos (by omega), show J + k - J = k by omega]
        rw [hA, hB]
        have h := sum_inv_one_add_le J
        have e : ∑ m ∈ Finset.range J, 2 / (1 + 3.48 * (m : ℝ)) =
            2 * ∑ m ∈ Finset.range J, 1 / (1 + 3.48 * (m : ℝ)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
        rw [e]; linarith

/-! ## Sharper constants for the line zeros

* `|ρ| ≥ max(½, |γ|)` on the critical line, so the windows at distance `d ≥ 1` get weight `1/(h d)`
  instead of `2/(1 + h d)`;
* `e^{a/2} + e^{b/2}` is kept instead of `2e^{|a|}` (for `ψ`, `b = log(y₀/x)` is very negative);
* the window height `h` and the Jensen radius `r ≥ √(1.5² + (h/2)²)` are parameters (`h = 6`, `r = 3.36`
  minimize `ZL(4 + 2(1 + log J)/h)` at `H = 3·10¹²`; `line_sum_le` has `h = 3.48`, `r = 2.3`). -/

/-- On the critical line: `‖M(½ + iγ)‖ max(½, |γ|) ≤ e^{δ²/2}(e^{a/2} + e^{b/2})`. -/
theorem norm_Mg_line_le' (a b δ y : ℝ) :
    ‖Mg a b δ (((1 / 2 : ℝ) : ℂ) + y * I)‖ * max (1 / 2) |y| ≤
      Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2)) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * I with hs
  have hg : ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ ≤ Real.exp (δ ^ 2 / 2) := by
    rw [norm_cexp_gauss]; apply Real.exp_le_exp.2
    simp only [hs, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add]
    nlinarith [sq_nonneg δ, sq_nonneg y, sq_nonneg (δ * y)]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hs] at this
  have hsre : s.re = 1 / 2 := by simp [hs]
  have h1 := norm_intExp_le' (a := a) (b := b) hs0
  rw [hsre] at h1
  have hsn : max (1 / 2) |y| ≤ ‖s‖ := by
    refine max_le ?_ ?_
    · have := Complex.abs_re_le_norm s; rw [hsre] at this; norm_num at this; linarith
    · have := Complex.abs_im_le_norm s; simpa [hs] using this
  have hpos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have h3 : ‖∫ w in b..a, cexp (s * w)‖ * max (1 / 2) |y| ≤ Real.exp (a / 2) + Real.exp (b / 2) := by
    calc ‖∫ w in b..a, cexp (s * w)‖ * max (1 / 2) |y|
        ≤ (Real.exp (a * (1 / 2)) + Real.exp (b * (1 / 2))) / ‖s‖ * ‖s‖ :=
          mul_le_mul h1 hsn (by positivity) (by positivity)
      _ = Real.exp (a * (1 / 2)) + Real.exp (b * (1 / 2)) := by field_simp
      _ = _ := by rw [mul_one_div, mul_one_div]
  rw [Mg, norm_mul]
  calc ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ * ‖∫ w in b..a, cexp (s * w)‖ * max (1 / 2) |y| =
      ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ * (‖∫ w in b..a, cexp (s * w)‖ * max (1 / 2) |y|) := by ring
    _ ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2)) :=
        mul_le_mul hg h3 (by positivity) (by positivity)

/-- `J = ⌊T₀/h⌋ + 1` line windows of height `h` on each side. -/
noncomputable def JlH (h T0 : ℝ) : ℕ := ⌊T0 / h⌋₊ + 1

theorem lt_JlH {h T0 : ℝ} (hh : 0 < h) (hT : 0 ≤ T0) : T0 < JlH h T0 * h := by
  unfold JlH; push_cast
  have := Nat.lt_floor_add_one (T0 / h)
  rw [div_lt_iff₀ hh] at this; linarith

/-- Zeros per line window of height `h` (Jensen radius `r`) below height `T₀`. -/
noncomputable def ZLh (h r T0 : ℝ) : ℝ := Real.log (BPz2 (T0 + h) / 0.355) / Real.log (10 / r)

theorem ZLh_nonneg {h r T0 : ℝ} (hr : 0 < r) (hr10 : r < 10) : 0 ≤ ZLh h r T0 :=
  div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos hr hr10).le

/-- `count_line_windowG` for windows of height `h`, radius `r ≥ √(1.5² + (h/2)²)`. -/
theorem count_line_windowH {h r T T0 : ℝ} (hh : 0 < h) (hr : 0 < r) (hr10 : r < 10)
    (hhr : 1.5 ^ 2 + (h / 2) ^ 2 ≤ r ^ 2) (hT0 : 0 ≤ T0) (S : Finset ℂ)
    (hS : S ⊆ zerosRectD zetaF T) (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ T0) (k : ℕ) :
    ∑ u ∈ S.filter (fun u => (⌊u.im / h⌋ + JlH h T0).toNat = k), (multRectD zetaF T u : ℝ) ≤
      ZLh h r T0 := by
  set F := S.filter (fun u => (⌊u.im / h⌋ + JlH h T0).toNat = k) with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · rw [hE, Finset.sum_empty]; exact ZLh_nonneg hr hr10
  set c := ((k : ℝ) - JlH h T0 + 1 / 2) * h with hc
  have hJ := lt_JlH hh hT0
  have hwin : ∀ u ∈ F, |u.im - c| ≤ h / 2 := by
    intro u hu
    obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
    have hw := mem_line_window hh hJ (him u huS)
    rw [hk] at hw
    have hc' : c = ((k : ℝ) - JlH h T0) * h + h / 2 := by rw [hc]; ring
    rw [abs_le]; constructor <;> nlinarith [hw.1, hw.2]
  have hball : ∀ u ∈ F, ‖u - (2 + c * I)‖ ≤ r := by
    intro u hu
    have hre' := hre u (Finset.mem_filter.1 hu).1
    refine norm_le_of_re_im (a := 1.5) (b := h / 2) hr.le ?_ ?_ hhr
    · simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [hre']; norm_num
    · simp only [Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, zero_add]
      simpa using hwin u hu
  have h1 := sum_multRectD_le polyDatum_zeta2 F ((Finset.filter_subset _ _).trans hS) c hr hr10 hball
  have hcT : |c| ≤ |T0 + h| := by
    have h0 := hwin u0 hu0
    have h0' := him u0 (Finset.mem_filter.1 hu0).1
    rw [abs_of_pos (by linarith : (0:ℝ) < T0 + h)]
    have := abs_sub_abs_le_abs_sub c u0.im
    rw [abs_sub_comm] at this
    linarith
  refine h1.trans ?_
  unfold ZLh
  exact div_le_div_of_nonneg_right (polyDatum_zeta2.log_mono hcT) (log_ratio_pos hr hr10).le

theorem sum_inv_max_leH {h : ℝ} (hh : 0 < h) (J : ℕ) :
    ∑ m ∈ Finset.range J, 1 / max (1 / 2 : ℝ) (h * (m : ℝ)) ≤ 2 + (1 + Real.log J) / h := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · rw [Finset.sum_range_zero]
    have : 0 ≤ (1 + Real.log ((0 : ℕ) : ℝ)) / h := div_nonneg (by simp) hh.le
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h1 : ∑ m ∈ Finset.range n, 1 / max (1 / 2 : ℝ) (h * ((m + 1 : ℕ) : ℝ)) ≤
      (1 / h) * ∑ m ∈ Finset.range n, ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    calc 1 / max (1 / 2 : ℝ) (h * ((m + 1 : ℕ) : ℝ)) ≤ 1 / (h * ((m + 1 : ℕ) : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (le_max_right _ _)
      _ = 1 / h * ((m + 1 : ℕ) : ℝ)⁻¹ := by field_simp
  have h2 : ∑ m ∈ Finset.range n, ((m + 1 : ℕ) : ℝ)⁻¹ = (harmonic n : ℝ) := by
    simp [harmonic]
  have h3 := harmonic_le_one_add_log n
  have h4 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  have h0 : (1 : ℝ) / max (1 / 2) (h * ((0 : ℕ) : ℝ)) = 2 := by
    rw [Nat.cast_zero, mul_zero, max_eq_left (by norm_num)]; norm_num
  rw [h0]
  rw [h2] at h1
  have : (1 / h) * (harmonic n : ℝ) ≤ (1 + Real.log ((n + 1 : ℕ) : ℝ)) / h := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right (by linarith) hh.le
  linarith

/-- **Line zeros**, sharper, with windows of height `h`: `Σ m_ρ g(ρ) ≤ ZL · C · (4 + 2(1 + log J)/h)`
if `g(ρ) max(½, |γ|) ≤ C`. -/
theorem line_sum_leH {T H h r : ℝ} (hH : 0 ≤ H) (hh : 0 < h) (hr : 0 < r) (hr10 : r < 10)
    (hhr : 1.5 ^ 2 + (h / 2) ^ 2 ≤ r ^ 2) (S : Finset ℂ) (hS : S ⊆ zerosRectD zetaF T)
    (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ H) (g : ℂ → ℝ) (hg0 : ∀ u ∈ S, 0 ≤ g u)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ u ∈ S, g u * max (1 / 2) |u.im| ≤ C) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u ≤
      ZLh h r H * C * (4 + 2 * (1 + Real.log (JlH h H)) / h) := by
  set J := JlH h H with hJdef
  set idx : ℂ → ℕ := fun u => (⌊u.im / h⌋ + J).toNat with hidx
  have hJ := lt_JlH hh hH
  have hZL0 : 0 ≤ ZLh h r H := ZLh_nonneg hr hr10
  set d : ℕ → ℝ := fun k => if J ≤ k then ((k - J : ℕ) : ℝ) else ((J - 1 - k : ℕ) : ℝ) with hd
  set w : ℕ → ℝ := fun k => 1 / max (1 / 2) (h * d k) with hw
  have hd0 : ∀ k, 0 ≤ d k := fun k => by simp only [hd]; split_ifs <;> positivity
  have hw0 : ∀ k, 0 ≤ w k := fun k => one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _))
  have hmaps : ∀ u ∈ S, idx u ∈ Finset.range (2 * J) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h :=
      mem_line_window hh hJ (him u hu)
    have := (abs_le.1 (him u hu)).2
    rw [Finset.mem_range]
    have h1 : (((idx u : ℕ) : ℝ) - J) * h < J * h := by linarith [hwin.1]
    have h2 : ((idx u : ℕ) : ℝ) < 2 * J := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hh.le
      nlinarith
    exact_mod_cast h2
  have hwin_g : ∀ u ∈ S, g u ≤ C * w (idx u) := by
    intro u hu
    have hwin : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im ∧ u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h :=
      mem_line_window hh hJ (him u hu)
    have habs : h * d (idx u) ≤ |u.im| := by
      rw [hd]; simp only
      split_ifs with hk
      · rw [Nat.cast_sub hk]
        have : (((idx u : ℕ) : ℝ) - J) * h ≤ u.im := hwin.1
        have hp : 0 ≤ (((idx u : ℕ) : ℝ) - J) * h :=
          mul_nonneg (sub_nonneg.2 (Nat.cast_le.2 hk)) hh.le
        rw [abs_of_nonneg (by linarith)]
        linarith
      · push Not at hk
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : u.im ≤ (((idx u : ℕ) : ℝ) - J + 1) * h := hwin.2
        have hk' : ((idx u : ℕ) : ℝ) + 1 ≤ J := by exact_mod_cast hk
        have hp : 0 ≤ ((J : ℝ) - ((idx u : ℕ) : ℝ) - 1) * h := mul_nonneg (by linarith) hh.le
        rw [abs_of_nonpos (by linarith)]
        push_cast; linarith
    have hmpos : 0 < max (1 / 2 : ℝ) |u.im| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hm2 : 0 < max (1 / 2 : ℝ) (h * d (idx u)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hmm : max (1 / 2 : ℝ) (h * d (idx u)) ≤ max (1 / 2) |u.im| := max_le_max le_rfl habs
    have hgu : g u ≤ C / max (1 / 2) |u.im| := by rw [le_div_iff₀ hmpos]; exact hg u hu
    refine hgu.trans ?_
    simp only [hw]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hC hm2 hmm
  calc ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g u
      = ∑ k ∈ Finset.range (2 * J), ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range (2 * J), ZLh h r H * (C * w k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hcount := count_line_windowH hh hr hr10 hhr hH S hS hre him k
        calc ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * g u
            ≤ ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ) * (C * w k) := by
              refine Finset.sum_le_sum fun u hu => ?_
              obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              rw [← hk]; exact hwin_g u huS
          _ = (∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ)) * (C * w k) := by
              rw [Finset.sum_mul]
          _ ≤ ZLh h r H * (C * w k) :=
              mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (hw0 k))
    _ = ZLh h r H * C * ∑ k ∈ Finset.range (2 * J), w k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ZLh h r H * C * (4 + 2 * (1 + Real.log J) / h) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hZL0 hC)
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : J ≤ 2 * J)]
        have hA : ∑ k ∈ Finset.range J, w k = ∑ m ∈ Finset.range J, 1 / max (1 / 2 : ℝ) (h * (m : ℝ)) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          simp only [hw, hd]
          rw [if_neg (by omega), show J - 1 - (J - 1 - k) = k by omega]
        have hB : ∑ k ∈ Finset.Ico J (2 * J), w k = ∑ m ∈ Finset.range J, 1 / max (1 / 2 : ℝ) (h * (m : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range, show 2 * J - J = J by omega]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hw, hd]
          rw [if_pos (by omega), show J + k - J = k by omega]
        rw [hA, hB]
        have hs := sum_inv_max_leH hh J
        calc _ ≤ (2 + (1 + Real.log J) / h) + (2 + (1 + Real.log J) / h) := add_le_add hs hs
          _ = _ := by ring

/-! ## Zeros above `H`: Gaussian windows -/

/-- `EB = 2e^{δ²/2 + |a|} e^{−δ²H²/2}/H`, `ρ = e^{−4.4δ²H}`. -/
noncomputable def EBg (a δ H : ℝ) : ℝ :=
  2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * H ^ 2 / 2)) / H
noncomputable def rhoG (δ H : ℝ) : ℝ := Real.exp (-(4.4 * δ ^ 2 * H))

theorem tail_sum_gauss {T H δ a b x : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hb : b ≤ 0) (hx : 1 ≤ x)
    (S : Finset ℂ) (hS : S ⊆ zerosRectD zetaF T) (him : ∀ u ∈ S, H < |u.im|) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (‖Mg a b δ u‖ * x ^ u.re) ≤
      x * (EBg a δ H * (2 * Z3g BPz2 H / (1 - rhoG δ H) + 2 * c3g 10 H / (1 - rhoG δ H) ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu =>
    ⟨(zerosRectD_zetaF_strip (hS hu)).2.1, (zerosRectD_zetaF_strip (hS hu)).2.2.1⟩
  set idx : ℂ → ℕ := fun u => ⌊(|u.im| - H) / 4.4⌋₊ with hidx
  set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
  have hρ0 : 0 ≤ rhoG δ H := (Real.exp_pos _).le
  have hρ1 : rhoG δ H < 1 := by
    rw [rhoG, Real.exp_lt_one_iff]; have : 0 < 4.4 * δ ^ 2 * H := by positivity
    linarith
  have hEB : 0 ≤ EBg a δ H := by unfold EBg; positivity
  have hpt : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) ≤ x * (m u * (EBg a δ H * rhoG δ H ^ idx u)) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hre u hu
    have hHu := him u hu
    have hγ0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hHu; linarith
    have hM := norm_Mg_strip_le (a := a) (δ := δ) hb h1 h2 hγ0
    have hk : H + 4.4 * idx u ≤ |u.im| := by
      have := Nat.floor_le (show 0 ≤ (|u.im| - H) / 4.4 from div_nonneg (by linarith) (by norm_num))
      rw [le_div_iff₀ (by norm_num)] at this; simp only [hidx]; linarith
    have hsq : H ^ 2 + 8.8 * H * idx u ≤ u.im ^ 2 := by
      have hk0 : (0:ℝ) ≤ idx u := Nat.cast_nonneg _
      have : (H + 4.4 * idx u) ^ 2 ≤ |u.im| ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
      rw [sq_abs] at this; nlinarith
    have hgauss : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) ≤
        Real.exp (-(δ ^ 2 * H ^ 2 / 2)) * rhoG δ H ^ idx u := by
      rw [rhoG, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg δ]
    have hMb : ‖Mg a b δ u‖ ≤ EBg a δ H * rhoG δ H ^ idx u := by
      have hγ : 0 < |u.im| := abs_pos.2 hγ0
      rw [EBg]
      calc ‖Mg a b δ u‖ = ‖Mg a b δ u‖ * |u.im| / |u.im| := by field_simp
        _ ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) / H := by
            rw [div_le_div_iff₀ hγ hH]
            calc ‖Mg a b δ u‖ * |u.im| * H ≤
                (2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * u.im ^ 2 / 2))) * |u.im| :=
                  mul_le_mul hM hHu.le hH.le (by positivity)
              _ = _ := by ring
        _ ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) * (Real.exp (-(δ ^ 2 * H ^ 2 / 2)) * rhoG δ H ^ idx u) / H := by
            gcongr
        _ = _ := by ring
    have hxr : x ^ u.re ≤ x := by
      calc x ^ u.re ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx h2.le
        _ = x := Real.rpow_one x
    have hm0 : 0 ≤ m u := Nat.cast_nonneg _
    calc m u * (‖Mg a b δ u‖ * x ^ u.re) ≤ m u * ((EBg a δ H * rhoG δ H ^ idx u) * x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hMb hxr (by positivity) (by positivity)) hm0
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hx0.le
  exact sum_geom_windows m (fun u _ => Nat.cast_nonneg _) idx
    (by have := (polyDatum_zeta2.log_pos H).le
        unfold Z3g; have := (log_ratio_pos (r := 3) (by norm_num) (by norm_num)).le; positivity)
    (by unfold c3g; have := (log_ratio_pos (r := 3) (by norm_num) (by norm_num)).le; positivity)
    hEB hρ0 hρ1 (fun k => count_tail_windowG polyDatum_zeta2 hH S hS hre him k)

end TernaryGoldbach.Explicit
