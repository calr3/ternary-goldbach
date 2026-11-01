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
lies on the critical line. -/
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

end TernaryGoldbach.Explicit
