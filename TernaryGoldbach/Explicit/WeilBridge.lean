import TernaryGoldbach.Explicit.WeilFormula
import TernaryGoldbach.Explicit.ZetaPoly

/-!
# From zeros of `ξ` to zeros of `zetaF`

The Weil formula (`weil_formula`) counts the zeros of `ξ` in `R_T = [−1/2, 3/2] × [−T, T]` with
`mult T`; the explicit formula for `ψ` sums over the zeros of `zetaF = (s − 1)ζ(s)` with
`multRectD zetaF T`. In the strip both multiplicities are the order of vanishing
(`ξ = (s Γℝ(s)) · zetaF` near `u`, with `s Γℝ(s)` analytic and nonzero for `ℜu > 0`), so
`multRectD zetaF T u = mult T' u` and `u ∈ zerosRectD zetaF T ↔ u ∈ rectZerosXi T'` for any
`T, T' > |ℑu|` (`multRectD_eq_mult`, `mem_rectZerosXi_of_mem`).
-/

open Complex Metric Set Filter
open scoped Real Topology

namespace TernaryGoldbach.Explicit

theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) (fun w hw => ?_) (hU.mem_nhds hs)
  have hm : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hw' : 0 < w.re := hw
    linarith
  have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    ext w; rw [Gammaℝ]
  rw [e]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul ?_).differentiableWithinAt
  exact (Complex.differentiableAt_Gamma _ hm).comp w (by fun_prop)

/-- **`ord_u ξ = ord_u zetaF`** for `ℜu > 0`. -/
theorem analyticOrderAt_xiF_eq {u : ℂ} (hu : 0 < u.re) :
    analyticOrderAt xiF u = analyticOrderAt zetaF u := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [(differentiable_xiF.analyticAt 1).analyticOrderAt_eq_zero.2 (by rw [xiF_one]; norm_num),
      (differentiable_zetaF.analyticAt 1).analyticOrderAt_eq_zero.2 (by
        rw [zetaF]; simp)]
  have hev : xiF =ᶠ[𝓝 u] (fun w => w * Gammaℝ w) * zetaF := by
    have hU : {w : ℂ | 0 < w.re ∧ w ≠ 1} ∈ 𝓝 u :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds ⟨hu, hu1⟩
    filter_upwards [hU] with w hw using xiF_eq hw.1 hw.2
  have ha : AnalyticAt ℂ (fun w => w * Gammaℝ w) u := analyticAt_id.mul (analyticAt_Gammaℝ hu)
  have hne : u * Gammaℝ u ≠ 0 :=
    mul_ne_zero (by intro h; rw [h] at hu; simp at hu) (Gammaℝ_ne_zero_of_re_pos hu)
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha (differentiable_zetaF.analyticAt u),
    ha.analyticOrderAt_eq_zero.2 hne, zero_add]

/-- Equal orders give equal divisors (on any closed balls containing `u`). -/
theorem divB_eq_of_analyticOrderAt_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {c c' u : ℂ} {R R' : ℝ} (hu : u ∈ closedBall c R) (hu' : u ∈ closedBall c' R')
    (h : analyticOrderAt f u = analyticOrderAt g u) : divB f c R u = divB g c' R' u := by
  rw [divB, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hu,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hg.analyticAt z : AnalyticOnNhd ℂ g (closedBall c' R')) hu', h]

theorem mem_closedBall_two_RT {T : ℝ} {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1) (him : |u.im| < T) :
    u ∈ closedBall (2 : ℂ) (RT T) ∧ ‖u - 2‖ < RT T / 2 := by
  have hn : ‖u - 2‖ ≤ |(u - 2).re| + |(u - 2).im| := Complex.norm_le_abs_re_add_abs_im _
  have hre : |(u - 2).re| ≤ 2 := by
    simp only [Complex.sub_re, Complex.re_ofNat]; rw [abs_le]; constructor <;> linarith
  have him' : |(u - 2).im| = |u.im| := by simp
  have hlt : ‖u - 2‖ < RT T / 2 := by unfold RT; linarith
  refine ⟨?_, hlt⟩
  rw [mem_closedBall, dist_eq_norm]
  have : 0 ≤ T := (abs_nonneg _).trans him.le
  unfold RT at hlt ⊢; linarith

theorem mem_closedBall_half_six {T : ℝ} (hT : 1 ≤ T) {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1)
    (him : |u.im| < T) : u ∈ closedBall (1 / 2 : ℂ) (6 * T) ∧ ‖u - 1 / 2‖ < 6 * T / 2 := by
  have hn : ‖u - 1 / 2‖ ≤ |(u - 1 / 2).re| + |(u - 1 / 2).im| := Complex.norm_le_abs_re_add_abs_im _
  have hre : |(u - 1 / 2).re| ≤ 1 / 2 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
    rw [abs_le]; constructor <;> linarith
  have him' : |(u - 1 / 2).im| = |u.im| := by simp
  have hlt : ‖u - 1 / 2‖ < 6 * T / 2 := by linarith
  refine ⟨?_, hlt⟩
  rw [mem_closedBall, dist_eq_norm]; linarith

/-- **The multiplicities agree** in the strip. -/
theorem multRectD_eq_mult {T T' : ℝ} (hT' : 1 ≤ T') {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1)
    (him : |u.im| < T) (him' : |u.im| < T') : multRectD zetaF T u = mult T' u := by
  have hb := (mem_closedBall_two_RT h0 h1 him).1
  have hb' := (mem_closedBall_half_six hT' h0 h1 him').1
  rw [multRectD, mult, divB_eq_of_analyticOrderAt_eq differentiable_zetaF differentiable_xiF hb hb'
    (analyticOrderAt_xiF_eq h0).symm]

/-- **A zero of `zetaF` in `R_T` (in the strip) is a zero of `ξ` in `R_{T'}`** for `T' > |ℑu|`. -/
theorem mem_rectZerosXi_of_mem {T T' : ℝ} (hT' : 1 ≤ T') {u : ℂ} (hu : u ∈ zerosRectD zetaF T)
    (h0 : 0 < u.re) (h1 : u.re < 1) (him' : |u.im| < T') : u ∈ rectZerosXi T' := by
  rw [zerosRectD, Finset.mem_filter] at hu
  obtain ⟨hz, -, -, hT1, hT2⟩ := hu
  rw [zT_im] at hT1; rw [wT_im] at hT2
  have him : |u.im| < T := abs_lt.2 ⟨hT1, hT2⟩
  have hb := mem_closedBall_two_RT h0 h1 him
  have hb' := mem_closedBall_half_six hT' h0 h1 him'
  have hd := (mem_zerosIn hz).2
  rw [rectZerosXi, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support]
  refine ⟨⟨?_, hb'.2⟩, ?_, ?_, ?_, ?_⟩
  · rwa [← divB_eq_of_analyticOrderAt_eq differentiable_zetaF differentiable_xiF hb.1 hb'.1
      (analyticOrderAt_xiF_eq h0).symm]
  · rw [zT_re]; linarith
  · rw [wT_re]; linarith
  · rw [zT_im]; linarith [(abs_lt.1 him').1]
  · rw [wT_im]; linarith [(abs_lt.1 him').2]

end TernaryGoldbach.Explicit
