import TernaryGoldbach.MinorArcs.GMono
import Mathlib.NumberTheory.Chebyshev

/-!
# [H, Prop. 11.2.3]: from `η₂` to `η_* = (η₂ *_M φ)(κ·)` — pieces of the corrected form

`S_{η_*}(α, x) = ∫ S_{η₂}(α, wy) φ(w) dw/w` with `y = x/κ` (`S_etaStar_eq`).  If
`2α = a/q + δ/y`, then at scale `wy` the approximation reads `2α = a/q + (wδ)/(wy)`, so
Theorem 3.1.1 at scale `wy` is in terms of `r_w = max(1, w|δ|/8) q`, **not** [H]'s
`r = max(1, |δ|/8) q` (see `NOTES.md`, "Prop 11.2.3 erratum").  Since `r_w ≥ min(1, w) r` and
`g` is non-increasing (`gx_antitoneOn`), the per-scale bound is `g_{wy}(min(1, w) r)`.

This file has the pieces that `Prop1123b.lean` assembles into the form used (`prop_11_2_3'`):
the trivial bound `|S_{η₂}(α, z)| ≤ 17 z` (`norm_S_eta2_le_trivial`, from Chebyshev's
`ψ(z) ≤ (log 4 + 4) z`; [H] uses `1.04488 z`, Cor. C.1.3), `r_le_cube_root`, `min_mul_max_le`,
and the integrability of `φ`.
-/

open Real Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 etaStar S phi κ eta2_nonneg eta2_le eta2_eq_zero)

/-- The trivial bound `|S_{η₂}(α, z)| ≤ 3 ψ(z) ≤ 17 z`. -/
theorem norm_S_eta2_le_trivial {z : ℝ} (hz : 0 < z) (α : ℝ) : ‖S eta2 z α‖ ≤ 17 * z := by
  unfold S
  have hs : ∀ n ∉ Finset.range (⌊z⌋₊ + 1),
      ((Λ n * eta2 (n / z) : ℝ) : ℂ) * TernaryGoldbach.e (n * α) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff, Nat.floor_lt hz.le] at hn
    rw [eta2_eq_zero, mul_zero, Complex.ofReal_zero, zero_mul]
    rintro ⟨-, h1⟩
    rw [div_lt_one hz] at h1
    linarith
  rw [tsum_eq_sum hs]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n ∈ Finset.range (⌊z⌋₊ + 1),
      ‖((Λ n * eta2 (n / z) : ℝ) : ℂ) * TernaryGoldbach.e (n * α)‖ ≤ 3 * Λ n := by
    intro n _
    rw [norm_mul, TernaryGoldbach.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (eta2_nonneg _))]
    nlinarith [eta2_le (n / z), @ArithmeticFunction.vonMangoldt_nonneg n]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hpsi : ∑ n ∈ Finset.range (⌊z⌋₊ + 1), Λ n = Chebyshev.psi z := by
    have e : Finset.range (⌊z⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊z⌋₊) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [e, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
    rfl
  rw [hpsi]
  have h4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have := Chebyshev.psi_le_const_mul_self hz.le
  nlinarith

/-- `r = max(1, |δ|/8) q ≤ x^{1/3}/6` for an approximation as in Theorem 3.1.1 with
`q ≤ x^{1/3}/6` (`δ₀q = 2r ≤ x^{1/3}/3`). -/
theorem r_le_cube_root {α x δ : ℝ} {a : ℤ} {q : ℕ} (hx : 2.16e20 ≤ x)
    (h : Approx2 α x δ a q (3 / 4 * x ^ (2 / 3 : ℝ))) (hq : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) / 6) :
    max 1 (|δ| / 8) * q ≤ x ^ (1 / 3 : ℝ) / 6 := by
  obtain ⟨hT, hT3, hT23, -⟩ := cube_root_facts hx
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hq0 : (0 : ℝ) < q := by linarith
  have hd := h.2.2.2.1
  rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by rw [hT23]; positivity), one_mul] at hd
  rcases le_total 1 (|δ| / 8) with hm | hm
  · rw [max_eq_right hm]
    have : |δ| * q * (3 / 4 * (x ^ (1 / 3 : ℝ)) ^ 2) ≤ (x ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [hT3]
      calc |δ| * q * (3 / 4 * (x ^ (1 / 3 : ℝ)) ^ 2) = |δ| * (q * (3 / 4 * x ^ (2 / 3 : ℝ))) := by
            rw [hT23]; ring
        _ ≤ x := hd
    have hT0 : 0 < x ^ (1 / 3 : ℝ) := by linarith
    nlinarith
  · rw [max_eq_left hm]; linarith

/-- `min(1, w) · max(1, |δ|/8) ≤ max(1, w|δ|/8)`. -/
theorem min_mul_max_le {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    min 1 w * max 1 (d / 8) ≤ max 1 (w * d / 8) := by
  rcases le_total w 1 with h | h
  · rw [min_eq_right h, mul_max_of_nonneg _ _ hw.le, mul_one]
    exact max_le_max h (le_of_eq (by ring))
  · rw [min_eq_left h, one_mul]
    exact max_le_max le_rfl (by nlinarith)

theorem integrable_phi : Integrable phi := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [phi, Real.rpow_two]
  ring_nf

theorem phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

end TernaryGoldbach.MinorArcs
