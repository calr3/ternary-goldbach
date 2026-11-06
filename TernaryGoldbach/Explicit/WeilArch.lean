import TernaryGoldbach.Explicit.WeilWeights
import TernaryGoldbach.Explicit.Digamma

/-!
# The archimedean term of the Weil formula

`Re ψ(¼ + iy) ≤ ψ_N(y) = log(N + ¼) + ½ log(1 + y²/(N − ¾)²) − Σ_{k<N} (k + ¼)/((k + ¼)² + y²)`
(`re_digamma_quarter_le`; `re_digamma_le` at `¼ + N` and the recurrence `N` times). `ψ_N` is even
and nondecreasing in `|y|` (`psiN_mono`), and close to `Re ψ(¼ + iy)` for `N` large
(at `y = 0`, `N = 10`: `−4.18` against `−4.227`).
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- `ψ_N(y)`, an upper bound for `Re ψ(¼ + iy)`. -/
noncomputable def psiN (N : ℕ) (y : ℝ) : ℝ :=
  Real.log (N + 1 / 4) + 1 / 2 * Real.log (1 + y ^ 2 / (N - 3 / 4) ^ 2) -
    ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2)

theorem re_digamma_quarter_le {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    (Complex.digamma (((1 / 4 : ℝ) : ℂ) + y * I)).re ≤ psiN N y := by
  set z : ℂ := ((1 / 4 : ℝ) : ℂ) + y * I with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hrec := Complex.digamma_apply_add_nat (not_neg_nat_of_re_pos (by rw [hzre]; norm_num : 0 < z.re)) N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e : z + (N : ℂ) = (((1 / 4 + N : ℝ)) : ℂ) + y * I := by rw [hz]; push_cast; ring
  have h1 := re_digamma_le (σ := 1 / 4 + N) (t := y) (by linarith)
  rw [← e] at h1
  have hsum : (∑ k ∈ range N, (z + (k : ℂ))⁻¹).re =
      ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, hzre, hzim,
      add_zero]
    ring
  have : (Complex.digamma z).re = (Complex.digamma (z + N)).re -
      (∑ k ∈ range N, (z + (k : ℂ))⁻¹).re := by rw [hrec, Complex.add_re]; ring
  rw [this, hsum]
  unfold psiN
  rw [show (1 / 4 + (N : ℝ) - 1) = (N : ℝ) - 3 / 4 by ring, show (1 / 4 + (N : ℝ)) = (N : ℝ) + 1 / 4 by ring]
    at h1
  linarith

theorem psiN_neg (N : ℕ) (y : ℝ) : psiN N (-y) = psiN N y := by
  unfold psiN; simp only [neg_sq]

theorem psiN_abs (N : ℕ) (y : ℝ) : psiN N |y| = psiN N y := by
  unfold psiN; simp only [sq_abs]

/-- `ψ_N` is nondecreasing in `|y|`. -/
theorem psiN_mono {N : ℕ} (hN : 1 ≤ N) {y y' : ℝ} (h : |y| ≤ |y'|) : psiN N y ≤ psiN N y' := by
  have hsq : y ^ 2 ≤ y' ^ 2 := by rw [← sq_abs y, ← sq_abs y']; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < ((N : ℝ) - 3 / 4) ^ 2 := by nlinarith
  unfold psiN
  have hlog : Real.log (1 + y ^ 2 / (N - 3 / 4) ^ 2) ≤ Real.log (1 + y' ^ 2 / (N - 3 / 4) ^ 2) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hs : ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y' ^ 2) ≤
      ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) :=
    Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

theorem continuous_psiN (N : ℕ) : Continuous (psiN N) := by
  unfold psiN
  have h1 : Continuous fun y : ℝ => Real.log (1 + y ^ 2 / ((N : ℝ) - 3 / 4) ^ 2) := by
    refine Continuous.log (by fun_prop) fun y => ?_
    have : 0 ≤ y ^ 2 / ((N : ℝ) - 3 / 4) ^ 2 := by positivity
    linarith
  refine (continuous_const.add (continuous_const.mul h1)).sub (continuous_finsetSum _ fun k _ => ?_)
  refine continuous_const.div (by fun_prop) fun y => ?_
  have : 0 < ((k : ℝ) + 1 / 4) ^ 2 + y ^ 2 := by positivity
  exact this.ne'

/-! ### `B` is even; `H̃` and `A` on the critical line -/

theorem sincC_neg (w : ℂ) : sincC (-w) = sincC w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [sincC_of_ne (neg_ne_zero.2 hw), sincC_of_ne hw, Complex.sin_neg, neg_div_neg_eq]

theorem WB_neg (ℓ : ℝ) (m : ℕ) (z : ℂ) : WB ℓ m (-z) = WB ℓ m z := by
  unfold WB; rw [mul_neg, sincC_neg]

theorem Bsq_neg (ℓ : ℝ) (m : ℕ) (y : ℝ) : Bsq ℓ m (-y) = Bsq ℓ m y := by
  unfold Bsq; rw [Complex.ofReal_neg, WB_neg]

theorem WB_ofReal_eq (ℓ : ℝ) (m : ℕ) (x : ℝ) : WB ℓ m (x : ℂ) = (((WB ℓ m (x : ℂ)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [WB_ofReal_im])

theorem WB_sq_ofReal (ℓ : ℝ) (m : ℕ) (x : ℝ) : WB ℓ m (x : ℂ) ^ 2 = ((Bsq ℓ m x : ℝ) : ℂ) := by
  rw [WB_ofReal_eq, Bsq]; push_cast; ring

/-- `H̃_t(½ + iy) = B(y − t)² + B(y + t)²`. -/
theorem WHt_line (ℓ : ℝ) (m : ℕ) (t y : ℝ) :
    WHt ℓ m t (((1 / 2 : ℝ) : ℂ) + y * I) = ((Bsq ℓ m (y - t) + Bsq ℓ m (y + t) : ℝ) : ℂ) := by
  unfold WHt
  have e1 : ((1 / 2 : ℝ) : ℂ) + y * I = 1 / 2 + (y : ℂ) * I := by push_cast; ring
  have e2 : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + y * I) = 1 / 2 + ((-y : ℝ) : ℂ) * I := by push_cast; ring
  rw [e2, e1, WH_line, WH_line, WB_sq_ofReal, WB_sq_ofReal,
    show (-y - t) = -(y + t) by ring, Bsq_neg]
  push_cast; ring

/-- `A_N(y) = −½ log π + ½ ψ_N(y/2)`, an upper bound for `Re A(½ + iy)`. -/
noncomputable def aN (N : ℕ) (y : ℝ) : ℝ := -(1 / 2) * Real.log π + 1 / 2 * psiN N (y / 2)

theorem archF_line_re_le {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    (archF (((1 / 2 : ℝ) : ℂ) + y * I)).re ≤ aN N y := by
  unfold archF aN
  have e : (((1 / 2 : ℝ) : ℂ) + y * I) / 2 = ((1 / 4 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e]
  have h := re_digamma_quarter_le hN (y / 2)
  have hl : (Complex.log π).re = Real.log π := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
    Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, neg_zero, zero_div, zero_mul, sub_zero, hl]
  linarith

theorem aN_neg (N : ℕ) (y : ℝ) : aN N (-y) = aN N y := by
  unfold aN; rw [neg_div, psiN_neg]

theorem aN_mono {N : ℕ} (hN : 1 ≤ N) {y y' : ℝ} (h : |y| ≤ |y'|) : aN N y ≤ aN N y' := by
  unfold aN
  have : |y / 2| ≤ |y' / 2| := by rw [abs_div, abs_div]; gcongr
  linarith [psiN_mono hN this]

theorem continuous_aN (N : ℕ) : Continuous (aN N) := by
  unfold aN; exact continuous_const.add (continuous_const.mul ((continuous_psiN N).comp (by fun_prop)))

end TernaryGoldbach.Explicit
