import RSBounds.SchoenfeldSexticSmoothing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# Sextic smoothing of the Chebyshev function

The order-6 analogue of `PolynomialPsi`: an upper/lower sandwich for `ψ` and the exact
sixth-difference identity for its truncated-power primitive
`Psi6 t = ∑ Λ(n) (t - n)_+^6 / 720`. No zeta explicit formula, zero-count estimate or RH
hypothesis is used.

One common finite range `0 ≤ n ≤ N` is used throughout. The hypothesis `x + 6h ≤ N` makes it
adequate for all seven arguments in the forward difference.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticPsi

open SchoenfeldSexticSmoothing

/-- The sixth truncated-power primitive of a point mass. -/
noncomputable def sexticPrimitive (t : ℝ) : ℝ := (max t 0) ^ 6 / 720

/-- A common finite truncation of the sixth primitive of psi. -/
noncomputable def psi6Trunc (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * sexticPrimitive (t - n)

/-- The canonical finite truncated-power primitive. -/
noncomputable def Psi6 (t : ℝ) : ℝ := psi6Trunc ⌊t⌋₊ t

/-- Forward sixth difference, before normalization by the step size. -/
def sixthDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + 6 * h) - 6 * f (x + 5 * h) + 15 * f (x + 4 * h) - 20 * f (x + 3 * h) +
    15 * f (x + 2 * h) - 6 * f (x + h) + f x

/-- Polynomial upper smoothing of psi. -/
noncomputable def psiUpper (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x + 6 * h - n) / h)

/-- Polynomial lower smoothing of psi. -/
noncomputable def psiLower (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x - n) / h)

/-- Psi represented on any sufficiently large common finite range. -/
theorem psi_eq_indicator_sum {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x ≤ N) :
    Chebyshev.psi x =
      ∑ n ∈ Icc 0 N, if (n : ℝ) ≤ x then (Λ n : ℝ) else 0 := by
  have hfloor : ⌊x⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le hx).trans hN
  have hs : (Icc 0 N).filter (fun n : ℕ => (n : ℝ) ≤ x) = Icc 0 ⌊x⌋₊ := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h0, _⟩, hn⟩
      exact ⟨h0, (Nat.le_floor_iff hx).2 hn⟩
    · rintro ⟨h0, hn⟩
      exact ⟨⟨h0, hn.trans hfloor⟩, (Nat.le_floor_iff hx).1 hn⟩
  rw [Chebyshev.psi_eq_sum_Icc, ← hs, sum_filter]

/-- The lower smoothing never exceeds psi. -/
theorem psiLower_le_psi {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : psiLower N x h ≤ Chebyshev.psi x := by
  rw [psi_eq_indicator_sum hx hN]
  unfold psiLower
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · rw [if_pos hn]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (W_le_one ((x - n) / h))
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [if_neg hn, W_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith [lt_of_not_ge hn]) hh.le), mul_zero]

/-- The upper smoothing majorizes psi, including at prime-power jumps. -/
theorem psi_le_psiUpper {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : Chebyshev.psi x ≤ psiUpper N x h := by
  rw [psi_eq_indicator_sum hx hN]
  unfold psiUpper
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · have hw : 6 ≤ (x + 6 * h - n) / h := (le_div_iff₀ hh).2 (by linarith)
    rw [if_pos hn, W_eq_one_of_six_le hw, mul_one]
  · rw [if_neg hn]
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (W_nonneg _)

/-- The two polynomial smoothings sandwich psi on one common truncation. -/
theorem psi_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N) :
    psiLower N x h ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ psiUpper N x h :=
  ⟨psiLower_le_psi hx hh (by linarith), psi_le_psiUpper hx hh (by linarith)⟩

/-- A sufficiently large finite truncation equals the canonical primitive. -/
theorem psi6Trunc_eq_Psi6 {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : t ≤ N) :
    psi6Trunc N t = Psi6 t := by
  have hfloor : ⌊t⌋₊ ≤ N := by exact_mod_cast (Nat.floor_le ht).trans hN
  unfold Psi6 psi6Trunc
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hfloor)
  intro n hn hn'
  have hnf : ⌊t⌋₊ < n := by
    have hn0 : 0 ≤ n := Nat.zero_le n
    simp only [mem_Icc, hn0, true_and] at hn'
    omega
  have hnt : t < n := (Nat.floor_lt ht).1 hnf
  simp [sexticPrimitive, max_eq_right (show t - n ≤ 0 by linarith)]

/-- Sixth differences commute with finite sums. -/
theorem sixthDifference_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x h : ℝ) :
    sixthDifference (fun t => ∑ i ∈ s, f i t) x h =
      ∑ i ∈ s, sixthDifference (f i) x h := by
  simp only [sixthDifference, sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Sixth differences commute with scalar multiplication. -/
theorem sixthDifference_mul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    sixthDifference (fun t => c * f t) x h = c * sixthDifference f x h := by
  unfold sixthDifference
  ring

/-- The normalized sixth difference of one truncated power is the sextic CDF weight. -/
theorem sixthDifference_sexticPrimitive {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    sixthDifference (fun t => sexticPrimitive (t - a)) x h / h ^ 6 =
      W ((x + 6 * h - a) / h) := by
  have hd (t : ℝ) : max (t / h) 0 = max t 0 / h := by
    simpa only [zero_div] using max_div_div_right hh.le t 0
  have e1 : (x + 6 * h - a) / h - 1 = (x + 5 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e2 : (x + 6 * h - a) / h - 2 = (x + 4 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e3 : (x + 6 * h - a) / h - 3 = (x + 3 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e4 : (x + 6 * h - a) / h - 4 = (x + 2 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e5 : (x + 6 * h - a) / h - 5 = (x + h - a) / h := by
    field_simp [hh.ne']; ring
  have e6 : (x + 6 * h - a) / h - 6 = (x - a) / h := by
    field_simp [hh.ne']; ring
  unfold sixthDifference sexticPrimitive W
  rw [e1, e2, e3, e4, e5, e6]
  simp only [hd, div_pow]
  ring

/-- The normalized forward difference of the finite sixth primitive is exactly the upper
polynomial smoothing. -/
theorem sixthDifference_psi6Trunc {h : ℝ} (hh : 0 < h) (N : ℕ) (x : ℝ) :
    sixthDifference (psi6Trunc N) x h / h ^ 6 = psiUpper N x h := by
  unfold psi6Trunc psiUpper
  rw [sixthDifference_sum, sum_div]
  apply sum_congr rfl
  intro n _
  rw [sixthDifference_mul, mul_div_assoc,
    sixthDifference_sexticPrimitive hh]

/-- The canonical sixth primitive has the same difference identity whenever the finite upper sum
contains its complete support. -/
theorem sixthDifference_Psi6 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N) :
    sixthDifference Psi6 x h / h ^ 6 = psiUpper N x h := by
  have h0 := psi6Trunc_eq_Psi6 hx (show x ≤ N by linarith)
  have h1 := psi6Trunc_eq_Psi6 (show 0 ≤ x + h by linarith)
    (show x + h ≤ N by linarith)
  have h2 := psi6Trunc_eq_Psi6 (show 0 ≤ x + 2 * h by linarith)
    (show x + 2 * h ≤ N by linarith)
  have h3 := psi6Trunc_eq_Psi6 (show 0 ≤ x + 3 * h by linarith)
    (show x + 3 * h ≤ N by linarith)
  have h4 := psi6Trunc_eq_Psi6 (show 0 ≤ x + 4 * h by linarith)
    (show x + 4 * h ≤ N by linarith)
  have h5 := psi6Trunc_eq_Psi6 (show 0 ≤ x + 5 * h by linarith)
    (show x + 5 * h ≤ N by linarith)
  have h6 := psi6Trunc_eq_Psi6 (show 0 ≤ x + 6 * h by linarith) hN
  have hd : sixthDifference Psi6 x h = sixthDifference (psi6Trunc N) x h := by
    unfold sixthDifference
    rw [h0, h1, h2, h3, h4, h5, h6]
  rw [hd]
  exact sixthDifference_psi6Trunc hh N x

/-- The backward-shifted forward difference is exactly the lower smoothing. -/
theorem sixthDifference_Psi6_lower {x h : ℝ} (hh : 0 < h) (hx : 6 * h ≤ x)
    {N : ℕ} (hN : x ≤ N) :
    sixthDifference Psi6 (x - 6 * h) h / h ^ 6 = psiLower N x h := by
  have ht := sixthDifference_Psi6 (x := x - 6 * h) (by linarith) hh
    (show x - 6 * h + 6 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel] using ht

/-- Once the two polynomial smoothings have controlled errors, the cost of unsmoothing is
precisely `3h`. -/
theorem psi_error_of_polynomial_errors {x h E : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N)
    (hupper : |psiUpper N x h - (x + 3 * h)| ≤ E)
    (hlower : |psiLower N x h - (x - 3 * h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + 3 * h := by
  obtain ⟨hlo, hup⟩ := psi_sandwich hx hh hN
  obtain ⟨hu1, hu2⟩ := abs_le.mp hupper
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlower
  rw [abs_le]
  constructor <;> linarith

end TernaryGoldbach.RSBounds.SchoenfeldSexticPsi
