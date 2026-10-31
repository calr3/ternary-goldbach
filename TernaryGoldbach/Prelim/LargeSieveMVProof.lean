import TernaryGoldbach.CircleMethod
import TernaryGoldbach.Prelim.HilbertCsc

/-!
# The sharp large sieve inequalities (Montgomery–Vaughan), proved

From the Hilbert inequalities on the circle (`HilbertCsc.lean`), by duality:

* `∑_n |∑_r b_r e(α_r n)|² = N ∑ |b_r|² + ∑_{r≠r'} b̄_r b_{r'} K(α_{r'} − α_r)`, with the Dirichlet
  kernel `K(x) = ∑_{M<n≤M+N} e(nx) = (e((M+N+½)x) − e((M+½)x))/(2i sin πx)`. The off-diagonal part
  is a difference of two `csc`-forms, so it is at most `(4.66/π) ∑ |b_r|²/δ_r ≤ (3/2) ∑ |b_r|²/δ_r`,
  resp. `δ⁻¹ ∑ |b_r|²`.
* Duality gives `∑_r (N + (3/2)δ_r⁻¹)⁻¹ |S(α_r)|² ≤ ∑ |a_n|²` and `∑_r |S(α_r)|² ≤ (N + δ⁻¹)‖a‖²`.
* **Dilation** improves `N + δ⁻¹` to `N − 1 + δ⁻¹`: the sequence `a_n` placed at `kn` has length
  `k(N−1)+1`, and the `δ/k`-separated points `(α_r + j)/k` (`j < k`) give `k ∑_r |S(α_r)|²
  ≤ (k(N−1) + 1 + kδ⁻¹)‖a‖²`; let `k → ∞`.
-/

open Finset Complex Filter Topology

namespace TernaryGoldbach.Prelim.LS

open TernaryGoldbach (e e_add conj_e norm_e e_zero)
open TernaryGoldbach.Prelim.Hilbert (cscForm csc_weighted csc_uniform)

theorem e_half_sub (x : ℝ) : e (x / 2) - e (-(x / 2)) = 2 * I * Complex.sin (Real.pi * x) := by
  simp only [e, Complex.sin]
  have h1 : (2 * (Real.pi : ℂ) * I * ((x / 2 : ℝ) : ℂ)) = (Real.pi * x : ℂ) * I := by push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * I * ((-(x / 2) : ℝ) : ℂ)) = -((Real.pi * x : ℂ) * I) := by
    push_cast; ring
  rw [h1, h2]
  simp only [neg_mul]
  have hI : I * I = -1 := I_mul_I
  linear_combination (Complex.exp ((Real.pi : ℂ) * x * I) - Complex.exp (-((Real.pi : ℂ) * x * I))) * hI

theorem e_int (n : ℤ) : e n = 1 := by
  simp only [e]
  rw [show 2 * (Real.pi : ℂ) * I * ((n : ℝ) : ℂ) = n * (2 * Real.pi * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- The Dirichlet kernel, telescoped: `(∑_{M<n≤M+N} e(xn))(e(x/2) − e(−x/2)) =
e(x(M+N) + x/2) − e(xM + x/2)`. -/
theorem kernel_mul (x : ℝ) (M N : ℕ) :
    (∑ n ∈ Ioc M (M + N), e (x * n)) * (e (x / 2) - e (-(x / 2))) =
      e (x * (M + N : ℕ) + x / 2) - e (x * M + x / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show M + (N + 1) = M + N + 1 by ring, sum_Ioc_succ_top (by omega), add_mul, ih]
    rw [mul_sub, ← e_add, ← e_add]
    have : x * ((M + N : ℕ) : ℝ) + x / 2 = x * ((M + N + 1 : ℕ) : ℝ) + -(x / 2) := by push_cast; ring
    rw [this]; ring

variable {ι : Type*} [DecidableEq ι]

theorem sin_ne_zero_of_not_int {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : Complex.sin (Real.pi * x) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]; intro k hk
  apply hx k
  have : ((Real.pi * x : ℝ) : ℂ) = (k : ℂ) * Real.pi := by push_cast; rw [← hk]
  have h' : Real.pi * x = k * Real.pi := by exact_mod_cast this
  have := Real.pi_pos
  nlinarith

omit [DecidableEq ι] in
/-- The off-diagonal coefficient. -/
theorem offdiag_term (α : ι → ℝ) (b : ι → ℂ) (M N : ℕ) {r r' : ι}
    (hx : ∀ n : ℤ, α r' - α r ≠ n) :
    starRingEnd ℂ (b r) * b r' * ∑ n ∈ Ioc M (M + N), e ((α r' - α r) * n) =
      -(1 / (2 * I * Real.pi)) *
        (starRingEnd ℂ (b r * e (α r * ((M + N : ℕ) + 1 / 2))) * (b r' * e (α r' * ((M + N : ℕ) + 1 / 2))) *
            (Real.pi / Complex.sin (Real.pi * (α r - α r' : ℝ))) -
          starRingEnd ℂ (b r * e (α r * (M + 1 / 2))) * (b r' * e (α r' * (M + 1 / 2))) *
            (Real.pi / Complex.sin (Real.pi * (α r - α r' : ℝ)))) := by
  set x := α r' - α r with hxdef
  have hsin := sin_ne_zero_of_not_int hx
  have hker := kernel_mul x M N
  rw [e_half_sub] at hker
  have hsum : ∑ n ∈ Ioc M (M + N), e (x * n) =
      (e (x * (M + N : ℕ) + x / 2) - e (x * M + x / 2)) / (2 * I * Complex.sin (Real.pi * x)) := by
    rw [← hker]; field_simp
  have hsin' : Complex.sin (Real.pi * (α r - α r' : ℝ)) = -Complex.sin (Real.pi * x) := by
    rw [← Complex.sin_neg]; congr 1; simp only [hxdef]; push_cast; ring
  have hA : starRingEnd ℂ (b r * e (α r * ((M + N : ℕ) + 1 / 2))) * (b r' * e (α r' * ((M + N : ℕ) + 1 / 2))) =
      starRingEnd ℂ (b r) * b r' * e (x * (M + N : ℕ) + x / 2) := by
    rw [map_mul, conj_e]
    have : x * ((M + N : ℕ) : ℝ) + x / 2 = -(α r * ((M + N : ℕ) + 1 / 2)) + α r' * ((M + N : ℕ) + 1 / 2) := by
      simp only [hxdef]; ring
    rw [this, e_add]; ring
  have hB : starRingEnd ℂ (b r * e (α r * (M + 1 / 2))) * (b r' * e (α r' * (M + 1 / 2))) =
      starRingEnd ℂ (b r) * b r' * e (x * M + x / 2) := by
    rw [map_mul, conj_e]
    have : x * (M : ℝ) + x / 2 = -(α r * (M + 1 / 2)) + α r' * (M + 1 / 2) := by
      simp only [hxdef]; ring
    rw [this, e_add]; ring
  have hcomm : (fun n : ℕ => e ((α r' - α r) * n)) = fun n : ℕ => e (x * n) := rfl
  rw [hcomm, hsum, hA, hB, hsin']
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- **The duality expansion.** -/
theorem dual_expand (s : Finset ι) (α : ι → ℝ)
    (hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n) (b : ι → ℂ) (M N : ℕ) :
    ((∑ n ∈ Ioc M (M + N), ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 : ℝ) : ℂ) =
      N * ((∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ) -
        (1 / (2 * I * Real.pi)) * (cscForm s α (fun r => b r * e (α r * ((M + N : ℕ) + 1 / 2))) -
          cscForm s α (fun r => b r * e (α r * (M + 1 / 2)))) := by
  have hnorm : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ w * w := fun w => by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hpt : ∀ n : ℕ, ((‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 : ℝ) : ℂ) = ∑ r ∈ s, ∑ r' ∈ s,
      starRingEnd ℂ (b r) * starRingEnd ℂ (e (α r * n)) * (b r' * e (α r' * n)) := by
    intro n
    rw [hnorm, map_sum, sum_mul_sum]
    simp only [map_mul]
  rw [Complex.ofReal_sum, sum_congr rfl fun n _ => hpt n]
  -- expand and swap sums
  have hexp : ∑ n ∈ Ioc M (M + N), ∑ r ∈ s, ∑ r' ∈ s,
      starRingEnd ℂ (b r) * starRingEnd ℂ (e (α r * n)) * (b r' * e (α r' * n)) =
      ∑ r ∈ s, ∑ r' ∈ s, starRingEnd ℂ (b r) * b r' * ∑ n ∈ Ioc M (M + N), e ((α r' - α r) * n) := by
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun r' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [conj_e, show (α r' - α r) * n = -(α r * n) + α r' * n by ring, e_add]; ring
  rw [hexp]
  have hsplit : ∀ r ∈ s, ∀ r' ∈ s, starRingEnd ℂ (b r) * b r' * ∑ n ∈ Ioc M (M + N), e ((α r' - α r) * n) =
      (if r = r' then (N : ℂ) * (starRingEnd ℂ (b r) * b r) else 0) +
        (if r = r' then 0 else -(1 / (2 * I * Real.pi)) *
          (starRingEnd ℂ (b r * e (α r * ((M + N : ℕ) + 1 / 2))) * (b r' * e (α r' * ((M + N : ℕ) + 1 / 2))) *
              (Real.pi / Complex.sin (Real.pi * (α r - α r' : ℝ))) -
            starRingEnd ℂ (b r * e (α r * (M + 1 / 2))) * (b r' * e (α r' * (M + 1 / 2))) *
              (Real.pi / Complex.sin (Real.pi * (α r - α r' : ℝ))))) := by
    intro r hr r' hr'
    by_cases h : r = r'
    · subst h
      rw [if_pos rfl, if_pos rfl, add_zero]
      simp only [sub_self, zero_mul, e_zero, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
        Nat.add_sub_cancel_left]
      ring
    · rw [if_neg h, if_neg h, zero_add]
      exact offdiag_term α b M N (fun n hn => hdist r' hr' r hr (Ne.symm h) n hn)
  rw [sum_congr rfl fun r hr => sum_congr rfl fun r' hr' => hsplit r hr r' hr']
  simp only [sum_add_distrib]
  have hdiag : ∑ r ∈ s, ∑ r' ∈ s, (if r = r' then (N : ℂ) * (starRingEnd ℂ (b r) * b r) else 0) =
      N * ((∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun r hr => ?_
    rw [sum_ite_eq, if_pos hr, hnorm]
  rw [hdiag]
  simp only [cscForm]
  rw [sub_eq_add_neg]
  congr 1
  rw [← sum_sub_distrib, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_sub_distrib, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun r' _ => ?_
  split_ifs <;> ring

/-! ### Dual bounds -/

theorem dual_bound_aux (s : Finset ι) (α : ι → ℝ)
    (hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n) (b : ι → ℂ) (M N : ℕ) {B : ℝ}
    (hB : ∀ t : ℝ, ‖cscForm s α (fun r => b r * e (α r * t))‖ ≤ B) :
    ∑ n ∈ Ioc M (M + N), ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 ≤
      N * ∑ r ∈ s, ‖b r‖ ^ 2 + B / Real.pi := by
  have h := congrArg Complex.re (dual_expand s α hdist b M N)
  rw [Complex.ofReal_re] at h
  rw [h]
  have hre : (N * ((∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ)).re = N * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.sub_re, hre]
  set w := (1 / (2 * I * Real.pi)) * (cscForm s α (fun r => b r * e (α r * ((M + N : ℕ) + 1 / 2))) -
    cscForm s α (fun r => b r * e (α r * (M + 1 / 2))))
  have hw : ‖w‖ ≤ B / Real.pi := by
    have hpi := Real.pi_pos
    simp only [w, norm_mul, norm_div, norm_one, Complex.norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_two, Real.norm_eq_abs, abs_of_pos hpi, mul_one]
    have h1 := hB ((M + N : ℕ) + 1 / 2)
    have h2 := hB (M + 1 / 2)
    have h3 := norm_sub_le (cscForm s α (fun r => b r * e (α r * ((M + N : ℕ) + 1 / 2))))
      (cscForm s α (fun r => b r * e (α r * (M + 1 / 2))))
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hpi]
    nlinarith
  have := Complex.re_le_norm (-w)
  rw [Complex.neg_re, norm_neg] at this
  linarith

/-- The dual weighted bound: `∑_n |∑_r b_r e(α_r n)|² ≤ ∑_r |b_r|² (N + (3/2)δ_r⁻¹)`. -/
theorem dual_weighted (s : Finset ι) (α δ : ι → ℝ) (hδ : ∀ r ∈ s, 0 < δ r)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ r ≤ |(α r - α r') - round (α r - α r')|) (b : ι → ℂ)
    (M N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 ≤
      ∑ r ∈ s, ‖b r‖ ^ 2 * (N + 3 / 2 * (δ r)⁻¹) := by
  have hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n :=
    fun r hr r' hr' h => Hilbert.dist_of_sep (hδ r hr) (hsep r hr r' hr' h)
  have hB : ∀ t : ℝ, ‖cscForm s α (fun r => b r * e (α r * t))‖ ≤ 4.66 * ∑ r ∈ s, ‖b r‖ ^ 2 / δ r := by
    intro t
    refine (csc_weighted s α δ hδ hsep _).trans (le_of_eq ?_)
    congr 1; refine sum_congr rfl fun r _ => ?_
    rw [norm_mul, norm_e, mul_one]
  refine (dual_bound_aux s α hdist b M N hB).trans ?_
  have hpi := Real.pi_gt_d4
  set Sd := ∑ r ∈ s, ‖b r‖ ^ 2 / δ r with hSd
  have hS : 0 ≤ Sd := sum_nonneg fun r hr => div_nonneg (sq_nonneg _) (hδ r hr).le
  have hc : 4.66 * Sd / Real.pi ≤ 3 / 2 * Sd := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  calc N * ∑ r ∈ s, ‖b r‖ ^ 2 + 4.66 * Sd / Real.pi ≤ N * ∑ r ∈ s, ‖b r‖ ^ 2 + 3 / 2 * Sd := by
        linarith
    _ = _ := by
        rw [hSd, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun r _ => by ring

/-- The dual uniform bound: `∑_n |∑_r b_r e(α_r n)|² ≤ (N + δ⁻¹) ∑_r |b_r|²`. -/
theorem dual_uniform (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(α r - α r') - round (α r - α r')|) (b : ι → ℂ)
    (M N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 ≤ (N + δ⁻¹) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n :=
    fun r hr r' hr' h => Hilbert.dist_of_sep hδ (hsep r hr r' hr' h)
  have hB : ∀ t : ℝ, ‖cscForm s α (fun r => b r * e (α r * t))‖ ≤
      Real.pi / δ * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    intro t
    refine (csc_uniform s α hδ hδ1 hsep _).trans (le_of_eq ?_)
    congr 1; refine sum_congr rfl fun r _ => ?_
    rw [norm_mul, norm_e, mul_one]
  refine (dual_bound_aux s α hdist b M N hB).trans (le_of_eq ?_)
  have hpi := Real.pi_pos
  field_simp

/-! ### Duality -/

omit [DecidableEq ι] in
/-- From a dual bound `∑_n |∑_r b_r e(α_r n)|² ≤ ∑_r |b_r|² c_r` to
`∑_r c_r⁻¹ |∑_n a_n e(α_r n)|² ≤ ∑_n |a_n|²`. -/
theorem primal_of_dual (s : Finset ι) (α : ι → ℝ) (c : ι → ℝ) (hc : ∀ r ∈ s, 0 < c r) (A : Finset ℕ)
    (hdual : ∀ b : ι → ℂ, ∑ n ∈ A, ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * c r)
    (a : ℕ → ℂ) :
    ∑ r ∈ s, (c r)⁻¹ * ‖∑ n ∈ A, a n * e (α r * n)‖ ^ 2 ≤ ∑ n ∈ A, ‖a n‖ ^ 2 := by
  set S : ι → ℂ := fun r => ∑ n ∈ A, a n * e (α r * n)
  set X := ∑ r ∈ s, (c r)⁻¹ * ‖S r‖ ^ 2
  set b : ι → ℂ := fun r => ((c r)⁻¹ : ℂ) * starRingEnd ℂ (S r)
  set D : ℕ → ℂ := fun n => ∑ r ∈ s, b r * e (α r * n)
  have hX0 : 0 ≤ X := sum_nonneg fun r hr => mul_nonneg (inv_nonneg.2 (hc r hr).le) (sq_nonneg _)
  have hXc : (X : ℂ) = ∑ n ∈ A, a n * D n := by
    simp only [X, D, b, S, Complex.ofReal_sum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    have : ((((c r)⁻¹ * ‖∑ n ∈ A, a n * e (α r * n)‖ ^ 2) : ℝ) : ℂ) =
        ((c r)⁻¹ : ℂ) * starRingEnd ℂ (∑ n ∈ A, a n * e (α r * n)) * ∑ n ∈ A, a n * e (α r * n) := by
      rw [Complex.ofReal_mul, mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [this, mul_sum]
    refine sum_congr rfl fun n _ => by ring
  have hD : ∑ n ∈ A, ‖D n‖ ^ 2 ≤ X := by
    refine (hdual b).trans (le_of_eq ?_)
    refine sum_congr rfl fun r hr => ?_
    simp only [b, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc r hr),
      Complex.norm_conj]
    have := (hc r hr).ne'
    field_simp
  -- Cauchy–Schwarz
  have hCS : X ≤ √(∑ n ∈ A, ‖a n‖ ^ 2) * √X := by
    have h1 : X ≤ ∑ n ∈ A, ‖a n‖ * ‖D n‖ := by
      have := congrArg (‖·‖) hXc
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0] at this
      rw [this]
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq A (fun n => ‖a n‖) (fun n => ‖D n‖)
    have h3 : ∑ n ∈ A, ‖a n‖ * ‖D n‖ ≤ √(∑ n ∈ A, ‖a n‖ ^ 2) * √(∑ n ∈ A, ‖D n‖ ^ 2) := by
      rw [← Real.sqrt_mul (sum_nonneg fun n _ => sq_nonneg _)]
      exact Real.le_sqrt_of_sq_le h2
    refine h1.trans (h3.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ ∑ n ∈ A, ‖a n‖ ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; exact hA0
  · have hsX := Real.sqrt_pos.2 hpos
    have h1 : √X * √X ≤ √(∑ n ∈ A, ‖a n‖ ^ 2) * √X := by rw [Real.mul_self_sqrt hX0]; exact hCS
    have h2 : √X ≤ √(∑ n ∈ A, ‖a n‖ ^ 2) := le_of_mul_le_mul_right h1 hsX
    calc X = √X * √X := (Real.mul_self_sqrt hX0).symm
      _ ≤ √(∑ n ∈ A, ‖a n‖ ^ 2) * √(∑ n ∈ A, ‖a n‖ ^ 2) :=
          mul_le_mul h2 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hA0

/-! ### The large sieves -/

/-- **The weighted large sieve** (Montgomery–Vaughan, [MV73, (1.6)]). -/
theorem large_sieve_weighted (s : Finset ι) (α δ : ι → ℝ) (hδ : ∀ r ∈ s, 0 < δ r)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ r ≤ |(α r - α r') - round (α r - α r')|)
    (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ((N : ℝ) + 3 / 2 * (δ r)⁻¹)⁻¹ * ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2 ≤
      ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 :=
  primal_of_dual s α (fun r => (N : ℝ) + 3 / 2 * (δ r)⁻¹)
    (fun r hr => by have := hδ r hr; positivity) _ (fun b => dual_weighted s α δ hδ hsep b M N) a

/-- The large sieve with `N + δ⁻¹`. -/
theorem large_sieve_uniform (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(α r - α r') - round (α r - α r')|)
    (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2 ≤
      ((N : ℝ) + δ⁻¹) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hc : (0 : ℝ) < N + δ⁻¹ := by positivity
  have hdual : ∀ b : ι → ℂ, ∑ n ∈ Ioc M (M + N), ‖∑ r ∈ s, b r * e (α r * n)‖ ^ 2 ≤
      ∑ r ∈ s, ‖b r‖ ^ 2 * ((N : ℝ) + δ⁻¹) := by
    intro b
    refine (dual_uniform s α hδ hδ1 hsep b M N).trans (le_of_eq ?_)
    rw [mul_sum]; exact sum_congr rfl fun r _ => by ring
  have h := primal_of_dual s α (fun _ => (N : ℝ) + δ⁻¹) (fun _ _ => hc) (Ioc M (M + N)) hdual a
  rw [← mul_sum] at h
  rwa [inv_mul_le_iff₀ hc] at h

omit [DecidableEq ι] in
/-- Reindexing the dilated sequence. -/
theorem dilate_sum {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hN : 1 ≤ N) (f : ℕ → ℂ) :
    ∑ m ∈ Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1)),
      (if k ∣ m then f m else 0) = ∑ n ∈ Ioc M (M + N), f (k * n) := by
  rw [← sum_filter]
  have hset : (Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1))).filter (k ∣ ·) =
      (Ioc M (M + N)).image (k * ·) := by
    have hk1 : k * (M + 1) ≥ 1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have htop : k * (M + 1) - 1 + (k * (N - 1) + 1) = k * (M + N) := by
      have : k * (M + N) = k * (M + 1) + k * (N - 1) := by
        rw [← mul_add]; congr 1; omega
      omega
    rw [htop]
    ext m
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨q, rfl⟩⟩
      refine ⟨q, ⟨?_, ?_⟩, rfl⟩
      · by_contra hq; push Not at hq
        have : k * q ≤ k * M := Nat.mul_le_mul_left k hq
        have : k * (M + 1) = k * M + k := by ring
        omega
      · exact (Nat.mul_le_mul_left_iff (by omega)).1 h2
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, Nat.mul_le_mul_left k h2⟩, dvd_mul_right k n⟩
      have : k * (M + 1) ≤ k * n := Nat.mul_le_mul_left k h1
      omega
  rw [hset, sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h]

/-- **The large sieve, optimal form** `N − 1 + δ⁻¹` (Selberg; Montgomery–Vaughan), by dilation. -/
theorem large_sieve_opt (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(α r - α r') - round (α r - α r')|)
    (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2 ≤
      ((N : ℝ) - 1 + δ⁻¹) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0; simp
  set X := ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2
  set A := ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun n _ => sq_nonneg _
  -- for every `k ≥ 1`: `X ≤ (N − 1 + 1/k + δ⁻¹) A`
  have hk : ∀ k : ℕ, 1 ≤ k → X ≤ ((N : ℝ) - 1 + 1 / k + δ⁻¹) * A := by
    intro k hk1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    set β : ι × ℕ → ℝ := fun p => (α p.1 + p.2) / k
    set a' : ℕ → ℂ := fun m => if k ∣ m then a (m / k) else 0
    have hδk : 0 < δ / k := div_pos hδ hk0
    have hδk1 : δ / k ≤ 1 := (div_le_self hδ.le (by exact_mod_cast hk1)).trans hδ1
    have hsep' : ∀ p ∈ s ×ˢ range k, ∀ q ∈ s ×ˢ range k, p ≠ q →
        δ / k ≤ |(β p - β q) - round (β p - β q)| := by
      intro p hp q hq hpq
      have hp1 := (mem_product.1 hp).1
      have hq1 := (mem_product.1 hq).1
      have hp2 := mem_range.1 (mem_product.1 hp).2
      have hq2 := mem_range.1 (mem_product.1 hq).2
      set m := round (β p - β q)
      have hx : (β p - β q) - m = ((α p.1 - α q.1) + ((p.2 : ℝ) - q.2 - k * m)) / k := by
        simp only [β]; field_simp; ring
      rw [hx, abs_div, abs_of_pos hk0, div_le_div_iff_of_pos_right hk0]
      by_cases hr : p.1 = q.1
      · have hj : p.2 ≠ q.2 := fun h => hpq (Prod.ext hr h)
        rw [hr, sub_self, zero_add]
        have hint : ((p.2 : ℤ) - q.2 - k * m) ≠ 0 := by
          intro h0
          have : (p.2 : ℤ) - q.2 = k * m := by linarith
          rcases eq_or_ne m 0 with hm | hm
          · rw [hm, mul_zero] at this; omega
          · have h1 : (k : ℤ) ≤ |(k : ℤ) * m| := by
              rw [abs_mul, abs_of_pos (by exact_mod_cast hk1)]
              exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hm)
            rw [← this] at h1
            have : |(p.2 : ℤ) - q.2| < k := by rw [abs_lt]; constructor <;> omega
            linarith
        have h1 : (1 : ℝ) ≤ |(((p.2 : ℤ) - q.2 - k * m : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hint
        push_cast at h1
        linarith
      · have h1 := hsep p.1 hp1 q.1 hq1 hr
        have h2 := round_le (α p.1 - α q.1) (k * m - p.2 + q.2)
        refine h1.trans (h2.trans (le_of_eq ?_))
        congr 1; push_cast; ring
    have hLS := large_sieve_uniform (s ×ˢ range k) β hδk hδk1 hsep' (k * (M + 1) - 1)
      (k * (N - 1) + 1) a'
    -- the left side
    have hS : ∀ p ∈ s ×ˢ range k, ∑ m ∈ Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1)),
        a' m * e (β p * m) = ∑ n ∈ Ioc M (M + N), a n * e (α p.1 * n) := by
      intro p hp
      have := dilate_sum hk1 M N hN1 (fun m => a (m / k) * e (β p * m))
      simp only [a', ite_mul, zero_mul]
      rw [this]
      refine sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n (by omega)]
      congr 1
      have : β p * ((k * n : ℕ) : ℝ) = α p.1 * n + (p.2 * n : ℕ) := by
        simp only [β]; push_cast; field_simp
      rw [this, e_add]
      have : e ((p.2 * n : ℕ) : ℝ) = 1 := by
        have := e_int ((p.2 * n : ℕ) : ℤ); push_cast at this ⊢; exact this
      rw [this, mul_one]
    have hR : ∑ m ∈ Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1)), ‖a' m‖ ^ 2 = A := by
      have := dilate_sum hk1 M N hN1 (fun m => ((‖a (m / k)‖ ^ 2 : ℝ) : ℂ))
      have h2 : ∑ m ∈ Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1)), ‖a' m‖ ^ 2 =
          ∑ m ∈ Ioc (k * (M + 1) - 1) (k * (M + 1) - 1 + (k * (N - 1) + 1)),
            (if k ∣ m then ‖a (m / k)‖ ^ 2 else 0) :=
        sum_congr rfl fun m _ => by simp only [a']; split_ifs <;> simp
      rw [h2]
      have h3 := congrArg Complex.re this
      simp only [Complex.re_sum, apply_ite Complex.re, Complex.ofReal_re, Complex.zero_re] at h3
      rw [h3]
      refine sum_congr rfl fun n _ => by rw [Nat.mul_div_cancel_left n (by omega)]
    rw [sum_congr rfl fun p hp => by rw [hS p hp], hR, sum_product] at hLS
    simp only [sum_const, card_range, nsmul_eq_mul] at hLS
    rw [← mul_sum] at hLS
    -- `k X ≤ (k(N−1) + 1 + k/δ) A`
    have hNc : ((k * (N - 1) + 1 : ℕ) : ℝ) = k * ((N : ℝ) - 1) + 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN1]; push_cast; ring
    rw [hNc, inv_div] at hLS
    rw [show ((N : ℝ) - 1 + 1 / k + δ⁻¹) * A = (k * ((N : ℝ) - 1) + 1 + k / δ) * A / k by
      field_simp]
    rw [le_div_iff₀ hk0]; linarith
  -- let `k → ∞`
  have hlim : Tendsto (fun k : ℕ => ((N : ℝ) - 1 + 1 / k + δ⁻¹) * A) atTop
      (𝓝 (((N : ℝ) - 1 + 0 + δ⁻¹) * A)) :=
    ((tendsto_one_div_atTop_nhds_zero_nat.const_add _).add_const _).mul_const _
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with k hk1
  exact hk k hk1

end TernaryGoldbach.Prelim.LS
