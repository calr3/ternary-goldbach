import Mathlib

/-!
# The eigenvector identity for generalized Hilbert matrices

Let `x : ι → ℝ` be injective, `c : ι → ℝ`, `a_{nm} = 1/(x_n − x_m)` (`a_{nn} = 0`) and
`H_{nm} = c_n c_m a_{nm}`. If `Hz = νz` with `Re ν = 0`, then
`|ν|² ∑|z_l|² = ∑_{l,n} c_l² c_n² a_{nl}² |z_l|² + ∑_{l,m} c_l c_m a_{lm}² (c_l² + c_m²) Re(z̄_l z_m)`.

This is the summed form of [Preissmann–Lévêque, *On generalized weighted Hilbert matrices*,
arXiv:1303.1085, Lemma 5(b)], which generalizes the method of Montgomery–Vaughan. The proof: by
partial fractions, `∑_n c_n² a_{nl} a_{nm} = a_{lm}(σ_l − σ_m) + a_{lm}²(c_l² + c_m²)` for `l ≠ m`,
where `σ_l = ∑_n c_n² a_{nl}`; the `σ`-part of `‖Hz‖²` is `(ν + ν̄)∑σ_l|z_l|² = 0`.

We also record: a Hermitian matrix all of whose eigenvalues satisfy `|μ| ≤ C` has
`|z^* A z| ≤ C ‖z‖²`.
-/

open Finset Complex Matrix

namespace TernaryGoldbach.Prelim.Hilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `a_{nm} = 1/(x_n − x_m)`, `a_{nn} = 0`. -/
noncomputable def hk (x : ι → ℝ) (n m : ι) : ℝ := if n = m then 0 else 1 / (x n - x m)

omit [Fintype ι] in
theorem hk_self (x : ι → ℝ) (n : ι) : hk x n n = 0 := by simp [hk]

omit [Fintype ι] in
theorem hk_anti (x : ι → ℝ) (n m : ι) : hk x m n = -hk x n m := by
  unfold hk
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
    rw [show x m - x n = -(x n - x m) by ring, div_neg]

omit [Fintype ι] in
/-- Partial fractions for distinct `n, l, m`. -/
theorem hk_partial {x : ι → ℝ} (hx : Function.Injective x) {n l m : ι} (hnl : n ≠ l) (hnm : n ≠ m)
    (hlm : l ≠ m) : hk x n l * hk x n m = hk x l m * hk x n l + hk x m l * hk x n m := by
  simp only [hk, if_neg hnl, if_neg hnm, if_neg hlm, if_neg (Ne.symm hlm)]
  have h1 : x n - x l ≠ 0 := sub_ne_zero.2 (hx.ne hnl)
  have h2 : x n - x m ≠ 0 := sub_ne_zero.2 (hx.ne hnm)
  have h3 : x l - x m ≠ 0 := sub_ne_zero.2 (hx.ne hlm)
  have h4 : x m - x l ≠ 0 := sub_ne_zero.2 (hx.ne (Ne.symm hlm))
  field_simp
  ring

/-- `σ_l = ∑_n c_n² a_{nl}`. -/
noncomputable def sig (x c : ι → ℝ) (l : ι) : ℝ := ∑ n, c n ^ 2 * hk x n l

/-- The key sum: `∑_n c_n² a_{nl} a_{nm} = a_{lm}(σ_l − σ_m) + a_{lm}²(c_l² + c_m²)` for `l ≠ m`. -/
theorem key_sum {x : ι → ℝ} (hx : Function.Injective x) (c : ι → ℝ) {l m : ι} (hlm : l ≠ m) :
    ∑ n, c n ^ 2 * (hk x n l * hk x n m) =
      hk x l m * (sig x c l - sig x c m) + hk x l m ^ 2 * (c l ^ 2 + c m ^ 2) := by
  have hpt : ∀ n, c n ^ 2 * (hk x n l * hk x n m) =
      c n ^ 2 * (hk x l m * hk x n l + hk x m l * hk x n m) +
        ((if n = l then c l ^ 2 * hk x l m ^ 2 else 0) +
          (if n = m then c m ^ 2 * hk x l m ^ 2 else 0)) := by
    intro n
    by_cases hnl : n = l
    · subst hnl
      simp only [hk_self, if_true, if_neg hlm, hk_anti x n m]; ring
    · by_cases hnm : n = m
      · subst hnm
        simp only [hk_self, if_neg hnl, if_true, hk_anti x l n]; ring
      · rw [hk_partial hx hnl hnm hlm, if_neg hnl, if_neg hnm]; ring
  rw [sum_congr rfl fun n _ => hpt n, sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    if_pos (mem_univ _), if_pos (mem_univ _)]
  have hs : ∑ n, c n ^ 2 * (hk x l m * hk x n l + hk x m l * hk x n m) =
      hk x l m * sig x c l + hk x m l * sig x c m := by
    simp only [sig, mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => by ring
  rw [hs, hk_anti x l m]; ring

/-- **The eigenvector identity.** -/
theorem eigen_identity {x : ι → ℝ} (hx : Function.Injective x) (c : ι → ℝ) (z : ι → ℂ) {ν : ℂ}
    (hν : ν.re = 0)
    (heig : ∀ n, ∑ m, ((c n * c m * hk x n m : ℝ) : ℂ) * z m = ν * z n) :
    ‖ν‖ ^ 2 * ∑ n, ‖z n‖ ^ 2 =
      ∑ l, ∑ n, c l ^ 2 * c n ^ 2 * hk x n l ^ 2 * ‖z l‖ ^ 2 +
        ∑ l, ∑ m, c l * c m * hk x l m ^ 2 * (c l ^ 2 + c m ^ 2) * (starRingEnd ℂ (z l) * z m).re := by
  set Hz : ι → ℂ := fun n => ∑ m, ((c n * c m * hk x n m : ℝ) : ℂ) * z m with hHz
  -- `‖ν‖² ∑ |z|² = Re ∑_n conj(Hz_n) Hz_n`.
  have h1 : ‖ν‖ ^ 2 * ∑ n, ‖z n‖ ^ 2 = (∑ n, starRingEnd ℂ (Hz n) * Hz n).re := by
    rw [re_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [show Hz n = ν * z n from heig n, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, norm_mul]; ring
  -- Expand `∑_n conj(Hz_n) Hz_n = ∑_{l,m} c_l c_m z̄_l z_m ∑_n c_n² a_{nl} a_{nm}`.
  have h2 : ∑ n, starRingEnd ℂ (Hz n) * Hz n =
      ∑ l, ∑ m, ((c l * c m * ∑ n, c n ^ 2 * (hk x n l * hk x n m) : ℝ) : ℂ) *
        (starRingEnd ℂ (z l) * z m) := by
    have hpt : ∀ n, starRingEnd ℂ (Hz n) * Hz n = ∑ l, ∑ m,
        ((c l * c m * (c n ^ 2 * (hk x n l * hk x n m)) : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m) := by
      intro n
      simp only [hHz, map_sum, map_mul, Complex.conj_ofReal]
      rw [sum_mul_sum]
      refine sum_congr rfl fun l _ => sum_congr rfl fun m _ => ?_
      push_cast; ring
    rw [sum_congr rfl fun n _ => hpt n, sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_mul, ← Complex.ofReal_sum, mul_sum]
  -- Split by `l = m`.
  have h3 : ∀ l m, ((c l * c m * ∑ n, c n ^ 2 * (hk x n l * hk x n m) : ℝ) : ℂ) *
      (starRingEnd ℂ (z l) * z m) =
      (if l = m then ((∑ n, c l ^ 2 * c n ^ 2 * hk x n l ^ 2 * ‖z l‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((c l * c m * hk x l m * (sig x c l - sig x c m) : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m) +
        ((c l * c m * hk x l m ^ 2 * (c l ^ 2 + c m ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m) := by
    intro l m
    by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl, hk_self]
      simp only [mul_zero, zero_mul, Complex.ofReal_zero, add_zero, zero_pow two_ne_zero]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast [mul_sum, sum_mul]
      refine sum_congr rfl fun n _ => by ring
    · rw [if_neg hlm, key_sum hx c hlm]; push_cast; ring
  -- The `σ`-part vanishes.
  have h4 : ∑ l, ∑ m, ((c l * c m * hk x l m * (sig x c l - sig x c m) : ℝ) : ℂ) *
      (starRingEnd ℂ (z l) * z m) = 0 := by
    have hA : ∑ l, ∑ m, ((c l * c m * hk x l m * sig x c l : ℝ) : ℂ) *
        (starRingEnd ℂ (z l) * z m) = ν * ∑ l, (sig x c l : ℂ) * (starRingEnd ℂ (z l) * z l) := by
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      have := heig l
      calc ∑ m, ((c l * c m * hk x l m * sig x c l : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m)
          = (sig x c l : ℂ) * starRingEnd ℂ (z l) * ∑ m, ((c l * c m * hk x l m : ℝ) : ℂ) * z m := by
            rw [mul_sum]; refine sum_congr rfl fun m _ => by push_cast; ring
        _ = _ := by rw [this]; ring
    have hB : ∑ l, ∑ m, ((c l * c m * hk x l m * sig x c m : ℝ) : ℂ) *
        (starRingEnd ℂ (z l) * z m) =
          -starRingEnd ℂ ν * ∑ m, (sig x c m : ℂ) * (starRingEnd ℂ (z m) * z m) := by
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      have := congrArg (starRingEnd ℂ) (heig m)
      simp only [map_sum, map_mul, Complex.conj_ofReal] at this
      calc ∑ l, ((c l * c m * hk x l m * sig x c m : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m)
          = -((sig x c m : ℂ) * z m *
              ∑ l, ((c m * c l * hk x m l : ℝ) : ℂ) * starRingEnd ℂ (z l)) := by
            rw [mul_sum, ← sum_neg_distrib]
            refine sum_congr rfl fun l _ => ?_
            rw [hk_anti x m l]; push_cast; ring
        _ = _ := by rw [this]; ring
    simp only [mul_sub, Complex.ofReal_sub, sub_mul, sum_sub_distrib]
    rw [show (∑ l, ∑ m, ((c l * c m * hk x l m * sig x c l : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m)) -
        ∑ l, ∑ m, ((c l * c m * hk x l m * sig x c m : ℝ) : ℂ) * (starRingEnd ℂ (z l) * z m) = 0 from ?_]
    rw [hA, hB]
    have hre : starRingEnd ℂ ν = -ν := by
      apply Complex.ext <;> simp [hν]
    rw [hre]; ring
  rw [h1, h2]
  simp_rw [h3]
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true]
  rw [h4, add_zero]
  simp only [Complex.add_re, Complex.re_sum, Complex.ofReal_re, Complex.re_ofReal_mul]

/-! ### Quadratic forms of Hermitian matrices -/

omit [DecidableEq ι] in
theorem dot_self_eq (w : ι → ℂ) : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- If all eigenvalues of a Hermitian `A` satisfy `|μ| ≤ C`, then `|z^* A z| ≤ C ‖z‖²`. -/
theorem quad_form_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {C : ℝ}
    (hC : ∀ i, |hA.eigenvalues i| ≤ C) (z : ι → ℂ) :
    ‖star z ⬝ᵥ (A *ᵥ z)‖ ≤ C * ∑ i, ‖z i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set w := star U *ᵥ z with hw
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hstar : star w = star z ᵥ* U := by
    rw [hw, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hquad : star z ⬝ᵥ (A *ᵥ z) = star w ⬝ᵥ (D *ᵥ w) := by
    rw [hAeq, hstar, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      hw]
  have hnorm : ∑ i, ‖w i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    have h := dot_self_eq w
    rw [hstar, ← Matrix.dotProduct_mulVec, hw, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec,
      dot_self_eq] at h
    exact_mod_cast h.symm
  rw [hquad, ← hnorm]
  have hD : star w ⬝ᵥ (D *ᵥ w) = ∑ i, (hA.eigenvalues i : ℂ) * ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [D, dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, show (‖w i‖ ^ 2 : ℝ) = Complex.normSq (w i) from
      (Complex.normSq_eq_norm_sq _).symm, Complex.normSq_eq_conj_mul_self]
    exact mul_left_comm (starRingEnd ℂ (w i)) _ (w i)
  rw [hD, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖w i‖)]
  exact mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)

/-- The eigenvector `b_i` of `A` is a nonzero solution of `A b = μ_i b`, with `∑ ‖b‖² = 1`. -/
theorem eigenvector_spec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    A *ᵥ ⇑(hA.eigenvectorBasis i) = (hA.eigenvalues i : ℂ) • ⇑(hA.eigenvectorBasis i) ∧
      ∑ j, ‖(hA.eigenvectorBasis i) j‖ ^ 2 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [hA.mulVec_eigenvectorBasis i]
    ext j; simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  · have h := (hA.eigenvectorBasis).orthonormal.1 i
    rw [EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [one_pow] at h2
    rw [Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg _)] at h2
    exact h2

end TernaryGoldbach.Prelim.Hilbert
