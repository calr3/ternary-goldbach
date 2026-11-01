import TernaryGoldbach.MinorArcs.LargeSieveArcs

/-!
# `Σ_{q ≤ r, q odd} μ²(q)/φ(q)` for `r = 150000`

* **Numerical axiom** `sum_odd_mu_sq_div_totient` ([B, §14.1]: `= 6.798779…`), a finite sum, checked
  with directed-rounding decimal arithmetic by `scripts/check_sum_mu2_phi.py`.
* `sum_Qset_mPhi`: the moduli of `𝔐_{δ₀,r}` (odd `q ≤ r`, even `q ≤ 2r`) give twice the odd sum,
  since `μ²(2q')/φ(2q') = [q' odd] μ²(q')/φ(q')`.
-/

open Finset

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.MinorArcs (Qset qt)

/-- `μ²(q)/φ(q)`. -/
noncomputable def mPhi (q : ℕ) : ℝ := (if Squarefree q then (1 : ℝ) else 0) / q.totient

theorem moebius_sq_eq (q : ℕ) :
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = if Squarefree q then 1 else 0 := by
  split_ifs with h
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

/-- **Numerical axiom** ([B, §14.1]): `Σ_{q ≤ 150000, q odd} μ²(q)/φ(q) = 6.798779…`
(rigorous enclosure `[6.7987791731235030762, 6.7987791731235030763]` by
`scripts/check_sum_mu2_phi.py`). -/
axiom sum_odd_mu_sq_div_totient :
    6.798779 ≤ ∑ q ∈ (Icc 1 150000).filter Odd,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient ∧
      ∑ q ∈ (Icc 1 150000).filter Odd,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient ≤ 6.79878

theorem sum_odd_mPhi_bounds :
    6.798779 ≤ ∑ q ∈ (Icc 1 150000).filter Odd, mPhi q ∧
      ∑ q ∈ (Icc 1 150000).filter Odd, mPhi q ≤ 6.79878 := by
  have h : ∀ q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient = mPhi q := fun q => by
    rw [moebius_sq_eq, mPhi]
  have hax := sum_odd_mu_sq_div_totient
  simp_rw [h] at hax
  exact hax

theorem mPhi_two_mul (q : ℕ) : mPhi (2 * q) = if Odd q then mPhi q else 0 := by
  split_ifs with ho
  · have hcop : Nat.Coprime 2 q := (Nat.coprime_two_left).2 ho
    have hsq : Squarefree (2 * q) ↔ Squarefree q := by
      rw [Nat.squarefree_mul hcop]; simp [Nat.squarefree_two]
    unfold mPhi
    rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
    simp only [hsq]
  · have he : Even q := Nat.not_odd_iff_even.1 ho
    obtain ⟨k, rfl⟩ := he
    have hns : ¬Squarefree (2 * (k + k)) := by
      intro hs
      have h4 : 2 * 2 ∣ 2 * (k + k) := ⟨k, by ring⟩
      have := hs 2 h4
      norm_num at this
    unfold mPhi; rw [if_neg hns, zero_div]

/-- **The moduli of `𝔐_{8,r₀}`**: `Σ_{q ∈ Qset r₀} μ²(q)/φ(q) = 2 Σ_{q ≤ r₀ odd} μ²(q)/φ(q)`. -/
theorem sum_Qset_mPhi :
    ∑ q ∈ Qset 150000, mPhi q = 2 * ∑ q ∈ (Icc 1 150000).filter Odd, mPhi q := by
  have hQ : Qset 150000 = (Icc 1 300000).filter fun q => (qt q : ℝ) ≤ 2 * 150000 := by
    unfold Qset; congr 1; norm_num
  rw [hQ, ← Finset.sum_filter_add_sum_filter_not _ Odd]
  have h1 : ((Icc 1 300000).filter fun q => (qt q : ℝ) ≤ 2 * 150000).filter Odd =
      (Icc 1 150000).filter Odd := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    unfold qt
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, ho⟩
      rw [if_neg (Nat.not_even_iff_odd.2 ho)] at h2
      have : q ≤ 150000 := by exact_mod_cast (by push_cast at h2; linarith : (q : ℝ) ≤ 150000)
      exact ⟨⟨h1, this⟩, ho⟩
    · rintro ⟨⟨h1, h2⟩, ho⟩
      refine ⟨⟨⟨h1, by omega⟩, ?_⟩, ho⟩
      rw [if_neg (Nat.not_even_iff_odd.2 ho)]
      have : (q : ℝ) ≤ 150000 := by exact_mod_cast h2
      push_cast; linarith
  have h2 : ((Icc 1 300000).filter fun q => (qt q : ℝ) ≤ 2 * 150000).filter (fun q => ¬Odd q) =
      (Icc 1 150000).image (fun q => 2 * q) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.not_odd_iff_even]
    simp only [Finset.mem_Icc]
    unfold qt
    constructor
    · rintro ⟨⟨⟨h1, h3⟩, -⟩, ⟨k, rfl⟩⟩
      exact ⟨k, ⟨by omega, by omega⟩, by ring⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨k, by ring⟩⟩
      rw [if_pos ⟨k, by ring⟩]
      have : (k : ℝ) ≤ 150000 := by exact_mod_cast hk2
      push_cast; linarith
  rw [h1, h2, sum_image (fun a _ b _ h => by omega)]
  simp_rw [mPhi_two_mul]
  rw [← sum_filter]
  ring

theorem sum_Qset_mPhi_bounds :
    13.597558 ≤ ∑ q ∈ Qset 150000, mPhi q ∧ ∑ q ∈ Qset 150000, mPhi q ≤ 13.59756 := by
  rw [sum_Qset_mPhi]
  have := sum_odd_mPhi_bounds
  constructor <;> linarith [this.1, this.2]

end TernaryGoldbach.MajorArcs
