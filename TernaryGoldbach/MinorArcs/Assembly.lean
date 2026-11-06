import TernaryGoldbach.MinorArcs.Decomposition
import TernaryGoldbach.MinorArcs.GcdSums

/-!
# Assembling the minor-arc bound [H, §6.1]: `S_{0,∞}`, `S_{0,2}`

`S_{0,∞} = 0` for `V ≤ x/4`, `|S_{0,2}| ≤ 3 log x` (only powers of `2` contribute), and so
`|S_{η₂}| ≤ |S_{I,1}| + |S_{I,2}| + |S_{II}| + 3 log x`.
-/

open Real Finset
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

theorem norm_wt_le (α x : ℝ) (n : ℕ) : ‖wt α x n‖ ≤ 3 := by
  rw [wt, norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Helfgott.eta2_nonneg _)]
  exact Helfgott.eta2_le _

/-- [H, §6.1]: `S_{0,∞} = 0` for `V ≤ x/4`. -/
theorem S0inf_eq_zero (α : ℝ) {x : ℝ} (hx : 0 < x) {V : ℕ} (hV : (V : ℝ) ≤ x / 4) :
    S0inf α x V = 0 := by
  refine sum_eq_zero fun n hn => ?_
  have hnV : (n : ℝ) ≤ V := by exact_mod_cast (mem_Icc.1 hn).2
  have : eta2 (n / x) = 0 := Helfgott.eta2_eq_zero fun h => by
    have := h.1; rw [lt_div_iff₀ hx] at this; linarith
  simp [wt, this]

/-- [H, §6.1]: `|S_{0,2}| ≤ 3 log x` (crude: `η₂ ≤ 3`, `∑_{2^k ≤ x} log 2 ≤ log x`). -/
theorem norm_S0two_le (α : ℝ) {x : ℝ} (hx : 1 ≤ x) : ‖S0two α x‖ ≤ 3 * Real.log x := by
  set N := ⌊x⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have h1 : ‖S0two α x‖ ≤ ∑ n ∈ Icc 1 N with 2 ∣ n, (Λ n : ℝ) * 3 := by
    unfold S0two
    refine (norm_sum_le _ _).trans ?_
    rw [sum_filter]
    refine sum_le_sum fun n _ => ?_
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    by_cases ho : Odd n
    · have : ¬ 2 ∣ n := by
        rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ho
      simp [ho, this]
    · have : 2 ∣ n := by
        rw [← even_iff_two_dvd]; exact Nat.not_odd_iff_even.1 ho
      rw [if_neg ho, if_pos this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      exact mul_le_mul_of_nonneg_left (norm_wt_le _ _ _) hΛ
  have h2 := sum_vonMangoldt_pow_dvd_le Nat.prime_two le_rfl (fun _ => (3 : ℝ))
    (fun _ => by norm_num) (N := N)
  have h3 : Real.log 2 * ∑ _α ∈ Icc 1 (Nat.log 2 N), (3 : ℝ) ≤ 3 * Real.log x := by
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have hK : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ x :=
      (Nat.cast_le.2 (Nat.pow_log_le_self 2 (by omega))).trans (Nat.floor_le (by linarith))
    have := Real.log_le_log (by positivity) hK
    push_cast at this
    rw [Real.log_pow] at this
    nlinarith
  simp only [pow_one, Nat.cast_ofNat] at h2
  linarith

/-- [H, (3.11)] in norm: `|S_{η₂}| ≤ |S_{I,1}| + |S_{I,2}| + |S_{II}| + 3 log x` for `V ≤ x/4`. -/
theorem norm_S_le_parts (α : ℝ) {x : ℝ} (hx : 1 ≤ x) (U V : ℕ) (hV : (V : ℝ) ≤ x / 4) :
    ‖S eta2 x α‖ ≤ ‖typeILog α x U‖ + ‖typeI2 α x U V‖ + ‖typeII α x U V‖ + 3 * Real.log x := by
  rw [decomposition α (by linarith) U V, S0inf_eq_zero α (by linarith) hV, add_zero]
  have := norm_S0two_le α hx
  calc _ ≤ ‖typeILog α x U - typeI2 α x U V + typeII α x U V‖ + ‖S0two α x‖ := norm_add_le _ _
    _ ≤ ‖typeILog α x U‖ + ‖typeI2 α x U V‖ + ‖typeII α x U V‖ + ‖S0two α x‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ _ := by gcongr

end TernaryGoldbach.MinorArcs
