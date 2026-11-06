import TernaryGoldbach.Prelim.SmallPsi

/-! `ψ(n) < 1.03883 n` for `1 ≤ n ≤ 700`, kernel-checked (extends `Small.psi_lt_small`). -/

open Finset

namespace TernaryGoldbach.Prelim.Small

theorem loop_700 : loop 103883 100000 700 0 1 = true := by decide +kernel

/-- `ψ(n) < 1.03883 n` for `1 ≤ n ≤ 700` (kernel-checked). -/
theorem psi_lt_small_700 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 700) :
    ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) < 1.03883 * n := by
  have hchk := loop_spec 103883 100000 700 0 (by rw [lcmUpto_zero]; exact loop_700) n
    (by omega) (by omega)
  have hlog := log_lt_of_chk (by norm_num) (Nat.lcmUpto_pos n) hchk
  have hψ := Chebyshev.psi_eq_log_lcmUpto n
  have e : Chebyshev.psi n = ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]; rfl
  rw [← e, hψ]
  norm_num at hlog ⊢
  linarith

end TernaryGoldbach.Prelim.Small
