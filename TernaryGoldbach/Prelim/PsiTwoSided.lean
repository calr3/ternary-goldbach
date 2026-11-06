import TernaryGoldbach.Prelim.SmallPsiTableMain
import TernaryGoldbach.Explicit.PsiRanges

/-!
# `|ψ(n) − n| ≤ c(n) √n` on `[12, 10¹⁷]`

`c(n) = 1` for `n < 10⁶` (`SmallTab.small_table`, kernel-checked) and `c(n) = cW(n)` on
`[10⁶, 10¹⁷]` (`Explicit.psi_mid`, the Weil-window explicit formula; `cW ≤ 33` up to `10⁸`,
`cW ≤ 72`). Also `n − 2.3662√n ≤ θ(n) ≤ n` for `12 ≤ n < 10⁶`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

/-- The constant of `psi_two_sided`. -/
noncomputable def cB (n : ℕ) : ℝ := if n < 1000000 then 1 else Explicit.cW n

theorem cB_le_72 (n : ℕ) : cB n ≤ 72 := by
  unfold cB; split_ifs
  · norm_num
  · exact Explicit.cW_le_72 _

theorem cB_le_33 {n : ℕ} (h : n ≤ 10 ^ 8) : cB n ≤ 33 := by
  unfold cB; split_ifs
  · norm_num
  · exact Explicit.cW_le_33 (by
      have : ((n : ℕ) : ℝ) ≤ ((10 ^ 8 : ℕ) : ℝ) := by exact_mod_cast h
      norm_num at this ⊢; linarith)

private theorem cast_le_of {n : ℕ} {a : ℝ} {b : ℕ} (h : n ≤ b) (hb : (b : ℝ) = a) : (n : ℝ) ≤ a := by
  rw [← hb]; exact_mod_cast h

theorem cB_le_355 {n : ℕ} (h : n ≤ 32000000000) : cB n ≤ 35.5 := by
  unfold cB; split_ifs with h1
  · norm_num
  · exact Explicit.cW_le_355 (by push Not at h1; have : (1000000 : ℝ) ≤ n := by exact_mod_cast h1
                                 linarith) (cast_le_of h (by norm_num))

theorem cB_le_315 {n : ℕ} (h1 : 10000000 < n) (h : n ≤ 100000000) : cB n ≤ 31.5 := by
  unfold cB; rw [if_neg (by omega)]
  exact Explicit.cW_le_315 (by have : (10000000 : ℝ) < n := by exact_mod_cast h1
                               linarith) (cast_le_of h (by norm_num))

theorem cB_le_4282 {n : ℕ} (h1 : 320000000000 < n) (h : n ≤ 3200000000000) : cB n ≤ 42.82 := by
  unfold cB; rw [if_neg (by omega)]
  exact Explicit.cW_le_4282 (by have : (320000000000 : ℝ) < n := by exact_mod_cast h1
                                linarith) (cast_le_of h (by norm_num))

theorem cB_le_4508 {n : ℕ} (h1 : 320000000000 < n) (h : n ≤ 10000000000000) : cB n ≤ 45.08 := by
  unfold cB; rw [if_neg (by omega)]
  exact Explicit.cW_le_4508 (by have : (320000000000 : ℝ) < n := by exact_mod_cast h1
                                linarith) (cast_le_of h (by norm_num))

theorem cB_small {n : ℕ} (h : n < 1000000) : cB n = 1 := by unfold cB; rw [if_pos h]

theorem thS_add_ppS (n : ℕ) : SmallTab.thS n + SmallTab.ppS n = ∑ m ∈ Icc 1 n, (Λ m : ℝ) := by
  unfold SmallTab.thS SmallTab.ppS
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]; ring
  · ring

theorem psi_Icc_eq (n : ℕ) : Helfgott.psi n = ∑ m ∈ Icc 1 n, (Λ m : ℝ) := by
  rw [Helfgott.psi, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  simp [Finset.Ico_add_one_right_eq_Icc]

variable [Fact TernaryGoldbach.RHUpTo] in
/-- **`|ψ(n) − n| ≤ c(n) √n` for `12 ≤ n ≤ 10¹⁷`.** -/
theorem psi_two_sided {n : ℕ} (h1 : 12 ≤ n) (h2 : n ≤ 10 ^ 17) :
    |∑ m ∈ Icc 1 n, (Λ m : ℝ) - n| ≤ cB n * √(n : ℝ) := by
  rcases lt_or_ge n 1000000 with h | h
  · rw [cB_small h, one_mul]
    obtain ⟨r1, r2, -, -⟩ := SmallTab.small_table (t := (n : ℝ)) (by exact_mod_cast h1) (by exact_mod_cast h)
    rw [Nat.floor_natCast, thS_add_ppS] at r1 r2
    norm_num at r1 r2
    rw [abs_le]; constructor <;> linarith
  · unfold cB; rw [if_neg (by omega)]
    have ha : ((1000000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hb : (n : ℝ) ≤ ((10 ^ 17 : ℕ) : ℝ) := by exact_mod_cast h2
    have hm := Explicit.psi_mid (x := (n : ℝ)) (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    rw [Explicit.psiR, Nat.floor_natCast, psi_Icc_eq] at hm
    exact hm

/-- `n − 2.3662 √n ≤ θ(n) ≤ n` for `12 ≤ n < 10⁶`. -/
theorem theta_small_two_sided {n : ℕ} (h1 : 12 ≤ n) (h2 : n < 1000000) :
    (n : ℝ) - 2.3662 * √(n : ℝ) ≤ ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p ∧
      ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p ≤ n := by
  obtain ⟨-, -, r3, r4⟩ := SmallTab.small_table (t := (n : ℝ)) (by exact_mod_cast h1) (by exact_mod_cast h2)
  rw [Nat.floor_natCast] at r3 r4
  unfold SmallTab.thS at r3 r4
  norm_num at r4
  exact ⟨by linarith, r3⟩

end TernaryGoldbach.Prelim
