import TernaryGoldbach.Prelim.MoebiusSchData
import TernaryGoldbach.Explicit.LogNumerics

/-!
# `|m(x)| log x ≤ mprof(x)` for `x ≥ 11815`

`m(x) = ∑_{n ≤ x} μ(n)/n`. The step function `mprof`:
* `0.03` below `X₀ + 1 = 10⁸ + 1`: the kernel walk on `[11815, 2 160 535)` (`SmallMu.m_small`) and
  El Marraki's inequality with `|M(u)| ≤ 0.571 √u` beyond (`Sch.m_mid`);
* `0.092`, `0.09`, `0.08`, `0.035` on the cells of the induction, up to `T` (`Sch.m_cells`);
* `0.075` beyond `T` (`Sch.m_tail`).
The steps are at cell boundaries (`Sch.bndsM`): `9 001 713 129`, `1 525 381 771 989 686`,
`747 499 893 696 668 303 884 288` and `T ≈ e^{160.54}`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.Explicit

/-- The end of the cells, `T ≈ e^{160.54}`. -/
def Tcells : ℕ := 5273264915796702340408371151172679619749656857014800716447501879607296

/-- The stepped bound for `|m(x)| log x`. -/
noncomputable def mprof (x : ℝ) : ℝ :=
  if x < 100000001 then 0.03 else if x < 9001713129 then 0.092
  else if x < 1525381771989686 then 0.09 else if x < 747499893696668303884288 then 0.08
  else if x < Tcells then 0.035 else 0.075

theorem mprof_le (x : ℝ) : mprof x ≤ 0.14 := by
  unfold mprof; split_ifs <;> norm_num

theorem mprof_nonneg (x : ℝ) : 0 ≤ mprof x := by
  unfold mprof; split_ifs <;> norm_num

theorem Tcells_eq : Sch.TT = Tcells := by decide +kernel

/-- `mprof x = profq ⌊x⌋`. -/
theorem mprof_eq_profq {x : ℝ} (hx : 0 ≤ x) : mprof x = (Sch.profq ⌊x⌋₊ : ℝ) := by
  have key : ∀ B : ℕ, x < B ↔ ⌊x⌋₊ < B := fun B => (Nat.floor_lt hx).symm
  have k5 : x < (Tcells : ℝ) ↔
      ⌊x⌋₊ < 5273264915796702340408371151172679619749656857014800716447501879607296 := key Tcells
  unfold mprof Sch.profq
  have k1 := key 100000001
  have k2 := key 9001713129
  have k3 := key 1525381771989686
  have k4 := key 747499893696668303884288
  push_cast at k1 k2 k3 k4
  simp only [k1, k2, k3, k4, k5]
  split_ifs <;> norm_num

/-- The kernel range: `|m(x)| log x ≤ 0.03` for `11815 ≤ x < 2 160 535`. -/
theorem m_small_real {x : ℝ} (h1 : 11815 ≤ x) (h2 : x < 2160535) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ 0.03 := by
  set k := ⌊x⌋₊ with hk
  have hx0 : 0 < x := by linarith
  have hk1 : 11815 ≤ k := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : k ≤ 2160534 := by
    have : k < 2160535 := (Nat.floor_lt hx0.le).2 (by exact_mod_cast h2)
    omega
  have h := SmallMu.m_small hk1 hk2
  have hlog : Real.log x ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log hx0 (Nat.lt_floor_add_one x).le
  exact le_trans (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)) h

variable [Fact TernaryGoldbach.PlattGRH]

/-- **`|m(x)| log x ≤ mprof(x)` for `x ≥ 11815`.** -/
theorem moebius_log_le {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ mprof x := by
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨hc, Sf, hS1, hS2⟩ := Sch.m_cells
  rcases lt_or_ge x 100000001 with h1 | h1
  · have e : mprof x = 0.03 := by unfold mprof; rw [if_pos h1]
    rw [e]
    rcases lt_or_ge x 2160535 with h2 | h2
    · exact m_small_real hx h2
    · exact Sch.m_mid h2 h1
  rcases lt_or_ge x (Sch.TT : ℝ) with h2 | h2
  · rw [mprof_eq_profq hx0]
    exact hc x (by norm_num [Sch.X0]; linarith) h2
  · have e : mprof x = 0.075 := by
      have hT : (Tcells : ℝ) ≤ x := by rw [← Tcells_eq]; exact h2
      unfold mprof
      have a1 : ¬ x < 100000001 := by linarith
      have a5 : ¬ x < Tcells := by linarith
      have hTb : (747499893696668303884288 : ℝ) < Tcells := by norm_num [Tcells]
      have a4 : ¬ x < 747499893696668303884288 := by linarith
      have a3 : ¬ x < 1525381771989686 := by linarith
      have a2 : ¬ x < 9001713129 := by linarith
      simp only [a1, a2, a3, a4, a5, if_false]
    rw [e]
    exact Sch.m_tail h2 hS1 hS2

/-- **`|m(x)| ≤ 0.14/log x`** for `x ≥ 11815`. -/
theorem abs_m_le_014 {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.14 / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [le_div_iff₀ hl]
  exact (moebius_log_le hx).trans (mprof_le x)

/-- `|m(x)| ≤ 0.09/log x` for `x ≥ 10¹⁰`. -/
theorem abs_m_le_009 {x : ℝ} (hx : 1e10 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.09 / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos (by norm_num at hx; linarith)
  rw [le_div_iff₀ hl]
  refine (moebius_log_le (by norm_num at hx ⊢; linarith)).trans ?_
  unfold mprof
  have h1 : ¬ x < 100000001 := by norm_num at hx ⊢; linarith
  have h2 : ¬ x < 9001713129 := by norm_num at hx ⊢; linarith
  rw [if_neg h1, if_neg h2]
  split_ifs <;> norm_num

end TernaryGoldbach.Prelim
