/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Range2
import RSBounds.Moebius003.Tail

/-!
# The theorem of `mobius003.tex`, from its inputs

The proof of the theorem (§6 of the note): the four ranges `[11815, 6·10⁵]` (input (m)),
`(6·10⁵, 10⁹)` (Lemma 7(c)), `[10⁹, D_end)` (the cells) and `[D_end, ∞)` (Corollary 11).
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Real

/-- The theorem at natural numbers: `|m(n)| log(n + 1) ≤ 0.03` for `n ≥ 11815`. -/
theorem main_nat (h : Inputs) {n : ℕ} (hn : 11815 ≤ n) : |msum n| * Real.log (n + 1) ≤ 0.03 := by
  by_cases h1 : n ≤ 6 * 10 ^ 5
  · exact h.small n hn h1
  by_cases h2 : n < X0
  · exact range2 h (by omega) h2
  have hc := cells h
  by_cases h3 : n < Dend
  · exact hc.mBound n (by omega) h3
  · exact tail h hc (by omega)

/-- **The theorem of `mobius003.tex`**: `Target` holds. -/
theorem target : Target := by
  intro hS hP hM hm hW hGH hRH
  have h := Inputs.of_target_hyps hS hP hM hm hW hGH hRH
  intro x hx
  have hn : 11815 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have key := main_nat h hn
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hle : Real.log x ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) :=
    Real.log_le_log (by linarith) (Nat.lt_floor_add_one x).le
  change |msum ⌊x⌋₊| ≤ 0.03 / Real.log x
  rw [le_div_iff₀ hlogx]
  calc |msum ⌊x⌋₊| * Real.log x ≤ |msum ⌊x⌋₊| * Real.log ((⌊x⌋₊ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ ≤ 0.03 := key

end TernaryGoldbach.RSBounds.Moebius003
