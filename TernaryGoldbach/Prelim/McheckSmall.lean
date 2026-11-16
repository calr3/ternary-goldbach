import TernaryGoldbach.Prelim.SmallMcheckMain

/-!
# `|m̌(x)| ≤ 1.00303` for `1 ≤ x ≤ 2·10⁵`, and `∑_{t < 2·10⁵} |M(t)|/t ≤ 131`

From the kernel walk (`SmallMcheck.lean`, `SmallMcheckData*.lean`, `SmallMcheckMain.lean`): the
bound at the integers `k ≤ 2·10⁵`, and in between by monotonicity on each `[k, k+1]`. The maximum
is `m̌(29) = 1.0030213…` ([Ramb, Cor. 1.10]: "`1.00303` can be replaced by `m̌(30)`").
-/

open Finset

namespace TernaryGoldbach.Prelim

/-- `|m̌(x)| ≤ 1.00303` for `1 ≤ x ≤ 2·10⁵`. -/
theorem abs_mcheck_le_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 200000) : |mcheck x| ≤ 1.00303 := by
  obtain ⟨-, hP⟩ := SmallMcheck.walk_all
  set k := ⌊x⌋₊ with hkdef
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hx1)
  have hkx : (k : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxk : x < k + 1 := Nat.lt_floor_add_one x
  have hk2 : k ≤ 200000 := by
    have : (k : ℝ) ≤ 200000 := hkx.trans hx2
    exact_mod_cast this
  rcases (show k < 200000 ∨ k = 200000 by omega) with hlt | heq
  · exact SmallMcheck.abs_mcheck_le_of_ends hk1 (hP k hk1 hk2) (hP (k + 1) (by omega) (by omega))
      hkx (by linarith)
  · have hk' : (k : ℝ) = 200000 := by exact_mod_cast heq
    have hx : x = ((200000 : ℕ) : ℝ) := by push_cast; linarith
    rw [hx]
    exact hP 200000 (by norm_num) le_rfl

/-- `∑_{t < 2·10⁵} |M(t)|/t ≤ 131`. -/
theorem sum_abs_mertR_div_le : ∑ t ∈ Ico (1 : ℕ) 200000, |mertR t| / (t : ℝ) ≤ 131 := by
  obtain ⟨hg, -⟩ := SmallMcheck.walk_all
  have h := hg.2.2.2.2.2.2
  have hB : (SmallMcheck.B : ℝ) = 10 ^ 20 := by norm_num [SmallMcheck.B]
  simp only [hB] at h
  have hs : (0 : ℝ) ≤ ∑ t ∈ Ico (1 : ℕ) 200000, |mertR t| / (t : ℝ) :=
    sum_nonneg fun t _ => by positivity
  norm_num at h
  linarith

end TernaryGoldbach.Prelim
