import TernaryGoldbach.Prelim.MVLemma8
import TernaryGoldbach.Prelim.SmallProdAp
import TernaryGoldbach.Prelim.SmallG
import TernaryGoldbach.Prelim.SmallW
import TernaryGoldbach.Prelim.Ramare

/-!
# [MV73, Lemma 7]: `G(r) = ∑_{s ≤ r} μ(s)²/φ(s) ≥ log r + 1.07` for `r ≥ 6`

For `r ≥ 21400` this follows from Ramaré's estimate `G(r) = log r + c_E + O*(7.284 r^{−1/3})`
(`Prelim.ramare_Gq`, [H, (12.12)]); for `6 ≤ r < 21400` it is checked by the kernel
(`SmallG.lemma7_small`).
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim.MV

/-- `G(r)` as Ramaré's `G_1(r)`. -/
theorem GS_eq_GqP (r : ℕ) : GS r = TernaryGoldbach.Prelim.GqP 1 r := by
  unfold GS TernaryGoldbach.Prelim.GqP
  rw [Nat.floor_natCast, filter_true_of_mem (fun x _ => Nat.coprime_one_right x)]
  refine sum_congr rfl fun n _ => ?_
  unfold gS
  have h := ArithmeticFunction.moebius_sq (n := n)
  have h' : ((μ n : ℝ)) ^ 2 = if Squarefree n then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this; rw [this]
  rw [h']; split_ifs <;> simp

/-- **[MV73, Lemma 7]**: `G(r) ≥ log r + 1.07` for `r ≥ 6`. -/
theorem lemma7 (r : ℕ) (h6 : 6 ≤ r) : Real.log r + 1.07 ≤ GS r := by
  rcases lt_or_ge r 21400 with hr | hr
  · exact TernaryGoldbach.Prelim.SmallG.lemma7_small r h6 hr
  obtain ⟨c, hc1, -, hram⟩ := TernaryGoldbach.Prelim.ramare_Gq
  have hr' : (21400 : ℝ) ≤ r := by exact_mod_cast hr
  have h := (abs_le.1 (hram 1 le_rfl r (by linarith))).1
  have hS : TernaryGoldbach.Prelim.SqP 1 = 0 := by simp [TernaryGoldbach.Prelim.SqP]
  have hf : TernaryGoldbach.Prelim.f1qP 1 = 1 := by simp [TernaryGoldbach.Prelim.f1qP]
  rw [hS, hf] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul, mul_one, add_zero] at h
  -- `r^{−1/3} ≤ 1/27.75`
  have h3 : (27.75 : ℝ) ≤ (r : ℝ) ^ (1 / 3 : ℝ) := by
    calc (27.75 : ℝ) = ((27.75 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (r : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have h4 : (r : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 / 27.75 := by
    rw [Real.rpow_neg (by positivity), ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  rw [GS_eq_GqP]
  nlinarith

/-- **[MV73, Lemma 8]** (with kernel checks for `R < 1000`): for `R ≥ 2`,
`∑_{r ≤ R} (1 + r/R)⁻¹ μ(r)²/φ(r) > log R + 0.25068`. -/
theorem lemma8 {R : ℝ} (hR : 2 ≤ R) : Real.log R + 0.25068 ≤ WR R := by
  rcases lt_or_ge R 6 with h | h
  · exact (lemma8_tiny hR h).le
  rcases lt_or_ge R 1000 with h' | h'
  · exact (TernaryGoldbach.Prelim.SmallW.lemma8_mid h h').le
  · exact lemma8_large lemma7 h'

end TernaryGoldbach.Prelim.MV
