import TernaryGoldbach.Prelim.SmallMstarMain
import TernaryGoldbach.Prelim.MstarLarge

/-!
# [H, (2.22)] with [H]'s constant: `|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ (4/5) (q/φ(q))/log(x/q)`

[H] quotes it from Ramaré [Ramb, Thm 1.12] (who has `0.78`), for `1 ≤ q < x`. Ramaré's route:
`|m_q(x)| ≤ ∑_{d ∣ q squarefree} S(x/d)/d` with `S(y) = ∑_{w ≤ √y} |m(y/w²)|/w²`
(`MstarReduce.lean`), and `S(y) log y ≤ 0.8` for all `y ≥ 1`:
* for `1 ≤ y < e¹⁰` by the kernel (`SmallMstar*.lean`; `S` depends only on `⌊y⌋`); the maximum of
  `S(k) log(k+1)` there is `0.7832`, at `k = 10`;
* for `y ≥ e¹⁰` from Ramaré's `0.03/log x` and the kernel-checked `|m(z)| ≤ √(2/z)` below `11815`
  (`MstarLarge.lean`, at most `0.72`).

The only hypothesis is `RamareMoebius`, which is proved from `PlattGRH`
(`ramareMoebius_of_plattGRH`). The minor arcs use the bound with `2.8`
(`LiouvilleBound.abs_sum_moebius_div_coprime_le_log`), under the same hypothesis; this file records
[H]'s statement and is not used by the main theorems.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

theorem exp_10_lt : Real.exp 10 < 22027 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 10 < 2.7182818286 ^ 10 := by gcongr
    _ < 22027 := by norm_num

/-- `S(y)` depends only on `⌊y⌋`. -/
theorem Sm_eq_floor {y : ℝ} : Sm y = Sm (⌊y⌋₊ : ℝ) := by
  unfold Sm
  rw [Nat.floor_natCast]
  refine sum_congr rfl fun w _ => ?_
  have : msumR (y / ((w * w : ℕ) : ℝ)) = msumR ((⌊y⌋₊ : ℝ) / ((w * w : ℕ) : ℝ)) := by
    rw [msumR, msumR, Nat.floor_div_natCast, Nat.floor_div_eq_div]
  rw [this]

/-- `S(y) log y ≤ 0.8` for `1 ≤ y < e¹⁰`, from the kernel check at `k = ⌊y⌋`. -/
theorem Sm_mul_log_le_small {y : ℝ} (h1 : 1 ≤ y) (h2 : y < Real.exp 10) :
    Sm y * Real.log y ≤ 0.8 := by
  set k := ⌊y⌋₊ with hk
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : k ≤ 22026 := by
    have hy : y < ((22027 : ℕ) : ℝ) := by push_cast; exact lt_trans h2 exp_10_lt
    have := (Nat.floor_lt (by linarith : (0 : ℝ) ≤ y)).2 hy
    omega
  have hS := SmallMstar.walk_all k hk1 hk2
  rw [Sm_eq_floor, ← hk]
  have hlog : Real.log y ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log (by linarith) (Nat.lt_floor_add_one y).le
  calc Sm (k : ℝ) * Real.log y ≤ Sm (k : ℝ) * Real.log ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlog (Sm_nonneg _)
    _ ≤ 0.8 := hS

/-- `S(y) log y ≤ 0.8` for all `y ≥ 1`. -/
theorem Sm_mul_log_le [Fact RamareMoebius] {y : ℝ} (hy : 1 ≤ y) : Sm y * Real.log y ≤ 0.8 := by
  rcases lt_or_ge y (Real.exp 10) with h | h
  · exact Sm_mul_log_le_small hy h
  · exact Sm_mul_log_le_large h

/-- **[H, (2.22)]** with [H]'s constant ([Ramb, Thm 1.12]): for `1 ≤ q < x`,
`|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ (4/5) (q/φ(q))/log(x/q)`. -/
theorem abs_sum_moebius_div_coprime_le_log_sharp [Fact RamareMoebius] {x : ℝ} {q : ℕ}
    (hq : 1 ≤ q) (hqx : (q : ℝ) < x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      4 / 5 * (q / Nat.totient q) / Real.log (x / q) := by
  have h := abs_sum_coprime_le_of_Sm (C := 0.8) (fun y hy => Sm_mul_log_le hy) hq hqx
  have e : (4 / 5 : ℝ) = 0.8 := by norm_num
  rw [e]
  exact h

end TernaryGoldbach.Prelim
