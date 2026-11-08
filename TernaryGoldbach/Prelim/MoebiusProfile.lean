import TernaryGoldbach.Prelim.MoebiusCases

/-!
# `|m(x)| log x ≤ mprof(x)` for `x ≥ 11815`

`m(x) = ∑_{n ≤ x} μ(n)/n`. The step function `mprof`:
`0.03` on `[11815, 2 160 535)` (the kernel walk, `SmallMu.m_small`), then `0.14`, `0.1`, `0.08`,
`0.065` up to `e^{200}` and `0.09` beyond (the identity, `MoebiusCases.lean`, from `CDEMertens`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.Explicit

/-- The stepped bound for `|m(x)| log x`. -/
noncomputable def mprof (x : ℝ) : ℝ :=
  if x < 2160535 then 0.03 else if x < 10000000 then 0.14 else if x < 49603849 then 0.1
  else if x < 10000000000 then 0.08 else if Real.log x < 200 then 0.065 else 0.09

theorem mprof_le (x : ℝ) : mprof x ≤ 0.14 := by
  unfold mprof; split_ifs <;> norm_num

theorem mprof_nonneg (x : ℝ) : 0 ≤ mprof x := by
  unfold mprof; split_ifs <;> norm_num

theorem exp_100_ge : (1e43 : ℝ) ≤ Real.exp 100 := by
  have h1 := exp_nat_ge' 100
  push_cast at h1
  have h3 : (1e43 : ℝ) ≤ 2.7182818283 ^ 100 := by norm_num
  linarith

theorem exp_200_ge : (1e86 : ℝ) ≤ Real.exp 200 := by
  have h1 := exp_nat_ge' 200
  push_cast at h1
  have h3 : (1e86 : ℝ) ≤ 2.7182818283 ^ 200 := by norm_num
  linarith

theorem le_of_log_ge {x c B : ℝ} (hx : 0 < x) (hc : c ≤ Real.log x) (hB : B ≤ Real.exp c) : B ≤ x := by
  have := Real.exp_le_exp.2 hc
  rw [Real.exp_log hx] at this
  linarith

/-- The kernel range: `|m(x)| log x ≤ 0.03` for `11815 ≤ x < 2 160 535`. -/
theorem m_small_real {x : ℝ} (h1 : 11815 ≤ x) (h2 : x < 2160535) : |mx x| * Real.log x ≤ 0.03 := by
  set k := ⌊x⌋₊ with hk
  have hx0 : 0 < x := by linarith
  have hk1 : 11815 ≤ k := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : k ≤ 2160534 := by
    have : k < 2160535 := (Nat.floor_lt hx0.le).2 (by exact_mod_cast h2)
    omega
  have h := SmallMu.m_small hk1 hk2
  have hlog : Real.log x ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log hx0 (Nat.lt_floor_add_one x).le
  unfold mx
  rw [← hk]
  exact le_trans (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)) h

variable [Fact TernaryGoldbach.PlattGRH]

/-- **`|m(x)| log x ≤ mprof(x)` for `x ≥ 11815`.** -/
theorem moebius_profile (hCDE : CDEMertens) {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ mprof x := by
  change |mx x| * Real.log x ≤ mprof x
  have hx0 : 0 < x := by linarith
  unfold mprof
  split_ifs with a1 a2 a3 a4 a5
  · exact m_small_real hx a1
  · push Not at a1
    rcases lt_or_ge x (3000000 : ℕ) with b | b
    · exact c1 hCDE (by exact_mod_cast a1) b
    rcases lt_or_ge x (5000000 : ℕ) with b' | b'
    · exact c2 hCDE b b'
    · exact c3 hCDE b' (by exact_mod_cast a2)
  · push Not at a2
    rcases lt_or_ge x (20000000 : ℕ) with b | b
    · exact c4 hCDE (by exact_mod_cast a2) b
    · exact c5 hCDE b (by exact_mod_cast a3)
  · push Not at a3
    rcases lt_or_ge x (100000000 : ℕ) with b | b
    · exact c6 hCDE (by exact_mod_cast a3) b
    rcases lt_or_ge x (999950884 : ℕ) with b' | b'
    · exact c7 hCDE b b'
    rcases lt_or_ge x (1579983001 : ℕ) with b'' | b''
    · exact c8 hCDE b' b''
    · exact c9 hCDE b'' (by exact_mod_cast a4)
  · push Not at a4
    rcases lt_or_ge x (100000000000 : ℕ) with b | b
    · exact c10 hCDE (by exact_mod_cast a4) b
    rcases lt_or_ge x (49000000000000 : ℕ) with b' | b'
    · exact c11 hCDE b b'
    rcases lt_or_ge x (100000000000000000 : ℕ) with b'' | b''
    · exact c12 hCDE b' b''
    rcases le_or_gt (Real.log x) 100 with b3 | b3
    · exact c13 hCDE b'' b3
    · exact c14 hCDE (le_of_log_ge hx0 b3.le (by have := exp_100_ge; norm_num at this ⊢; linarith)) a5.le
  · push Not at a4 a5
    rcases le_or_gt (Real.log x) 20001 with b | b
    · exact c15 hCDE (le_of_log_ge hx0 a5 (by have := exp_200_ge; norm_num at this ⊢; linarith)) b
    · exact c16 hCDE (le_of_log_ge hx0 b.le le_rfl)

end TernaryGoldbach.Prelim
