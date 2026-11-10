import TernaryGoldbach.Prelim.MuSieveMain
import TernaryGoldbach.Prelim.ElMarraki
import TernaryGoldbach.Prelim.SmallMertens

/-!
# `|M(u)| ≤ 0.571 √u` for `100 ≤ u ≤ 100 001 092`

From the trial-division walk (`SmallMu.M_small`, up to `2 160 534`) and the packed sieve
(`MuSieve.M_sieve`, beyond); and the starting constant `C(X₀) = M(X₀) − N(X₀)/log(X₀+1)` of the induction
at `X₀ = 10⁸`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch

theorem Mn_eq_Mz (u : ℕ) : Mn u = (MuSieve.Mz u : ℝ) := by
  unfold Mn MuSieve.Mz; push_cast
  rw [show Ioc 0 u = Icc 1 u by ext; simp; omega]

theorem M_low {u : ℕ} (h1 : 100 ≤ u) (h2 : u ≤ 100001092) : |Mn u| ≤ 0.571 * √(u : ℝ) := by
  rcases le_or_gt u 2160534 with h | h
  · have := SmallMu.M_small h1 h
    rw [show Mn u = ∑ k ∈ Icc 1 u, (μ k : ℝ) by unfold Mn; rw [show Ioc 0 u = Icc 1 u by ext; simp; omega]]
    have hs := Real.sqrt_nonneg (u : ℝ)
    linarith
  · have hs := MuSieve.M_sieve h h2
    rw [Mn_eq_Mz]
    have hr : ((10 ^ 6 * (MuSieve.Mz u * MuSieve.Mz u) : ℤ) : ℝ) ≤ ((326041 * (u : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hs
    push_cast at hr
    have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    have hsq := Real.sq_sqrt hu
    rw [abs_le]
    have hb : ((MuSieve.Mz u : ℝ)) ^ 2 ≤ (0.571 * √(u : ℝ)) ^ 2 := by
      rw [mul_pow, hsq]; nlinarith
    have hpos : 0 ≤ 0.571 * √(u : ℝ) := by positivity
    constructor <;> nlinarith [sq_nonneg ((MuSieve.Mz u : ℝ) + 0.571 * √(u : ℝ)),
      sq_nonneg ((MuSieve.Mz u : ℝ) - 0.571 * √(u : ℝ))]

/-- `1/√(m+1) ≤ 2(√(m+1) − √m)`. -/
theorem inv_sqrt_step' (m : ℕ) : (1 : ℝ) / √((m + 1 : ℕ) : ℝ) ≤ 2 * (√((m + 1 : ℕ) : ℝ) - √(m : ℝ)) := by
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hs1 : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hm1
  have hs0 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
  have hle : √(m : ℝ) ≤ √((m + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hsq1 := Real.mul_self_sqrt hm1.le
  have hsq0 := Real.mul_self_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [div_le_iff₀ hs1]
  have e : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
  nlinarith

/-- `∑_{a < n ≤ b} 1/√n ≤ 2(√b − √a)`. -/
theorem sum_inv_sqrt_Ioc' {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / √(n : ℝ) ≤ 2 * (√(b : ℝ) - √(a : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    have := ih (by omega)
    have := inv_sqrt_step' (a + k)
    linarith

/-- The start of the induction. -/
def X0 : ℕ := 100000000

/-- `|C(X₀)| ≤ 626`, with `C(X₀) = M(X₀) − N(X₀)/log(X₀+1)`. -/
theorem C0_le : |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)| ≤ 626 := by
  have hl : (1842 : ℝ) / 100 ≤ Real.log ((X0 : ℝ) + 1) := by
    have := Small.le_log_of_chk (cN := 1842) (cD := 100) (L := 100000001) (by norm_num) (by norm_num)
      (by decide +kernel)
    have e : ((X0 : ℝ) + 1) = ((100000001 : ℕ) : ℝ) := by norm_num [X0]
    rw [e]; exact_mod_cast this
  have hl0 : 0 < Real.log ((X0 : ℝ) + 1) := by linarith
  rw [C_eq X0 (by norm_num [X0]), abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
  have hterm : ∀ n ∈ Ioc 0 X0, |Mn n * (Real.log ((n : ℝ) + 1) - Real.log n)| ≤
      (if n < 100 then 1 else 0.571 * (1 / √(n : ℝ))) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hd0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n :=
      sub_nonneg.2 (Real.log_le_log hn0 (by linarith))
    have hd : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [← Real.log_div (by linarith) hn0.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    rw [abs_mul, abs_of_nonneg hd0]
    split_ifs with h
    · have := abs_Mn_le n
      calc |Mn n| * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ n * (1 / n) :=
            mul_le_mul this hd hd0 (by positivity)
        _ = 1 := by field_simp
    · have hM := M_low (u := n) (by omega) (by unfold X0 at h2; omega)
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
      have hsq := Real.mul_self_sqrt hn0.le
      calc |Mn n| * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 0.571 * √(n : ℝ) * (1 / n) :=
            mul_le_mul hM hd hd0 (by positivity)
        _ = 0.571 * (√(n : ℝ) / n) := by ring
        _ = 0.571 * (1 / √(n : ℝ)) := by rw [Real.sqrt_div_self']
  have hsplit : ∑ n ∈ Ioc 0 X0, (if n < 100 then (1 : ℝ) else 0.571 * (1 / √(n : ℝ))) =
      ∑ n ∈ Ioc 0 99, (1 : ℝ) + 0.571 * ∑ n ∈ Ioc 99 X0, (1 / √(n : ℝ)) := by
    rw [← Finset.sum_Ioc_consecutive _ (by norm_num : 0 ≤ 99) (by norm_num [X0] : 99 ≤ X0), mul_sum]
    have e1 : ∑ n ∈ Ioc (0 : ℕ) 99, (if n < 100 then (1 : ℝ) else 0.571 * (1 / √(n : ℝ))) = ∑ n ∈ Ioc (0 : ℕ) 99, (1 : ℝ) :=
      sum_congr rfl fun n hn => by rw [if_pos (by have := (mem_Ioc.1 hn).2; omega)]
    have e2 : ∑ n ∈ Ioc 99 X0, (if n < 100 then (1 : ℝ) else 0.571 * (1 / √(n : ℝ))) =
        ∑ n ∈ Ioc 99 X0, 0.571 * (1 / √(n : ℝ)) :=
      sum_congr rfl fun n hn => by rw [if_neg (by have := (mem_Ioc.1 hn).1; omega)]
    rw [e1, e2]
  have hs := sum_inv_sqrt_Ioc' (a := 99) (b := X0) (by norm_num [X0])
  have hsX : √((X0 : ℕ) : ℝ) = 10000 := by
    rw [show ((X0 : ℕ) : ℝ) = 10000 ^ 2 by norm_num [X0]]; exact Real.sqrt_sq (by norm_num)
  have hs99 := Real.sqrt_nonneg ((99 : ℕ) : ℝ)
  have hc : ∑ n ∈ Ioc 0 99, (1 : ℝ) = 99 := by rw [sum_const, Nat.card_Ioc]; norm_num
  calc |∑ n ∈ Ioc 0 X0, Mn n * (Real.log ((n : ℝ) + 1) - Real.log n)|
      ≤ ∑ n ∈ Ioc 0 X0, |Mn n * (Real.log ((n : ℝ) + 1) - Real.log n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 X0, (if n < 100 then (1 : ℝ) else 0.571 * (1 / √(n : ℝ))) := sum_le_sum hterm
    _ ≤ 626 * Real.log ((X0 : ℝ) + 1) := by
        rw [hsplit, hc]
        rw [hsX] at hs
        have h3 : (0.571 : ℝ) * ∑ n ∈ Ioc 99 X0, (1 / √(n : ℝ)) ≤ 0.571 * 20000 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); exact le_trans hs (by linarith)
        linarith

end TernaryGoldbach.Prelim.Sch
