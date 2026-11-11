/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Defs
import Mathlib.Tactic.Simproc.Factors

/-!
# `M(t)` for `t ≤ 32`

Generated: `μ(t)` for `t ≤ 32` from the factorizations (via the `Nat.primeFactorsList` simproc),
then `M(t)` by `M(t+1) = M(t) + μ(t+1)`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

theorem mu_eval (n : ℕ) (hn : n ≠ 0) :
    μ n = if (Nat.primeFactorsList n).Nodup then (-1) ^ (Nat.primeFactorsList n).length else 0 := by
  split_ifs with h
  · rw [moebius_apply_of_squarefree ((Nat.squarefree_iff_nodup_primeFactorsList hn).2 h),
      cardFactors_apply]
  · exact moebius_eq_zero_of_not_squarefree
      (fun hs => h ((Nat.squarefree_iff_nodup_primeFactorsList hn).1 hs))

theorem mu_1 : μ 1 = 1 := by rw [mu_eval 1 (by norm_num)]; simp
theorem mu_2 : μ 2 = -1 := by rw [mu_eval 2 (by norm_num)]; simp
theorem mu_3 : μ 3 = -1 := by rw [mu_eval 3 (by norm_num)]; simp
theorem mu_4 : μ 4 = 0 := by rw [mu_eval 4 (by norm_num)]; simp
theorem mu_5 : μ 5 = -1 := by rw [mu_eval 5 (by norm_num)]; simp
theorem mu_6 : μ 6 = 1 := by rw [mu_eval 6 (by norm_num)]; simp
theorem mu_7 : μ 7 = -1 := by rw [mu_eval 7 (by norm_num)]; simp
theorem mu_8 : μ 8 = 0 := by rw [mu_eval 8 (by norm_num)]; simp
theorem mu_9 : μ 9 = 0 := by rw [mu_eval 9 (by norm_num)]; simp
theorem mu_10 : μ 10 = 1 := by rw [mu_eval 10 (by norm_num)]; simp
theorem mu_11 : μ 11 = -1 := by rw [mu_eval 11 (by norm_num)]; simp
theorem mu_12 : μ 12 = 0 := by rw [mu_eval 12 (by norm_num)]; simp
theorem mu_13 : μ 13 = -1 := by rw [mu_eval 13 (by norm_num)]; simp
theorem mu_14 : μ 14 = 1 := by rw [mu_eval 14 (by norm_num)]; simp
theorem mu_15 : μ 15 = 1 := by rw [mu_eval 15 (by norm_num)]; simp
theorem mu_16 : μ 16 = 0 := by rw [mu_eval 16 (by norm_num)]; simp
theorem mu_17 : μ 17 = -1 := by rw [mu_eval 17 (by norm_num)]; simp
theorem mu_18 : μ 18 = 0 := by rw [mu_eval 18 (by norm_num)]; simp
theorem mu_19 : μ 19 = -1 := by rw [mu_eval 19 (by norm_num)]; simp
theorem mu_20 : μ 20 = 0 := by rw [mu_eval 20 (by norm_num)]; simp
theorem mu_21 : μ 21 = 1 := by rw [mu_eval 21 (by norm_num)]; simp
theorem mu_22 : μ 22 = 1 := by rw [mu_eval 22 (by norm_num)]; simp
theorem mu_23 : μ 23 = -1 := by rw [mu_eval 23 (by norm_num)]; simp
theorem mu_24 : μ 24 = 0 := by rw [mu_eval 24 (by norm_num)]; simp
theorem mu_25 : μ 25 = 0 := by rw [mu_eval 25 (by norm_num)]; simp
theorem mu_26 : μ 26 = 1 := by rw [mu_eval 26 (by norm_num)]; simp
theorem mu_27 : μ 27 = 0 := by rw [mu_eval 27 (by norm_num)]; simp
theorem mu_28 : μ 28 = 0 := by rw [mu_eval 28 (by norm_num)]; simp
theorem mu_29 : μ 29 = -1 := by rw [mu_eval 29 (by norm_num)]; simp
theorem mu_30 : μ 30 = -1 := by rw [mu_eval 30 (by norm_num)]; simp
theorem mu_31 : μ 31 = -1 := by rw [mu_eval 31 (by norm_num)]; simp
theorem mu_32 : μ 32 = 0 := by rw [mu_eval 32 (by norm_num)]; simp

theorem M_val_0 : M 0 = 0 := M_zero
theorem M_val_1 : M 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, M_succ, M_val_0, show (0 + 1 : ℕ) = 1 from rfl, mu_1]; norm_num
theorem M_val_2 : M 2 = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, M_succ, M_val_1, show (1 + 1 : ℕ) = 2 from rfl, mu_2]; norm_num
theorem M_val_3 : M 3 = -1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, M_succ, M_val_2, show (2 + 1 : ℕ) = 3 from rfl, mu_3]; norm_num
theorem M_val_4 : M 4 = -1 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, M_succ, M_val_3, show (3 + 1 : ℕ) = 4 from rfl, mu_4]; norm_num
theorem M_val_5 : M 5 = -2 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, M_succ, M_val_4, show (4 + 1 : ℕ) = 5 from rfl, mu_5]; norm_num
theorem M_val_6 : M 6 = -1 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, M_succ, M_val_5, show (5 + 1 : ℕ) = 6 from rfl, mu_6]; norm_num
theorem M_val_7 : M 7 = -2 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, M_succ, M_val_6, show (6 + 1 : ℕ) = 7 from rfl, mu_7]; norm_num
theorem M_val_8 : M 8 = -2 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, M_succ, M_val_7, show (7 + 1 : ℕ) = 8 from rfl, mu_8]; norm_num
theorem M_val_9 : M 9 = -2 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, M_succ, M_val_8, show (8 + 1 : ℕ) = 9 from rfl, mu_9]; norm_num
theorem M_val_10 : M 10 = -1 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, M_succ, M_val_9, show (9 + 1 : ℕ) = 10 from rfl, mu_10]; norm_num
theorem M_val_11 : M 11 = -2 := by
  rw [show (11 : ℕ) = 10 + 1 from rfl, M_succ, M_val_10, show (10 + 1 : ℕ) = 11 from rfl, mu_11]; norm_num
theorem M_val_12 : M 12 = -2 := by
  rw [show (12 : ℕ) = 11 + 1 from rfl, M_succ, M_val_11, show (11 + 1 : ℕ) = 12 from rfl, mu_12]; norm_num
theorem M_val_13 : M 13 = -3 := by
  rw [show (13 : ℕ) = 12 + 1 from rfl, M_succ, M_val_12, show (12 + 1 : ℕ) = 13 from rfl, mu_13]; norm_num
theorem M_val_14 : M 14 = -2 := by
  rw [show (14 : ℕ) = 13 + 1 from rfl, M_succ, M_val_13, show (13 + 1 : ℕ) = 14 from rfl, mu_14]; norm_num
theorem M_val_15 : M 15 = -1 := by
  rw [show (15 : ℕ) = 14 + 1 from rfl, M_succ, M_val_14, show (14 + 1 : ℕ) = 15 from rfl, mu_15]; norm_num
theorem M_val_16 : M 16 = -1 := by
  rw [show (16 : ℕ) = 15 + 1 from rfl, M_succ, M_val_15, show (15 + 1 : ℕ) = 16 from rfl, mu_16]; norm_num
theorem M_val_17 : M 17 = -2 := by
  rw [show (17 : ℕ) = 16 + 1 from rfl, M_succ, M_val_16, show (16 + 1 : ℕ) = 17 from rfl, mu_17]; norm_num
theorem M_val_18 : M 18 = -2 := by
  rw [show (18 : ℕ) = 17 + 1 from rfl, M_succ, M_val_17, show (17 + 1 : ℕ) = 18 from rfl, mu_18]; norm_num
theorem M_val_19 : M 19 = -3 := by
  rw [show (19 : ℕ) = 18 + 1 from rfl, M_succ, M_val_18, show (18 + 1 : ℕ) = 19 from rfl, mu_19]; norm_num
theorem M_val_20 : M 20 = -3 := by
  rw [show (20 : ℕ) = 19 + 1 from rfl, M_succ, M_val_19, show (19 + 1 : ℕ) = 20 from rfl, mu_20]; norm_num
theorem M_val_21 : M 21 = -2 := by
  rw [show (21 : ℕ) = 20 + 1 from rfl, M_succ, M_val_20, show (20 + 1 : ℕ) = 21 from rfl, mu_21]; norm_num
theorem M_val_22 : M 22 = -1 := by
  rw [show (22 : ℕ) = 21 + 1 from rfl, M_succ, M_val_21, show (21 + 1 : ℕ) = 22 from rfl, mu_22]; norm_num
theorem M_val_23 : M 23 = -2 := by
  rw [show (23 : ℕ) = 22 + 1 from rfl, M_succ, M_val_22, show (22 + 1 : ℕ) = 23 from rfl, mu_23]; norm_num
theorem M_val_24 : M 24 = -2 := by
  rw [show (24 : ℕ) = 23 + 1 from rfl, M_succ, M_val_23, show (23 + 1 : ℕ) = 24 from rfl, mu_24]; norm_num
theorem M_val_25 : M 25 = -2 := by
  rw [show (25 : ℕ) = 24 + 1 from rfl, M_succ, M_val_24, show (24 + 1 : ℕ) = 25 from rfl, mu_25]; norm_num
theorem M_val_26 : M 26 = -1 := by
  rw [show (26 : ℕ) = 25 + 1 from rfl, M_succ, M_val_25, show (25 + 1 : ℕ) = 26 from rfl, mu_26]; norm_num
theorem M_val_27 : M 27 = -1 := by
  rw [show (27 : ℕ) = 26 + 1 from rfl, M_succ, M_val_26, show (26 + 1 : ℕ) = 27 from rfl, mu_27]; norm_num
theorem M_val_28 : M 28 = -1 := by
  rw [show (28 : ℕ) = 27 + 1 from rfl, M_succ, M_val_27, show (27 + 1 : ℕ) = 28 from rfl, mu_28]; norm_num
theorem M_val_29 : M 29 = -2 := by
  rw [show (29 : ℕ) = 28 + 1 from rfl, M_succ, M_val_28, show (28 + 1 : ℕ) = 29 from rfl, mu_29]; norm_num
theorem M_val_30 : M 30 = -3 := by
  rw [show (30 : ℕ) = 29 + 1 from rfl, M_succ, M_val_29, show (29 + 1 : ℕ) = 30 from rfl, mu_30]; norm_num
theorem M_val_31 : M 31 = -4 := by
  rw [show (31 : ℕ) = 30 + 1 from rfl, M_succ, M_val_30, show (30 + 1 : ℕ) = 31 from rfl, mu_31]; norm_num
theorem M_val_32 : M 32 = -4 := by
  rw [show (32 : ℕ) = 31 + 1 from rfl, M_succ, M_val_31, show (31 + 1 : ℕ) = 32 from rfl, mu_32]; norm_num

end TernaryGoldbach.RSBounds.Moebius003
