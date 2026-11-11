/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.ElMarraki
import RSBounds.Moebius003.Misc

/-!
# Lemma 7(c) of the note: the range `(6·10⁵, 10⁹)`

El Marraki's inequality with (M) and Lemma 7(a) give `|m(n)| ≤ 3c_M/√n + (log n)/n` for
`33 ≤ n ≤ 10⁹`. Instead of the note's monotonicity argument, `(6·10⁵, 10⁹]` is cut into the
intervals `[600001, 679297]`, `[679297, 1605044]`, `[1605044, 10⁹]`, and on each `[a, b]` the
bound `log(b+1) (3c_M/√a + (log b)/a) ≤ 0.03` is checked by `decide +kernel`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Finset Real

theorem msum_le_range2 (h : Inputs) {n : ℕ} (h1 : 33 ≤ n) (h2 : n ≤ X0) :
    |msum n| ≤ 3 * cM / Real.sqrt n + Real.log n / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  have hEM := el_marraki (x := n) (by omega)
  have hM := abs_M_le_sqrt h h1 h2
  have hS := S_le h h1 (by omega)
  have h33 := S33_le
  have hs32 : (5.656 : ℝ) ≤ Real.sqrt 32 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsn1 : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by
    exact_mod_cast Nat.sub_le n 1)
  have hS' : S n ≤ 2 * cM * Real.sqrt n := by unfold cM at *; nlinarith
  have e1 : cM * Real.sqrt n / n = cM / Real.sqrt n := by
    rw [div_eq_div_iff hn.ne' hs.ne', mul_assoc, hsq]
  have e2 : 2 * cM * Real.sqrt n / n = 2 * cM / Real.sqrt n := by
    rw [div_eq_div_iff hn.ne' hs.ne', mul_assoc, hsq]
  calc |msum n| ≤ |M n| / n + S n / n + Real.log n / n := hEM
    _ ≤ cM * Real.sqrt n / n + 2 * cM * Real.sqrt n / n + Real.log n / n := by gcongr
    _ = 3 * cM / Real.sqrt n + Real.log n / n := by rw [e1, e2]; ring

/-- The check of one interval `[a, b]`. -/
def r2ok (a b : ℕ) : Bool :=
  decide (LogCert.logHi ((b : ℚ) + 1) * (3 * (571 / 1000) / LogCert.sqrtLo a +
    LogCert.logHi b / a) ≤ 3 / 100) && decide (0 < LogCert.sqrtLo a) && decide (1 ≤ a) && decide (a ≤ b)

theorem r2_1 : r2ok 600001 679297 = true := by decide +kernel
theorem r2_2 : r2ok 679297 1605044 = true := by decide +kernel
theorem r2_3 : r2ok 1605044 1000000000 = true := by decide +kernel

theorem r2ok_sound (h : Inputs) {a b : ℕ} (hab : r2ok a b = true) {n : ℕ} (hna : a ≤ n) (hnb : n ≤ b)
    (h33 : 33 ≤ n) (hX : n ≤ X0) : |msum n| * Real.log (n + 1) ≤ 0.03 := by
  simp only [r2ok, Bool.and_eq_true, decide_eq_true_eq] at hab
  obtain ⟨⟨⟨hchk, hs0⟩, ha1⟩, _⟩ := hab
  have hchk' := (Rat.cast_le (K := ℝ)).mpr hchk
  push_cast at hchk'
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hm := msum_le_range2 h h33 hX
  have hsa : (LogCert.sqrtLo a : ℝ) ≤ Real.sqrt a := by
    have := LogCert.sqrtLo_le (a : ℚ); push_cast at this; exact this
  have hsa0 : (0 : ℝ) < LogCert.sqrtLo a := by exact_mod_cast hs0
  have hsn : Real.sqrt a ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hna)
  have hlb : Real.log n ≤ LogCert.logHi b := by
    have := LogCert.le_logHi (q := (b : ℚ)) (by exact_mod_cast (by omega : 0 < b))
    push_cast at this
    exact (Real.log_le_log hn (by exact_mod_cast hnb)).trans this
  have hlb1 : Real.log ((n : ℝ) + 1) ≤ LogCert.logHi ((b : ℚ) + 1) := by
    have := LogCert.le_logHi (q := (b : ℚ) + 1) (by positivity)
    push_cast at this
    exact (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n + 1 ≤ b + 1))).trans this
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hcM : cM = 571 / 1000 := by unfold cM; norm_num
  have hb1 : 3 * cM / Real.sqrt n ≤ 3 * (571 / 1000) / LogCert.sqrtLo a := by
    rw [hcM]; gcongr; linarith
  have hb2 : Real.log n / n ≤ LogCert.logHi b / a := by
    gcongr
    linarith
  have hpos : 0 ≤ 3 * cM / Real.sqrt n + Real.log n / n := by unfold cM; positivity
  calc |msum n| * Real.log (n + 1) ≤ (3 * cM / Real.sqrt n + Real.log n / n) * Real.log (n + 1) :=
        mul_le_mul_of_nonneg_right hm hlog1
    _ ≤ (3 * (571 / 1000) / LogCert.sqrtLo a + LogCert.logHi b / a) *
          LogCert.logHi ((b : ℚ) + 1) := by
        apply mul_le_mul (by linarith) hlb1 hlog1
        have : (0 : ℝ) ≤ (LogCert.logHi b : ℝ) := le_trans hlog0 hlb
        positivity
    _ ≤ 0.03 := by rw [mul_comm]; norm_num at hchk' ⊢; linarith

/-- Lemma 7(c): `|m(n)| log(n + 1) ≤ 0.03` for `6·10⁵ < n < 10⁹`. -/
theorem range2 (h : Inputs) {n : ℕ} (h1 : 6 * 10 ^ 5 < n) (h2 : n < X0) :
    |msum n| * Real.log (n + 1) ≤ 0.03 := by
  have hX : n ≤ X0 := h2.le
  by_cases ha : n ≤ 679297
  · exact r2ok_sound h r2_1 (by omega) ha (by omega) hX
  by_cases hb : n ≤ 1605044
  · exact r2ok_sound h r2_2 (by omega) hb (by omega) hX
  · exact r2ok_sound h r2_3 (by omega) (by unfold X0 at hX; omega) (by omega) hX

end TernaryGoldbach.RSBounds.Moebius003
