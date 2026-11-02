import TernaryGoldbach.MinorArcs.LSQuot5

/-!
# [H, Prop 12.2.4]

For `Q ≥ 20000 Q₀`, `Q₀ ≥ 10⁵`, `log Q₀ ≤ 0.6 log Q`, `1 ≤ q ≤ Q₀`, `1 ≤ s ≤ Q₀/q`:
`G_q(Q₀/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E) · G_q(Q/sq)`.

With `R = Q₀/sq`: `R ≥ λ(q)` by (12.12) (`regionL`); otherwise, for `q ≥ 2.2·10¹⁰` by
`regionS` with `large_q_hS`, and for `q < 2.2·10¹⁰` by the finite check `prop1224_check`
(`regionS` or `checkC_suffices`).
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem hcc_large {q : ℕ} (hq : 22000000000 ≤ q) :
    Real.exp Real.eulerMascheroniConstant * Real.log 1.03 +
      2.50637 / Real.log (Real.log q) ≤ 0.86 := by
  have hq' : (22000000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 23.8143 ≤ Real.log q := log_Q1_ge.trans (Real.log_le_log (by norm_num) hq')
  have h1 : Real.log 1.03 ≤ 0.03 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.03); linarith
  have h0 : 0 ≤ Real.log 1.03 := Real.log_nonneg (by norm_num)
  have hγ := exp_gamma_le_sharp
  have hll : 3.16 ≤ Real.log (Real.log q) := by
    have h := le_log_num (z := 23.8143) 3 0.16 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at h
    have := Real.log_le_log (by norm_num) hlq
    linarith
  have h2 : 2.50637 / Real.log (Real.log q) ≤ 2.50637 / 3.16 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hll
  have h3 : Real.exp Real.eulerMascheroniConstant * Real.log 1.03 ≤ 1.7882 * 0.03 :=
    mul_le_mul hγ h1 h0 (by norm_num)
  have : (1.7882 : ℝ) * 0.03 + 2.50637 / 3.16 ≤ 0.86 := by norm_num
  linarith

theorem hcc_small {q : ℕ} (hq : 8.53 ≤ Real.log q) :
    Real.exp Real.eulerMascheroniConstant * Real.log 0.826 +
      2.50637 / Real.log (Real.log q) ≤ 0.86 := by
  have h1 : Real.log 0.826 ≤ -0.191 := by
    have h := le_log_num (z := 1 / 0.826) 0 0.191 (by norm_num) (by norm_num)
      (by unfold taylor6; norm_num)
    rw [one_div, Real.log_inv] at h
    push_cast at h; linarith
  have hγ := TernaryGoldbach.Prelim.exp_gamma_ge
  have hll : 2.1435 ≤ Real.log (Real.log q) := by
    have h := le_log_num (z := 8.53) 2 0.1435 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at h
    have := Real.log_le_log (by norm_num) hq
    linarith
  have h2 : 2.50637 / Real.log (Real.log q) ≤ 2.50637 / 2.1435 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hll
  have h3 : Real.exp Real.eulerMascheroniConstant * Real.log 0.826 ≤ 1.625 * (-0.191) := by
    nlinarith
  have : (1.625 : ℝ) * (-0.191) + 2.50637 / 2.1435 ≤ 0.86 := by norm_num
  linarith

/-- **[H, Prop 12.2.4]**. -/
theorem prop_12_2_4 {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) (_hqQ : (q : ℝ) ≤ Q₀) {s : ℝ}
    (hs : 1 ≤ s) (hsQ : s ≤ Q₀ / q) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hR : 1 ≤ Q₀ / (s * q) := by
    rw [le_div_iff₀ hsq, one_mul]; rw [le_div_iff₀ hq0] at hsQ; exact hsQ
  set R := Q₀ / (s * q) with hRdef
  have hR0 : 0 < R := by linarith
  rcases le_or_gt (lamQ q) R with hL | hL
  · exact regionL hQ hQ₀ hρ hq hs hR hL
  rcases le_or_gt 22000000000 q with hbig | hsmall
  · have hq' : (22000000000 : ℝ) ≤ q := by exact_mod_cast hbig
    have hlq : 3 ≤ Real.log q := by
      have := log_Q1_ge.trans (Real.log_le_log (by norm_num) hq'); linarith
    exact regionS hQ hQ₀ hρ hq hs hR (by norm_num) hlq (hcc_large hbig) (large_q_hS hbig hR hL)
  · set n := ⌊R⌋₊
    have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hR)
    have hnR : (n : ℝ) ≤ R := Nat.floor_le hR0.le
    have hRn : R < (n : ℝ) + 1 := Nat.lt_floor_add_one R
    rcases prop1224_check q hq hsmall n hn1 (lt_of_le_of_lt hnR hL) with ⟨hlq, hS⟩ | hC
    · have hh : Real.log q + 1.039 * R ≤ 0.826 * ((q : ℝ) * R) ^ ((2 : ℝ) / 9) := by
        have h1 : ((q : ℝ) * n) ^ ((2 : ℝ) / 9) ≤ ((q : ℝ) * R) ^ ((2 : ℝ) / 9) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hnR hq0.le) (by norm_num)
        nlinarith
      exact regionS hQ hQ₀ hρ hq hs hR (by norm_num) (by linarith) (hcc_small hlq) hh
    · exact checkC_suffices hQ hQ₀ hρ hq hs hR hC

end TernaryGoldbach.MinorArcs
