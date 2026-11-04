import TernaryGoldbach.MinorArcs.LSQuot9

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# [H, Prop 12.2.4]

For `Q ≥ 20000 Q₀`, `Q₀ ≥ 10⁵`, `log Q₀ ≤ 0.6 log Q`, `1 ≤ q ≤ Q₀`, `1 ≤ s ≤ Q₀/q`:
`G_q(Q₀/sq) ≤ (log Q₀ + 2)/(log Q + c_E) · G_q(Q/sq)`.

With `c₊ = 2` in place of [H]'s `1.36`. For `q ≥ 2.2·10¹⁰`, [H]'s argument gives the bound with
`1.36`: `R ≥ λ(q)` by (12.12) (`regionL`), otherwise `regionS` with `large_q_hS`. For
`q < 2.2·10¹⁰` and `R ∈ [n, n+1)`: `n ≤ 3` by `Phi2_small`, `n ≥ 4` by removing the primes `> 13`
from `q` (`Phi2_reduce`) and the kernel checks for the divisors of `30030` (`Phi2_base`).
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

/-- `(l + 1.36)/(L + c_E) ≤ (l + 2)/(L + c_E)`. -/
theorem weaken_136 {G G' l L : ℝ} (hG' : 0 ≤ G') (hL : 0 < L + cE)
    (h : G ≤ (l + 1.36) / (L + cE) * G') : G ≤ (l + 2) / (L + cE) * G' := by
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hG')
  exact div_le_div_of_nonneg_right (by linarith) hL.le

/-- **[H, Prop 12.2.4] with `c₊ = 2`** (for [H]'s `1.36`). -/
theorem prop_12_2_4 {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) (_hqQ : (q : ℝ) ≤ Q₀) {s : ℝ}
    (hs : 1 ≤ s) (hsQ : s ≤ Q₀ / q) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 2) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hR : 1 ≤ Q₀ / (s * q) := by
    rw [le_div_iff₀ hsq, one_mul]; rw [le_div_iff₀ hq0] at hsQ; exact hsQ
  have hLQ : 0 < Real.log Q + cE := by
    have : 0 < Real.log Q := Real.log_pos (by linarith)
    unfold cE; linarith
  have hG' := Gq_nonneg_q q (Q / (s * q))
  set R := Q₀ / (s * q) with hRdef
  rcases le_or_gt 22000000000 q with hbig | hsmall
  · -- large `q`: [H]'s argument, with `1.36`
    refine weaken_136 hG' hLQ ?_
    rcases le_or_gt (lamQ q) R with hL | hL
    · exact regionL hQ hQ₀ hρ hq hs hR hL
    have hq' : (22000000000 : ℝ) ≤ q := by exact_mod_cast hbig
    have hlq : 3 ≤ Real.log q := by
      have := log_Q1_ge.trans (Real.log_le_log (by norm_num) hq'); linarith
    exact regionS hQ hQ₀ hρ hq hs hR (by norm_num) hlq (hcc_large hbig) (large_q_hS hbig hR hL)
  · -- `q < 2.2·10¹⁰`: the reduction to `Φ`
    refine checkC2_suffices hQ hQ₀ hρ hq hs hR ?_
    set n := ⌊R⌋₊
    have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hR)
    rcases le_or_gt n 3 with hn3 | hn4
    · exact Phi2_small hq hsmall hn1 hn3
    · have h := Phi2_reduce hn1 (fun A hA => Phi2_base hA (by omega)) q hq hsmall
      exact (Phi2_anti q n (le_max_left _ _)).trans h

end TernaryGoldbach.MinorArcs
