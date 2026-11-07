import TernaryGoldbach.Explicit.WeilNumB
import TernaryGoldbach.Prelim.SmallMertens

/-!
# The Weil-window bound in numbers

Parameters `ℓ = 0.173`, `m = 2`, `N = 20`, `R = 13`, grids `n_A = 8`, `r = 5/4`, `n_B = 20`
(`U = 2.39 · 1.25²⁰ ≈ 207.3`). Constants: `p0 ≤ 0.24567`, `kap1 ≤ 0.16385`, `kap0 ≤ −0.23516`.
The Riemann sums of regions A and B are rational computations with certified logarithms
(`x ≤ e_lo^a T₁₂(f)` gives `log x ≤ a + f`), checked by the kernel (`decide +kernel`, no
`native_decide`). Result (`line_sum_numH`): given `RHBelow H` with `10⁸ ≤ H ≤ 3·10¹⁰`, for
`3/Y₁ ≤ δ ≤ 1/208` (`Y₁ + 13 ≤ H/2`), with `L = log(1/δ)`,
`Σ_{|γ| ≤ H} m_ρ ‖Mg(ρ)‖ ≤ e^{δ²/8}(e^{a/2} + e^{b/2}) (JW(δ) + e^{−δ²Y₁²/2} LWH(H))`,
`JW(δ) = 0.16385 L² − 0.4271 L + 7.2032 + 57.73 δ`. (`scripts/weil_chain.py`, `weil_numbers.py`,
`cert_tables.py`.)
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval
open TernaryGoldbach.Prelim.Small (T12 ELpow T12_le_exp ELpow_le EHpow T12up exp_le_T12up EHpow_ge)

namespace TernaryGoldbach.Explicit

/-! ### Certificates for `log` and `exp` -/

theorem T12_nonneg {f : ℚ} (hf : 0 ≤ f) : (0 : ℝ) ≤ ((T12 f : ℚ) : ℝ) := by
  unfold T12; push_cast; positivity

theorem exp_ge_cert (a : ℕ) {f : ℚ} (hf : 0 ≤ f) :
    ((ELpow a : ℚ) : ℝ) * ((T12 f : ℚ) : ℝ) ≤ Real.exp ((a : ℝ) + (f : ℝ)) := by
  rw [Real.exp_add]
  exact mul_le_mul (ELpow_le a) (T12_le_exp hf) (T12_nonneg hf) (Real.exp_pos _).le

theorem exp_le_cert (a : ℕ) {f : ℚ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Real.exp ((a : ℝ) + (f : ℝ)) ≤ ((EHpow a : ℚ) : ℝ) * ((T12up f : ℚ) : ℝ) := by
  rw [Real.exp_add]
  exact mul_le_mul (EHpow_ge a) (exp_le_T12up hf0 hf1) (Real.exp_pos _).le
    ((Real.exp_pos _).le.trans (EHpow_ge a))

theorem log_le_cert {x : ℝ} (q : ℚ) (hxq : x = q) (hq : 0 < q) (a : ℕ) (f : ℚ) (hf : 0 ≤ f)
    (h : q ≤ ELpow a * T12 f) : Real.log x ≤ (a : ℝ) + (f : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [hxq, Real.log_le_iff_le_exp hq']
  have h' : ((q : ℚ) : ℝ) ≤ ((ELpow a : ℚ) : ℝ) * ((T12 f : ℚ) : ℝ) := by exact_mod_cast h
  exact h'.trans (exp_ge_cert a hf)

theorem le_log_cert {x : ℝ} (q : ℚ) (hxq : x = q) (a : ℕ) (f : ℚ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (h : EHpow a * T12up f ≤ q) : (a : ℝ) + (f : ℝ) ≤ Real.log x := by
  have h' : ((EHpow a : ℚ) : ℝ) * ((T12up f : ℚ) : ℝ) ≤ ((q : ℚ) : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) ((exp_le_cert a hf0 hf1).trans h')
  rw [hxq, Real.le_log_iff_exp_le hpos]
  exact (exp_le_cert a hf0 hf1).trans h'

/-- `e^{−(a+f)} ≤ u` from `1 ≤ u e_lo^a T₁₂(f)`. -/
theorem exp_neg_le_cert (a : ℕ) (f u : ℚ) (hf : 0 ≤ f) (h : 1 ≤ u * (ELpow a * T12 f)) :
    Real.exp (-((a : ℝ) + (f : ℝ))) ≤ u := by
  have h' : (1 : ℝ) ≤ (u : ℝ) * (((ELpow a : ℚ) : ℝ) * ((T12 f : ℚ) : ℝ)) := by exact_mod_cast h
  have hE := exp_ge_cert a hf
  have hu : 0 ≤ (u : ℝ) := by
    by_contra hneg; push Not at hneg
    have : (u : ℝ) * (((ELpow a : ℚ) : ℝ) * ((T12 f : ℚ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (mul_nonneg (by unfold ELpow; push_cast; positivity) (T12_nonneg hf))
    linarith
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  calc (1 : ℝ) ≤ (u : ℝ) * (((ELpow a : ℚ) : ℝ) * ((T12 f : ℚ) : ℝ)) := h'
    _ ≤ (u : ℝ) * Real.exp ((a : ℝ) + (f : ℝ)) := mul_le_mul_of_nonneg_left hE hu
    _ = _ := by ring

/-- `v ≤ e^{−(a+f)}` from `v e_hi^a T₁₂⁺(f) ≤ 1`. -/
theorem le_exp_neg_cert (a : ℕ) (f v : ℚ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (h : v * (EHpow a * T12up f) ≤ 1) :
    (v : ℝ) ≤ Real.exp (-((a : ℝ) + (f : ℝ))) := by
  have h' : (v : ℝ) * (((EHpow a : ℚ) : ℝ) * ((T12up f : ℚ) : ℝ)) ≤ 1 := by exact_mod_cast h
  have hE := exp_le_cert a hf0 hf1
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  rcases le_or_gt (v : ℝ) 0 with hv | hv
  · nlinarith [Real.exp_pos ((a : ℝ) + (f : ℝ))]
  · calc (v : ℝ) * Real.exp ((a : ℝ) + (f : ℝ)) ≤ (v : ℝ) * (((EHpow a : ℚ) : ℝ) * ((T12up f : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hE hv.le
      _ ≤ 1 := h'

/-! ### The atoms -/

theorem log_five_fourths_le : Real.log (5 / 4) ≤ 0.223145 := by
  have := log_le_cert (x := 5 / 4) (5 / 4) (by norm_num) (by norm_num) 0 (44629 / 200000) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_five_fourths_nonneg : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num)

theorem log_three_halves_le : Real.log (3 / 2) ≤ 0.405467 := by
  have := log_le_cert (x := 3 / 2) (3 / 2) (by norm_num) (by norm_num) 0 (405467 / 1000000) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_three_le' : Real.log 3 ≤ 1.098614 := by
  have := log_le_cert (x := 3) 3 (by norm_num) (by norm_num) 1 (49307 / 500000) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_81_77_le : Real.log (81 / 77) ≤ 0.050645 := by
  have := log_le_cert (x := 81 / 77) (81 / 77) (by norm_num) (by norm_num) 0 (10129 / 200000) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_81_4_le : Real.log (81 / 4) ≤ 3.008156 := by
  have := log_le_cert (x := 81 / 4) (81 / 4) (by norm_num) (by norm_num) 3 (2039 / 250000) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_13_ge : 2.564948 ≤ Real.log 13 := by
  have := le_log_cert (x := 13) 13 (by norm_num) 2 (141237 / 250000) (by norm_num) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_pi_ge' : 1.144728 ≤ Real.log π := by
  have h := le_log_cert (x := 3.141592) (392699 / 125000) (by norm_num) 1 (18091 / 125000) (by norm_num)
    (by norm_num) (by decide +kernel)
  have h2 : Real.log 3.141592 ≤ Real.log π := Real.log_le_log (by norm_num) Real.pi_gt_d6.le
  norm_num at h ⊢; linarith

/-- `U = 2.39 · 1.25²⁰`. -/
theorem U_eq : (2.39 : ℝ) * 1.25 ^ 20 = ((911712646484375 / 4398046511104 : ℚ) : ℝ) := by norm_num

theorem log_U_ge : 5.334163 ≤ Real.log (2.39 * 1.25 ^ 20) := by
  have := le_log_cert (x := 2.39 * 1.25 ^ 20) (911712646484375 / 4398046511104) U_eq 5 (334163 / 1000000)
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at this ⊢; linarith

theorem log_U_le : Real.log (2.39 * 1.25 ^ 20) ≤ 5.334166 := by
  have := log_le_cert (x := 2.39 * 1.25 ^ 20) (911712646484375 / 4398046511104) U_eq (by norm_num) 5
    (167083 / 500000) (by norm_num) (by decide +kernel)
  norm_num at this ⊢; linarith

theorem exp_346_le : Real.exp (2 * 0.173) ≤ ((T12up (173 / 500) : ℚ) : ℝ) := by
  have := exp_le_cert 0 (f := 173 / 500) (by norm_num) (by norm_num)
  norm_num [EHpow] at this ⊢; exact this

/-! ### The constants `p0`, `kap1`, `kap0` -/

def kBq : ℚ := 469746497818104801491777112091 / 40824000000000000000000000000

theorem kB_val : kB 0.173 13 = ((kBq : ℚ) : ℝ) := by unfold kB kBq; norm_num

theorem kB_pos : 0 < kB 0.173 13 := by rw [kB_val]; unfold kBq; norm_num

theorem K0_val : K0 0.173 13 = (2 * 0.173) ^ 4 * ((kBq : ℚ) : ℝ) := by unfold K0; rw [kB_val]

theorem p0_le : p0 0.173 13 ≤ 0.24567 := by
  have hq : 2 * T12up (173 / 500) / kBq ≤ 24567 / 100000 := by unfold kBq; decide +kernel
  have hq' : (2 : ℝ) * ((T12up (173 / 500) : ℚ) : ℝ) / ((kBq : ℚ) : ℝ) ≤ 0.24567 := by
    have := (Rat.cast_le (K := ℝ)).2 hq; push_cast at this; norm_num at this ⊢; exact this
  unfold p0; rw [kB_val]
  have hk : (0 : ℝ) < ((kBq : ℚ) : ℝ) := by unfold kBq; norm_num
  calc 2 * Real.exp (2 * 0.173) / ((kBq : ℚ) : ℝ) ≤ 2 * ((T12up (173 / 500) : ℚ) : ℝ) / ((kBq : ℚ) : ℝ) := by
        gcongr; exact exp_346_le
    _ ≤ 0.24567 := hq'

theorem kap1_le : kap1 0.173 13 ≤ 0.16385 := by
  unfold kap1
  rw [I0_two (by norm_num), K0_val]
  have hpi := Real.pi_gt_d6
  have hnum : (0 : ℝ) ≤ 1 + 32 / (3 * 13 ^ 3) / ((2 * 0.173) ^ 4 * ((kBq : ℚ) : ℝ)) := by
    unfold kBq; norm_num
  calc (1 + 32 / (3 * 13 ^ 3) / ((2 * 0.173) ^ 4 * ((kBq : ℚ) : ℝ))) / (2 * π) ≤
      (1 + 32 / (3 * 13 ^ 3) / ((2 * 0.173) ^ 4 * ((kBq : ℚ) : ℝ))) / (2 * 3.141592) := by
        gcongr
    _ ≤ 0.16385 := by unfold kBq; norm_num

theorem rpow_13_le : (13 : ℝ) ^ (-(5 / 2) : ℝ) ≤ 0.0016412 := by
  have hs : (3.6055 : ℝ) ≤ √13 := Real.le_sqrt_of_sq_le (by norm_num)
  have e : (13 : ℝ) ^ (-(5 / 2) : ℝ) = 1 / (169 * √13) := by
    rw [Real.rpow_neg (by norm_num), show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_two, ← Real.sqrt_eq_rpow]
    norm_num
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

theorem kap0_le : kap0 0.173 20 13 ≤ -0.23516 := by
  unfold kap0 cN OffC
  rw [I0_two (by norm_num), I1_two (by norm_num), K0_val]
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hl2 := Real.log_two_gt_d9
  have hlpi := log_pi_ge'
  have hl81 := log_81_77_le
  have hl4 := log_81_4_le
  have hr13 := rpow_13_le
  have he := exp_346_le
  have e1 : ((20 : ℕ) : ℝ) + 1 / 4 = 81 / 4 := by norm_num
  have e2 : (((20 : ℕ) : ℝ) + 1 / 4) / (((20 : ℕ) : ℝ) - 3 / 4) = 81 / 77 := by norm_num
  rw [e2, e1]
  have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) Real.pi_pos.ne'
  rw [hlog2pi]
  set K := (2 * 0.173 : ℝ) ^ 4 * ((kBq : ℚ) : ℝ) with hK
  have hKv : K = (2 * 0.173 : ℝ) ^ 4 * ((kBq : ℚ) : ℝ) := hK
  have hK1 : (0.164912 : ℝ) ≤ K := by rw [hKv]; unfold kBq; norm_num
  have hK0 : 0 < K := by linarith
  have hT : ((T12up (173 / 500) : ℚ) : ℝ) ≤ 1.4135 := by
    have : T12up (173 / 500) ≤ 14135 / 10000 := by decide +kernel
    have := (Rat.cast_le (K := ℝ)).2 this; norm_num at this ⊢; exact this
  -- the bracket
  set B := -(1 / 2) * (Real.log 2 + Real.log π) + 1 / 2 * Real.log (81 / 77) +
    (1 / 2 * (Real.log (81 / 4) - Real.log π) * (32 / (3 * 13 ^ 3)) + 12.8 * 13 ^ (-(5 / 2) : ℝ)) / K with hB
  have hc : 1 / 2 * (Real.log (81 / 4) - Real.log π) ≤ 0.931714 := by linarith
  have hnum : 1 / 2 * (Real.log (81 / 4) - Real.log π) * (32 / (3 * 13 ^ 3)) + 12.8 * 13 ^ (-(5 / 2) : ℝ) ≤
      0.931714 * (32 / (3 * 13 ^ 3)) + 12.8 * 0.0016412 := by
    have := mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 32 / (3 * 13 ^ 3))
    linarith
  have hnum0 : 0 ≤ 0.931714 * (32 / (3 * 13 ^ 3)) + 12.8 * (0.0016412 : ℝ) := by norm_num
  have hfrac : (1 / 2 * (Real.log (81 / 4) - Real.log π) * (32 / (3 * 13 ^ 3)) + 12.8 * 13 ^ (-(5 / 2) : ℝ)) / K ≤
      (0.931714 * (32 / (3 * 13 ^ 3)) + 12.8 * 0.0016412) / 0.164912 :=
    (div_le_div_of_nonneg_right hnum hK0.le).trans (div_le_div_of_nonneg_left hnum0 (by norm_num) hK1)
  have hBle : B ≤ -0.738799 := by rw [hB]; norm_num at hfrac ⊢; linarith
  have hB1 : 1 / π * B ≤ 1 / 3.141593 * (-0.738799) := by
    have h1 : 1 / π * B ≤ 1 / π * (-0.738799) := mul_le_mul_of_nonneg_left hBle (by positivity)
    have h2 : 1 / π * (-0.738799 : ℝ) ≤ 1 / 3.141593 * (-0.738799) := by
      rw [mul_comm, mul_comm (1 / 3.141593 : ℝ)]
      exact mul_le_mul_of_nonpos_left (one_div_le_one_div_of_le Real.pi_pos hpi2.le) (by norm_num)
    linarith
  have hoff : (4 : ℝ) ^ 2 * Real.exp (↑(2 : ℕ) * 0.173) * 1e-15 / K ≤ 1e-12 := by
    rw [div_le_iff₀ hK0]
    have : Real.exp (↑(2 : ℕ) * 0.173) ≤ 1.4135 := by push_cast; linarith
    nlinarith
  linarith

theorem kap_pos : 0 ≤ (-0.23516 : ℝ) + 0.16385 * Real.log 13 := by
  have := log_13_ge; nlinarith

theorem exp_692_lt : Real.exp (2 * (2 : ℕ) * 0.173) < 2 := by
  have h := Real.log_two_gt_d9
  have : (2 * (2 : ℕ) * 0.173 : ℝ) < Real.log 2 := by push_cast; linarith
  calc Real.exp (2 * (2 : ℕ) * 0.173) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 this
    _ = 2 := Real.exp_log (by norm_num)

/-! ### Regions A and B: certified Riemann sums -/

def lq : ℚ := 173 / 1000
def P0q : ℚ := 24567 / 100000
def K1q : ℚ := 16385 / 100000
def K0q : ℚ := -23516 / 100000
def PIlo : ℚ := 3141592 / 1000000
def smallQ (y : ℚ) : ℚ := (1 / (2 * y) + 1 / (16 * y ^ 2)) / PIlo
def yQ (t : List (ℕ × ℚ)) (k : ℕ) : ℚ := ((t.getD k (0, 0)).1 : ℚ) + (t.getD k (0, 0)).2

def hAq : ℚ := 1539 / 800
def tabA : List (ℕ × ℚ) := [(2, 140591 / 200000), (2, 206051 / 250000), (2, 116541 / 125000), (3, 14947 / 500000), (3, 118781 / 1000000), (3, 25051 / 125000), (3, 8621 / 31250), (3, 173019 / 500000)]
def termAq (k : ℕ) : ℚ :=
  (P0q / (max 1 (lq * (k * hAq))) ^ 4 + K1q * yQ tabA k + K0q + smallQ (k * hAq + 13)) / (239 / 100) * hAq

theorem tabA_logs : ∀ k ∈ List.range 8,
    ((k : ℚ) + 1) * hAq + 13 ≤ ELpow (tabA.getD k (0, 0)).1 * T12 (tabA.getD k (0, 0)).2 := by
  decide +kernel
theorem tabA_f : ∀ k ∈ List.range 8, 0 ≤ (tabA.getD k (0, 0)).2 := by decide +kernel
theorem sumA_le : ∑ k ∈ range 8, termAq k ≤ 26618 / 10000 := by decide +kernel

def aBq (k : ℕ) : ℚ := 13 + 239 / 100 * (5 / 4) ^ k
def LRq : ℚ := 44629 / 200000
def tabB : List (ℕ × ℚ) := [(3, 183433 / 500000), (3, 78461 / 200000), (3, 21161 / 50000), (3, 460567 / 1000000), (3, 50537 / 100000), (3, 55869 / 100000), (3, 77697 / 125000), (3, 139 / 200), (3, 779793 / 1000000), (3, 27393 / 31250), (3, 985707 / 1000000), (4, 107247 / 1000000), (4, 30119 / 125000), (4, 193149 / 500000), (4, 542529 / 1000000), (4, 708719 / 1000000), (4, 883843 / 1000000), (5, 33419 / 500000), (5, 256661 / 1000000), (5, 113081 / 250000)]
def termBq (k : ℕ) : ℚ :=
  (P0q / (max 1 (lq * aBq k)) ^ 4 + K1q * yQ tabB k + K0q + smallQ (aBq k + 13)) * LRq

theorem tabB_logs : ∀ k ∈ List.range 20,
    aBq (k + 1) + 13 ≤ ELpow (tabB.getD k (0, 0)).1 * T12 (tabB.getD k (0, 0)).2 := by
  decide +kernel
theorem tabB_f : ∀ k ∈ List.range 20, 0 ≤ (tabB.getD k (0, 0)).2 := by decide +kernel
theorem sumB_le : ∑ k ∈ range 20, termBq k ≤ 198 / 100 := by decide +kernel

theorem cast_lq : (0.173 : ℝ) = ((lq : ℚ) : ℝ) := by unfold lq; norm_num
theorem cast_P0q : (0.24567 : ℝ) = ((P0q : ℚ) : ℝ) := by unfold P0q; norm_num
theorem cast_K1q : (0.16385 : ℝ) = ((K1q : ℚ) : ℝ) := by unfold K1q; norm_num
theorem cast_K0q : (-0.23516 : ℝ) = ((K0q : ℚ) : ℝ) := by unfold K0q; norm_num

theorem inv_pi_le : 1 / π ≤ 1 / ((PIlo : ℚ) : ℝ) :=
  one_div_le_one_div_of_le (by unfold PIlo; norm_num) (by
    have := Real.pi_gt_d6; unfold PIlo; push_cast; norm_num at this ⊢; linarith)

theorem kap_pos_q : 0 ≤ ((K0q : ℚ) : ℝ) + ((K1q : ℚ) : ℝ) * Real.log 13 := by
  rw [← cast_K0q, ← cast_K1q]; exact kap_pos

theorem RegA_le : RegA 0.173 0.24567 0.16385 (-0.23516) 13 8 ≤ 2.6618 := by
  have eh : ((13 : ℝ) + 2.39) / ((8 : ℕ) : ℝ) = ((hAq : ℚ) : ℝ) := by unfold hAq; norm_num
  unfold RegA
  rw [eh, cast_lq, cast_P0q, cast_K1q, cast_K0q]
  have hK1 : (0 : ℝ) ≤ ((K1q : ℚ) : ℝ) := by unfold K1q; norm_num
  have hh : (0 : ℝ) < ((hAq : ℚ) : ℝ) := by unfold hAq; norm_num
  have key : ∀ k ∈ range 8, PsiBarG ((lq : ℚ) : ℝ) ((P0q : ℚ) : ℝ) ((K1q : ℚ) : ℝ) ((K0q : ℚ) : ℝ) 13
      ((k : ℝ) * ((hAq : ℚ) : ℝ)) (((k : ℝ) + 1) * ((hAq : ℚ) : ℝ)) / 2.39 * ((hAq : ℚ) : ℝ) ≤
      ((termAq k : ℚ) : ℝ) := by
    intro k hk
    have hk' : k ∈ List.range 8 := List.mem_range.2 (Finset.mem_range.1 hk)
    have hlog : Real.log (((k : ℝ) + 1) * ((hAq : ℚ) : ℝ) + 13) ≤ ((yQ tabA k : ℚ) : ℝ) := by
      have := log_le_cert (x := ((k : ℝ) + 1) * ((hAq : ℚ) : ℝ) + 13) (((k : ℚ) + 1) * hAq + 13)
        (by push_cast; ring) (by unfold hAq; positivity) _ _ (tabA_f k hk') (tabA_logs k hk')
      unfold yQ; push_cast; exact this
    have hS : (0 : ℝ) ≤ 1 / (2 * ((k : ℝ) * ((hAq : ℚ) : ℝ) + 13)) +
        1 / (16 * ((k : ℝ) * ((hAq : ℚ) : ℝ) + 13) ^ 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) * ((hAq : ℚ) : ℝ) := by positivity
      positivity
    calc _ ≤ (((P0q : ℚ) : ℝ) / max 1 (((lq : ℚ) : ℝ) * ((k : ℝ) * ((hAq : ℚ) : ℝ))) ^ 4 +
          ((K1q : ℚ) : ℝ) * ((yQ tabA k : ℚ) : ℝ) + ((K0q : ℚ) : ℝ) +
          1 / ((PIlo : ℚ) : ℝ) * (1 / (2 * ((k : ℝ) * ((hAq : ℚ) : ℝ) + 13)) +
            1 / (16 * ((k : ℝ) * ((hAq : ℚ) : ℝ) + 13) ^ 2))) / 2.39 * ((hAq : ℚ) : ℝ) := by
          unfold PsiBarG smallT
          have h1 := mul_le_mul_of_nonneg_left hlog hK1
          have h2 := mul_le_mul_of_nonneg_right inv_pi_le hS
          gcongr ?_ / _ * _
          linarith
      _ = ((termAq k : ℚ) : ℝ) := by unfold termAq smallQ; push_cast; ring
  calc _ ≤ ∑ k ∈ range 8, ((termAq k : ℚ) : ℝ) := Finset.sum_le_sum key
    _ = ((∑ k ∈ range 8, termAq k : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ 2.6618 := by have := (Rat.cast_le (K := ℝ)).2 sumA_le; norm_num at this ⊢; exact this

theorem RegB_le : RegB 0.173 0.24567 0.16385 (-0.23516) 13 1.25 20 ≤ 1.98 := by
  have er : (1.25 : ℝ) = (((5 / 4 : ℚ) : ℚ) : ℝ) := by norm_num
  have e239 : (2.39 : ℝ) = (((239 / 100 : ℚ) : ℚ) : ℝ) := by norm_num
  unfold RegB
  rw [cast_lq, cast_P0q, cast_K1q, cast_K0q]
  have hK1 : (0 : ℝ) ≤ ((K1q : ℚ) : ℝ) := by unfold K1q; norm_num
  have hP0 : (0 : ℝ) ≤ ((P0q : ℚ) : ℝ) := by unfold P0q; norm_num
  have haB : ∀ k : ℕ, (13 : ℝ) + 2.39 * 1.25 ^ k = ((aBq k : ℚ) : ℝ) := fun k => by
    unfold aBq; push_cast; norm_num
  have key : ∀ k ∈ range 20, PsiBarG ((lq : ℚ) : ℝ) ((P0q : ℚ) : ℝ) ((K1q : ℚ) : ℝ) ((K0q : ℚ) : ℝ) 13
      (13 + 2.39 * 1.25 ^ k) (13 + 2.39 * 1.25 ^ (k + 1)) * Real.log 1.25 ≤ ((termBq k : ℚ) : ℝ) := by
    intro k hk
    have hk' : k ∈ List.range 20 := List.mem_range.2 (Finset.mem_range.1 hk)
    rw [haB k, haB (k + 1)]
    have ha0 : (0 : ℝ) ≤ ((aBq k : ℚ) : ℝ) := by rw [← haB k]; positivity
    have hlog : Real.log (((aBq (k + 1) : ℚ) : ℝ) + 13) ≤ ((yQ tabB k : ℚ) : ℝ) := by
      have := log_le_cert (x := ((aBq (k + 1) : ℚ) : ℝ) + 13) (aBq (k + 1) + 13)
        (by push_cast; ring) (by unfold aBq; positivity) _ _ (tabB_f k hk') (tabB_logs k hk')
      unfold yQ; push_cast; exact this
    have hS : (0 : ℝ) ≤ 1 / (2 * (((aBq k : ℚ) : ℝ) + 13)) + 1 / (16 * (((aBq k : ℚ) : ℝ) + 13) ^ 2) := by
      positivity
    set Pb := ((P0q : ℚ) : ℝ) / max 1 (((lq : ℚ) : ℝ) * ((aBq k : ℚ) : ℝ)) ^ 4 +
          ((K1q : ℚ) : ℝ) * ((yQ tabB k : ℚ) : ℝ) + ((K0q : ℚ) : ℝ) +
          1 / ((PIlo : ℚ) : ℝ) * (1 / (2 * (((aBq k : ℚ) : ℝ) + 13)) + 1 / (16 * (((aBq k : ℚ) : ℝ) + 13) ^ 2))
      with hPb
    have hle : PsiBarG ((lq : ℚ) : ℝ) ((P0q : ℚ) : ℝ) ((K1q : ℚ) : ℝ) ((K0q : ℚ) : ℝ) 13
        ((aBq k : ℚ) : ℝ) ((aBq (k + 1) : ℚ) : ℝ) ≤ Pb := by
      unfold PsiBarG smallT
      have h1 := mul_le_mul_of_nonneg_left hlog hK1
      have h2 := mul_le_mul_of_nonneg_right inv_pi_le hS
      rw [hPb]; linarith
    have hnn := PsiBarG_nonneg (ℓ := ((lq : ℚ) : ℝ)) (R := 13) (by norm_num) hP0 hK1 kap_pos_q
      (a := ((aBq k : ℚ) : ℝ)) (b := ((aBq (k + 1) : ℚ) : ℝ)) ha0 (by rw [← haB (k + 1)]; positivity)
    have hl0 : 0 ≤ Real.log 1.25 := Real.log_nonneg (by norm_num)
    have hlr : Real.log 1.25 ≤ ((LRq : ℚ) : ℝ) := by
      have := log_five_fourths_le; unfold LRq; norm_num at this ⊢; linarith
    calc _ ≤ Pb * Real.log 1.25 := mul_le_mul_of_nonneg_right hle hl0
      _ ≤ Pb * ((LRq : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hlr (hnn.trans hle)
      _ = ((termBq k : ℚ) : ℝ) := by rw [hPb]; unfold termBq smallQ; push_cast; ring
  calc _ ≤ ∑ k ∈ range 20, ((termBq k : ℚ) : ℝ) := Finset.sum_le_sum key
    _ = ((∑ k ∈ range 20, termBq k : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ 1.98 := by have := (Rat.cast_le (K := ℝ)).2 sumB_le; norm_num at this ⊢; exact this

/-! ### The Gaussian constants `E⁺`, `F⁺` -/

theorem e_half_le : Real.exp (-(1 / 2)) ≤ 0.60653066 := by
  have := exp_neg_le_cert 0 (1 / 2) (60653066 / 100000000) (by norm_num) (by decide +kernel)
  norm_num at this ⊢; exact this
theorem e_2532 : 0.45783336 ≤ Real.exp (-(25 / 32)) ∧ Real.exp (-(25 / 32)) ≤ 0.45783337 := by
  have h1 := le_exp_neg_cert 0 (25 / 32) (45783336 / 100000000) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_neg_le_cert 0 (25 / 32) (45783337 / 100000000) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨h1, h2⟩
theorem e_98 : 0.32465246 ≤ Real.exp (-(9 / 8)) ∧ Real.exp (-(9 / 8)) ≤ 0.32465247 := by
  have h1 := le_exp_neg_cert 1 (1 / 8) (32465246 / 100000000) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_neg_le_cert 1 (1 / 8) (32465247 / 100000000) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨h1, h2⟩
theorem e_2 : 0.13533528 ≤ Real.exp (-2) ∧ Real.exp (-2) ≤ 0.13533529 := by
  have h1 := le_exp_neg_cert 2 0 (13533528 / 100000000) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_neg_le_cert 2 0 (13533529 / 100000000) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨h1, h2⟩
theorem e_92 : 0.01110899 ≤ Real.exp (-(9 / 2)) ∧ Real.exp (-(9 / 2)) ≤ 0.011109 := by
  have h1 := le_exp_neg_cert 4 (1 / 2) (1110899 / 100000000) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_neg_le_cert 4 (1 / 2) (1110900 / 100000000) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨h1, h2⟩

theorem EpD_le : EpD ≤ 0.350366 := by
  unfold EpD
  have := e_half_le; have := e_2532; have := e_98; have := e_2; have := e_92
  norm_num at *
  linarith

theorem FpD_le : FpD ≤ 0.16389 := by
  have h1 := e_half_le; have h2 := e_2532; have h3 := e_98; have h4 := e_2; have h5 := e_92
  have l1 := log_five_fourths_le; have l2 := log_three_halves_le
  have l3 := Real.log_two_lt_d9; have l4 := log_three_le'
  have n1 : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num)
  have n2 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have n3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have n4 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have d1 : 0 ≤ Real.exp (-(1 / 2)) - Real.exp (-(25 / 32)) := sub_nonneg.2 (Real.exp_le_exp.2 (by norm_num))
  have d2 : 0 ≤ Real.exp (-(25 / 32)) - Real.exp (-(9 / 8)) := sub_nonneg.2 (Real.exp_le_exp.2 (by norm_num))
  have d3 : 0 ≤ Real.exp (-(9 / 8)) - Real.exp (-2) := sub_nonneg.2 (Real.exp_le_exp.2 (by norm_num))
  have d4 : 0 ≤ Real.exp (-2) - Real.exp (-(9 / 2)) := sub_nonneg.2 (Real.exp_le_exp.2 (by norm_num))
  have p1 := mul_le_mul l1 (show Real.exp (-(1 / 2)) - Real.exp (-(25 / 32)) ≤ 0.60653066 - 0.45783336 by
    linarith [h2.1]) d1 (by norm_num)
  have p2 := mul_le_mul l2 (show Real.exp (-(25 / 32)) - Real.exp (-(9 / 8)) ≤ 0.45783337 - 0.32465246 by
    linarith [h2.2, h3.1]) d2 (by norm_num)
  have p3 := mul_le_mul l3.le (show Real.exp (-(9 / 8)) - Real.exp (-2) ≤ 0.32465247 - 0.13533528 by
    linarith [h3.2, h4.1]) d3 (by norm_num)
  have p4 := mul_le_mul l4 (show Real.exp (-2) - Real.exp (-(9 / 2)) ≤ 0.13533529 - 0.01110899 by
    linarith [h4.2, h5.1]) d4 (by norm_num)
  have e : FpD = Real.log (5 / 4) * (Real.exp (-(1 / 2)) - Real.exp (-(25 / 32))) +
      Real.log (3 / 2) * (Real.exp (-(25 / 32)) - Real.exp (-(9 / 8))) / (25 / 16) +
      Real.log 2 * (Real.exp (-(9 / 8)) - Real.exp (-2)) / (9 / 4) +
      Real.log 3 * (Real.exp (-2) - Real.exp (-(9 / 2))) / 4 + Real.exp (-(9 / 2)) / 3 := by
    unfold FpD; norm_num; ring
  rw [e]
  linarith [h5.2]

/-! ### Regions C and D, and the total -/

theorem PhiC_inv {δ : ℝ} (hδ : 0 < δ) (c₀ κ₁ c₂ : ℝ) :
    PhiC δ c₀ κ₁ c₂ (1 / δ) = κ₁ / 2 * Real.log (1 / δ) ^ 2 + (c₀ - 7 * κ₁ / 32) * Real.log (1 / δ) -
      7 * c₀ / 32 + 15 * κ₁ / 128 - 35 / 24 * c₂ * δ := by
  unfold PhiC; field_simp; ring

theorem PhiC_U_ge {δ U c₀ κ₁ c₂ : ℝ} (hU : 0 < U) (hδ : 0 ≤ δ) (hc2 : 0 ≤ c₂)
    (hX4 : 0 ≤ c₀ / 4 + κ₁ * (Real.log U / 4 - 1 / 16)) :
    c₀ * Real.log U + κ₁ / 2 * Real.log U ^ 2 - (δ * U) ^ 2 / 2 * (c₀ / 2 + κ₁ * (Real.log U / 2 - 1 / 4)) -
      c₂ / U - c₂ * δ ^ 2 * U / 2 ≤ PhiC δ c₀ κ₁ c₂ U := by
  have e : PhiC δ c₀ κ₁ c₂ U - (c₀ * Real.log U + κ₁ / 2 * Real.log U ^ 2 -
      (δ * U) ^ 2 / 2 * (c₀ / 2 + κ₁ * (Real.log U / 2 - 1 / 4)) - c₂ / U - c₂ * δ ^ 2 * U / 2) =
      (δ * U) ^ 4 / 8 * (c₀ / 4 + κ₁ * (Real.log U / 4 - 1 / 16)) + c₂ * δ ^ 4 * U ^ 3 / 24 := by
    unfold PhiC; field_simp; ring
  have : 0 ≤ (δ * U) ^ 4 / 8 * (c₀ / 4 + κ₁ * (Real.log U / 4 - 1 / 16)) + c₂ * δ ^ 4 * U ^ 3 / 24 := by
    positivity
  linarith

/-- The closed-form window bound. -/
noncomputable def JW (δ : ℝ) : ℝ := 0.16385 * Real.log (1 / δ) ^ 2 - 0.4271 * Real.log (1 / δ) + 7.2032 + 57.73 * δ

theorem Jtot_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 208) :
    2 * (RegA 0.173 0.24567 0.16385 (-0.23516) 13 8 + RegB 0.173 0.24567 0.16385 (-0.23516) 13 1.25 20 +
      RegC 0.173 0.24567 0.16385 (-0.23516) 13 (2.39 * 1.25 ^ 20) δ +
      RegD 0.173 0.24567 0.16385 (-0.23516) 13 (2.39 * 1.25 ^ 20) δ) ≤ JW δ := by
  have hA := RegA_le
  have hB := RegB_le
  have hl1 := log_U_ge
  have hl2 := log_U_le
  have hE := EpD_le
  have hF := FpD_le
  have hE0 : 0 ≤ EpD := by
    have := e_half_le; have := e_2532; have := e_98; have := e_2; have := e_92
    unfold EpD; norm_num
    have d1 : Real.exp (-(25 / 32)) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.2 (by norm_num)
    have d2 : Real.exp (-(9 / 8)) ≤ Real.exp (-(25 / 32)) := Real.exp_le_exp.2 (by norm_num)
    have d3 : Real.exp (-2) ≤ Real.exp (-(9 / 8)) := Real.exp_le_exp.2 (by norm_num)
    have d4 : Real.exp (-(9 / 2)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by norm_num)
    have := Real.exp_pos (-(9 / 2 : ℝ))
    linarith
  unfold RegC RegD JW
  generalize hU : (2.39 : ℝ) * 1.25 ^ 20 = U at hl1 hl2 ⊢
  have hUv : U = 2.39 * 1.25 ^ 20 := hU.symm
  have hU1 : (207.29 : ℝ) ≤ U := by rw [hUv]; norm_num
  have hU2 : U ≤ 207.3 := by rw [hUv]; norm_num
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU1
  -- `c₀`
  have hc0a : -0.23516 ≤ c0C 0.173 0.24567 (-0.23516) 13 U := by
    unfold c0C
    have h0 : 0 < max 1 (0.173 * (U + 13)) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have : (0 : ℝ) ≤ 0.24567 / max 1 (0.173 * (U + 13)) ^ 4 := by positivity
    linarith
  have hc0b : c0C 0.173 0.24567 (-0.23516) 13 U ≤ -0.2351598 := by
    unfold c0C
    have hm : (38 : ℝ) ≤ max 1 (0.173 * (U + 13)) := le_trans (by linarith) (le_max_right _ _)
    have : (0.24567 : ℝ) / max 1 (0.173 * (U + 13)) ^ 4 ≤ 0.24567 / 38 ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hm 4)
    have : (0.24567 : ℝ) / 38 ^ 4 ≤ 0.0000002 := by norm_num
    linarith
  -- `c₂`
  have hpi := Real.pi_gt_d6
  have hc2a : 0 ≤ c2C 0.16385 13 U := by unfold c2C; positivity
  have hc2b : c2C 0.16385 13 U ≤ 4.41936 := by
    unfold c2C
    have h1 : 1 / (2 * π) ≤ 1 / (2 * 3.141592) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h3 : 16 * 3.141592 * 207.29 ≤ 16 * π * U :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpi.le (by norm_num)) hU1 (by norm_num) (by positivity)
    have h2 : 1 / (16 * π * U) ≤ 1 / (16 * 3.141592 * 207.29) := one_div_le_one_div_of_le (by norm_num) h3
    linarith
  -- `L`
  have hL5 : 5 ≤ Real.log (1 / δ) := by
    have h208 : (208 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have h5 : Real.exp 5 ≤ 208 := by
      have := Real.exp_one_lt_d9
      have e5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      have := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 5
      rw [e5]; linarith [show (2.7182818286 : ℝ) ^ 5 ≤ 208 by norm_num]
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith
  -- region C
  generalize hc₀ : c0C 0.173 0.24567 (-0.23516) 13 U = c₀ at hc0a hc0b ⊢
  generalize hc₂ : c2C 0.16385 13 U = c₂ at hc2a hc2b ⊢
  have hC1 := PhiC_inv hδ0 c₀ 0.16385 c₂
  generalize hL : Real.log (1 / δ) = L at hL5 hC1 ⊢
  generalize hl : Real.log U = ℓ₁ at hl1 hl2
  have hX4 : 0 ≤ c₀ / 4 + 0.16385 * (ℓ₁ / 4 - 1 / 16) := by linarith
  have hC2 := PhiC_U_ge (δ := δ) (c₀ := c₀) (κ₁ := 0.16385) (c₂ := c₂) hU0 hδ0.le hc2a (by rw [hl]; exact hX4)
  rw [hl] at hC2
  have hδU : δ * U ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hU2 hδ0.le
    linarith
  have hδU0 : 0 ≤ δ * U := by positivity
  -- region D
  have hD0 : 0 ≤ c₀ + 0.16385 * L + c₂ * δ := by
    have := mul_nonneg hc2a hδ0.le
    linarith
  have hD : (c₀ + 0.16385 * L + c₂ * δ) * EpD ≤ (c₀ + 0.16385 * L + c₂ * δ) * 0.350366 :=
    mul_le_mul_of_nonneg_left hE hD0
  -- products of atoms
  have p1 : c₀ * L ≤ -0.2351598 * L := mul_le_mul_of_nonneg_right hc0b (by linarith)
  have p2 : -0.23516 * 5.334166 ≤ c₀ * ℓ₁ := by
    have := mul_le_mul_of_nonpos_left hl2 (by linarith : c₀ ≤ 0)
    linarith
  have p3 : 5.334163 ^ 2 ≤ ℓ₁ ^ 2 := pow_le_pow_left₀ (by norm_num) hl1 2
  have hX2 : 0 ≤ c₀ / 2 + 0.16385 * (ℓ₁ / 2 - 1 / 4) := by linarith
  have hX2' : c₀ / 2 + 0.16385 * (ℓ₁ / 2 - 1 / 4) ≤ 0.2784677 := by linarith
  have p4 : (δ * U) ^ 2 / 2 * (c₀ / 2 + 0.16385 * (ℓ₁ / 2 - 1 / 4)) ≤ δ * (207.3 * 0.2784677 / 2) := by
    have hsq : (δ * U) ^ 2 ≤ δ * U := by
      rw [sq]; calc δ * U * (δ * U) ≤ δ * U * 1 := mul_le_mul_of_nonneg_left hδU hδU0
        _ = δ * U := mul_one _
    have h1 := mul_le_mul hsq hX2' hX2 hδU0
    have h2 : δ * U * 0.2784677 ≤ δ * 207.3 * 0.2784677 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU2 hδ0.le) (by norm_num)
    linarith
  have p5 : c₂ * δ ^ 2 * U / 2 - 35 / 24 * c₂ * δ + c₂ * δ * 0.350366 ≤ 0 := by
    have e : c₂ * δ ^ 2 * U / 2 - 35 / 24 * c₂ * δ + c₂ * δ * 0.350366 =
        c₂ * δ * (δ * U / 2 - 35 / 24 + 0.350366) := by ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc2a hδ0.le) (by linarith)
  have p6 : c₂ / U ≤ 4.41936 / 207.29 := by
    calc c₂ / U ≤ 4.41936 / U := div_le_div_of_nonneg_right hc2b hU0.le
      _ ≤ 4.41936 / 207.29 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hU1
  rw [hC1]
  linarith [hA, hB, hC2, hD, hF, p1, p2, p3, p4, p5, p6, hc0a, hc0b]

/-- **The line zeros `|γ| ≤ H` in numbers**, under RH up to `H ∈ [10⁸, 3·10¹⁰]`: for
`1/2 ≤ Y₁`, `Y₁ + 13 ≤ H/2`, `3/Y₁ ≤ δ ≤ 1/208`,
`Σ m_ρ ‖Mg(ρ)‖ ≤ e^{δ²/8}(e^{a/2} + e^{b/2}) (JW(δ) + e^{−δ²Y₁²/2} LWH(H))`. -/
theorem line_sum_numH {H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10) (hY₁0 : 1 / 2 ≤ Y₁)
    (hY₁ : Y₁ + 13 ≤ H / 2) {δ : ℝ} (hδ0 : 3 / Y₁ ≤ δ) (hδ1 : δ ≤ 1 / 208) (a b T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ H), (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) *
        (JW δ + Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H) := by
  have hY0 : 0 < Y₁ := by linarith
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδ0
  have hUδ : (2.39 : ℝ) * 1.25 ^ 20 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    have : (2.39 : ℝ) * 1.25 ^ 20 ≤ 208 := by norm_num
    nlinarith
  have hW : 3 / δ ≤ Y₁ := by
    rw [div_le_iff₀ hδ]; rw [div_le_iff₀ hY0] at hδ0; linarith
  refine (line_sum_closedH (ℓ := 0.173) (by norm_num) (by norm_num) exp_692_lt (N := 20) (by norm_num)
    hRH hH1 hH2 (R := 13) (by norm_num) hY₁0 hY₁ (by norm_num) kB_pos p0_le kap1_le kap0_le kap_pos
    (r := 1.25) (by norm_num) (nA := 8) (nB := 20) (by norm_num) (by norm_num) hδ hUδ hW a b T).trans ?_
  gcongr
  exact Jtot_le hδ hδ1

end TernaryGoldbach.Explicit
