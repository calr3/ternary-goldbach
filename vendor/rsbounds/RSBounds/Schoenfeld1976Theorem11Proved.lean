import RSBounds.SchoenfeldWalk11Data
import RSBounds.SchoenfeldTheorem11Ge23
import RSBounds.Schoenfeld1976Theorem7Proved

/-!
# Schoenfeld (1976), Theorem 11 in full, given PsiCert

`SchoenfeldTheorem11Ge23` proves (7.2), (7.3) and (7.4) for `x ≥ e^23`. Below:

* `[1500, e^23]`: PsiCert, `|ψ(x) − x| ≤ (4/5)√x`, and for `θ` also
  `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5}) ≤ 3.12 √x` (Mathlib, and `ψ(y) < 1.04 y`
  for `y < 10⁵` from the walk). Here `ε₀(x) ≥ 0.13` on `[1500, 10⁴]` and `ε₀(x) ≥ 0.063` on
  `[10⁴, e^23]` (`SchoenfeldPrimeWalk.eps_ge`, with `log 2` bounds and
  `eˣ < 1/(1 − x)`), far more than `3.92/√x`;
* below 1500: the blocks of `SchoenfeldWalk11Data`.

PsiCert is certified outside this project and enters as a hypothesis.
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Theorem11Proved

local notation "ε₀" => Goals.Schoenfeld1976.epsilon0

theorem exp23_le : Real.exp 23 ≤ 9800000000 := by
  have h := Real.exp_one_lt_d9
  calc Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 23 := by gcongr
    _ ≤ 9800000000 := by norm_num

/-- `exp (1 + f) < 2.7182818286 / (1 − f)` for `0 < f < 1`. -/
theorem exp_one_add_lt {f : ℝ} (h0 : 0 < f) (h1 : f < 1) :
    Real.exp (1 + f) < 2.7182818286 / (1 - f) := by
  rw [Real.exp_add]
  have he := Real.exp_one_lt_d9
  have hf := Real.exp_bound_div_one_sub_of_interval' h0 h1
  have hpos : 0 < 1 - f := by linarith
  calc Real.exp 1 * Real.exp f < 2.7182818286 * (1 / (1 - f)) :=
        mul_lt_mul he hf.le (Real.exp_pos f) (by norm_num)
    _ = 2.7182818286 / (1 - f) := by ring

theorem w_le {u f w : ℝ} (hu : u = 1 + f) (h0 : 0 < f) (h1 : f < 1) (hw : 0 < w)
    (h : 2.7182818286 / (1 - f) ≤ 1 / w) : w ≤ Real.exp (-u) := by
  rw [Real.exp_neg, hu]
  have h2 := (exp_one_add_lt h0 h1).trans_le h
  rw [lt_div_iff₀ hw] at h2
  rw [le_inv_comm₀ hw (Real.exp_pos _)]
  rw [inv_eq_one_div]
  rw [le_div_iff₀ hw]
  linarith

theorem eps_mid1 {x : ℝ} (h1 : 1500 ≤ x) (h2 : x ≤ 10000) : 0.13 ≤ ε₀ x := by
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have ha : 10 * Real.log 2 ≤ Real.log 1500 := by
    have e : Real.log ((2 : ℝ) ^ 10) = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hb : Real.log 10000 ≤ 14 * Real.log 2 := by
    have e : Real.log ((2 : ℝ) ^ 14) = 14 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) (by norm_num)
  have h := SchoenfeldPrimeWalk.eps_ge (s := 0.92) (u := 1.0031) (w := 0.3667) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h1 h2 (by norm_num; linarith) (by norm_num; linarith)
    (w_le (f := 0.0031) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  linarith

theorem eps_mid2 {x : ℝ} (h1 : 10000 ≤ x) (h2 : x ≤ Real.exp 23) : 0.063 ≤ ε₀ x := by
  have l2 := Real.log_two_gt_d9
  have ha : 13 * Real.log 2 ≤ Real.log 10000 := by
    have e : Real.log ((2 : ℝ) ^ 13) = 13 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) (by norm_num)
  have h := SchoenfeldPrimeWalk.eps_ge (s := 0.98) (u := 1.5442) (w := 0.1676) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h1 h2 (by norm_num; linarith)
    (by rw [Real.log_exp]; norm_num)
    (w_le (f := 0.5442) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  linarith

/-- `ψ(y) < 1.04 y` for `1 ≤ y < 10⁵` (the walk). -/
theorem psi_lt {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 100000) : Chebyshev.psi y < 1.04 * y :=
  Schoenfeld1976Theorem7.psi_lt (fun _ h1 h2 => SchoenfeldPrimeWalk.good h1 h2) h1 h2

theorem psi_sub_theta_le {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 9800000000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 3.12 * Real.sqrt x := by
  have hdec := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hsq : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have h3 : x ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt x := by
    rw [← hsq]; exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have h5 : x ^ ((5 : ℝ)⁻¹) ≤ Real.sqrt x := by
    rw [← hsq]; exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [hsq] at hdec
  have hs1 : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt x < 100000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num; linarith)
  have g3 : 1 ≤ x ^ ((3 : ℝ)⁻¹) := Real.one_le_rpow h1 (by norm_num)
  have g5 : 1 ≤ x ^ ((5 : ℝ)⁻¹) := Real.one_le_rpow h1 (by norm_num)
  have p1 := psi_lt hs1 hs2
  have p3 := psi_lt g3 (by linarith)
  have p5 := psi_lt g5 (by linarith)
  linarith

section

variable (hcert : Goals.Schoenfeld1976.PsiCert)
include hcert

theorem mid {x : ℝ} (h1 : 1500 ≤ x) (h2 : x ≤ Real.exp 23) :
    |Chebyshev.psi x - x| < x * ε₀ x ∧ |Chebyshev.theta x - x| < x * ε₀ x := by
  have hx : x ≤ 9800000000 := h2.trans exp23_le
  have hc := hcert x h1 (by linarith)
  have hd := psi_sub_theta_le (by linarith) hx
  have hθ := Chebyshev.theta_le_psi x
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  -- `3.92 √x < x ε₀(x)`
  have key : 3.92 * Real.sqrt x < x * ε₀ x := by
    rcases le_or_gt x 10000 with h | h
    · have he := eps_mid1 h1 h
      have hs38 : 38 ≤ Real.sqrt x := by
        rw [show (38 : ℝ) = Real.sqrt (38 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num; linarith)
      have t1 : 38 * 0.13 ≤ Real.sqrt x * ε₀ x := mul_le_mul hs38 he (by norm_num) hs
      have t2 := mul_le_mul_of_nonneg_left t1 hs
      have t3 : Real.sqrt x * (Real.sqrt x * ε₀ x) = x * ε₀ x := by rw [← mul_assoc, hxx]
      linarith
    · have he := eps_mid2 h.le h2
      have hs100 : 100 ≤ Real.sqrt x := by
        rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num; linarith)
      have t1 : 100 * 0.063 ≤ Real.sqrt x * ε₀ x := mul_le_mul hs100 he (by norm_num) hs
      have t2 := mul_le_mul_of_nonneg_left t1 hs
      have t3 : Real.sqrt x * (Real.sqrt x * ε₀ x) = x * ε₀ x := by rw [← mul_assoc, hxx]
      linarith
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  refine ⟨?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

variable (hRH : Goals.FiniteRH 1894438.5122)
include hRH

/-- Theorem 11, (7.2). -/
theorem psi11 {x : ℝ} (hx : 17 ≤ x) : |Chebyshev.psi x - x| < x * ε₀ x := by
  rcases lt_or_ge x 1500 with h | h
  · exact SchoenfeldPrimeWalk.small_psi hx h
  rcases le_or_gt x (Real.exp 23) with h' | h'
  · exact (mid hcert h h').1
  · exact SchoenfeldTheorem11Ge23.psi_lt hRH h'.le

/-- Theorem 11, (7.3). -/
theorem theta11 {x : ℝ} (hx : 101 ≤ x) : |Chebyshev.theta x - x| < x * ε₀ x := by
  rcases lt_or_ge x 1500 with h | h
  · exact SchoenfeldPrimeWalk.small_theta hx h
  rcases le_or_gt x (Real.exp 23) with h' | h'
  · exact (mid hcert h h').2
  · exact SchoenfeldTheorem11Ge23.theta_lt hRH h'.le

/-- Theorem 11, (7.4) as established on printed page 349. -/
theorem psiUpper11 {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧ Chebyshev.psi x - x < x * ε₀ x := by
  refine ⟨by linarith [Chebyshev.theta_le_psi x], ?_⟩
  rcases lt_or_ge x 17 with h | h
  · exact SchoenfeldPrimeWalk.small_psi_upper hx h
  · exact lt_of_le_of_lt (le_abs_self _) (psi11 hcert hRH h)

end

/-- (7.2), given PsiCert. -/
theorem proved_psi (hcert : Goals.Schoenfeld1976.PsiCert) : Goals.Schoenfeld1976.PsiTheorem11 :=
  fun hRH _ hx => psi11 hcert hRH hx

/-- (7.3), given PsiCert. -/
theorem proved_theta (hcert : Goals.Schoenfeld1976.PsiCert) :
    Goals.Schoenfeld1976.ThetaTheorem11 :=
  fun hRH _ hx => theta11 hcert hRH hx

/-- (7.4), given PsiCert. -/
theorem proved_psiUpper (hcert : Goals.Schoenfeld1976.PsiCert) :
    Goals.Schoenfeld1976.PsiUpperTheorem11 :=
  fun hRH _ hx => psiUpper11 hcert hRH hx

end TernaryGoldbach.RSBounds.Schoenfeld1976Theorem11Proved
