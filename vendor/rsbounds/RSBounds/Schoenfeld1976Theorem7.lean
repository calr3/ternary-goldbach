import RSBounds.SchoenfeldPrimeWalk
import RSBounds.Schoenfeld1976PsiThetaLog
import RSBounds.Schoenfeld1976TargetsExtra

/-!
# Schoenfeld (1976), Theorem 7*: (5.5a*), (5.5b*), (5.6a*) and (5.6*)

Each display is split into three ranges:

* `x < 1.35·10⁶`: the kernel walk `SchoenfeldPrimeWalk` (taken here as the hypothesis `hgood`,
  discharged in `Schoenfeld1976Theorem7Proved`);
* `x ≤ e^22` (`≤ 3.6·10⁹`): PsiCert, `|ψ(x) − x| ≤ (4/5)√x`. For (5.6*) also
  `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` (Mathlib) with `ψ(y) < 1.04 y` for
  `y < 10⁵` (the walk);
* `x ≥ e^22`: (5.6b*) (`Schoenfeld1976PsiThetaLog`), whose constant `0.0077629` is smaller.

The middle range needs `κ√x < c x / log x`, which reduces, with `y = √x`, to `2κ log y < c y`;
`log y / y` is decreasing, so one bound `log y₀ < L` at the bottom of the range suffices
(`sqrt_lt_div_log`).
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Theorem7

open SchoenfeldPrimeWalk (Good div_log_le)

/-! ## Numerical lemmas -/

theorem exp22_le : Real.exp 22 ≤ 3600000000 := by
  have h := Real.exp_one_lt_d9
  calc Real.exp 22 = Real.exp 1 ^ 22 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 22 := by gcongr
    _ ≤ 3600000000 := by norm_num

theorem log_lt_of {y L f : ℝ} (n : ℕ) (hf : 0 ≤ f) (hL : L = n + f) (hy : 0 < y)
    (h : y < (2.7182818283 : ℝ) ^ n * (1 + f + f ^ 2 / 2 + f ^ 3 / 6)) : Real.log y < L := by
  rw [Real.log_lt_iff_lt_exp hy, hL]
  exact lt_of_lt_of_le h (Schoenfeld1976Rows2.exp_lower n hf)

theorem log447 : Real.log 447 < 6.164 :=
  log_lt_of (f := 0.164) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem log500 : Real.log 500 < 6.29 :=
  log_lt_of (f := 0.29) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem log1161 : Real.log 1161 < 7.12 :=
  log_lt_of (f := 0.12) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `κ √x < c x / log x` for `√x ≥ y₀`, given `log y₀ < L` and `2κL ≤ c y₀`. -/
theorem sqrt_lt_div_log {κ c y0 L x : ℝ} (hκ : 0 < κ) (hy0 : 3 ≤ y0) (hL : Real.log y0 < L)
    (hc : 2 * κ * L ≤ c * y0) (hx : y0 ^ 2 ≤ x) :
    κ * Real.sqrt x < c * x / Real.log x := by
  have hy : y0 ≤ Real.sqrt x := by
    rw [show y0 = Real.sqrt (y0 ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hx
  set y := Real.sqrt x with hy_def
  have hy3 : 3 ≤ y := le_trans hy0 hy
  have hx0 : 0 < x := by nlinarith
  have hyy : y ^ 2 = x := Real.sq_sqrt hx0.le
  have hlogx : Real.log x = 2 * Real.log y := by
    rw [← hyy, Real.log_pow]; push_cast; ring
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hly0 : 0 < Real.log y0 := Real.log_pos (by linarith)
  have hy0p : 0 < y0 := by linarith
  have hmono := div_log_le hy0 hy
  rw [div_le_div_iff₀ hly0 hly] at hmono
  have h2 : Real.log y * y0 < L * y := by nlinarith
  have h3 : 2 * κ * Real.log y * y0 < c * y * y0 := by nlinarith
  have key : 2 * κ * Real.log y < c * y := lt_of_mul_lt_mul_right h3 hy0p.le
  rw [hlogx, lt_div_iff₀ (by positivity), ← hyy]
  nlinarith [mul_lt_mul_of_pos_right key (by linarith : (0 : ℝ) < y)]

/-- `a x^{1/3} ≤ √x` once `a⁶ ≤ x`. -/
theorem cube_root_le {a x : ℝ} (ha : 0 ≤ a) (hx0 : 0 < x) (hx : a ^ 6 ≤ x) :
    a * x ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt x := by
  have h6 : a ≤ x ^ ((6 : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos ha hx0.le (by norm_num : (0 : ℝ) < 6)).2
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hx
  have h := mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hx0.le ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (6 : ℝ)⁻¹ + (3 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

/-- `a x^{1/5} ≤ √x` once `a¹⁰ ≤ x³`. -/
theorem fifth_root_le {a x : ℝ} (ha : 0 ≤ a) (hx0 : 0 < x) (hx : a ^ 10 ≤ x ^ 3) :
    a * x ^ ((5 : ℝ)⁻¹) ≤ Real.sqrt x := by
  have h10 : a ≤ x ^ (3 / 10 : ℝ) := by
    apply (Real.rpow_le_rpow_iff ha (Real.rpow_nonneg hx0.le (3 / 10 : ℝ))
      (by norm_num : (0 : ℝ) < 10)).mp
    rw [← Real.rpow_mul hx0.le]
    rw [show (3 / 10 : ℝ) * 10 = 3 by norm_num]
    simpa only [Real.rpow_ofNat] using hx
  have h := mul_le_mul_of_nonneg_right h10 (Real.rpow_nonneg hx0.le ((5 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (3 / 10 : ℝ) + (5 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

theorem div_log_mono {c₁ c₂ x : ℝ} (h : c₁ ≤ c₂) (hx : 1 < x) :
    c₁ * x / Real.log x ≤ c₂ * x / Real.log x := by
  rw [div_le_div_iff_of_pos_right (Real.log_pos hx)]
  nlinarith

theorem div_log_pos {c x : ℝ} (hc : 0 < c) (hx : 1 < x) : 0 < c * x / Real.log x :=
  div_pos (by nlinarith) (Real.log_pos hx)

section

variable (hgood : ∀ n : ℕ, 1 ≤ n → n < 1350000 → Good n)
include hgood

/-! ## The walk at a real point -/

theorem walk_at {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x < 1350000) :
    (x < 250000 → Chebyshev.theta x < x) ∧
    (x < 100000 → Chebyshev.psi x - x < 0.04 * x) ∧
    (89909 ≤ x → x < 200000 → x - Chebyshev.psi x < 0.0220646 * x / Real.log x) ∧
    (161971 ≤ x → x < 200000 → Chebyshev.psi x - x < 0.0220646 * x / Real.log x) ∧
    (758711 ≤ x → |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hn2 : ⌊x⌋₊ < 1350000 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx2)
  obtain ⟨g1, g2, g3, g4, g5⟩ := hgood _ hn1 hn2 x hnx (Nat.lt_floor_add_one x)
  have lt_of {N : ℕ} (h : x < N) : ⌊x⌋₊ < N := by exact_mod_cast hnx.trans_lt h
  have le_of {N : ℕ} (h : (N : ℝ) ≤ x) : N ≤ ⌊x⌋₊ := Nat.le_floor h
  refine ⟨fun h => g1 (lt_of (N := 250000) (by exact_mod_cast h)),
    fun h => g2 (lt_of (N := 100000) (by exact_mod_cast h)),
    fun h1 h2 => g3 (le_of (N := 89909) (by exact_mod_cast h1))
      (lt_of (N := 200000) (by exact_mod_cast h2)),
    fun h1 h2 => g4 (le_of (N := 161971) (by exact_mod_cast h1))
      (lt_of (N := 200000) (by exact_mod_cast h2)),
    fun h => g5 (le_of (N := 758711) (by exact_mod_cast h)) hn2⟩

/-- `ψ(y) < 1.04 y` for `1 ≤ y < 10⁵`. -/
theorem psi_lt {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 100000) : Chebyshev.psi y < 1.04 * y := by
  have := (walk_at hgood hy1 (by linarith)).2.1 hy2
  linarith

/-- `ψ(x) − θ(x) ≤ 1.155 √x` for `1.35·10⁶ ≤ x ≤ 3.6·10⁹`. -/
theorem psi_sub_theta_le {x : ℝ} (hx1 : 1350000 ≤ x) (hx2 : x ≤ 3600000000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.155 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hdec := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hsq : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsq] at hdec
  have hs1 : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
  have hs2 : Real.sqrt x < 100000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num; linarith)
  have hc := cube_root_le (a := 10.5) (by norm_num) hx0 (by norm_num; linarith)
  have hf := fifth_root_le (a := 68.8) (by norm_num) hx0
    (le_trans (by norm_num : (68.8 : ℝ) ^ 10 ≤ 1350000 ^ 3) (by gcongr))
  have h3 : 1 ≤ x ^ ((3 : ℝ)⁻¹) := Real.one_le_rpow (by linarith) (by norm_num)
  have h5 : 1 ≤ x ^ ((5 : ℝ)⁻¹) := Real.one_le_rpow (by linarith) (by norm_num)
  have p1 := psi_lt hgood hs1 hs2
  have p3 := psi_lt hgood h3 (by linarith)
  have p5 := psi_lt hgood h5 (by linarith)
  linarith

/-! ## The four displays -/

variable (hRH : Goals.FiniteRH 1894438.5122) (hcert : Goals.Schoenfeld1976.PsiCert)
include hRH hcert

/-- `|ψ(x) − x| < 0.0220646 x / log x` for `x ≥ 2·10⁵`. -/
theorem psi_log_high {x : ℝ} (hx : 200000 ≤ x) :
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x := by
  rcases le_or_gt x (Real.exp 22) with h | h
  · have hx' : x ≤ 3600000000 := h.trans exp22_le
    calc |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x := hcert x (by linarith) (by linarith)
      _ < _ := sqrt_lt_div_log (y0 := 447) (L := 6.164) (by norm_num) (by norm_num) log447
          (by norm_num) (by norm_num; linarith)
  · have h1 := (Schoenfeld1976PsiThetaLog.psiThetaLog hRH h.le).1
    have h2 := div_log_mono (c₁ := 0.0077629) (c₂ := 0.0220646) (by norm_num)
      (show (1 : ℝ) < x by linarith)
    linarith

/-- (5.5a*). -/
theorem psiLog {x : ℝ} (hx : 161971 ≤ x) :
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x := by
  rcases lt_or_ge x 200000 with h | h
  · obtain ⟨-, -, g3, g4, -⟩ := walk_at hgood (by linarith) (by linarith)
    rw [abs_lt]
    exact ⟨by linarith [g3 (by linarith) h], g4 hx h⟩
  · exact psi_log_high hgood hRH hcert h

/-- (5.5b*). -/
theorem psiLogLower {x : ℝ} (hx : 89909 ≤ x) :
    -(0.0220646 * x / Real.log x) < Chebyshev.psi x - x := by
  rcases lt_or_ge x 200000 with h | h
  · obtain ⟨-, -, g3, -, -⟩ := walk_at hgood (by linarith) (by linarith)
    linarith [g3 hx h]
  · exact (abs_lt.mp (psi_log_high hgood hRH hcert h)).1

/-- (5.6a*). -/
theorem thetaLogUpper {x : ℝ} (hx : 1 < x) :
    Chebyshev.theta x - x < 0.0201384 * x / Real.log x := by
  have hpos := div_log_pos (c := 0.0201384) (by norm_num) hx
  rcases lt_or_ge x 250000 with h | h
  · linarith [(walk_at hgood hx.le (by linarith)).1 h]
  rcases le_or_gt x (Real.exp 22) with h' | h'
  · have hx' : x ≤ 3600000000 := h'.trans exp22_le
    have h1 := hcert x (by linarith) (by linarith)
    have h2 := Chebyshev.theta_le_psi x
    have h3 : 4 / 5 * Real.sqrt x < 0.0201384 * x / Real.log x :=
      sqrt_lt_div_log (y0 := 500) (L := 6.29) (by norm_num) (by norm_num) log500
        (by norm_num) (by norm_num; linarith)
    linarith [le_abs_self (Chebyshev.psi x - x)]
  · have h1 := (Schoenfeld1976PsiThetaLog.psiThetaLog hRH h'.le).2
    have h2 := div_log_mono (c₁ := 0.0077629) (c₂ := 0.0201384) (by norm_num) hx
    linarith [le_abs_self (Chebyshev.theta x - x)]

/-- (5.6*). -/
theorem thetaLog {x : ℝ} (hx : 758711 ≤ x) :
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x := by
  rcases lt_or_ge x 1350000 with h | h
  · exact (walk_at hgood (by linarith) h).2.2.2.2 hx
  rcases le_or_gt x (Real.exp 22) with h' | h'
  · have hx' : x ≤ 3600000000 := h'.trans exp22_le
    have h1 := abs_le.mp (hcert x (by linarith) (by linarith))
    have h2 := Chebyshev.theta_le_psi x
    have h3 := psi_sub_theta_le hgood h hx'
    have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h4 : 1.955 * Real.sqrt x < 0.0239922 * x / Real.log x :=
      sqrt_lt_div_log (y0 := 1161) (L := 7.12) (by norm_num) (by norm_num) log1161
        (by norm_num) (by norm_num; linarith)
    rw [abs_lt]
    constructor <;> linarith
  · have h1 := (Schoenfeld1976PsiThetaLog.psiThetaLog hRH h'.le).2
    have h2 := div_log_mono (c₁ := 0.0077629) (c₂ := 0.0239922) (by norm_num)
      (show (1 : ℝ) < x by linarith)
    linarith

end

end TernaryGoldbach.RSBounds.Schoenfeld1976Theorem7
