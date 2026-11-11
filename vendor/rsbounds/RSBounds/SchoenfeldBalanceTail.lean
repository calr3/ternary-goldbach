import RSBounds.SchoenfeldBalanceMain

/-!
# Theorem 11 parameter balance: the residual estimates

Schoenfeld (1976), pp. 345–348, (7.31)–(7.42), for the exact formal envelope.

The paper ends with `|ψ(x) − x| < x ε₀(x) M(v) L(v)` (7.37), where
`L(v) = {v⁶/(2v² − 1)}^{1/4}` (7.38) and `M(v)` (7.39) are both `< 1` for `log x ≥ 1737`
((7.40)–(7.42)). The slack that absorbs every residual term is `d = log(17/2π) < 1`: on p. 347
Schoenfeld replaces `v + d/X` in `G₀` by `v + 1/X`. Here that slack is kept as an explicit
factor `1 − (1 − d)/(X + 1)` (`P4_le`), in place of the paper's exponential bookkeeping with
the constants 0.29, 0.62, 0.92 and 3.68. The residual terms are then bounded directly
(`tail_le`, `q_bounds`, `rosserR_bounds`, `G2_bounds`, `small_terms_le`).
-/

open Real Set

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceTail

open SchoenfeldBalanceAlgebra SchoenfeldBalanceV SchoenfeldBalanceMain

/-- `d = log(17/2π) ≤ 0.996`, so `1 − d ≥ 0.004`. -/
theorem d_le : SchoenfeldWeightedZeros.d ≤ 0.996 := by
  rw [SchoenfeldBalanceVNumeric.d_eq, Real.log_le_iff_le_exp (by positivity)]
  have hpi : 3.141592 < π := Real.pi_gt_d6
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : (1 : ℝ) - 0.004 ≤ Real.exp (-0.004) := by
    have := Real.add_one_le_exp (-0.004 : ℝ)
    linarith
  have hexp : Real.exp 0.996 = Real.exp 1 * Real.exp (-0.004) := by
    rw [← Real.exp_add]
    norm_num
  rw [hexp]
  calc 17 / (2 * π) ≤ 17 / (2 * 3.141592) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    _ ≤ 2.7182818283 * (1 - 0.004) := by norm_num
    _ ≤ Real.exp 1 * Real.exp (-0.004) :=
        mul_le_mul he.le h1 (by norm_num) (Real.exp_pos _).le

/-- `X(X + 1)e^{−X}` decreases for `X ≥ 2` (via `e^s ≥ 1 + s + s²/2`, no derivatives). -/
theorem tail_mono {X X0 : ℝ} (hX0 : 2 ≤ X0) (hX : X0 ≤ X) :
    X * (X + 1) * Real.exp (-X) ≤ X0 * (X0 + 1) * Real.exp (-X0) := by
  have hs0 : 0 ≤ X - X0 := by linarith
  have hq : 1 + (X - X0) + (X - X0) ^ 2 / 2 ≤ Real.exp (X - X0) :=
    Real.quadratic_le_exp_of_nonneg hs0
  have hXe : Real.exp (-X0) = Real.exp (-X) * Real.exp (X - X0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have key : X * (X + 1) ≤ X0 * (X0 + 1) * (1 + (X - X0) + (X - X0) ^ 2 / 2) := by
    have h1 : 0 ≤ X0 ^ 2 - X0 - 1 := by nlinarith
    have h2 : 0 ≤ X0 ^ 2 + X0 - 2 := by nlinarith
    nlinarith [mul_nonneg hs0 h1, mul_nonneg (sq_nonneg (X - X0)) h2]
  rw [hXe]
  have hpos : 0 < Real.exp (-X) := Real.exp_pos _
  have hc : 0 ≤ X0 * (X0 + 1) := mul_nonneg (by linarith) (by linarith)
  calc X * (X + 1) * Real.exp (-X)
      ≤ X0 * (X0 + 1) * (1 + (X - X0) + (X - X0) ^ 2 / 2) * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ ≤ X0 * (X0 + 1) * Real.exp (X - X0) * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hc) hpos.le
    _ = X0 * (X0 + 1) * (Real.exp (-X) * Real.exp (X - X0)) := by ring

/-- The value at `X = 13.4192`, which `log x ≥ 1737` implies. -/
theorem tail_numeric : 13.4192 * (13.4192 + 1) * Real.exp (-13.4192) ≤ 2.95e-4 := by
  have he1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h13 : (2.7182818283 : ℝ) ^ 13 ≤ Real.exp 13 := by
    have : Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) he1.le 13
  have hq : 1 + 0.4192 + 0.4192 ^ 2 / 2 ≤ Real.exp 0.4192 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hsplit : Real.exp 13.4192 = Real.exp 13 * Real.exp 0.4192 := by
    rw [← Real.exp_add]
    norm_num
  have hbig : (2.7182818283 : ℝ) ^ 13 * (1 + 0.4192 + 0.4192 ^ 2 / 2) ≤ Real.exp 13.4192 := by
    rw [hsplit]
    exact mul_le_mul h13 hq (by norm_num) (Real.exp_pos _).le
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc (13.4192 : ℝ) * (13.4192 + 1)
      ≤ 2.95e-4 * ((2.7182818283 : ℝ) ^ 13 * (1 + 0.4192 + 0.4192 ^ 2 / 2)) := by norm_num
    _ ≤ 2.95e-4 * Real.exp 13.4192 := mul_le_mul_of_nonneg_left hbig (by norm_num)

theorem tail_le {X : ℝ} (hX : 13.4192 ≤ X) : X * (X + 1) * Real.exp (-X) ≤ 2.95e-4 :=
  (tail_mono (by norm_num) hX).trans tail_numeric

/-- With `s = √X e^{−X}`: `s (X + 1) ≤ 2.95·10⁻⁴`. -/
theorem s_mul_le {X : ℝ} (hX : 13.4192 ≤ X) :
    Real.sqrt X * Real.exp (-X) * (X + 1) ≤ 2.95e-4 := by
  have hs : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  calc Real.sqrt X * Real.exp (-X) * (X + 1) ≤ X * Real.exp (-X) * (X + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)
          (by linarith)
    _ = X * (X + 1) * Real.exp (-X) := by ring
    _ ≤ 2.95e-4 := tail_le hX

/-- (7.38), (7.40): `L(v)⁴ = v⁶/(2v² − 1) ≤ 1` for `0.8 ≤ v ≤ 1`. -/
theorem L_le {v : ℝ} (hv8 : 0.8 ≤ v) (hv1 : v ≤ 1) : v ^ 6 ≤ 2 * v ^ 2 - 1 := by
  have hv2 : 0.64 ≤ v ^ 2 := by nlinarith
  have h1 : 0 ≤ 1 - v ^ 2 := by nlinarith
  have h2 : 0 ≤ v ^ 4 + v ^ 2 - 1 := by nlinarith [sq_nonneg (v ^ 2)]
  nlinarith [mul_nonneg h1 h2]

/-- `L(v)⁴M(v)⁴ ≤ 1` (pp. 347–348), as `v⁴(v + 1/X)(v + 3/(2X))e^{−2Y} ≤ 2v² − 1`.
It uses `(1 + a)(1 + b) ≤ e^{a + b}` and `2X(1 − v) ≥ 9/4 > √5`; the latter follows from
`v < v₁` ((7.41)–(7.42)). -/
theorem LM_le {X v : ℝ} (hX : 0 < X) (hv8 : 0.8 ≤ v) (hv1 : v ≤ 1)
    (hgap : 9 / 4 ≤ 2 * X * (1 - v)) :
    v ^ 4 * (v + 1 / X) * (v + 3 / (2 * X)) * Real.exp (-(2 * Ylow X v)) ≤ 2 * v ^ 2 - 1 := by
  have hv : 0 < v := by linarith
  have hvX : 0 < v * X := by positivity
  have e1 : v ^ 4 * (v + 1 / X) * (v + 3 / (2 * X)) =
      v ^ 6 * ((1 + 1 / (v * X)) * (1 + 3 / (2 * (v * X)))) := by
    field_simp

  have hab : (1 + 1 / (v * X)) * (1 + 3 / (2 * (v * X))) ≤
      Real.exp (1 / (v * X) + 3 / (2 * (v * X))) := by
    rw [Real.exp_add]
    have ha0 : 0 ≤ 1 / (v * X) := by positivity
    have hb0 : 0 ≤ 3 / (2 * (v * X)) := by positivity
    have h1 := Real.add_one_le_exp (1 / (v * X))
    have h2 := Real.add_one_le_exp (3 / (2 * (v * X)))
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (Real.exp_pos _).le
  have hY : 1 / (v * X) + 3 / (2 * (v * X)) ≤ 2 * Ylow X v := by
    have e2 : 1 / (v * X) + 3 / (2 * (v * X)) = 5 / (2 * X) / v := by
      field_simp
      ring
    have e3 : 2 * Ylow X v = 2 * X * (1 - v) ^ 2 / v := by
      unfold Ylow
      ring
    rw [e2, e3]
    apply div_le_div_of_nonneg_right _ hv.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 9 / 4) hgap]
  have hexp : Real.exp (1 / (v * X) + 3 / (2 * (v * X))) * Real.exp (-(2 * Ylow X v)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    linarith
  have hL := L_le hv8 hv1
  rw [e1]
  have hv6 : 0 ≤ v ^ 6 := by positivity
  calc v ^ 6 * ((1 + 1 / (v * X)) * (1 + 3 / (2 * (v * X)))) * Real.exp (-(2 * Ylow X v))
      ≤ v ^ 6 * Real.exp (1 / (v * X) + 3 / (2 * (v * X))) * Real.exp (-(2 * Ylow X v)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hv6) (Real.exp_pos _).le
    _ = v ^ 6 * (Real.exp (1 / (v * X) + 3 / (2 * (v * X))) * Real.exp (-(2 * Ylow X v))) := by
        ring
    _ ≤ v ^ 6 * 1 := mul_le_mul_of_nonneg_left hexp hv6
    _ ≤ 2 * v ^ 2 - 1 := by linarith

/-- (7.31): `G₀ ≤ G₁`; indeed `G₀/G₁ ≤ 2v² − 1 ≤ 1`. -/
theorem G0_le_G1 {d X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv1 : v ≤ 1) (hv2 : 1 < 2 * v ^ 2)
    (hd : 0 ≤ d) : G0 d X v ≤ G1 d X v := by
  unfold G0 G1
  have h2 : 0 < 2 * v ^ 2 - 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  have hA : d / X ≤ (1 + 2 * d) / (2 * X) := by
    rw [div_le_div_iff₀ hX (by positivity)]
    nlinarith
  have hB : 0 ≤ v + d / X := by positivity
  have hC : 2 * v ^ 2 - 1 ≤ 1 := by nlinarith
  have h3 : (v + d / X) * (2 * v ^ 2 - 1) ≤ v + (1 + 2 * d) / (2 * X) := by
    nlinarith [mul_le_mul_of_nonneg_left hC hB]
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg v)]

/-- **The decisive estimate.** With `P = (G₀G₁)^{1/4} e^{−Y/2}` (so `2δ = P ε₀` by (7.24a)),
`P⁴ ≤ 1 − (1 − d)/(X + 1)`. Schoenfeld p. 347 bounds `G₀ = v²(v + d/X)` by `v²(v + 1/X)` and
`(1 + 2d)/2 ≤ 3/2`, using `d < 1`; the factor kept here is what that step gives away. -/
theorem P4_le {X v d : ℝ} (hX : 0 < X) (hv8 : 0.8 ≤ v) (hv1 : v ≤ 1)
    (hgap : 9 / 4 ≤ 2 * X * (1 - v)) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    G0 d X v * G1 d X v * Real.exp (-(2 * Ylow X v)) ≤ 1 - (1 - d) / (X + 1) := by
  have hv : 0 < v := by linarith
  have hv2 : 0 < 2 * v ^ 2 - 1 := by nlinarith
  have hLM := LM_le hX hv8 hv1 hgap
  have hE : 0 < Real.exp (-(2 * Ylow X v)) := Real.exp_pos _
  have hvX0 : 0 < v * X := by positivity
  have hvX : 0 < v * X + 1 := by linarith
  have hX' : X ≠ 0 := hX.ne'
  have hvX' : v * X + 1 ≠ 0 := hvX.ne'
  have hv2' : 2 * v ^ 2 - 1 ≠ 0 := hv2.ne'
  have hG : G0 d X v * G1 d X v * Real.exp (-(2 * Ylow X v)) =
      (v + 1 / X) * (1 - (1 - d) / (v * X + 1)) * (v + (1 + 2 * d) / (2 * X)) * v ^ 4 *
        Real.exp (-(2 * Ylow X v)) / (2 * v ^ 2 - 1) := by
    unfold G0 G1
    field_simp
    ring
  have h2 : v + (1 + 2 * d) / (2 * X) ≤ v + 3 / (2 * X) := by
    have : (1 + 2 * d) / (2 * X) ≤ 3 / (2 * X) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hc : 0 ≤ 1 - (1 - d) / (v * X + 1) := by
    rw [sub_nonneg, div_le_one hvX]
    linarith
  have hc2 : 1 - (1 - d) / (v * X + 1) ≤ 1 - (1 - d) / (X + 1) := by
    have : (1 - d) / (X + 1) ≤ (1 - d) / (v * X + 1) :=
      div_le_div_of_nonneg_left (by linarith) hvX (by nlinarith)
    linarith
  have hw : 0 ≤ (v + 1 / X) * (1 - (1 - d) / (v * X + 1)) := mul_nonneg (by positivity) hc
  rw [hG, div_le_iff₀ hv2]
  calc (v + 1 / X) * (1 - (1 - d) / (v * X + 1)) * (v + (1 + 2 * d) / (2 * X)) * v ^ 4 *
        Real.exp (-(2 * Ylow X v))
      ≤ (v + 1 / X) * (1 - (1 - d) / (v * X + 1)) * (v + 3 / (2 * X)) * v ^ 4 *
        Real.exp (-(2 * Ylow X v)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hw
    _ = (1 - (1 - d) / (v * X + 1)) *
        (v ^ 4 * (v + 1 / X) * (v + 3 / (2 * X)) * Real.exp (-(2 * Ylow X v))) := by ring
    _ ≤ (1 - (1 - d) / (v * X + 1)) * (2 * v ^ 2 - 1) := mul_le_mul_of_nonneg_left hLM hc
    _ ≤ (1 - (1 - d) / (X + 1)) * (2 * v ^ 2 - 1) := mul_le_mul_of_nonneg_right hc2 hv2.le

/-- From `P⁴ ≤ 1 − a` with `0 ≤ a ≤ 1`: `P ≤ 1 − a/4`. -/
theorem le_one_sub_quarter {P a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h4 : P ^ 4 ≤ 1 - a) :

    P ≤ 1 - a / 4 := by
  have hb : 0 ≤ 1 - a / 4 := by linarith
  have hbern : 1 - a ≤ (1 - a / 4) ^ 4 := by
    have hu : 0 ≤ 6 - 4 * (a / 4) + (a / 4) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (a / 4)) hu]
  exact le_of_pow_le_pow_left₀ (by norm_num) hb (h4.trans hbern)

/-- `P = √√(G₀G₁) e^{−Y/2}` satisfies `P⁴ = G₀G₁e^{−2Y}`. -/
theorem P_pow_four {d X v : ℝ} (h0 : 0 < G0 d X v) (h1 : 0 < G1 d X v) :
    (Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) * Real.exp (-(Ylow X v / 2))) ^ 4 =
      G0 d X v * G1 d X v * Real.exp (-(2 * Ylow X v)) := by
  have hg : 0 ≤ G0 d X v * G1 d X v := by positivity
  rw [mul_pow]
  have e1 : Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) ^ 4 = G0 d X v * G1 d X v := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hg]
  have e2 : Real.exp (-(Ylow X v / 2)) ^ 4 = Real.exp (-(2 * Ylow X v)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e1, e2]

/-- `2δ = P · √(8/(17π)) √X e^{−X}`: (7.24a), with `√(8/(17π)) = 2√(2/(17π))`. -/
theorem two_delta_eq (d X v : ℝ) :
    2 * delta d X v =
      Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) * Real.exp (-(Ylow X v / 2)) *
        (Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X))) := by
  have h8 : Real.sqrt (8 / (17 * π)) = 2 * Real.sqrt (2 / (17 * π)) := by
    rw [show (8 : ℝ) / (17 * π) = 2 ^ 2 * (2 / (17 * π)) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  unfold delta
  rw [h8]
  ring

/-- `q(T) ≥ 0` and `q(T) ≤ 0.015/T` for `T ≥ 1894438.5122`. -/
theorem q_bounds {T : ℝ} (hT : 1894438.5122 ≤ T) :
    0 ≤ SchoenfeldZeroWeights.q T ∧ SchoenfeldZeroWeights.q T ≤ 0.015 / T := by
  have hTp : 0 < T := by linarith
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : π < 3.15 := Real.pi_lt_d2
  have h12 : 12 ≤ Real.log (T / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have e12 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e12]
    calc Real.exp 1 ^ 12 * (2 * π) ≤ 2.7182818286 ^ 12 * (2 * 3.15) :=
          mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le he.le 12) (by linarith)
            (by positivity) (by positivity)
      _ ≤ 1894438.5122 := by norm_num
      _ ≤ T := hT
  have hlT : 12 ≤ Real.log T := by
    have : Real.log (T / (2 * π)) ≤ Real.log T :=
      Real.log_le_log (by positivity) (div_le_self hTp.le (by linarith))
    linarith
  have hnum0 : 0 ≤ 0.137 + 0.443 / Real.log T := by
    have : 0 ≤ 0.443 / Real.log T := div_nonneg (by norm_num) (by linarith)
    linarith
  have hnum : 0.137 + 0.443 / Real.log T ≤ 0.18 := by
    have : 0.443 / Real.log T ≤ 0.443 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlT
    linarith
  have hden : 0 ≤ T * Real.log (T / (2 * π)) := mul_nonneg hTp.le (by linarith)
  unfold SchoenfeldZeroWeights.q
  constructor
  · exact div_nonneg hnum0 hden
  · calc (0.137 + 0.443 / Real.log T) / (T * Real.log (T / (2 * π)))
        ≤ 0.18 / (T * Real.log (T / (2 * π))) := div_le_div_of_nonneg_right hnum hden
      _ ≤ 0.18 / (T * 12) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left h12 hTp.le)
      _ = 0.015 / T := by
          rw [div_eq_div_iff (by positivity) hTp.ne']
          ring

/-- `0 ≤ R(T₂) ≤ X` for `T₂ = 17e^{vX}`, `0 < v ≤ 1`, `X ≥ 7`, where
`R(T) = 0.137 log T + 0.443 log log T + 1.588`. Schoenfeld's (7.13) amounts to `R(T₂) < 0.41X`. -/

theorem rosserR_bounds {X v : ℝ} (hX : 7 ≤ X) (hv : 0 < v) (hv1 : v ≤ 1) :
    0 ≤ rosserR 1.588 (17 * Real.exp (v * X)) ∧ rosserR 1.588 (17 * Real.exp (v * X)) ≤ X := by
  unfold rosserR
  have hlog : Real.log (17 * Real.exp (v * X)) = Real.log 17 + v * X := by
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have he3 : Real.exp 1 < 3 := SchoenfeldBalanceVNumeric.exp_one_bounds.2
  have he27 : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have hl1 : 1 ≤ Real.log 17 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith
  have hl3 : Real.log 17 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e3]
    have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he27.le 3
    nlinarith
  rw [hlog]
  have hXp : 0 < X := by linarith
  have hvX : 0 < v * X := by positivity
  have hvX1 : v * X ≤ X := by nlinarith
  have hL1 : 1 ≤ Real.log 17 + v * X := by linarith
  have hll0 : 0 ≤ Real.log (Real.log 17 + v * X) := Real.log_nonneg hL1
  have hll : Real.log (Real.log 17 + v * X) ≤ Real.log 17 + v * X - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  constructor
  · nlinarith
  · nlinarith

/-- `R₂(δ) ≤ 4 + 12.3δ` for `0 ≤ δ ≤ 0.01`. -/
theorem R2_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.01) : QuadraticZeroKernel.R2 δ ≤ 4 + 12.3 * δ := by
  have hsq : δ ^ 2 ≤ 0.01 * δ := by nlinarith
  have hcu : δ ^ 3 ≤ 0.0001 * δ := by nlinarith
  have hu : (1 + δ) ^ 3 + 1 ≤ 2 + 3.05 * δ := by nlinarith
  unfold QuadraticZeroKernel.R2
  have h0 : 0 ≤ (1 + δ) ^ 3 + 1 := by positivity
  nlinarith [mul_le_mul hu hu h0 (by linarith)]

/-- `1 ≤ G₂ ≤ 1 + 4δ` for `0 ≤ δ ≤ 0.01` and `0 ≤ 2πq(T) ≤ δ/10` ((7.20)). -/
theorem G2_bounds {δ T : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.01) (hq0 : 0 ≤ SchoenfeldZeroWeights.q T)
    (hq : 2 * π * SchoenfeldZeroWeights.q T ≤ δ / 10) : 1 ≤ G2 δ T ∧ G2 δ T ≤ 1 + 4 * δ := by
  have hR := R2_ge hδ
  have hR2 := R2_le hδ hδ1
  have hpq : 0 ≤ 2 * π * SchoenfeldZeroWeights.q T := by positivity
  have hR0 : 0 ≤ QuadraticZeroKernel.R2 δ := by linarith
  unfold G2
  constructor
  · rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · rw [div_le_iff₀ (by norm_num)]
    have hf : 1 + 2 * π * SchoenfeldZeroWeights.q T ≤ 1 + δ / 10 := by linarith
    nlinarith [mul_le_mul hR2 hf (by linarith) (by linarith)]

/-- `2X(1 − v) ≥ 9/4` when `v < v₁` and `X ≥ 13.4192` ((7.29), (7.41)). -/
theorem gap_of_lt_v1 {X v : ℝ} (hX : 13.4192 ≤ X) (hv : v < vj 1 X) :
    9 / 4 ≤ 2 * X * (1 - v) := by
  have hXp : 0 < X := by linarith
  have h1 := SchoenfeldBalanceVNumeric.one_sub_vj 1 X hXp
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hlog : 9 / 4 ≤ Real.log (17 / ((2 + 3 * 1) * π) * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have e9 : Real.exp (9 / 4) ^ 4 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have he3 : Real.exp 1 < 3 := SchoenfeldBalanceVNumeric.exp_one_bounds.2
    have h14 : Real.exp (9 / 4) ≤ 14 := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by norm_num)
      rw [e9]
      calc Real.exp 1 ^ 9 ≤ 3 ^ 9 := pow_le_pow_left₀ (Real.exp_pos 1).le he3.le 9
        _ ≤ 14 ^ 4 := by norm_num
    calc Real.exp (9 / 4) ≤ 14 := h14
      _ ≤ 17 / ((2 + 3 * 1) * 3.15) * 13.4192 := by norm_num
      _ ≤ 17 / ((2 + 3 * 1) * π) * X := by
          apply mul_le_mul _ hX (by norm_num) (by positivity)
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          linarith
  have hv1 : 1 - vj 1 X < 1 - v := by linarith
  rw [h1, div_lt_iff₀ (by positivity)] at hv1
  nlinarith

/-- The critical-line, left-contour, constant and `ψ − θ` terms are negligible. With
`1/δ² ≤ 72.25 e^{2X}`, `R₂ ≤ 4.1`, `X ≥ 1` and `log x ≥ 8X + 80`, their sum is at most
`10⁻⁴ x √X e^{−X}/(X + 1)`. -/
theorem small_terms_le {x X δ r : ℝ} (hx : 1 < x) (hX : 1 ≤ X) (hlog : 8 * X + 80 ≤ Real.log x)
    (hδ : 0 < δ) (hδT : 1 / δ ^ 2 ≤ 72.25 * Real.exp X ^ 2) (hr0 : 0 ≤ r) (hr : r ≤ 4.1) :
    r / δ ^ 2 * Real.sqrt x * (0.0463 / 14.13) + 150000 / (δ ^ 2 * Real.sqrt x) +
        Real.log (2 * π) + 6.5 * Real.sqrt x ≤
      1e-4 * x * (Real.sqrt X * Real.exp (-X) / (X + 1)) := by
  have hxp : 0 < x := by linarith
  have hw0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hww : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxp.le
  have hE0 : 0 < Real.exp X := Real.exp_pos X
  have hE1 : 1 ≤ Real.exp X := Real.one_le_exp (by linarith)
  have hwbig : Real.exp X ^ 4 * Real.exp 40 ≤ Real.sqrt x := by
    have e4 : Real.exp X ^ 4 * Real.exp 40 = Real.exp (4 * X + 40) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    rw [e4, Real.le_sqrt (Real.exp_pos _).le hxp.le]
    have e : Real.exp (4 * X + 40) ^ 2 = Real.exp (8 * X + 80) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    calc Real.exp (8 * X + 80) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlog
      _ = x := Real.exp_log hxp
  have he40 : 1.1e11 ≤ Real.exp 40 := by
    have e40 : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e40]
    have he : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
    calc (1.1e11 : ℝ) ≤ 2.7 ^ 40 := by norm_num
      _ ≤ Real.exp 1 ^ 40 := pow_le_pow_left₀ (by norm_num) he.le 40
  have hE4 : 1 ≤ Real.exp X ^ 4 := one_le_pow₀ hE1
  have hw1 : 1 ≤ Real.sqrt x := by nlinarith
  have hD1 : 1 ≤ 72.25 * Real.exp X ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hE1]
  have hDw : 1 ≤ 72.25 * Real.exp X ^ 2 * Real.sqrt x := by nlinarith
  have hlog2pi : Real.log (2 * π) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have : 2 * π < 2 * 3.15 := by have := Real.pi_lt_d2; linarith
    have he : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
    have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e2]
    nlinarith
  have hrδ : r / δ ^ 2 ≤ 4.1 * (72.25 * Real.exp X ^ 2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hr hδT (by positivity) (by norm_num)
  have t1 : r / δ ^ 2 * Real.sqrt x * (0.0463 / 14.13) ≤
      0.014 * (72.25 * Real.exp X ^ 2 * Real.sqrt x) := by
    have := mul_le_mul_of_nonneg_right hrδ hw0.le
    have h0 : 0 ≤ r / δ ^ 2 * Real.sqrt x := by positivity
    nlinarith
  have t2 : 150000 / (δ ^ 2 * Real.sqrt x) ≤ 150000 * (72.25 * Real.exp X ^ 2 * Real.sqrt x) := by
    have h1 : 150000 / (δ ^ 2 * Real.sqrt x) = 150000 * (1 / δ ^ 2) * (1 / Real.sqrt x) := by
      field_simp
    have h2 : 1 / Real.sqrt x ≤ Real.sqrt x := by
      rw [div_le_iff₀ hw0]
      nlinarith
    rw [h1]
    calc 150000 * (1 / δ ^ 2) * (1 / Real.sqrt x)
        ≤ 150000 * (72.25 * Real.exp X ^ 2) * Real.sqrt x :=
          mul_le_mul (mul_le_mul_of_nonneg_left hδT (by norm_num)) h2 (by positivity)
            (by positivity)
      _ = 150000 * (72.25 * Real.exp X ^ 2 * Real.sqrt x) := by ring
  have hsum : r / δ ^ 2 * Real.sqrt x * (0.0463 / 14.13) + 150000 / (δ ^ 2 * Real.sqrt x) +
      Real.log (2 * π) + 6.5 * Real.sqrt x ≤
        150009 * (72.25 * Real.exp X ^ 2 * Real.sqrt x) := by
    nlinarith
  -- Lower bound for the right side: `√X e^{−X}/(X + 1) ≥ e^{−2X} = 1/(e^X)²`.
  have hsX : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hX1 : X + 1 ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have hrhs : 1 / Real.exp X ^ 2 ≤ Real.sqrt X * Real.exp (-X) / (X + 1) := by
    rw [Real.exp_neg, div_le_div_iff₀ (by positivity) (by linarith)]
    have e : Real.sqrt X * (Real.exp X)⁻¹ * Real.exp X ^ 2 = Real.sqrt X * Real.exp X := by
      field_simp
    rw [e, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hsX hE0.le]

  have key : 150009 * 72.25 * Real.exp X ^ 4 ≤ 1e-4 * Real.sqrt x := by
    nlinarith
  calc r / δ ^ 2 * Real.sqrt x * (0.0463 / 14.13) + 150000 / (δ ^ 2 * Real.sqrt x) +
        Real.log (2 * π) + 6.5 * Real.sqrt x
      ≤ 150009 * (72.25 * Real.exp X ^ 2 * Real.sqrt x) := hsum
    _ ≤ 1e-4 * Real.sqrt x ^ 2 * (1 / Real.exp X ^ 2) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right key hw0.le
        nlinarith
    _ ≤ 1e-4 * x * (Real.sqrt X * Real.exp (-X) / (X + 1)) := by
        rw [hww]
        exact mul_le_mul_of_nonneg_left hrhs (by positivity)

end TernaryGoldbach.RSBounds.SchoenfeldBalanceTail
