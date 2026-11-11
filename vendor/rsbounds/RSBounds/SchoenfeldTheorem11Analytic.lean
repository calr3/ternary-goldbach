import RSBounds.SchoenfeldBalanceTail
import RSBounds.PsiThetaElementary
import RSBounds.Schoenfeld1976Targets

/-!
# Schoenfeld (1976), Theorem 11 for `x ≥ e^{1737}`

Given the finite RH verification through height `1894438.5122`, for `x ≥ e^{1737}`:
`|ψ(x) − x| < x ε₀(x)`, `|θ(x) − x| < x ε₀(x)`, and `θ(x) − x ≤ ψ(x) − x < x ε₀(x)`,
with `ε₀(x) = √(8/(17π)) X^{1/2} e^{−X}`, `X = √(log x / R)`, `R = 9.645908801`.

This is the range that the paper's analytic argument covers: p. 348 concludes that (7.2) and
(7.3) hold for all `x ≥ e^{1737}`. The smaller ranges of (7.2)–(7.4) use the paper's table and
finite checks and are not covered here, so `Goals.Schoenfeld1976.PsiTheorem11`,
`ThetaTheorem11` and `PsiUpperTheorem11` remain open.

The parameters are Schoenfeld's: `v` with `k(v) = 1` (7.27), `T₂ = 17e^{vX}` (7.5) and `δ` from
(7.24a). The analytic input is the exact formal envelope
`SchoenfeldQuadraticLeft.psi_error_le_envelope`; `SchoenfeldBalanceMain.allowances_le` is the
analogue of (7.26), and `SchoenfeldBalanceTail` replaces (7.31)–(7.42).
-/

open Real Set

namespace TernaryGoldbach.RSBounds.SchoenfeldTheorem11Analytic

open SchoenfeldBalanceAlgebra SchoenfeldBalanceV SchoenfeldBalanceMain SchoenfeldBalanceTail

/-- The split parameter and the facts about it that the proof uses ((7.27)–(7.30)). -/
theorem split_facts {X : ℝ} (hX : 13.4192 ≤ X) :
    ∃ v, vj 0 X < v ∧ k SchoenfeldWeightedZeros.d X v = 1 ∧ 0.85 ≤ v ∧ v < 1 ∧
      9 / 4 ≤ 2 * X * (1 - v) ∧ 1 < 2 * v ^ 2 := by
  have hX41 : (13.41 : ℝ) ≤ X := by linarith
  obtain ⟨v, ⟨hv0, hv1⟩, hk⟩ := SchoenfeldBalanceVNumeric.exists_split_parameter hX41
  have hv85 : 0.85 ≤ v := by
    have h := SchoenfeldBalanceVNumeric.one_sub_v0_le hX41
    have : (4 : ℝ) / (2 * 13.41) ≤ 0.15 := by norm_num
    linarith
  have hgap : 9 / 4 ≤ 2 * X * (1 - v) := gap_of_lt_v1 hX hv1
  have hXp : 0 < X := by linarith
  refine ⟨v, hv0, hk, hv85, ?_, hgap, ?_⟩
  · nlinarith
  · nlinarith

/-- `0.38 ≤ √(8/(17π)) ≤ 0.4`. -/
theorem c0_bounds : 0.38 ≤ Real.sqrt (8 / (17 * π)) ∧ Real.sqrt (8 / (17 * π)) ≤ 0.4 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    have := Real.pi_lt_d2
    nlinarith
  · rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]
    have := Real.pi_gt_three
    nlinarith

/-- The closing arithmetic, with every analytic quantity abstracted. Here `Ψ = |ψ(x) − x|`,
`W = 6.5√x`, `S₁, S₂, S₃` are the critical-line, left-contour and constant terms, `M` the
weighted allowances, `G = G₂`, `Q = G₀/G₁`, `B` the boundary factor, `u = s/(X + 1)`. -/
theorem close_arith {x u s c0 d a P δ G Q B M Ψ W S1 S2 S3 : ℝ}
    (henv : Ψ ≤ S1 + x * M + S2 + S3 + δ * x)
    (hsmall : S1 + S2 + S3 + W ≤ 1e-4 * x * u)
    (hall : M ≤ G * δ + B * (G * (1 + Q)))
    (hxp : 0 < x) (hG2lo : 1 ≤ G) (hG2hi : G ≤ 1 + 4 * δ) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 1)
    (hB : B ≤ 2 / 17 * s ^ 2) (hBnn : 0 ≤ B) (hδpos : 0 < δ) (hδle : δ ≤ 0.2 * s)
    (hδ1 : δ ≤ 0.001) (h2δ : 2 * δ = P * (c0 * s)) (hPle : P ≤ 1 - a / 4) (hs0 : 0 < s)
    (hc0 : 0.38 ≤ c0) (hu0 : 0 < u) (hs2u : s ^ 2 ≤ 2.95e-4 * u)
    (hau : a / 4 * (c0 * s) = (1 - d) * c0 / 4 * u) (hd1 : d ≤ 0.996) :
    Ψ + W < x * (c0 * s) := by
  have hGQ : G * (1 + Q) ≤ 2.01 := by
    have : G * (1 + Q) ≤ (1 + 4 * δ) * 2 :=
      mul_le_mul hG2hi (by linarith) (by linarith) (by linarith)
    linarith
  have hGQ0 : 0 ≤ G * (1 + Q) := mul_nonneg (by linarith) (by linarith)
  have hBGQ : B * (G * (1 + Q)) ≤ 2 / 17 * s ^ 2 * 2.01 :=
    mul_le_mul hB hGQ hGQ0 (by positivity)
  have hδsq : δ ^ 2 ≤ 0.04 * s ^ 2 := by
    have := mul_self_le_mul_self hδpos.le hδle
    linarith
  have hGδ : G * δ ≤ (1 + 4 * δ) * δ := mul_le_mul_of_nonneg_right hG2hi hδpos.le
  have hmain : G * δ + B * (G * (1 + Q)) + δ ≤ P * (c0 * s) + 0.41 * s ^ 2 := by
    linarith [sq_nonneg s]
  have hPc : P * (c0 * s) ≤ c0 * s - a / 4 * (c0 * s) := by
    have := mul_le_mul_of_nonneg_right hPle (by positivity : (0 : ℝ) ≤ c0 * s)
    linarith
  have hK : 3.8e-4 ≤ (1 - d) * c0 / 4 := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - d - 0.004)
      (by linarith : (0 : ℝ) ≤ c0 - 0.38)]
  have hxM : x * M ≤ x * (G * δ + B * (G * (1 + Q))) := mul_le_mul_of_nonneg_left hall hxp.le
  have hxu : 0 < x * u := mul_pos hxp hu0
  have h1 : x * (G * δ + B * (G * (1 + Q)) + δ) ≤ x * (P * (c0 * s) + 0.41 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hmain hxp.le
  have h2 : x * (P * (c0 * s) + 0.41 * s ^ 2) ≤
      x * (c0 * s - (1 - d) * c0 / 4 * u + 0.41 * (2.95e-4 * u)) := by
    apply mul_le_mul_of_nonneg_left _ hxp.le
    linarith
  have h3 : x * u * 3.8e-4 ≤ x * u * ((1 - d) * c0 / 4) := mul_le_mul_of_nonneg_left hK hxu.le
  linarith

/-- The main estimate, with room left for `ψ(x) − θ(x) ≤ 6.5√x`. -/
theorem core (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x < x * Goals.Schoenfeld1976.epsilon0 x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 1737 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hx
  obtain ⟨X, hXdef⟩ : ∃ X, X = Real.sqrt (Real.log x / 9.645908801) := ⟨_, rfl⟩
  have hX : 13.4192 ≤ X := by rw [hXdef]; exact SchoenfeldBalanceHeight.X_ge_of_log_ge hlogx
  have hXp : 0 < X := by linarith
  have hX2 : X ^ 2 = Real.log x / 9.645908801 := by rw [hXdef]; exact X_sq hx1.le
  have hε : Goals.Schoenfeld1976.epsilon0 x =
      Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X)) := by
    rw [hXdef]
    unfold Goals.Schoenfeld1976.epsilon0 Goals.Schoenfeld1976.X
    ring
  -- The split parameter `v` (7.27)–(7.30) and the split height `T₂ = 17e^{vX}`.
  obtain ⟨v, hv0, hk, hv85, hvlt1, hgap, hv2⟩ := split_facts hX
  have hv : 0 < v := by linarith
  have hv8 : 0.8 ≤ v := by linarith
  have hd0 := SchoenfeldBalanceVNumeric.d_nonneg
  have hd1 : SchoenfeldWeightedZeros.d ≤ 0.996 := d_le
  have h0 : 0 < G0 SchoenfeldWeightedZeros.d X v := by unfold G0; positivity
  have h1 : 0 < G1 SchoenfeldWeightedZeros.d X v := G1_pos hXp hd0 hv hv2
  have hT : (1894438.5122 : ℝ) ≤ 17 * Real.exp (v * X) :=
    SchoenfeldBalanceHeight.split_height_ge hX hv0.le
  have hTp : 0 < 17 * Real.exp (v * X) := by positivity
  -- `P = (G₀G₁)^{1/4}e^{−Y/2} ≤ 1 − a/4` with `a = (1 − d)/(X + 1)`.
  have hP4 : (Real.sqrt (Real.sqrt (G0 SchoenfeldWeightedZeros.d X v *
      G1 SchoenfeldWeightedZeros.d X v)) * Real.exp (-(Ylow X v / 2))) ^ 4 ≤
        1 - (1 - SchoenfeldWeightedZeros.d) / (X + 1) := by
    rw [P_pow_four h0 h1]
    exact P4_le hXp hv8 hvlt1.le hgap hd0 (by linarith)
  have h2δ := two_delta_eq SchoenfeldWeightedZeros.d X v
  obtain ⟨P, hPdef⟩ : ∃ P, P = Real.sqrt (Real.sqrt (G0 SchoenfeldWeightedZeros.d X v *
      G1 SchoenfeldWeightedZeros.d X v)) * Real.exp (-(Ylow X v / 2)) := ⟨_, rfl⟩
  rw [← hPdef] at hP4 h2δ
  obtain ⟨a, hadef⟩ : ∃ a, a = (1 - SchoenfeldWeightedZeros.d) / (X + 1) := ⟨_, rfl⟩
  rw [← hadef] at hP4
  have ha0 : 0 ≤ a := by rw [hadef]; exact div_nonneg (by linarith) (by linarith)
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one (by linarith)]; linarith
  have hPle : P ≤ 1 - a / 4 := le_one_sub_quarter ha0 ha1 hP4
  have hP1 : P ≤ 1 := by linarith
  -- `δ`, `s = √X e^{−X}` and `c₀ = √(8/(17π))`, so that `2δ = P c₀ s` and `ε₀ = c₀ s`.
  have hδpos := delta_pos hXp h0 h1
  have hdT := delta_mul_split_height hXp h0 h1 hk
  have hR := rosserR_bounds (by linarith : (7 : ℝ) ≤ X) hv hvlt1.le
  obtain ⟨hq0, hqT⟩ := SchoenfeldBalanceTail.q_bounds hT
  have hall := allowances_le hXp hv hv2 h0 h1 hk hq0 hR.1
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = delta SchoenfeldWeightedZeros.d X v := ⟨_, rfl⟩
  rw [← hδdef] at h2δ hδpos hdT hall
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt X * Real.exp (-X) := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = Real.sqrt (8 / (17 * π)) := ⟨_, rfl⟩
  rw [← hsdef, ← hc0def] at h2δ hε
  have hs0 : 0 < s := by
    rw [hsdef]
    have := Real.sqrt_pos.mpr hXp
    positivity
  have hsX : s * (X + 1) ≤ 2.95e-4 := by rw [hsdef]; exact s_mul_le hX
  have hs_small : s ≤ 2.95e-4 := by
    have : 0 ≤ s * X := mul_nonneg hs0.le hXp.le
    linarith
  have hc0lo : 0.38 ≤ c0 := by rw [hc0def]; exact c0_bounds.1
  have hc0hi : c0 ≤ 0.4 := by rw [hc0def]; exact c0_bounds.2
  have hc0pos : 0 < c0 := by linarith
  have hδle : δ ≤ 0.2 * s := by
    have : P * (c0 * s) ≤ 1 * (0.4 * s) :=
      mul_le_mul hP1 (mul_le_mul_of_nonneg_right hc0hi hs0.le) (by positivity) (by norm_num)
    linarith
  have hδ1 : δ ≤ 0.001 := by linarith
  have hδ2 : 2 * δ < 1 := by linarith
  -- `δ T₂ ≥ 2` ((7.21) with `G₀ ≤ G₁`), hence `1/δ² ≤ 72.25 e^{2X}`.
  have hG01 := G0_le_G1 hXp hv hvlt1.le hv2 hd0
  have hδT : 2 ≤ δ * (17 * Real.exp (v * X)) := by
    rw [hdT]
    have : 1 ≤ Real.sqrt (G1 SchoenfeldWeightedZeros.d X v / G0 SchoenfeldWeightedZeros.d X v) := by
      rw [Real.le_sqrt (by norm_num) (by positivity), one_pow, le_div_iff₀ h0, one_mul]
      exact hG01
    linarith
  have hTX : 17 * Real.exp (v * X) ≤ 17 * Real.exp X := by
    have : v * X ≤ X := mul_le_of_le_one_left hXp.le hvlt1.le
    have := Real.exp_le_exp.mpr this
    linarith
  have hδinv : 1 / δ ^ 2 ≤ 72.25 * Real.exp X ^ 2 := by
    have h2 : 2 ≤ δ * (17 * Real.exp X) :=
      le_trans hδT (mul_le_mul_of_nonneg_left hTX hδpos.le)
    rw [div_le_iff₀ (by positivity)]
    linarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) h2]
  -- `2πq(T₂) ≤ δ/10`, hence `1 ≤ G₂ ≤ 1 + 4δ`.
  have hq : 2 * π * SchoenfeldZeroWeights.q (17 * Real.exp (v * X)) ≤ δ / 10 := by
    have h1T : 1 / (17 * Real.exp (v * X)) ≤ δ / 2 := by
      rw [div_le_div_iff₀ hTp (by norm_num)]
      linarith
    have hpi : π < 3.15 := Real.pi_lt_d2
    calc 2 * π * SchoenfeldZeroWeights.q (17 * Real.exp (v * X))
        ≤ 2 * π * (0.015 / (17 * Real.exp (v * X))) :=
          mul_le_mul_of_nonneg_left hqT (by positivity)
      _ = 2 * π * 0.015 * (1 / (17 * Real.exp (v * X))) := by ring
      _ ≤ 2 * 3.15 * 0.015 * (δ / 2) :=
          mul_le_mul (by linarith) h1T (by positivity) (by norm_num)
      _ ≤ δ / 10 := by linarith
  obtain ⟨hG2lo, hG2hi⟩ := G2_bounds hδpos.le (by linarith) hq0 hq
  -- The envelope, with `log x / R = X²`.
  have hwin := window hXp hv hvlt1.le hv2
  have henv := SchoenfeldQuadraticLeft.psi_error_le_envelope hRH hx1 hδpos hδ2 hT
    (by rw [← hX2]; exact hwin.1) (by rw [← hX2]; exact hwin.2)
  unfold SchoenfeldQuadraticEnvelope.envelope at henv
  rw [← hX2] at henv
  -- The negligible terms.
  have hR2 : QuadraticZeroKernel.R2 δ ≤ 4.1 := by
    have := R2_le hδpos.le (by linarith)
    linarith
  have hR20 : 0 ≤ QuadraticZeroKernel.R2 δ := by
    have := R2_ge hδpos.le
    linarith
  have hlog8 : 8 * X + 80 ≤ Real.log x := by
    have e : Real.log x = 9.645908801 * X ^ 2 := by rw [hX2]; ring
    have : 13.4192 * X ≤ X * X := mul_le_mul_of_nonneg_right hX hXp.le
    linarith

  have hsmall := small_terms_le hx1 (by linarith) hlog8 hδpos hδinv hR20 hR2
  rw [← hsdef] at hsmall
  -- The boundary term: `B ≤ (2/17) s²`, from `R(T₂) ≤ X` and `Y ≥ 0`.
  have hY0 : 0 ≤ Ylow X v := by unfold Ylow; positivity
  have hEY : Real.exp (-Ylow X v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs2 : s ^ 2 = X * Real.exp (-(2 * X)) := by
    rw [hsdef, mul_pow, Real.sq_sqrt hXp.le, ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * -X = -(2 * X) by push_cast; ring]
  have hB : 2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
      Real.exp (-(2 * X)) / 17 ≤ 2 / 17 * s ^ 2 := by
    rw [hs2]
    have hRE : rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) ≤ X * 1 :=
      mul_le_mul hR.2 hEY (Real.exp_pos _).le hXp.le
    have hE2 : 0 ≤ Real.exp (-(2 * X)) := (Real.exp_pos _).le
    calc 2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
          Real.exp (-(2 * X)) / 17
        = 2 / 17 * (rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
          Real.exp (-(2 * X))) := by ring
      _ ≤ 2 / 17 * (X * 1 * Real.exp (-(2 * X))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRE hE2) (by norm_num)
      _ = 2 / 17 * (X * Real.exp (-(2 * X))) := by ring
  have hBnn : 0 ≤ 2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
      Real.exp (-(2 * X)) / 17 := by
    have := hR.1
    positivity
  have hQ : G0 SchoenfeldWeightedZeros.d X v / G1 SchoenfeldWeightedZeros.d X v ≤ 1 :=
    (div_le_one h1).mpr hG01
  have hQ0 : 0 ≤ G0 SchoenfeldWeightedZeros.d X v / G1 SchoenfeldWeightedZeros.d X v := by
    positivity
  -- The slack `a/4`: with `u = s/(X + 1)`, `(a/4)c₀ s = ((1 − d)c₀/4) u` and
  -- `s² ≤ 2.95·10⁻⁴ u`.
  obtain ⟨u, hudef⟩ : ∃ u, u = s / (X + 1) := ⟨_, rfl⟩
  rw [← hudef] at hsmall
  have hX1 : (0 : ℝ) < X + 1 := by linarith
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hs2u : s ^ 2 ≤ 2.95e-4 * u := by
    have e : s ^ 2 = u * (s * (X + 1)) := by
      rw [hudef, div_mul_eq_mul_div, eq_div_iff hX1.ne']
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsX hu0.le
    linarith
  have hau : a / 4 * (c0 * s) = (1 - SchoenfeldWeightedZeros.d) * c0 / 4 * u := by
    rw [hadef, hudef]
    ring
  rw [hε]
  exact close_arith henv hsmall hall hxp hG2lo hG2hi hQ0 hQ hB hBnn hδpos hδle hδ1 h2δ hPle
    hs0 hc0lo hu0 hs2u hau hd1

/-- **Theorem 11, (7.2), for `x ≥ e^{1737}`.** -/
theorem psi_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    |Chebyshev.psi x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  have h := core hRH hx
  have : 0 ≤ 6.5 * Real.sqrt x := by positivity
  linarith

/-- **Theorem 11, (7.3), for `x ≥ e^{1737}`**, using `0 ≤ ψ(x) − θ(x) ≤ 6.5√x`
(`PsiThetaElementary.psi_sub_theta_le`) in place of the paper's 1.43√x. -/
theorem theta_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  have h := core hRH hx
  have hx5 : (100000 : ℝ) ≤ x := by
    have : (100000 : ℝ) ≤ Real.exp 1737 := by
      have h1 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1737)
      norm_num at h1
      linarith
    linarith

  have hpt := PsiThetaElementary.psi_sub_theta_le hx5
  have htp := Chebyshev.theta_le_psi x
  have habs : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Chebyshev.psi x - x)]
    · linarith [le_abs_self (Chebyshev.psi x - x)]
  linarith

/-- **Theorem 11, (7.4) as established on p. 349, for `x ≥ e^{1737}`.** -/
theorem psi_upper (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * Goals.Schoenfeld1976.epsilon0 x := by
  refine ⟨by linarith [Chebyshev.theta_le_psi x], ?_⟩
  exact lt_of_le_of_lt (le_abs_self _) (psi_lt hRH hx)

end TernaryGoldbach.RSBounds.SchoenfeldTheorem11Analytic
