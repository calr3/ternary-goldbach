import TernaryGoldbach.MinorArcs.TypeIILarge
import TernaryGoldbach.MinorArcs.SecondParams
import TernaryGoldbach.MinorArcs.FirstChoiceTypeII

/-!
# Type II for `q > y` at the second parameters: reduction to functions of `L = log T`

Case (a1) of [B, §6.3.2]: `T/6 < q`, `16q ≤ x/U` (our `θ = 8`), via `typeII_638`. With
`u = 6q/T ≥ 1`, `ℓ = log u`, every term is bounded by its value at `u = 1` (up to a factor
`1.03` in one place) times `T^{5/2}`:
`|S_{II}| ≤ (√(12 F₀ X₀ B₀) + SEC(L)) T^{5/2}` (`typeII_a1`), where
`F₀ = 1.7882 log(L - 1.7917) + 0.9549` bounds `q/φ(q)` (Lemma C.2.2, `e^γ ≤ 1.7882`),
`X₀ = (L - 8.09) + (L - 1.0986)(log(L - 6.0119) - 0.732)` bounds `log(x/UW₀) + Φ` and
`B₀ = 0.15107(L - 8.09) + 0.027` bounds `κ₆/4 · log(x/UW₀) + κ₀ζ³-term`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-! ### Numerical constants -/

theorem log6_ge : (1.7917 : ℝ) ≤ Real.log 6 := by
  have := le_log_num (z := 6) 1 0.7917 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log3_ge : (1.0986 : ℝ) ≤ Real.log 3 := by
  have := le_log_num (z := 3) 1 0.0986 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log3_le : Real.log 3 ≤ 1.0987 := by
  have := log_le_num (z := 3) 1 0.0987 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_3266_ge : (8.09 : ℝ) ≤ Real.log 3266.64 := by
  have := le_log_num (z := 3266.64) 8 0.09 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_408_ge : (6.0119 : ℝ) ≤ Real.log 408.33 := by
  have := le_log_num (z := 408.33) 6 0.0119 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_1224_ge : (7.1106 : ℝ) ≤ Real.log 1224.99 := by
  have := le_log_num (z := 1224.99) 7 0.1106 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_408326_ge : (6.0119 : ℝ) ≤ Real.log 408.326 := by
  have := le_log_num (z := 408.326) 6 0.0119 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log8_le : Real.log 8 ≤ 2.0795 := by
  have := log_le_num (z := 8) 2 0.0795 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_8_3_le : Real.log (8 / 3) ≤ 0.9809 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  linarith [log8_le, log3_ge]

theorem log_8_le : Real.log 8.00008 ≤ 2.0795 := by
  have := log_le_num (z := 8.00008) 2 0.0795 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log8_ge : (2.0794 : ℝ) ≤ Real.log 8 := by
  have := le_log_num (z := 8) 2 0.0794 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem loglog8_ge : (0.732 : ℝ) ≤ Real.log (Real.log 8) := by
  have h := log8_ge
  have h2 : (0.732 : ℝ) ≤ Real.log 2.0794 := by
    have := le_log_num (z := 2.0794) 0 0.732 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at this ⊢; linarith
  exact h2.trans (Real.log_le_log (by norm_num) h)

theorem log_1e6_ge : (13.81 : ℝ) ≤ Real.log 1e6 := by
  have := le_log_num (z := 1e6) 13 0.81 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_1381_ge : (2.625 : ℝ) ≤ Real.log 13.81 := by
  have := le_log_num (z := 13.81) 2 0.625 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem pi_two_div_sq_le : 2 / π ^ 2 ≤ 0.2026425 := by
  have := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-! ### `κ₁` and simple parameter facts -/

/-- `κ₁ ≤ 0.24083` at the second parameters. -/
theorem kap1_le_second {T : ℝ} (hT : 6e6 ≤ T) : kap1 (T ^ 3) (U2 T) (V2 T) ≤ 0.24083 := by
  have hT0 : 0 < T := by linarith
  have hU := U2_ge' hT
  have hV := V2_ge' hT
  have hz := zeta3_le
  have hz0 := zeta3_nonneg
  have h1 : √(T ^ 3 / V2 T) ≤ 1.73206 * T := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
    have : T ^ 3 = T * T ^ 2 := by ring
    nlinarith [sq_nonneg T]
  have h2 : zeta3 * √(T ^ 3 / V2 T) / U2 T ≤ 27 * (1.73206 * T) / (1224.99 * T) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have := mul_le_mul hz h1 (Real.sqrt_nonneg _) (by norm_num)
    have : 0 ≤ zeta3 * √(T ^ 3 / V2 T) := by positivity
    nlinarith
  have h3 : 27 * (1.73206 * T) / (1224.99 * T) ≤ 0.0381766 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  unfold kap1
  have := pi_two_div_sq_le
  linarith

/-! ### The `ℓ = log(6q/T)` lemmas -/

/-- `(F₀ + 0.1296 ℓ)(X₀ + G ℓ) ≤ F₀ X₀ e^ℓ` for `F₀ ≥ 1`, `X₀ ≥ 14 G`, `G, ℓ ≥ 0`. -/
theorem decay_FX {F₀ X₀ G ℓ : ℝ} (hF : 1 ≤ F₀) (hX : 14 * G ≤ X₀) (hG : 0 ≤ G) (hℓ : 0 ≤ ℓ) :
    (F₀ + 0.1296 * ℓ) * (X₀ + G * ℓ) ≤ F₀ * X₀ * rexp ℓ := by
  have he := Real.quadratic_le_exp_of_nonneg hℓ
  have hX0 : 0 ≤ X₀ := by linarith
  have h1 : F₀ + 0.1296 * ℓ ≤ F₀ * (1 + 0.1296 * ℓ) := by nlinarith
  have h2 : X₀ + G * ℓ ≤ X₀ * (1 + ℓ / 14) := by nlinarith
  calc (F₀ + 0.1296 * ℓ) * (X₀ + G * ℓ) ≤ F₀ * (1 + 0.1296 * ℓ) * (X₀ * (1 + ℓ / 14)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = F₀ * X₀ * ((1 + 0.1296 * ℓ) * (1 + ℓ / 14)) := by ring
    _ ≤ F₀ * X₀ * rexp ℓ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg hℓ hℓ]

/-- `(c + ℓ)²(L' + ℓ) ≤ 1.03 c² L' e^ℓ` for `c = 2.0795`, `L' ≥ 16.5`, `ℓ ≥ 0`. -/
theorem decay_M3 {L' ℓ : ℝ} (hL : 16.5 ≤ L') (hℓ : 0 ≤ ℓ) :
    (2.0795 + ℓ) ^ 2 * (L' + ℓ) ≤ 1.03 * 2.0795 ^ 2 * L' * rexp ℓ := by
  have he := Real.sum_le_exp_of_nonneg hℓ 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have h3 : 0 ≤ ℓ ^ 3 := by positivity
  have h2 : 0 ≤ ℓ ^ 2 := by positivity
  have hL0 : 0 ≤ L' := by linarith
  nlinarith [mul_nonneg hL0 hℓ, mul_nonneg hL0 h2, mul_nonneg hL0 h3, mul_le_mul_of_nonneg_left he
    (by positivity : (0 : ℝ) ≤ 1.03 * 2.0795 ^ 2 * L')]

/-- `(2/3)(a√a - b√b) ≤ √a (a - b)` for `0 ≤ b ≤ a`. -/
theorem three_halves_sub_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    2 / 3 * (a * √a - b * √b) ≤ √a * (a - b) := by
  have ha : 0 ≤ a := hb.trans hab
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hs : √b ≤ √a := Real.sqrt_le_sqrt hab
  have h0 : 0 ≤ √b := Real.sqrt_nonneg _
  -- `a√a - b√b = (√a - √b)(a + √a√b + b)` and `a + √(ab) + b ≤ 3a/2 + ... `
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (sq_nonneg (√a - √b)), mul_nonneg h0 (sub_nonneg.2 hs),
    mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 hs)]

/-! ### Definitions of the bounding functions -/

noncomputable def a1F0 (L : ℝ) : ℝ := 1.7882 * Real.log (L - 1.7917) + 0.9549
noncomputable def a1G (L : ℝ) : ℝ := Real.log (L - 6.0119) - 0.732
noncomputable def a1X0 (L : ℝ) : ℝ := (L - 8.09) + (L - 1.0986) * a1G L
noncomputable def a1B0 (L : ℝ) : ℝ := 0.15107 * (L - 8.09) + 0.027
noncomputable def a1F2 (L : ℝ) : ℝ := 1.7882 * Real.log (2 * L) + 0.9549

/-- The secondary terms of case (a1), divided by `T^{5/2}`. -/
noncomputable def a1SEC (L : ℝ) : ℝ :=
  4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) +
    0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) +
    1.73206 * (√(L - 1.0986) + 1 / √(L - 1.0986)) + 0.028572 * √(2 * L - 7.1106))) +
  8 * 1.4262 * 1.73206 * √(0.24083 * 0.50001) +
  4 * √(0.24083 * a1F2 L / 2) * (0.057144 + 0.13418 * √(2 * L))

/-! ### `q/φ(q)` for `q ≥ 10⁶` -/

theorem div_totient_le_large {q : ℕ} (hq : (1e6 : ℝ) ≤ q) :
    (q : ℝ) / Nat.totient q ≤ 1.7882 * Real.log (Real.log q) + 0.9549 := by
  have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  have h1 := Prelim.div_totient_lt hq1 (by linarith) le_rfl
  have hl : 13.81 ≤ Real.log q := log_1e6_ge.trans (Real.log_le_log (by norm_num) hq)
  have hll : 2.625 ≤ Real.log (Real.log q) := log_1381_ge.trans (Real.log_le_log (by norm_num) hl)
  have hg := exp_gamma_le_sharp
  have h2 : 2.50637 / Real.log (Real.log q) ≤ 0.9549 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : rexp eulerMascheroniConstant * Real.log (Real.log q) ≤
      1.7882 * Real.log (Real.log q) := mul_le_mul_of_nonneg_right hg (by linarith)
  linarith

/-! ### The main term -/

set_option maxHeartbeats 4000000 in
/-- The main term of `typeII_638` (with `θ = 8`) at the second parameters, for `T/6 < q`,
`16q ≤ x/U`: `≤ √(12 F₀ X₀ B₀) T^{5/2}`. -/
theorem a1_M1_le {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : T / 6 < q)
    (hq16 : 16 * (q : ℝ) ≤ T ^ 3 / U2 T) :
    4 * T ^ 3 * √(1 / 4 / (2 * Nat.totient q)) *
      √((Real.log (T ^ 3 / (U2 T * (2 * 8 * q))) + Real.log (2 * q) *
        (Real.log (Real.log (T ^ 3 / U2 T / (2 * q))) -
          Real.log (Real.log (2 * 8 * q / (2 * q))))) *
        (0.15107 * Real.log (T ^ 3 / (U2 T * (2 * 8 * q))) +
          2 * zeta3 * √(T ^ 3 / (2 * 8 * q)) / U2 T)) ≤
    √(12 * a1F0 (Real.log T) * a1X0 (Real.log T) * a1B0 (Real.log T)) * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have hU := U2_ge' hT
  have hU0 : (0 : ℝ) < U2 T := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  -- `u = 6q/T ≥ 1`, `ℓ = log u`.
  set u := 6 * q / T with hudef
  have hu1 : 1 ≤ u := by rw [hudef, le_div_iff₀ hT0]; linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log u with hℓdef
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hu1
  have hexp : rexp ℓ = u := Real.exp_log hu0
  have hqu : (q : ℝ) = T / 6 * u := by rw [hudef]; field_simp
  have hlogq : Real.log q = Real.log (T / 6) + ℓ := by
    rw [hqu, Real.log_mul (by positivity) hu0.ne']
  have hlT6 : Real.log (T / 6) = L - Real.log 6 := Real.log_div hT0.ne' (by norm_num)
  have hlT6' : 13.81 ≤ Real.log (T / 6) :=
    log_1e6_ge.trans (Real.log_le_log (by norm_num) (by linarith))
  have hl6 := log6_ge
  -- `Λ`.
  set Λ := Real.log (T ^ 3 / (U2 T * (2 * 8 * q)))
  have hΛ0 : 0 ≤ Λ := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity), one_mul]
    rw [le_div_iff₀ hU0] at hq16; nlinarith
  have hΛ : Λ ≤ L - 8.09 - ℓ := by
    have h1 : T ^ 3 / (U2 T * (2 * 8 * q)) ≤ T / (3266.64 * u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hqu]
      have : 3266.64 * T ^ 2 * u ≤ U2 T * (2 * 8 * (T / 6 * u)) := by
        have := mul_le_mul_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 16 * (T / 6 * u))
        nlinarith
      have hT3 : T ^ 3 = T * T ^ 2 := by ring
      rw [hT3]; nlinarith [mul_le_mul_of_nonneg_left this hT0.le]
    have h2 : Real.log (T / (3266.64 * u)) = L - Real.log 3266.64 - ℓ := by
      rw [Real.log_div hT0.ne' (by positivity), Real.log_mul (by norm_num) hu0.ne']; ring
    have : Λ ≤ Real.log (T / (3266.64 * u)) := Real.log_le_log (by positivity) h1
    linarith [log_3266_ge]
  -- `Φ`.
  have h8 : 2 * 8 * (q : ℝ) / (2 * q) = 8 := by field_simp
  have hl2q : Real.log (2 * q) = L - Real.log 3 + ℓ := by
    have : (2 : ℝ) * q = T / 3 * u := by rw [hqu]; ring
    rw [this, Real.log_mul (by positivity) hu0.ne', Real.log_div hT0.ne' (by norm_num)]
  have hl3 := log3_ge
  have hl2q0 : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  have hin8 : 8 ≤ T ^ 3 / U2 T / (2 * q) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hinU : T ^ 3 / U2 T / (2 * q) ≤ T / (408.33 * u) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), hqu]
    have : 408.33 * T ^ 2 * u ≤ U2 T * (2 * (T / 6 * u)) := by
      have := mul_le_mul_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 2 * (T / 6 * u))
      nlinarith
    have hT3 : T ^ 3 = T * T ^ 2 := by ring
    rw [hT3]; nlinarith [mul_le_mul_of_nonneg_left this hT0.le]
  have hl8 := log8_ge
  have hlin : Real.log (T ^ 3 / U2 T / (2 * q)) ≤ L - 6.0119 := by
    have h1 := Real.log_le_log (by positivity) hinU
    have h2 : Real.log (T / (408.33 * u)) = L - Real.log 408.33 - ℓ := by
      rw [Real.log_div hT0.ne' (by positivity), Real.log_mul (by norm_num) hu0.ne']; ring
    linarith [log_408_ge]
  have hlin0 : 2.0794 ≤ Real.log (T ^ 3 / U2 T / (2 * q)) :=
    hl8.trans (Real.log_le_log (by norm_num) hin8)
  set G := a1G L
  have hGdef : G = Real.log (L - 6.0119) - 0.732 := rfl
  have hll8 := loglog8_ge
  have hbr0 : 0 ≤ Real.log (Real.log (T ^ 3 / U2 T / (2 * q))) - Real.log (Real.log 8) :=
    sub_nonneg.2 (Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hin8))
  have hbr : Real.log (Real.log (T ^ 3 / U2 T / (2 * q))) - Real.log (Real.log 8) ≤ G := by
    have := Real.log_le_log (by linarith) hlin
    rw [hGdef]; linarith
  have hG0 : 0 ≤ G := hbr0.trans hbr
  set Φ := Real.log (2 * q) * (Real.log (Real.log (T ^ 3 / U2 T / (2 * q))) -
    Real.log (Real.log (2 * 8 * q / (2 * q))))
  have hΦ0 : 0 ≤ Φ := by simp only [Φ]; rw [h8]; positivity
  have hΦ : Φ ≤ (L - 1.0986 + ℓ) * G := by
    simp only [Φ]; rw [h8]
    exact mul_le_mul (by linarith) hbr hbr0 (by linarith)
  set X0 := a1X0 L
  have hX0def : X0 = (L - 8.09) + (L - 1.0986) * G := rfl
  have hX : Λ + Φ ≤ X0 + G * ℓ := by rw [hX0def]; nlinarith
  have hX0G : 14 * G ≤ X0 := by rw [hX0def]; nlinarith
  -- `B`.
  have hz := zeta3_le
  have hz0 := zeta3_nonneg
  have hBz : 2 * zeta3 * √(T ^ 3 / (2 * 8 * q)) / U2 T ≤ 0.027 := by
    have h1 : √(T ^ 3 / (2 * 8 * q)) ≤ 0.61238 * T := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity), hqu]
      have hT3 : T ^ 3 = T * T ^ 2 := by ring
      rw [hT3]; nlinarith [mul_pos hT0 (mul_pos hT0 hT0), mul_nonneg (mul_nonneg hT0.le
        (mul_nonneg hT0.le hT0.le)) (sub_nonneg.2 hu1)]
    rw [div_le_iff₀ hU0]
    have := mul_le_mul hz h1 (Real.sqrt_nonneg _) (by norm_num)
    nlinarith
  set B := 0.15107 * Λ + 2 * zeta3 * √(T ^ 3 / (2 * 8 * q)) / U2 T
  set B0 := a1B0 L
  have hB0def : B0 = 0.15107 * (L - 8.09) + 0.027 := rfl
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have hB : B ≤ B0 := by simp only [B]; rw [hB0def]; nlinarith
  -- `F`.
  set F0 := a1F0 L
  have hF0def : F0 = 1.7882 * Real.log (L - 1.7917) + 0.9549 := rfl
  have hF := div_totient_le_large (q := q) (by linarith)
  have hllq : Real.log (Real.log q) ≤ Real.log (L - 1.7917) + ℓ * 0.07247 := by
    rw [hlogq, hlT6]
    have hpos : 0 < L - Real.log 6 := by linarith
    have h1 : Real.log (L - Real.log 6 + ℓ) = Real.log (L - Real.log 6) +
        Real.log (1 + ℓ / (L - Real.log 6)) := by
      rw [← Real.log_mul hpos.ne' (by positivity)]; congr 1; field_simp
    have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + ℓ / (L - Real.log 6) by positivity)
    have h3 : ℓ / (L - Real.log 6) ≤ ℓ * 0.07247 := by
      rw [div_le_iff₀ hpos]; nlinarith
    have h4 : Real.log (L - Real.log 6) ≤ Real.log (L - 1.7917) :=
      Real.log_le_log hpos (by linarith)
    rw [h1]; linarith
  have hFle : (q : ℝ) / Nat.totient q ≤ F0 + 0.1296 * ℓ := by rw [hF0def]; nlinarith
  have hF1 : 1 ≤ F0 := by
    rw [hF0def]
    have : 1 ≤ Real.log (L - 1.7917) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
    linarith
  -- Assemble.
  have hXB0 : 0 ≤ (Λ + Φ) * B := mul_nonneg (by linarith) hB0
  have hdec := decay_FX hF1 hX0G hG0 hℓ
  rw [hexp] at hdec
  have hkey : 2 * ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) / q ≤ 12 * F0 * X0 * B0 / T := by
    have hF00 : 0 ≤ F0 + 0.1296 * ℓ := by linarith
    have hX00 : 0 ≤ X0 + G * ℓ := by nlinarith
    have h1 : ((q : ℝ) / Nat.totient q) * (Λ + Φ) ≤ (F0 + 0.1296 * ℓ) * (X0 + G * ℓ) :=
      mul_le_mul hFle hX (by linarith) hF00
    have h2 : ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) ≤ F0 * X0 * u * B0 := by
      calc ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) = ((q : ℝ) / Nat.totient q) * (Λ + Φ) * B := by
            ring
        _ ≤ (F0 + 0.1296 * ℓ) * (X0 + G * ℓ) * B0 :=
            mul_le_mul h1 hB (hB0) (mul_nonneg hF00 hX00)
        _ ≤ F0 * X0 * u * B0 := mul_le_mul_of_nonneg_right hdec (by rw [hB0def]; nlinarith)
    rw [div_le_div_iff₀ hq0 hT0]
    have hq6 : 12 * F0 * X0 * B0 * q = 2 * T * (F0 * X0 * u * B0) := by rw [hqu]; ring
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * T)
    nlinarith
  -- `4 x √(1/(8φ)) √(XB) = x √(2 (q/φ) XB / q)`.
  have e1 : 4 * T ^ 3 * √(1 / 4 / (2 * Nat.totient q)) * √((Λ + Φ) * B) =
      T ^ 3 * √(2 * ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) / q) := by
    have e0 : 2 * ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) / q =
        4 ^ 2 * (1 / 4 / (2 * Nat.totient q)) * ((Λ + Φ) * B) := by
      field_simp; ring
    rw [e0, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2 * (1 / 4 / (2 * Nat.totient q)))
      ((Λ + Φ) * B), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 2) (1 / 4 / (2 * Nat.totient q)),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]; ring
  rw [e1]
  have hsT : 0 < √T := Real.sqrt_pos.2 hT0
  calc T ^ 3 * √(2 * ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) / q)
      ≤ T ^ 3 * √(12 * F0 * X0 * B0 / T) := by gcongr
    _ = √(12 * F0 * X0 * B0) * (T ^ 2 * √T) := by
        rw [Real.sqrt_div' _ hT0.le]
        have : T ^ 3 = T ^ 2 * √T * √T := by rw [mul_assoc, Real.mul_self_sqrt hT0.le]; ring
        rw [this]; field_simp

end TernaryGoldbach.MinorArcs
