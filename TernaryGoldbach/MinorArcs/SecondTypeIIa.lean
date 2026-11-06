import TernaryGoldbach.Prelim.MertensProduct
import TernaryGoldbach.MinorArcs.TypeIILarge
import TernaryGoldbach.MinorArcs.SecondParams
import TernaryGoldbach.MinorArcs.FirstChoiceTypeII

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Type II for `q > y` at the second parameters: reduction to functions of `L = log T`

Case (a1) of [H, §6.3.2]: `T/6 < q`, `16q ≤ x/U` (our `θ = 8`), via `typeII_638`. With
`u = 6q/T ≥ 1`, `ℓ = log u`, every term is bounded by its value at `u = 1` (up to a factor
`1.03` in one place) times `T^{5/2}`:
`|S_{II}| ≤ (√(12 F₀ X₀ B₀) + SEC(L)) T^{5/2}` (`typeII_a1`), where
`F₀ = 1.7882 log(L - 1.7917) + 0.9549` bounds `q/φ(q)` (Lemma C.2.2, `e^γ ≤ 1.7882`),
`X₀ = (L - 8.09) + (L - 1.0986)(log(L - 6.0119) - 0.732)` bounds `log(x/UW₀) + Φ` and
`B₀ = 0.15107(L - 8.09) + 0.0501` bounds `κ₆/4 · log(x/UW₀) + κ₀ζ³-term`.
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

theorem log_408326_ge : (6.0119 : ℝ) ≤ Real.log 408.32 := by
  have := le_log_num (z := 408.32) 6 0.0119 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log8_le : Real.log 8 ≤ 2.0795 := by
  have := log_le_num (z := 8) 2 0.0795 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_8_3_le : Real.log (8 / 3) ≤ 0.9809 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  linarith [log8_le, log3_ge]

theorem log_8_le : Real.log 8.0001 ≤ 2.0795 := by
  have := log_le_num (z := 8.0001) 2 0.0795 (by norm_num) (by norm_num) (by norm_num [taylor6])
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
  have h1 : √(T ^ 3 / V2 T) ≤ 1.73207 * T := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
    have : T ^ 3 = T * T ^ 2 := by ring
    nlinarith [sq_nonneg T]
  have h2 : zeta3 * √(T ^ 3 / V2 T) / U2 T ≤ 27 * (1.73207 * T) / (1224.99 * T) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have := mul_le_mul hz h1 (Real.sqrt_nonneg _) (by norm_num)
    have : 0 ≤ zeta3 * √(T ^ 3 / V2 T) := by positivity
    nlinarith
  have h3 : 27 * (1.73207 * T) / (1224.99 * T) ≤ 0.0381766 := by
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
noncomputable def a1B0 (L : ℝ) : ℝ := 0.15107 * (L - 8.09) + 0.0501
noncomputable def a1F2 (L : ℝ) : ℝ := 1.7882 * Real.log (2 * L) + 0.9549

/-- The secondary terms of case (a1), divided by `T^{5/2}`. -/
noncomputable def a1SEC (L : ℝ) : ℝ :=
  4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) +
    0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) +
    1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) + 0.028572 * √(2 * L - 7.1106))) +
  8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) +
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
        (0.15107 * Real.log (T ^ 3 / (U2 T * (2 * 8 * q))) + 0.0231 +
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
  set B := 0.15107 * Λ + 0.0231 + 2 * zeta3 * √(T ^ 3 / (2 * 8 * q)) / U2 T
  set B0 := a1B0 L
  have hB0def : B0 = 0.15107 * (L - 8.09) + 0.0501 := rfl
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

/-! ### The secondary terms -/

/-- Common facts for case (a1). -/
theorem a1_facts {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : T / 6 < q)
    (hq16 : 16 * (q : ℝ) ≤ T ^ 3 / U2 T) :
    (q : ℝ) * 19599.84 ≤ T ^ 2 ∧ T ^ 3 / U2 T ≤ T ^ 2 / 1224.99 ∧ (1e6 : ℝ) ≤ q := by
  have h1 := xU2_le hT
  have h2 : 16 * (q : ℝ) * 1224.99 ≤ T ^ 2 := by
    have := hq16.trans h1; rwa [le_div_iff₀ (by norm_num)] at this
  refine ⟨by linarith, h1, by linarith⟩

theorem a1_M2_le {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : T / 6 < q)
    (hq16 : 16 * (q : ℝ) ≤ T ^ 3 / U2 T) :
    4 * √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) *
      (2 * √(T ^ 3 / U2 T) + √(Real.log (2 * q)) * (2 * rexp 1 * √(2 * q) +
        4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q))))) ≤
    4 * √(0.24083 * a1F2 (Real.log T) / 2) * (0.057144 + 0.13418 * √(2 * Real.log T)) *
      (T ^ 2 * √T) := by
  obtain ⟨hqT, hxU, hq6⟩ := a1_facts hT hq hq16
  have hT0 : 0 < T := by linarith
  have hU0 := U2_pos hT
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
  set L := Real.log T
  have hL := fifteen_six_le_log hT
  have hκ := kap1_le_second hT
  have hκ0 : 0 ≤ kap1 (T ^ 3) (U2 T) (V2 T) := by unfold kap1; have := zeta3_nonneg; positivity
  -- `q/φ ≤ F₂`.
  have hF := div_totient_le_large (q := q) hq6
  have hlq : Real.log q ≤ 2 * L := by
    have : (q : ℝ) ≤ T ^ 2 := by nlinarith [sq_nonneg T]
    have := Real.log_le_log hq0 this
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlq1 : 13.81 ≤ Real.log q := log_1e6_ge.trans (Real.log_le_log (by norm_num) hq6)
  have hF2 : (q : ℝ) / Nat.totient q ≤ a1F2 L := by
    unfold a1F2
    have := Real.log_le_log (by linarith) hlq
    linarith
  have hF20 : 0 ≤ a1F2 L := le_trans (by positivity) hF2
  -- first factor.
  have hA : √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) ≤
      √(0.24083 * a1F2 L / 2) * (T * √T) := by
    have e : kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q) =
        kap1 (T ^ 3) (U2 T) (V2 T) * ((q : ℝ) / Nat.totient q) / 2 * T ^ 3 := by
      field_simp
    rw [e, Real.sqrt_mul (by positivity)]
    have hT3 : √(T ^ 3) = T * √T := by
      rw [show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hT0.le]
    rw [hT3]
    gcongr
  -- second factor.
  have hin8 : 8 ≤ T ^ 3 / U2 T / (2 * q) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hl8 := log8_ge
  have hlin0 : 2.0794 ≤ Real.log (T ^ 3 / U2 T / (2 * q)) :=
    hl8.trans (Real.log_le_log (by norm_num) hin8)
  have hB1 : 2 * √(T ^ 3 / U2 T) ≤ 0.057144 * T := by
    have : √(T ^ 3 / U2 T) ≤ 0.028572 * T := by
      rw [Real.sqrt_le_left (by positivity)]
      have : T ^ 2 / 1224.99 ≤ (0.028572 * T) ^ 2 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
      linarith
    linarith
  have hB2 : √(Real.log (2 * q)) ≤ √(2 * L) := by
    apply Real.sqrt_le_sqrt
    have : Real.log (2 * q) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg T])
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hB3 : 2 * rexp 1 * √(2 * q) ≤ 0.054918 * T := by
    have h1 : √(2 * q) ≤ 0.0101016 * T := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg T]
    have he := Real.exp_one_lt_d9
    have : 0 ≤ √(2 * (q : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hB4 : 4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q))) ≤ 0.079256 * T := by
    have : √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q))) ≤ 0.019814 * T := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
      have : T ^ 3 / U2 T ≤ (0.019814 * T) ^ 2 * 2.0794 := by
        have : T ^ 2 / 1224.99 ≤ (0.019814 * T) ^ 2 * 2.0794 := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
        linarith
      nlinarith [sq_nonneg (0.019814 * T)]
    linarith
  have hsum : 2 * √(T ^ 3 / U2 T) + √(Real.log (2 * q)) * (2 * rexp 1 * √(2 * q) +
      4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q)))) ≤
      (0.057144 + 0.13418 * √(2 * L)) * T := by
    have h1 : √(Real.log (2 * q)) * (2 * rexp 1 * √(2 * q) +
        4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q)))) ≤
        √(2 * L) * (0.134174 * T) :=
      mul_le_mul hB2 (by linarith) (by positivity) (Real.sqrt_nonneg _)
    have : 0 ≤ √(2 * L) * T := by positivity
    nlinarith
  calc 4 * √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) *
        (2 * √(T ^ 3 / U2 T) + √(Real.log (2 * q)) * (2 * rexp 1 * √(2 * q) +
          4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / (2 * q)))))
      ≤ 4 * (√(0.24083 * a1F2 L / 2) * (T * √T)) * ((0.057144 + 0.13418 * √(2 * L)) * T) := by
        gcongr
    _ = _ := by ring

theorem a1_M4_le {T : ℝ} (hT : 6e6 ≤ T) :
    8 * 1.4262 * T ^ 3 * √(kap1 (T ^ 3) (U2 T) (V2 T) * (1 / 2 + 1 / U2 T)) / √(V2 T) ≤
    8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have hκ := kap1_le_second hT
  have hκ0 : 0 ≤ kap1 (T ^ 3) (U2 T) (V2 T) := by unfold kap1; have := zeta3_nonneg; positivity
  have hU := U2_ge' hT
  have hV := V2_ge' hT
  have hsV : 0 < √(V2 T : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h1 : kap1 (T ^ 3) (U2 T) (V2 T) * (1 / 2 + 1 / U2 T) ≤ 0.24083 * 0.50001 := by
    have : 1 / (U2 T : ℝ) ≤ 0.00001 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have h2 : T ^ 3 / √(V2 T) ≤ 1.73207 * (T ^ 2 * √T) := by
    rw [div_le_iff₀ hsV]
    have h3 : √(0.33333 * T) ≤ √(V2 T) := Real.sqrt_le_sqrt hV
    have h4 : √(0.33333 * T) = √0.33333 * √T := Real.sqrt_mul (by norm_num) T
    have h5 : 1 ≤ 1.73207 * √0.33333 := by
      have : 0.577347 ≤ √0.33333 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      linarith
    have hsT : √T * √T = T := Real.mul_self_sqrt hT0.le
    have : T ^ 3 ≤ 1.73207 * (T ^ 2 * √T) * √(0.33333 * T) := by
      rw [h4]
      have : T ^ 3 = T ^ 2 * (√T * √T) := by rw [hsT]; ring
      rw [this]
      have : 0 ≤ T ^ 2 * √T * √T := by positivity
      nlinarith
    calc T ^ 3 ≤ 1.73207 * (T ^ 2 * √T) * √(0.33333 * T) := this
      _ ≤ _ := by gcongr
  calc 8 * 1.4262 * T ^ 3 * √(kap1 (T ^ 3) (U2 T) (V2 T) * (1 / 2 + 1 / U2 T)) / √(V2 T)
      = 8 * 1.4262 * √(kap1 (T ^ 3) (U2 T) (V2 T) * (1 / 2 + 1 / U2 T)) * (T ^ 3 / √(V2 T)) := by
        ring
    _ ≤ 8 * 1.4262 * √(0.24083 * 0.50001) * (1.73207 * (T ^ 2 * √T)) := by gcongr
    _ = _ := by ring

/-- `y ↦ √y + 1/√y` is increasing on `[1, ∞)`. -/
theorem sqrt_add_inv_sqrt_mono {y₁ y₂ : ℝ} (h1 : 1 ≤ y₁) (h12 : y₁ ≤ y₂) :
    √y₁ + 1 / √y₁ ≤ √y₂ + 1 / √y₂ := by
  have hs1 : 1 ≤ √y₁ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hs12 : √y₁ ≤ √y₂ := Real.sqrt_le_sqrt h12
  have hs2 : 1 ≤ √y₂ := hs1.trans hs12
  rw [← sub_nonneg]
  have e : √y₂ + 1 / √y₂ - (√y₁ + 1 / √y₁) = (√y₂ - √y₁) * (1 - 1 / (√y₁ * √y₂)) := by
    field_simp; ring
  rw [e]
  apply mul_nonneg (by linarith)
  rw [sub_nonneg, div_le_one (by positivity)]; nlinarith

set_option maxHeartbeats 4000000 in
theorem a1_M3_le {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : T / 6 < q)
    (hq16 : 16 * (q : ℝ) ≤ T ^ 3 / U2 T) :
    4 * (√(kap1 (T ^ 3) (U2 T) (V2 T)) * (√((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 *
      (Real.log (2 * 8 * q) * √(Real.log (2 * 8 * q)) - Real.log (V2 T) * √(Real.log (V2 T)))) +
      T ^ 3 * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) / √(V2 T) +
      √(T ^ 3) * √(Real.log (2 * 8 * q)) * √(2 * 8 * q))) ≤
    4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * √(Real.log T + 0.9809)) +
      0.007143 * (√(2 * Real.log T - 7.1106) * (Real.log T - 6.0119)) +
      1.73207 * (√(Real.log T - 1.0986) + 1 / √(Real.log T - 1.0986)) +
      0.028572 * √(2 * Real.log T - 7.1106))) * (T ^ 2 * √T) := by
  obtain ⟨hqT, hxU, hq6⟩ := a1_facts hT hq hq16
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hV := V2_ge' hT
  have hVle := V2_le hT0
  have hV0 : (0 : ℝ) < V2 T := by linarith
  have hsT : 0 < √T := Real.sqrt_pos.2 hT0
  have hss : √T * √T = T := Real.mul_self_sqrt hT0.le
  -- `u`, `ℓ`.
  set u := 6 * q / T with hudef
  have hu1 : 1 ≤ u := by rw [hudef, le_div_iff₀ hT0]; linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log u with hℓdef
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hu1
  have hexp : rexp ℓ = u := Real.exp_log hu0
  have hqu : (q : ℝ) = T / 6 * u := by rw [hudef]; field_simp
  -- logs.
  set A := Real.log (2 * 8 * q) with hAdef
  set Vl := Real.log (V2 T) with hVldef
  have hVl1 : 1 ≤ Vl := by
    rw [hVldef, Real.le_log_iff_exp_le hV0]; linarith [Real.exp_one_lt_d9]
  have hVlL : Vl ≤ L - 1.0986 := by
    have := Real.log_le_log hV0 hVle
    rw [Real.log_div hT0.ne' (by norm_num)] at this; linarith [log3_ge]
  have hVA : Vl ≤ A := Real.log_le_log hV0 (by linarith)
  have hA1 : A ≤ L + 0.9809 + ℓ := by
    have : (2 : ℝ) * 8 * q = T * (8 / 3) * u := by rw [hqu]; ring
    rw [hAdef, this, Real.log_mul (by positivity) hu0.ne', Real.log_mul hT0.ne' (by norm_num)]
    linarith [log_8_3_le]
  have hA2 : A ≤ 2 * L - 7.1106 := by
    have h1 : (2 : ℝ) * 8 * q ≤ T ^ 2 / 1224.99 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at this
    push_cast at this; rw [hAdef, hLdef]; linarith [log_1224_ge]
  have hAV1 : A - Vl ≤ 2.0795 + ℓ := by
    have h1 : (2 : ℝ) * 8 * q / V2 T ≤ 8.0001 * u := by
      rw [div_le_iff₀ hV0, hqu]; nlinarith [mul_le_mul_of_nonneg_left hV hu0.le, mul_pos hu0 hT0]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) hV0.ne', Real.log_mul (by norm_num) hu0.ne'] at this
    rw [hAdef, hVldef, hℓdef]; linarith [log_8_le]
  have hAV2 : A - Vl ≤ L - 6.0119 := by
    have h1 : (2 : ℝ) * 8 * q / V2 T ≤ T / 408.32 := by
      rw [div_le_div_iff₀ hV0 (by norm_num)]
      have : 2 * 8 * (q : ℝ) * 1224.99 ≤ T ^ 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hV hT0.le]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) hV0.ne', Real.log_div hT0.ne' (by norm_num)] at this
    rw [hAdef, hVldef, hLdef]; linarith [log_408326_ge]
  have hA0 : 0 ≤ A := by linarith
  -- `√κ`.
  have hκ := kap1_le_second hT
  have hsκ : √(kap1 (T ^ 3) (U2 T) (V2 T)) ≤ 0.49075 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  -- The four pieces.
  have hW : 2 / 3 * (A * √A - Vl * √Vl) ≤ √A * (A - Vl) :=
    three_halves_sub_le (by linarith) hVA
  have hM : √((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) ≤ T ^ 3 / (4 * √q) + √q * (T * √T) := by
    have h1 : √((T ^ 3) ^ 2 / (16 * q)) = T ^ 3 / (4 * √q) := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity),
        Real.sqrt_mul (by norm_num), show √(16 : ℝ) = 4 by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have h2 : √(q * T ^ 3) = √q * (T * √T) := by
      rw [Real.sqrt_mul hq0.le, show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hT0.le]
    rw [← h1, ← h2]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt (show 0 ≤ (T ^ 3) ^ 2 / (16 * q) by positivity),
      Real.sq_sqrt (show 0 ≤ (q : ℝ) * T ^ 3 by positivity),
      mul_nonneg (Real.sqrt_nonneg ((T ^ 3) ^ 2 / (16 * q))) (Real.sqrt_nonneg (q * T ^ 3))]
  -- piece 1a.
  have hP1a : T ^ 3 / (4 * √q) * (√A * (A - Vl)) ≤
      √6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) * (T ^ 2 * √T) := by
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    have hsq : √(q : ℝ) = √(T / 6) * √u := by rw [hqu, Real.sqrt_mul (by positivity)]
    have hT6 : √(T / 6) = √T / √6 := Real.sqrt_div' _ (by norm_num)
    have hs6 : 0 < √(6 : ℝ) := by positivity
    have e : T ^ 3 / (4 * √q) = √6 / 4 * (T ^ 2 * √T) / √u := by
      rw [hsq, hT6]
      have : T ^ 3 = T ^ 2 * (√T * √T) := by rw [hss]; ring
      rw [this]; field_simp
    rw [e]
    have hk : √A * (A - Vl) / √u ≤ √1.03 * 2.0795 * √(L + 0.9809) := by
      have h1 : √A * (A - Vl) ≤ √(L + 0.9809 + ℓ) * (2.0795 + ℓ) :=
        mul_le_mul (Real.sqrt_le_sqrt hA1) hAV1 (by linarith) (Real.sqrt_nonneg _)
      have h2 := decay_M3 (L' := L + 0.9809) (by linarith) hℓ
      rw [hexp] at h2
      rw [div_le_iff₀ hsu]
      have h3 : √(L + 0.9809 + ℓ) * (2.0795 + ℓ) ≤ √1.03 * 2.0795 * √(L + 0.9809) * √u := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2.0795 + ℓ by linarith), ← Real.sqrt_mul (by positivity),
          ← Real.sqrt_sq (show (0 : ℝ) ≤ 2.0795 by norm_num), ← Real.sqrt_mul (by norm_num),
          ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        nlinarith
      linarith
    calc √6 / 4 * (T ^ 2 * √T) / √u * (√A * (A - Vl))
        = √6 / 4 * (T ^ 2 * √T) * (√A * (A - Vl) / √u) := by ring
      _ ≤ √6 / 4 * (T ^ 2 * √T) * (√1.03 * 2.0795 * √(L + 0.9809)) := by gcongr
      _ = _ := by ring
  -- piece 1b.
  have hP1b : √q * (T * √T) * (√A * (A - Vl)) ≤
      0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) * (T ^ 2 * √T) := by
    have h1 : √(q : ℝ) ≤ 0.007143 * T := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg T]
    have h2 : √A * (A - Vl) ≤ √(2 * L - 7.1106) * (L - 6.0119) :=
      mul_le_mul (Real.sqrt_le_sqrt hA2) hAV2 (by linarith) (Real.sqrt_nonneg _)
    calc √q * (T * √T) * (√A * (A - Vl))
        ≤ 0.007143 * T * (T * √T) * (√(2 * L - 7.1106) * (L - 6.0119)) := by
          gcongr
      _ = _ := by ring
  -- piece 2.
  have hP2 : T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) ≤
      1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) * (T ^ 2 * √T) := by
    have h1 := sqrt_add_inv_sqrt_mono hVl1 hVlL
    have hsV : 0 < √(V2 T : ℝ) := Real.sqrt_pos.2 hV0
    have h2 : T ^ 3 / √(V2 T) ≤ 1.73207 * (T ^ 2 * √T) := by
      rw [div_le_iff₀ hsV]
      have h3 : √(0.33333 * T) ≤ √(V2 T) := Real.sqrt_le_sqrt hV
      have h4 : √(0.33333 * T) = √0.33333 * √T := Real.sqrt_mul (by norm_num) T
      have h5 : 1 ≤ 1.73207 * √0.33333 := by
        have : 0.577347 ≤ √0.33333 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        linarith
      have : T ^ 3 ≤ 1.73207 * (T ^ 2 * √T) * √(0.33333 * T) := by
        rw [h4]
        have : T ^ 3 = T ^ 2 * (√T * √T) := by rw [hss]; ring
        rw [this]
        have : 0 ≤ T ^ 2 * √T * √T := by positivity
        nlinarith
      calc T ^ 3 ≤ 1.73207 * (T ^ 2 * √T) * √(0.33333 * T) := this
        _ ≤ _ := by gcongr
    have hpos : 0 ≤ √Vl + 1 / √Vl := by positivity
    calc T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) = T ^ 3 / √(V2 T) * (√Vl + 1 / √Vl) := by ring
      _ ≤ 1.73207 * (T ^ 2 * √T) * (√(L - 1.0986) + 1 / √(L - 1.0986)) :=
          mul_le_mul h2 h1 hpos (by positivity)
      _ = _ := by ring
  -- piece 3.
  have hP3 : √(T ^ 3) * √A * √(2 * 8 * q) ≤ 0.028572 * √(2 * L - 7.1106) * (T ^ 2 * √T) := by
    have h1 : √(T ^ 3) = T * √T := by
      rw [show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hT0.le]
    have h2 : √(2 * 8 * (q : ℝ)) ≤ 0.028572 * T := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg T]
    rw [h1]
    calc T * √T * √A * √(2 * 8 * q) ≤ T * √T * √(2 * L - 7.1106) * (0.028572 * T) := by
          gcongr
      _ = _ := by ring
  -- Assemble.
  have hW0 : 0 ≤ 2 / 3 * (A * √A - Vl * √Vl) := by
    have := Real.sqrt_le_sqrt hVA
    have : 0 ≤ √Vl := Real.sqrt_nonneg _
    nlinarith
  have hsum : √((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 * (A * √A - Vl * √Vl)) ≤
      T ^ 3 / (4 * √q) * (√A * (A - Vl)) + √q * (T * √T) * (√A * (A - Vl)) := by
    calc √((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 * (A * √A - Vl * √Vl))
        ≤ (T ^ 3 / (4 * √q) + √q * (T * √T)) * (√A * (A - Vl)) :=
          mul_le_mul hM hW hW0 (by positivity)
      _ = _ := by ring
  have hin : √((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 * (A * √A - Vl * √Vl)) +
      T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) + √(T ^ 3) * √A * √(2 * 8 * q) ≤
      (√6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) +
      0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) +
      1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) +
      0.028572 * √(2 * L - 7.1106)) * (T ^ 2 * √T) := by
    nlinarith
  have hin0 : 0 ≤ √((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 * (A * √A - Vl * √Vl)) +
      T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) + √(T ^ 3) * √A * √(2 * 8 * q) := by positivity
  calc 4 * (√(kap1 (T ^ 3) (U2 T) (V2 T)) *
        (√((T ^ 3) ^ 2 / (16 * q) + q * T ^ 3) * (2 / 3 * (A * √A - Vl * √Vl)) +
          T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) + √(T ^ 3) * √A * √(2 * 8 * q)))
      ≤ 4 * (0.49075 * ((√6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) +
          0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) +
          1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) +
          0.028572 * √(2 * L - 7.1106)) * (T ^ 2 * √T))) := by
        gcongr
    _ = _ := by ring

/-- `|2α - a/q - k| ≤ 1/(qQ)` from `Approx2`. -/
theorem approx2_abs {α x δ Q : ℝ} {a : ℤ} {q : ℕ} (hx : 0 < x) (h : Approx2 α x δ a q Q) :
    ∃ k : ℤ, |2 * α - a / q - k| ≤ 1 / (q * Q) := by
  obtain ⟨-, -, ⟨k, hk⟩, hδ, -⟩ := h
  exact ⟨k, by rw [show 2 * α - a / q - k = δ / x by rw [hk]; ring]; exact hδ⟩

/-- **Case (a1) of the second choice**: `T/6 < q`, `16q ≤ x/U`:
`|S_{II}| ≤ (√(12 F₀ X₀ B₀) + SEC(L)) T^{5/2}`. -/
theorem typeII_a1 {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq : T / 6 < q) (hq16 : 16 * (q : ℝ) ≤ T ^ 3 / U2 T) :
    ‖typeII α (T ^ 3) (U2 T) (V2 T)‖ ≤
      (√(12 * a1F0 (Real.log T) * a1X0 (Real.log T) * a1B0 (Real.log T)) + a1SEC (Real.log T)) *
        (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨k, hα⟩ := approx2_abs (by positivity) h
  have hV := V2_le hT0
  have he := Real.exp_one_lt_d9
  have key := typeII_638 (θ := 8) h.1 h.2.1 hα (by positivity) (one_le_U2 hT) (V2_ge_2e6 hT)
    (Q2_ge hT) (by linarith) (by linarith) (by linarith)
  have h1 := a1_M1_le hT hq hq16
  have h2 := a1_M2_le hT hq hq16
  have h3 := a1_M3_le hT hq hq16
  have h4 := a1_M4_le hT
  refine key.trans ?_
  have e : (√(12 * a1F0 (Real.log T) * a1X0 (Real.log T) * a1B0 (Real.log T)) +
      a1SEC (Real.log T)) * (T ^ 2 * √T) =
      √(12 * a1F0 (Real.log T) * a1X0 (Real.log T) * a1B0 (Real.log T)) * (T ^ 2 * √T) +
      4 * √(0.24083 * a1F2 (Real.log T) / 2) * (0.057144 + 0.13418 * √(2 * Real.log T)) *
        (T ^ 2 * √T) +
      4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * √(Real.log T + 0.9809)) +
        0.007143 * (√(2 * Real.log T - 7.1106) * (Real.log T - 6.0119)) +
        1.73207 * (√(Real.log T - 1.0986) + 1 / √(Real.log T - 1.0986)) +
        0.028572 * √(2 * Real.log T - 7.1106))) * (T ^ 2 * √T) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) * (T ^ 2 * √T) := by
    unfold a1SEC; ring
  rw [e]
  linarith

end TernaryGoldbach.MinorArcs
