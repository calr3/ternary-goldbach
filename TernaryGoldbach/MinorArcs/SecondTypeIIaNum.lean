import TernaryGoldbach.MinorArcs.SecondTypeIIa

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Case (a1): the numerical inequality `√(12 F₀X₀B₀) + SEC(L) ≤ 1.413 L^{3/2}` for `L ≥ 15.6`

Interval arithmetic: on each piece `[a, b]` we bound the increasing factors (`F₀`, `X₀/L`, `F₂`,
`1 - 6.0119/L`) by their values at `b` and the decreasing ones (`B₀/L²` for `L ≥ 15.83`,
`1/L`, …) by their values at `a`; for `L ≥ 70` we use `log L ≤ log 70 + (L - 70)/70`-type
bounds.
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- The coefficient function: `a1SEC L ≤ a1E L · L^{3/2}`. -/
noncomputable def a1E (L : ℝ) : ℝ :=
  4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * (1 / L + 0.49045 / L ^ 2)) +
    0.007143 * (√2 * (1 - 6.0119 / L)) + 1.73207 * (1 / L + 1.0373 / L ^ 2) +
    0.028572 * √2 / L)) +
  8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) +
  4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L)

theorem a1SEC_le {L : ℝ} (hL : 15.6 ≤ L) : a1SEC L ≤ a1E L * (L * √L) := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < √L := Real.sqrt_pos.2 hL0
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  have hs2 : √(2 * L) = √2 * √L := Real.sqrt_mul (by norm_num) L
  -- (a)
  have ha : √(L + 0.9809) ≤ √L + 0.49045 / √L := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (√L + 0.49045 / √L) ^ 2 = L + 0.9809 + 0.49045 ^ 2 / L := by
      field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
    rw [this]; have : 0 ≤ 0.49045 ^ 2 / L := by positivity
    linarith
  -- (b), (d)
  have hb : √(2 * L - 7.1106) ≤ √2 * √L := by
    rw [← hs2]; exact Real.sqrt_le_sqrt (by linarith)
  -- (c)
  have hc : √(L - 1.0986) + 1 / √(L - 1.0986) ≤ √L + 1.0373 / √L := by
    have h1 : √(L - 1.0986) ≤ √L := Real.sqrt_le_sqrt (by linarith)
    have h2 : 1 / √(L - 1.0986) ≤ 1.0373 / √L := by
      have hp : 0 < √(L - 1.0986) := Real.sqrt_pos.2 (by linarith)
      rw [div_le_div_iff₀ hp hs, one_mul]
      have : √L ≤ 1.0373 * √(L - 1.0986) := by
        rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
        nlinarith
      linarith
    linarith
  have hk : 0 ≤ (0.49075 : ℝ) := by norm_num
  unfold a1SEC a1E
  have e1 : (√6 / 4 * (√1.03 * 2.0795 * (1 / L + 0.49045 / L ^ 2))) * (L * √L) =
      √6 / 4 * (√1.03 * 2.0795 * (√L + 0.49045 / √L)) := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
  have e2 : 0.007143 * (√2 * (1 - 6.0119 / L)) * (L * √L) =
      0.007143 * (√2 * √L * (L - 6.0119)) := by field_simp
  have e3 : 1.73207 * (1 / L + 1.0373 / L ^ 2) * (L * √L) = 1.73207 * (√L + 1.0373 / √L) := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
  have e4 : 0.028572 * √2 / L * (L * √L) = 0.028572 * (√2 * √L) := by field_simp
  have e5 : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) * (L * √L) =
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) := by field_simp
  have e6 : 4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L) * (L * √L) =
      4 * √(0.24083 * a1F2 L / 2) * (0.057144 + 0.13418 * √(2 * L)) := by
    rw [hs2]; field_simp
  have hA1 : √6 / 4 * (√1.03 * 2.0795 * √(L + 0.9809)) ≤
      √6 / 4 * (√1.03 * 2.0795 * (√L + 0.49045 / √L)) := by gcongr
  have hA2 : 0.007143 * (√(2 * L - 7.1106) * (L - 6.0119)) ≤ 0.007143 * (√2 * √L * (L - 6.0119)) := by
    gcongr; linarith
  have hA3 : 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) ≤ 1.73207 * (√L + 1.0373 / √L) := by
    gcongr
  have hA4 : 0.028572 * √(2 * L - 7.1106) ≤ 0.028572 * (√2 * √L) := by gcongr
  have expand : (4 * (0.49075 * (√6 / 4 * (√1.03 * 2.0795 * (1 / L + 0.49045 / L ^ 2)) +
      0.007143 * (√2 * (1 - 6.0119 / L)) + 1.73207 * (1 / L + 1.0373 / L ^ 2) +
      0.028572 * √2 / L)) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) +
      4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L)) * (L * √L) =
      4 * (0.49075 * ((√6 / 4 * (√1.03 * 2.0795 * (1 / L + 0.49045 / L ^ 2))) * (L * √L) +
        0.007143 * (√2 * (1 - 6.0119 / L)) * (L * √L) +
        1.73207 * (1 / L + 1.0373 / L ^ 2) * (L * √L) + 0.028572 * √2 / L * (L * √L))) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) * (L * √L) +
      4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L) * (L * √L) := by ring
  rw [expand, e1, e2, e3, e4, e5, e6]
  nlinarith

/-! ### One piece -/

/-- `(L - c)/L² ≤ (a - c)/a²` for `2c ≤ a ≤ L`. -/
theorem div_sq_anti {a L c : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a) (ha : 2 * c ≤ a) (haL : a ≤ L) :
    (L - c) / L ^ 2 ≤ (a - c) / a ^ 2 := by
  have hL0 : 0 < L := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 haL) (show 0 ≤ a * L - c * (L + a) by nlinarith)]

/-- `(L - c)/L² ≤ 1/(4c)`. -/
theorem div_sq_le_max {L c : ℝ} (hc : 0 < c) (hL : 0 < L) : (L - c) / L ^ 2 ≤ 1 / (4 * c) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (L - 2 * c)]

/-- The main term on a piece `[a, b]`. -/
theorem a1M1_piece {L a b u1 u2 Bb m : ℝ} (ha : 15.6 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (h1 : Real.log (b - 1.7917) ≤ u1) (h2 : Real.log (b - 6.0119) ≤ u2)
    (hB : 0.15107 * ((L - 7.7583) / L ^ 2) ≤ Bb) (hm0 : 0 ≤ m)
    (hm : 12 * (1.7882 * u1 + 0.9549) * (1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732)) * Bb ≤
      m ^ 2) :
    √(12 * a1F0 L * a1X0 L * a1B0 L) ≤ m * (L * √L) := by
  have hL0 : 0 < L := by linarith
  have hb0 : 0 < b := by linarith
  -- `F₀ ≤ 1.7882 u1 + 0.9549`.
  have hF : a1F0 L ≤ 1.7882 * u1 + 0.9549 := by
    unfold a1F0
    have := Real.log_le_log (by linarith) (show L - 1.7917 ≤ b - 1.7917 by linarith)
    linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  -- `G ≥ 0` and `X₀/L ≤ …`.
  have hG0 : 0 ≤ a1G L := by
    unfold a1G
    have : 1 ≤ Real.log (L - 6.0119) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
    linarith
  have hGb : a1G L ≤ u2 - 0.732 := by
    unfold a1G
    have := Real.log_le_log (by linarith) (show L - 6.0119 ≤ b - 6.0119 by linarith)
    linarith
  have hX : a1X0 L ≤ L * (1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732)) := by
    unfold a1X0
    have h1 : 1 - 8.09 / L ≤ 1 - 8.09 / b := by
      have : 8.09 / b ≤ 8.09 / L := div_le_div_of_nonneg_left (by norm_num) hL0 hLb
      linarith
    have h2 : 1 - 1.0986 / L ≤ 1 - 1.0986 / b := by
      have : 1.0986 / b ≤ 1.0986 / L := div_le_div_of_nonneg_left (by norm_num) hL0 hLb
      linarith
    have h3 : 0 ≤ 1 - 1.0986 / L := by
      rw [sub_nonneg, div_le_one hL0]; linarith
    have h4 : (1 - 1.0986 / L) * a1G L ≤ (1 - 1.0986 / b) * (u2 - 0.732) :=
      mul_le_mul h2 hGb hG0 (by linarith)
    have e : L - 8.09 + (L - 1.0986) * a1G L = L * ((1 - 8.09 / L) + (1 - 1.0986 / L) * a1G L) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hL0.le
  have hX0 : 0 ≤ a1X0 L := by
    unfold a1X0; nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 1.0986 by linarith) hG0]
  -- `B₀ ≤ 0.15107 (L - 7.7583)`: `B₀/L² ≤ Bb`.
  have hB0 : a1B0 L ≤ Bb * L ^ 2 := by
    unfold a1B0
    have : 0.15107 * (L - 7.7583) = Bb * L ^ 2 - (Bb * L ^ 2 - 0.15107 * (L - 7.7583)) := by ring
    have h' : 0.15107 * (L - 7.7583) ≤ Bb * L ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hB; linarith
    nlinarith
  have hB00 : 0 ≤ a1B0 L := by unfold a1B0; nlinarith
  have hXX : 0 ≤ 1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732) := by
    have := mul_nonneg hL0.le hX0
    by_contra hneg; push Not at hneg
    have : L * (1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732)) < 0 :=
      mul_neg_of_pos_of_neg hL0 hneg
    linarith
  have hprod : 12 * a1F0 L * a1X0 L * a1B0 L ≤ m ^ 2 * L ^ 3 := by
    have hBb : 0 ≤ Bb := le_trans (by positivity) (show 0 ≤ a1B0 L / L ^ 2 by positivity) |>.trans
      (by rw [div_le_iff₀ (by positivity)]; exact hB0)
    have hu1 : 0 ≤ 1.7882 * u1 + 0.9549 := hF0.trans hF
    calc 12 * a1F0 L * a1X0 L * a1B0 L
        ≤ 12 * (1.7882 * u1 + 0.9549) * (L * (1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732))) *
            (Bb * L ^ 2) := by
          apply mul_le_mul _ hB0 hB00 (by positivity)
          exact mul_le_mul (by linarith) hX hX0 (by positivity)
      _ = 12 * (1.7882 * u1 + 0.9549) * (1 - 8.09 / b + (1 - 1.0986 / b) * (u2 - 0.732)) * Bb *
            L ^ 3 := by ring
      _ ≤ m ^ 2 * L ^ 3 := by gcongr
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  rw [Real.sqrt_le_left (by positivity)]
  calc 12 * a1F0 L * a1X0 L * a1B0 L ≤ m ^ 2 * L ^ 3 := hprod
    _ = (m * (L * √L)) ^ 2 := by rw [mul_pow, mul_pow, sq (√L), hss]; ring

theorem sqrt6_le : √6 ≤ 2.44949 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
theorem sqrt103_le : √1.03 ≤ 1.01489 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
theorem sqrt2_le : √2 ≤ 1.414214 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
theorem sqrtK4_le : √(0.24083 * 0.50001) ≤ 0.347013 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The secondary coefficient on a piece `[a, b]` (rational constants). -/
theorem a1E_piece {L a b sa u3 w e : ℝ} (ha : 15.6 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hsa : sa ^ 2 ≤ a) (hsa0 : 0 < sa) (h3 : Real.log (2 * b) ≤ u3) (hw0 : 0 ≤ w)
    (hw : 0.24083 * (1.7882 * u3 + 0.9549) / 2 ≤ w ^ 2)
    (he : 4 * (0.49075 * (2.44949 / 4 * (1.01489 * 2.0795 * (1 / a + 0.49045 / a ^ 2)) +
      0.007143 * (1.414214 * (1 - 6.0119 / b)) + 1.73207 * (1 / a + 1.0373 / a ^ 2) +
      0.028572 * 1.414214 / a)) +
      8 * 1.4262 * 1.73207 * 0.347013 / (a * sa) +
      4 * w * (0.057144 / (a * sa) + 0.13418 * 1.414214 / a) ≤ e) :
    a1E L ≤ e := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  refine le_trans ?_ he
  unfold a1E
  have h1 : 1 / L ≤ 1 / a := one_div_le_one_div_of_le ha0 haL
  have h2 : 0.49045 / L ^ 2 ≤ 0.49045 / a ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ ha0.le haL 2)
  have h2' : 1.0373 / L ^ 2 ≤ 1.0373 / a ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ ha0.le haL 2)
  have h3' : 1 - 6.0119 / L ≤ 1 - 6.0119 / b := by
    have : 6.0119 / b ≤ 6.0119 / L := div_le_div_of_nonneg_left (by norm_num) hL0 hLb
    linarith
  have h3'' : 0 ≤ 1 - 6.0119 / L := by rw [sub_nonneg, div_le_one hL0]; linarith
  have hsa' : sa ≤ √a := Real.le_sqrt_of_sq_le hsa
  have hsL : sa ≤ √L := hsa'.trans (Real.sqrt_le_sqrt haL)
  have h4 : a * sa ≤ L * √L := mul_le_mul haL hsL hsa0.le hL0.le
  have h5 : ∀ c : ℝ, 0 ≤ c → c / (L * √L) ≤ c / (a * sa) := fun c hc =>
    div_le_div_of_nonneg_left hc (by positivity) h4
  have h6 : a1F2 L ≤ 1.7882 * u3 + 0.9549 := by
    unfold a1F2
    have := Real.log_le_log (by positivity) (show 2 * L ≤ 2 * b by linarith)
    linarith
  have hF2 : 0 ≤ a1F2 L := by
    unfold a1F2; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * L by linarith); positivity
  have hsw : √(0.24083 * a1F2 L / 2) ≤ w := by
    rw [Real.sqrt_le_left hw0]; nlinarith
  have s6 := sqrt6_le
  have s103 := sqrt103_le
  have s2 := sqrt2_le
  have sK := sqrtK4_le
  have h7 : 0.028572 * √2 / L ≤ 0.028572 * 1.414214 / a :=
    div_le_div_of_nonneg_left (by positivity) ha0 haL |>.trans' (by gcongr)
  have h8 : 0.13418 * √2 / L ≤ 0.13418 * 1.414214 / a :=
    div_le_div_of_nonneg_left (by positivity) ha0 haL |>.trans' (by gcongr)
  have h9 := h5 0.057144 (by norm_num)
  have h10 : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) ≤
      8 * 1.4262 * 1.73207 * 0.347013 / (a * sa) :=
    (h5 _ (by positivity)).trans (by gcongr)
  gcongr

/-! ### `L ≥ 70` -/

theorem log70_le : Real.log 70 ≤ 4.2486 := by
  have := log_le_num (z := 70) 4 0.2486 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log140_le : Real.log 140 ≤ 4.9418 := by
  have := log_le_num (z := 140) 4 0.9418 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem a1M1_asym {L : ℝ} (hL : 70 ≤ L) :
    √(12 * a1F0 L * a1X0 L * a1B0 L) ≤ 1.0002 * (L * √L) := by
  have hL0 : 0 < L := by linarith
  set s := Real.log L
  have hs0 : Real.log 70 ≤ s := Real.log_le_log (by norm_num) hL
  set d := s - Real.log 70
  have hd : 0 ≤ d := by simp only [d]; linarith
  have hs : s ≤ 4.2486 + d := by simp only [d]; linarith [log70_le]
  have hLd : 70 * (1 + d + d ^ 2 / 2) ≤ L := by
    have h1 := Real.quadratic_le_exp_of_nonneg hd
    have h2 : rexp d * 70 = L := by
      simp only [d, s]; rw [Real.exp_sub, Real.exp_log hL0, Real.exp_log (by norm_num)]; field_simp
    nlinarith
  have hG0 : 0 ≤ a1G L := by
    unfold a1G
    have : 1 ≤ Real.log (L - 6.0119) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
    linarith
  have hF : a1F0 L ≤ 1.7882 * s + 0.9549 := by
    unfold a1F0; have := Real.log_le_log (by linarith) (show L - 1.7917 ≤ L by linarith); linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  have hX : a1X0 L ≤ L * (s + 0.268) := by
    unfold a1X0
    have h1 : a1G L ≤ s - 0.732 := by
      unfold a1G; have := Real.log_le_log (by linarith) (show L - 6.0119 ≤ L by linarith); linarith
    nlinarith
  have hX0 : 0 ≤ a1X0 L := by
    unfold a1X0; nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 1.0986 by linarith) hG0]
  have hB : a1B0 L ≤ 0.15107 * L := by unfold a1B0; linarith
  have hB0 : 0 ≤ a1B0 L := by unfold a1B0; nlinarith
  have hs1 : 0 ≤ s := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 70 by norm_num)]
  have hpoly : 12 * (1.7882 * s + 0.9549) * (s + 0.268) * 0.15107 ≤ 1.0002 ^ 2 * L := by
    have : 12 * (1.7882 * s + 0.9549) * (s + 0.268) * 0.15107 ≤
        12 * (1.7882 * (4.2486 + d) + 0.9549) * (4.2486 + d + 0.268) * 0.15107 := by
      gcongr
    nlinarith [mul_nonneg hd hd]
  have hprod : 12 * a1F0 L * a1X0 L * a1B0 L ≤ 1.0002 ^ 2 * L ^ 3 := by
    calc 12 * a1F0 L * a1X0 L * a1B0 L ≤ 12 * (1.7882 * s + 0.9549) * (L * (s + 0.268)) *
          (0.15107 * L) := by
          apply mul_le_mul _ hB hB0
            (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (mul_nonneg hL0.le (by linarith)))
          exact mul_le_mul (by linarith) hX hX0 (mul_nonneg (by norm_num) (by linarith))
      _ = 12 * (1.7882 * s + 0.9549) * (s + 0.268) * 0.15107 * L ^ 2 := by ring
      _ ≤ 1.0002 ^ 2 * L * L ^ 2 := by gcongr
      _ = _ := by ring
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  rw [Real.sqrt_le_left (by positivity)]
  calc 12 * a1F0 L * a1X0 L * a1B0 L ≤ 1.0002 ^ 2 * L ^ 3 := hprod
    _ = (1.0002 * (L * √L)) ^ 2 := by rw [mul_pow, mul_pow, sq (√L), hss]; ring

theorem a1E_asym {L : ℝ} (hL : 70 ≤ L) : a1E L ≤ 0.1309 := by
  have hL0 : 0 < L := by linarith
  have hsL : 8.3666 ≤ √L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hlog : Real.log (2 * L) ≤ 4.9418 + (L - 70) / 70 := by
    have h1 : Real.log (2 * L) = Real.log 140 + Real.log (L / 70) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < L / 70 by positivity)
    have : L / 70 - 1 = (L - 70) / 70 := by field_simp
    linarith [log140_le]
  have hF20 : 0 ≤ a1F2 L := by
    unfold a1F2; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * L by linarith); positivity
  have hW : √(0.24083 * a1F2 L / 2) ≤ 1.0859 * (L / 70) := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold a1F2
    have hv : 1 ≤ L / 70 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have e : (L - 70) / 70 = L / 70 - 1 := by field_simp
    rw [e] at hlog
    nlinarith
  have s6 := sqrt6_le
  have s103 := sqrt103_le
  have s2 := sqrt2_le
  have sK := sqrtK4_le
  have h1 : 1 / L ≤ 1 / 70 := one_div_le_one_div_of_le (by norm_num) hL
  have h2 : 1 / L ^ 2 ≤ 1 / 4900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : 1 - 6.0119 / L ≤ 1 := by
    have : 0 ≤ 6.0119 / L := by positivity
    linarith
  have h3' : 0 ≤ 1 - 6.0119 / L := by rw [sub_nonneg, div_le_one hL0]; linarith
  have h4 : 1 / (L * √L) ≤ 1 / (70 * 8.3666) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul hL hsL (by norm_num) hL0.le)
  have hA : √6 / 4 * (√1.03 * 2.0795 * (1 / L + 0.49045 / L ^ 2)) ≤
      2.44949 / 4 * (1.01489 * 2.0795 * (1 / 70 + 0.49045 / 4900)) := by
    have : 0.49045 / L ^ 2 ≤ 0.49045 / 4900 := by
      rw [div_eq_mul_one_div 0.49045 (L ^ 2), div_eq_mul_one_div 0.49045 4900]; gcongr
    gcongr
  have hB : 1.73207 * (1 / L + 1.0373 / L ^ 2) ≤ 1.73207 * (1 / 70 + 1.0373 / 4900) := by
    have : 1.0373 / L ^ 2 ≤ 1.0373 / 4900 := by
      rw [div_eq_mul_one_div 1.0373 (L ^ 2), div_eq_mul_one_div 1.0373 4900]; gcongr
    gcongr
  have hC : 0.007143 * (√2 * (1 - 6.0119 / L)) ≤ 0.007143 * 1.414214 := by
    have : √2 * (1 - 6.0119 / L) ≤ 1.414214 * 1 := mul_le_mul s2 h3 h3' (by norm_num)
    linarith
  have hD : 0.028572 * √2 / L ≤ 0.028572 * 1.414214 / 70 := by
    rw [div_eq_mul_one_div (0.028572 * √2) L, div_eq_mul_one_div (0.028572 * 1.414214) 70]
    gcongr
  have hE : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) ≤
      8 * 1.4262 * 1.73207 * 0.347013 / (70 * 8.3666) := by
    rw [div_eq_mul_one_div _ (L * √L), div_eq_mul_one_div _ (70 * 8.3666)]; gcongr
  have hF : 4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L) ≤
      4 * 1.0859 * (0.057144 / (70 * 8.3666) * 70 + 0.13418 * 1.414214) / 70 := by
    have e : 4 * √(0.24083 * a1F2 L / 2) * (0.057144 / (L * √L) + 0.13418 * √2 / L) =
        4 * (√(0.24083 * a1F2 L / 2) / L) * (0.057144 / √L + 0.13418 * √2) := by
      field_simp
    rw [e]
    have hW' : √(0.24083 * a1F2 L / 2) / L ≤ 1.0859 / 70 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
    have hq : 0.057144 / √L ≤ 0.057144 / 8.3666 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsL
    have : 4 * (√(0.24083 * a1F2 L / 2) / L) * (0.057144 / √L + 0.13418 * √2) ≤
        4 * (1.0859 / 70) * (0.057144 / 8.3666 + 0.13418 * 1.414214) := by
      gcongr
    refine this.trans (le_of_eq ?_); ring
  unfold a1E
  have : (4 : ℝ) * (0.49075 * (2.44949 / 4 * (1.01489 * 2.0795 * (1 / 70 + 0.49045 / 4900)) +
      0.007143 * 1.414214 + 1.73207 * (1 / 70 + 1.0373 / 4900) +
      0.028572 * 1.414214 / 70)) +
      8 * 1.4262 * 1.73207 * 0.347013 / (70 * 8.3666) +
      4 * 1.0859 * (0.057144 / (70 * 8.3666) * 70 + 0.13418 * 1.414214) / 70 ≤ 0.1309 := by
    norm_num
  nlinarith

end TernaryGoldbach.MinorArcs
