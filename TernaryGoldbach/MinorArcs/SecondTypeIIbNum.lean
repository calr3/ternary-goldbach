import TernaryGoldbach.MinorArcs.SecondTypeIIb

/-!
# Case (b): the numerical inequality `√(12 F₀X₀ᵇB₀ᵇ) + SECᵇ(L) ≤ 1.413 L^{3/2}` for `L ≥ 15.6`

As for case (a1) (`SecondTypeIIaNum.lean`), by interval arithmetic on pieces, and a separate
argument for `L ≥ 55`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

noncomputable def bE (L : ℝ) : ℝ :=
  4 * (0.49075 * (0.612373 * (3.4658 * (1 / L + 1.1836 / L ^ 2)) +
    0.0019072 * (√2 * (1 - 6.0119 / L)) + 0.70712 * 1.73207 * (1 / L + 1.0373 / L ^ 2) +
    0.02158 * √2 / L)) +
  8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) +
  4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2))

theorem sqrt_add_le_aux {L c : ℝ} (hL : 0 < L) (hc : 0 ≤ c) : √(L + c) ≤ √L + c / 2 / √L := by
  have hs : 0 < √L := Real.sqrt_pos.2 hL
  have hss : √L * √L = L := Real.mul_self_sqrt hL.le
  rw [Real.sqrt_le_left (by positivity)]
  have : (√L + c / 2 / √L) ^ 2 = L + c + (c / 2) ^ 2 / L := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
  rw [this]; have : 0 ≤ (c / 2) ^ 2 / L := by positivity
  linarith

theorem bSEC_le {L : ℝ} (hL : 15.6 ≤ L) : bSEC L ≤ bE L * (L * √L) := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < √L := Real.sqrt_pos.2 hL0
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  have hs2 : √(2 * L) = √2 * √L := Real.sqrt_mul (by norm_num) L
  have ha : √(L + 2.3672) ≤ √L + 1.1836 / √L := by
    have := sqrt_add_le_aux hL0 (show (0 : ℝ) ≤ 2.3672 by norm_num); norm_num at this ⊢; linarith
  have ha' : √(L + 4.603) ≤ √L + 2.3015 / √L := by
    have := sqrt_add_le_aux hL0 (show (0 : ℝ) ≤ 4.603 by norm_num); norm_num at this ⊢; linarith
  have hb : √(2 * L - 7.1106) ≤ √2 * √L := by
    rw [← hs2]; exact Real.sqrt_le_sqrt (by linarith)
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
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  unfold bSEC bE
  have e1 : 0.612373 * (3.4658 * (1 / L + 1.1836 / L ^ 2)) * (L * √L) =
      0.612373 * (3.4658 * (√L + 1.1836 / √L)) := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
  have e2 : 0.0019072 * (√2 * (1 - 6.0119 / L)) * (L * √L) =
      0.0019072 * (√2 * √L * (L - 6.0119)) := by field_simp
  have e3 : 0.70712 * 1.73207 * (1 / L + 1.0373 / L ^ 2) * (L * √L) =
      0.70712 * 1.73207 * (√L + 1.0373 / √L) := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring
  have e4 : 0.02158 * √2 / L * (L * √L) = 0.02158 * (√2 * √L) := by field_simp
  have e5 : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) * (L * √L) =
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) := by field_simp
  have e6 : 4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2)) *
      (L * √L) = 4 * √(0.24083 * a1F0 L / 2) * (0.057144 + 0.0848 * (√L + 2.3015 / √L)) := by
    field_simp; rw [show √L ^ 2 = L by rw [sq, hss]]; ring_nf; rw [show √L ^ 2 = L by rw [sq, hss]];
      ring
  have hA1 : 0.612373 * (3.4658 * √(L + 2.3672)) ≤ 0.612373 * (3.4658 * (√L + 1.1836 / √L)) := by
    gcongr
  have hA2 : 0.0019072 * (√(2 * L - 7.1106) * (L - 6.0119)) ≤
      0.0019072 * (√2 * √L * (L - 6.0119)) := by gcongr; linarith
  have hA3 : 0.70712 * 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) ≤
      0.70712 * 1.73207 * (√L + 1.0373 / √L) := by gcongr
  have hA4 : 0.02158 * √(2 * L - 7.1106) ≤ 0.02158 * (√2 * √L) := by gcongr
  have hA5 : 4 * √(0.24083 * a1F0 L / 2) * (0.057144 + 0.0848 * √(L + 4.603)) ≤
      4 * √(0.24083 * a1F0 L / 2) * (0.057144 + 0.0848 * (√L + 2.3015 / √L)) := by gcongr
  have expand : (4 * (0.49075 * (0.612373 * (3.4658 * (1 / L + 1.1836 / L ^ 2)) +
      0.0019072 * (√2 * (1 - 6.0119 / L)) + 0.70712 * 1.73207 * (1 / L + 1.0373 / L ^ 2) +
      0.02158 * √2 / L)) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) +
      4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2))) *
        (L * √L) =
      4 * (0.49075 * (0.612373 * (3.4658 * (1 / L + 1.1836 / L ^ 2)) * (L * √L) +
        0.0019072 * (√2 * (1 - 6.0119 / L)) * (L * √L) +
        0.70712 * 1.73207 * (1 / L + 1.0373 / L ^ 2) * (L * √L) + 0.02158 * √2 / L * (L * √L))) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) * (L * √L) +
      4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2)) *
        (L * √L) := by ring
  rw [expand, e1, e2, e3, e4, e5, e6]
  nlinarith

/-- The main term of case (b) on a piece `[a, b]`. -/
theorem bM1_piece {L a b u1 u2 Bb m : ℝ} (ha : 15.6 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (h1 : Real.log (b - 1.7917) ≤ u1) (h2 : Real.log (b - 6.1452) ≤ u2)
    (hB : 0.15107 * ((L - 9.3884) / L ^ 2) ≤ Bb) (hm0 : 0 ≤ m)
    (hm : 12 * (1.7882 * u1 + 0.9549) * (1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037)) * Bb ≤
      m ^ 2) :
    √(12 * a1F0 L * bX0 L * bB0 L) ≤ m * (L * √L) := by
  have hL0 : 0 < L := by linarith
  have hb0 : 0 < b := by linarith
  have hF : a1F0 L ≤ 1.7882 * u1 + 0.9549 := by
    unfold a1F0
    have := Real.log_le_log (by linarith) (show L - 1.7917 ≤ b - 1.7917 by linarith)
    linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  have hG0 : 0 ≤ bG L := by
    unfold bG
    have : 1.2037 ≤ Real.log (L - 6.1452) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      have h := Real.exp_bound' (x := 0.2037) (by norm_num) (by norm_num) (n := 4) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      have e : rexp 1.2037 = rexp 1 * rexp 0.2037 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 0.2037, Real.exp_pos 1]
    linarith
  have hGb : bG L ≤ u2 - 1.2037 := by
    unfold bG
    have := Real.log_le_log (by linarith) (show L - 6.1452 ≤ b - 6.1452 by linarith)
    linarith
  have hX : bX0 L ≤ L * (1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037)) := by
    unfold bX0
    have h1 : 1 - 9.4778 / L ≤ 1 - 9.4778 / b := by
      have : 9.4778 / b ≤ 9.4778 / L := div_le_div_of_nonneg_left (by norm_num) hL0 hLb
      linarith
    have h2 : 1 - 0.9654 / L ≤ 1 - 0.9654 / b := by
      have : 0.9654 / b ≤ 0.9654 / L := div_le_div_of_nonneg_left (by norm_num) hL0 hLb
      linarith
    have h3 : 0 ≤ 1 - 0.9654 / L := by rw [sub_nonneg, div_le_one hL0]; linarith
    have h4 : (1 - 0.9654 / L) * bG L ≤ (1 - 0.9654 / b) * (u2 - 1.2037) :=
      mul_le_mul h2 hGb hG0 (by linarith)
    have e : L - 9.4778 + (L - 0.9654) * bG L = L * ((1 - 9.4778 / L) + (1 - 0.9654 / L) * bG L) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hL0.le
  have hX0 : 0 ≤ bX0 L := by
    unfold bX0; nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 0.9654 by linarith) hG0]
  have hB0 : bB0 L ≤ Bb * L ^ 2 := by
    unfold bB0
    have h' : 0.15107 * (L - 9.3884) ≤ Bb * L ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hB; linarith
    nlinarith
  have hB00 : 0 ≤ bB0 L := by unfold bB0; nlinarith
  have hXX : 0 ≤ 1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037) := by
    by_contra hneg; push Not at hneg
    have : L * (1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037)) < 0 :=
      mul_neg_of_pos_of_neg hL0 hneg
    linarith
  have hprod : 12 * a1F0 L * bX0 L * bB0 L ≤ m ^ 2 * L ^ 3 := by
    have hBb : 0 ≤ Bb := by
      have : 0 ≤ bB0 L / L ^ 2 := by positivity
      exact this.trans (by rw [div_le_iff₀ (by positivity)]; exact hB0)
    have hu1 : 0 ≤ 1.7882 * u1 + 0.9549 := hF0.trans hF
    calc 12 * a1F0 L * bX0 L * bB0 L
        ≤ 12 * (1.7882 * u1 + 0.9549) * (L * (1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037))) *
            (Bb * L ^ 2) := by
          apply mul_le_mul _ hB0 hB00 (by positivity)
          exact mul_le_mul (by linarith) hX hX0 (by positivity)
      _ = 12 * (1.7882 * u1 + 0.9549) * (1 - 9.4778 / b + (1 - 0.9654 / b) * (u2 - 1.2037)) * Bb *
            L ^ 3 := by ring
      _ ≤ m ^ 2 * L ^ 3 := by gcongr
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  rw [Real.sqrt_le_left (by positivity)]
  calc 12 * a1F0 L * bX0 L * bB0 L ≤ m ^ 2 * L ^ 3 := hprod
    _ = (m * (L * √L)) ^ 2 := by rw [mul_pow, mul_pow, sq (√L), hss]; ring

/-- The secondary coefficient of case (b) on a piece `[a, b]` (rational constants). -/
theorem bE_piece {L a b sa u1 w e : ℝ} (ha : 15.6 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hsa : sa ^ 2 ≤ a) (hsa0 : 0 < sa) (h1 : Real.log (b - 1.7917) ≤ u1) (hw0 : 0 ≤ w)
    (hw : 0.24083 * (1.7882 * u1 + 0.9549) / 2 ≤ w ^ 2)
    (he : 4 * (0.49075 * (0.612373 * (3.4658 * (1 / a + 1.1836 / a ^ 2)) +
      0.0019072 * (1.414214 * (1 - 6.0119 / b)) + 0.70712 * 1.73207 * (1 / a + 1.0373 / a ^ 2) +
      0.02158 * 1.414214 / a)) +
      8 * 1.4262 * 1.73207 * 0.347013 / (a * sa) +
      4 * w * (0.057144 / (a * sa) + 0.0848 * (1 / a + 2.3015 / a ^ 2)) ≤ e) :
    bE L ≤ e := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  refine le_trans ?_ he
  unfold bE
  have h1' : 1 / L ≤ 1 / a := one_div_le_one_div_of_le ha0 haL
  have h2 : 1.1836 / L ^ 2 ≤ 1.1836 / a ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ ha0.le haL 2)
  have h2' : 1.0373 / L ^ 2 ≤ 1.0373 / a ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ ha0.le haL 2)
  have h2'' : 2.3015 / L ^ 2 ≤ 2.3015 / a ^ 2 :=
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
  have h6 : a1F0 L ≤ 1.7882 * u1 + 0.9549 := by
    unfold a1F0
    have := Real.log_le_log (by linarith) (show L - 1.7917 ≤ b - 1.7917 by linarith)
    linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  have hsw : √(0.24083 * a1F0 L / 2) ≤ w := by
    rw [Real.sqrt_le_left hw0]; nlinarith
  have s2 := sqrt2_le
  have sK := sqrtK4_le
  have h7 : 0.02158 * √2 / L ≤ 0.02158 * 1.414214 / a :=
    div_le_div_of_nonneg_left (by positivity) ha0 haL |>.trans' (by gcongr)
  have h9 := h5 0.057144 (by norm_num)
  have h10 : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) ≤
      8 * 1.4262 * 1.73207 * 0.347013 / (a * sa) :=
    (h5 _ (by positivity)).trans (by gcongr)
  gcongr

theorem log55_le : Real.log 55 ≤ 4.0074 := by
  have := log_le_num (z := 55) 4 0.0074 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem bM1_asym {L : ℝ} (hL : 55 ≤ L) :
    √(12 * a1F0 L * bX0 L * bB0 L) ≤ 1.0091 * (L * √L) := by
  have hL0 : 0 < L := by linarith
  set s := Real.log L
  have hs0 : Real.log 55 ≤ s := Real.log_le_log (by norm_num) hL
  set d := s - Real.log 55
  have hd : 0 ≤ d := by simp only [d]; linarith
  have hs : s ≤ 4.0074 + d := by simp only [d]; linarith [log55_le]
  have hLd : 55 * (1 + d + d ^ 2 / 2) ≤ L := by
    have h1 := Real.quadratic_le_exp_of_nonneg hd
    have h2 : rexp d * 55 = L := by
      simp only [d, s]; rw [Real.exp_sub, Real.exp_log hL0, Real.exp_log (by norm_num)]; field_simp
    nlinarith
  have hs1 : 0 ≤ s := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 55 by norm_num)]
  have hG0 : 0 ≤ bG L := by
    unfold bG
    have : 1.2037 ≤ Real.log (L - 6.1452) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      have h := Real.exp_bound' (x := 0.2037) (by norm_num) (by norm_num) (n := 4) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      have e : rexp 1.2037 = rexp 1 * rexp 0.2037 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 0.2037, Real.exp_pos 1]
    linarith
  have hF : a1F0 L ≤ 1.7882 * s + 0.9549 := by
    unfold a1F0; have := Real.log_le_log (by linarith) (show L - 1.7917 ≤ L by linarith); linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  have hX : bX0 L ≤ L * (s - 0.2037) := by
    unfold bX0
    have h1 : bG L ≤ s - 1.2037 := by
      unfold bG; have := Real.log_le_log (by linarith) (show L - 6.1452 ≤ L by linarith); linarith
    nlinarith
  have hX0 : 0 ≤ bX0 L := by
    unfold bX0; nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 0.9654 by linarith) hG0]
  have hB : bB0 L ≤ 0.15107 * L := by unfold bB0; linarith
  have hB0 : 0 ≤ bB0 L := by unfold bB0; nlinarith
  have hl55 : (0.2037 : ℝ) ≤ Real.log 55 := by
    have := le_log_num (z := 55) 0 0.2037 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at this ⊢; linarith
  have hs2 : 0 ≤ s - 0.2037 := by linarith
  have hpoly : 12 * (1.7882 * s + 0.9549) * (s - 0.2037) * 0.15107 ≤ 1.0091 ^ 2 * L := by
    have : 12 * (1.7882 * s + 0.9549) * (s - 0.2037) * 0.15107 ≤
        12 * (1.7882 * (4.0074 + d) + 0.9549) * (4.0074 + d - 0.2037) * 0.15107 := by
      gcongr
    nlinarith [mul_nonneg hd hd]
  have hprod : 12 * a1F0 L * bX0 L * bB0 L ≤ 1.0091 ^ 2 * L ^ 3 := by
    calc 12 * a1F0 L * bX0 L * bB0 L ≤ 12 * (1.7882 * s + 0.9549) * (L * (s - 0.2037)) *
          (0.15107 * L) := by
          apply mul_le_mul _ hB hB0
            (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (mul_nonneg hL0.le hs2))
          exact mul_le_mul (by linarith) hX hX0 (mul_nonneg (by norm_num) (by linarith))
      _ = 12 * (1.7882 * s + 0.9549) * (s - 0.2037) * 0.15107 * L ^ 2 := by ring
      _ ≤ 1.0091 ^ 2 * L * L ^ 2 := by gcongr
      _ = _ := by ring
  have hss : √L * √L = L := Real.mul_self_sqrt hL0.le
  rw [Real.sqrt_le_left (by positivity)]
  calc 12 * a1F0 L * bX0 L * bB0 L ≤ 1.0091 ^ 2 * L ^ 3 := hprod
    _ = (1.0091 * (L * √L)) ^ 2 := by rw [mul_pow, mul_pow, sq (√L), hss]; ring

theorem bE_asym {L : ℝ} (hL : 55 ≤ L) : bE L ≤ 0.1628 := by
  have hL0 : 0 < L := by linarith
  have hsL : 7.4161 ≤ √L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  -- `F₀(L)/L² ≤ F₀(55)/55²` via `log(L - 1.7917) ≤ log 53.2083 + (L - 55)/53.2083`.
  have hlog : Real.log (L - 1.7917) ≤ 3.9743 + (L - 55) / 53.2 := by
    have h0 : Real.log 53.2083 ≤ 3.9743 := by
      have := log_le_num (z := 53.2083) 3 0.9743 (by norm_num) (by norm_num) (by norm_num [taylor6])
      norm_num at this ⊢; linarith
    have h1 : Real.log (L - 1.7917) = Real.log 53.2083 + Real.log ((L - 1.7917) / 53.2083) := by
      rw [← Real.log_mul (by norm_num) (div_pos (by linarith) (by norm_num)).ne']; congr 1; field_simp
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (L - 1.7917) / 53.2083 by
      apply div_pos <;> linarith)
    have h3 : (L - 1.7917) / 53.2083 - 1 ≤ (L - 55) / 53.2 := by
      rw [div_sub_one (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith
  have hF0 : 0 ≤ a1F0 L := by
    unfold a1F0; have := Real.log_nonneg (show (1 : ℝ) ≤ L - 1.7917 by linarith); positivity
  have hW : √(0.24083 * a1F0 L / 2) ≤ 1.0328 * (L / 55) := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold a1F0
    have hv : 1 ≤ L / 55 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have e : (L - 55) / 53.2 = 55 / 53.2 * (L / 55 - 1) := by field_simp
    rw [e] at hlog
    nlinarith
  have s2 := sqrt2_le
  have sK := sqrtK4_le
  have h1 : 1 / L ≤ 1 / 55 := one_div_le_one_div_of_le (by norm_num) hL
  have h3 : 1 - 6.0119 / L ≤ 1 := by
    have : 0 ≤ 6.0119 / L := by positivity
    linarith
  have h3' : 0 ≤ 1 - 6.0119 / L := by rw [sub_nonneg, div_le_one hL0]; linarith
  have hA : 0.612373 * (3.4658 * (1 / L + 1.1836 / L ^ 2)) ≤
      0.612373 * (3.4658 * (1 / 55 + 1.1836 / 3025)) := by
    have : 1.1836 / L ^ 2 ≤ 1.1836 / 3025 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    gcongr
  have hB : 0.70712 * 1.73207 * (1 / L + 1.0373 / L ^ 2) ≤ 0.70712 * 1.73207 * (1 / 55 + 1.0373 / 3025) := by
    have : 1.0373 / L ^ 2 ≤ 1.0373 / 3025 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    gcongr
  have hC : 0.0019072 * (√2 * (1 - 6.0119 / L)) ≤ 0.0019072 * 1.414214 := by
    have : √2 * (1 - 6.0119 / L) ≤ 1.414214 * 1 := mul_le_mul s2 h3 h3' (by norm_num)
    linarith
  have hD : 0.02158 * √2 / L ≤ 0.02158 * 1.414214 / 55 := by
    rw [div_eq_mul_one_div (0.02158 * √2) L, div_eq_mul_one_div (0.02158 * 1.414214) 55]
    gcongr
  have hE : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) / (L * √L) ≤
      8 * 1.4262 * 1.73207 * 0.347013 / (55 * 7.4161) := by
    rw [div_eq_mul_one_div _ (L * √L), div_eq_mul_one_div _ (55 * 7.4161)]
    have : 1 / (L * √L) ≤ 1 / (55 * 7.4161) :=
      one_div_le_one_div_of_le (by norm_num) (mul_le_mul hL hsL (by norm_num) hL0.le)
    gcongr
  have hF : 4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2)) ≤
      4 * 1.0328 * (0.057144 / 7.4161 + 0.0848 * (1 + 2.3015 / 55)) / 55 := by
    have e : 4 * √(0.24083 * a1F0 L / 2) * (0.057144 / (L * √L) + 0.0848 * (1 / L + 2.3015 / L ^ 2)) =
        4 * (√(0.24083 * a1F0 L / 2) / L) * (0.057144 / √L + 0.0848 * (1 + 2.3015 / L)) := by
      field_simp
    rw [e]
    have hW' : √(0.24083 * a1F0 L / 2) / L ≤ 1.0328 / 55 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
    have hq : 0.057144 / √L ≤ 0.057144 / 7.4161 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsL
    have hq2 : 2.3015 / L ≤ 2.3015 / 55 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have : 4 * (√(0.24083 * a1F0 L / 2) / L) * (0.057144 / √L + 0.0848 * (1 + 2.3015 / L)) ≤
        4 * (1.0328 / 55) * (0.057144 / 7.4161 + 0.0848 * (1 + 2.3015 / 55)) := by
      gcongr
    refine this.trans (le_of_eq ?_); ring
  unfold bE
  have : (4 : ℝ) * (0.49075 * (0.612373 * (3.4658 * (1 / 55 + 1.1836 / 3025)) +
      0.0019072 * 1.414214 + 0.70712 * 1.73207 * (1 / 55 + 1.0373 / 3025) +
      0.02158 * 1.414214 / 55)) +
      8 * 1.4262 * 1.73207 * 0.347013 / (55 * 7.4161) +
      4 * 1.0328 * (0.057144 / 7.4161 + 0.0848 * (1 + 2.3015 / 55)) / 55 ≤ 0.1628 := by
    norm_num
  nlinarith

end TernaryGoldbach.MinorArcs
