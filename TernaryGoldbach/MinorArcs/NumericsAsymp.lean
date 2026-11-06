import TernaryGoldbach.MinorArcs.NumericsCells

/-!
# The numerics for `y = x/κ ≥ 10¹⁰⁰`

With `r₂ = ⌊y^{1/4}⌋`: the levels `n ≤ N₈` (the last block point of cell 8) are bounded by the
chain of cell 8; for `N₈ ≤ n ≤ y^{1/4}`, `R_{y,2n} ≤ 0.6628` and crude bounds give
`ĝ(y, n) ≤ 26.6 n^{-1/4} + 1.398 (3.8 y^{-1/6} + h(y))`; `Σ n^{-5/4}` telescopes.
-/

open Real Set

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (κ)

/-- `R_{y,2n} ≤ 0.6628` when `n⁴ ≤ y`. -/
theorem R_le_of_pow_four {y n : ℝ} (hy : 0 < y) (hn : 1 ≤ n) (hny : n ^ 4 ≤ y) :
    R y (2 * n) ≤ 0.6628 := by
  have hn0 : 0 < n := by linarith
  have hY : 0 < y ^ (1 / 3 : ℝ) := by positivity
  have hY3 : (y ^ (1 / 3 : ℝ)) ^ 3 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  set B := 9 * y ^ (1 / 3 : ℝ) / (4.008 * n) with hB
  have hB0 : 0 < B := by positivity
  -- `8n ≤ B³`
  have hB3 : 8 * n ≤ B ^ 3 := by
    have e : B ^ 3 = 729 * y / (4.008 ^ 3 * n ^ 3) := by
      simp only [hB]; rw [div_pow, mul_pow, mul_pow, hY3]; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hn0 4]
  have hB1 : 1 < B := by
    by_contra h; push Not at h
    have : B ^ 3 ≤ 1 := pow_le_one₀ hB0.le h
    linarith
  have hlB : 0 < Real.log B := Real.log_pos hB1
  have h8 : Real.log (8 * n) ≤ 3 * Real.log B := by
    have := Real.log_le_log (by positivity) hB3
    rw [Real.log_pow] at this; push_cast at this; linarith
  unfold R
  rw [show 4 * (2 * n) = 8 * n by ring,
    show 9 * y ^ (1 / 3 : ℝ) / (2.004 * (2 * n)) = B by rw [hB]; ring]
  have hq : Real.log (8 * n) / (2 * Real.log B) ≤ 1.5 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ Real.log (8 * n) / (2 * Real.log B) :=
    div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hl : Real.log (1 + Real.log (8 * n) / (2 * Real.log B)) ≤ Real.log 2.5 :=
    Real.log_le_log (by linarith) (by linarith)
  have h25 : Real.log 2.5 ≤ 0.9164 := by
    have := log_le_num (z := 2.5) 0 0.9164 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- Crude bound for large levels: `ĝ(y, n) ≤ 2 n^{-1/4} + 1.398 (3.8 y^{-1/6} + h(y))` for
`8·10¹⁶ ≤ n`, `n⁴ ≤ y`, `y ≥ 10¹⁰⁰`. -/
theorem ghatY_le_asym {y n : ℝ} (hy : 1e100 ≤ y) (hn : 8e16 ≤ n) (hny : n ^ 4 ≤ y) :
    ghatY y n ≤ 2 * n ^ (-1 / 4 : ℝ) + 1.398 * (3.8 * y ^ (-1 / 6 : ℝ) + hfun y) := by
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < n := by linarith
  set t := n ^ (1 / 16 : ℝ) with ht_def
  have ht0 : 0 < t := by positivity
  have ht16 : t ^ 16 = n := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have ht11 : 11 ≤ t := by
    by_contra h; push Not at h
    have : t ^ 16 < 11 ^ 16 := by gcongr
    rw [ht16] at this; norm_num at this; linarith
  have hn8 : n ^ (1 / 8 : ℝ) = t ^ 2 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hn4 : n ^ (-1 / 4 : ℝ) = (t ^ 4)⁻¹ := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_neg hn0.le]; norm_num
  -- logarithms
  have hlog2n : Real.log (2 * n) ≤ 8.73 * t ^ 2 := by
    have h := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 * n by positivity) (show (0:ℝ) < 1 / 8 by norm_num)
    rw [Real.mul_rpow (by norm_num) hn0.le, hn8] at h
    have h2 : (2:ℝ) ^ (1 / 8 : ℝ) ≤ 1.0906 := by
      rw [show (1.0906 : ℝ) = ((1.0906 : ℝ) ^ (8:ℕ)) ^ (1 / 8 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
      exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    have : (2:ℝ) ^ (1 / 8 : ℝ) * t ^ 2 / (1 / 8) ≤ 8.73 * t ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg t]
    linarith
  have hlogn : Real.log n ≤ 8 * t ^ 2 := by
    have h := Real.log_le_rpow_div hn0.le (show (0:ℝ) < 1 / 8 by norm_num)
    rw [hn8] at h; linarith
  have hlogn39 : 38.9 ≤ Real.log n := by
    have := le_log_num (z := 8e16) 38 0.9 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hn
    norm_num at *; linarith
  have hll : 3.6 ≤ Real.log (Real.log n) := by
    have := le_log_num (z := 38.9) 3 0.6 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hlogn39
    norm_num at *; linarith
  have hll2 : Real.log (Real.log n) ≤ 8 * t ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith); linarith
  have hF : Fr n ≤ 14.4 * t ^ 2 := by
    unfold Fr
    have hg := exp_gamma_le_sharp
    have h1 : rexp eulerMascheroniConstant * Real.log (Real.log n) ≤ 1.7882 * (8 * t ^ 2) :=
      mul_le_mul hg hll2 (by linarith) (by norm_num)
    have h2 : 2.50637 / Real.log (Real.log n) ≤ 0.7 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have hFpos : 0 < Fr n := Fr_pos (by linarith)
  have hsF : √(Fr n) ≤ 3.795 * t := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hs2n : 1.414 * t ^ 8 ≤ √(2 * n) := by
    rw [Real.le_sqrt (by positivity) (by positivity), ← ht16]; nlinarith [pow_pos ht0 16]
  have hR := R_le_of_pow_four hy0 (by linarith) hny
  have hR0 : 0 ≤ R y (2 * n) := by
    have h6 : 6 * n ≤ y ^ (1 / 3 : ℝ) := le_rpow_third (by positivity) (by
      have : 216 * n ^ 3 ≤ n ^ 4 := by
        have : (216:ℝ) ≤ n := by linarith
        nlinarith [pow_pos hn0 3]
      nlinarith)
    exact R_nonneg (by linarith) (by linarith)
  have hl2n0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hA : (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.526 ≤ 22 * t ^ 3 := by
    have h1 : R y (2 * n) * Real.log (2 * n) ≤ 0.6628 * (8.73 * t ^ 2) :=
      mul_le_mul hR hlog2n hl2n0 (by norm_num)
    have h2 := mul_le_mul (add_le_add_right h1 0.8764) hsF (Real.sqrt_nonneg _) (by positivity)
    nlinarith [pow_pos ht0 3]
  have hA' : ((R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.526) / √(2 * n) ≤
      1.415 * (t ^ 4)⁻¹ := by
    have hpos : 0 < 1.414 * t ^ 8 := by positivity
    have hnum0 : 0 ≤ (R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.526 := by
      have := mul_nonneg hR0 hl2n0; positivity
    calc ((R y (2 * n) * Real.log (2 * n) + 0.8764) * √(Fr n) + 2.526) / √(2 * n)
        ≤ 22 * t ^ 3 / (1.414 * t ^ 8) := div_le_div₀ (by positivity) hA hpos hs2n
      _ ≤ 1.415 * (t ^ 4)⁻¹ := by
          rw [div_le_iff₀ hpos]
          have : 22 * t ^ 3 ≤ 1.415 * 1.414 * t ^ 4 := by nlinarith [pow_pos ht0 3]
          have e : 1.415 * (t ^ 4)⁻¹ * (1.414 * t ^ 8) = 1.415 * 1.414 * t ^ 4 := by
            field_simp
          rw [e]; exact this
  have hL : Lg (2 * n) / n ≤ 0.005 * (t ^ 4)⁻¹ := by
    unfold Lg
    rw [show 2 * n / 2 = n by ring]
    have h1 : Fr n * (13 / 4 * Real.log (2 * n) + 7.82) ≤ 14.4 * t ^ 2 * (13 / 4 * (8.73 * t ^ 2) + 7.82) :=
      mul_le_mul hF (by linarith) (by positivity) (by positivity)
    have ht2 : (121:ℝ) ≤ t ^ 2 := by nlinarith
    have hpoly : 14.4 * t ^ 2 * (13 / 4 * (8.73 * t ^ 2) + 7.82) + 13.66 * (8.73 * t ^ 2) + 37.55 ≤
        412 * t ^ 4 := by
      have e : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [e]; nlinarith [ht2]
    have hnum : Fr n * (13 / 4 * Real.log (2 * n) + 7.82) + 13.66 * Real.log (2 * n) + 37.55 ≤
        412 * t ^ 4 := by linarith
    rw [div_le_iff₀ hn0]
    have e : 0.005 * (t ^ 4)⁻¹ * n = 0.005 * t ^ 12 := by rw [← ht16]; field_simp
    rw [e]
    have : 412 * t ^ 4 ≤ 0.005 * t ^ 12 := by
      have h8 : (82400 : ℝ) ≤ t ^ 8 := by
        have : (11:ℝ) ^ 8 ≤ t ^ 8 := by gcongr
        norm_num at this; linarith
      have h412 : 412 ≤ 0.005 * t ^ 8 := by linarith
      calc 412 * t ^ 4 ≤ 0.005 * t ^ 8 * t ^ 4 := mul_le_mul_of_nonneg_right h412 (pow_pos ht0 4).le
        _ = 0.005 * t ^ 12 := by ring
    linarith
  have hgx : gx y n ≤ 1.42 * (t ^ 4)⁻¹ + 3.8 * y ^ (-1 / 6 : ℝ) := by
    unfold gx; linarith
  have hε : 17 * (670 / n) ^ 3 / 3 ≤ 0.01 * (t ^ 4)⁻¹ := by
    rw [← ht16]
    have e : 17 * (670 / t ^ 16) ^ 3 / 3 = 17 * 670 ^ 3 / 3 * ((t ^ 4)⁻¹ * (t ^ 44)⁻¹) := by
      field_simp
    rw [e]
    have h44 : (17 * 670 ^ 3 / 3 : ℝ) * (t ^ 44)⁻¹ ≤ 0.01 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have : (11:ℝ) ^ 44 ≤ t ^ 44 := by gcongr
      norm_num at this ⊢; nlinarith
    have : 0 ≤ (t ^ 4)⁻¹ := by positivity
    nlinarith
  have hh0 : 0 ≤ hfun y := hfun_nonneg (by linarith)
  have hmax : max (gx y n) (hfun y) ≤ gx y n + hfun y := by
    have : 0 ≤ gx y n := by
      unfold gx
      have := mul_nonneg hR0 hl2n0
      have : 0 ≤ Lg (2 * n) / n := by
        unfold Lg; rw [show 2 * n / 2 = n by ring]
        have : 0 ≤ Fr n * (13 / 4 * Real.log (2 * n) + 7.82) := mul_nonneg hFpos.le (by positivity)
        positivity
      positivity
    exact max_le (by linarith) (by linarith)
  unfold ghatY
  rw [hn4]
  have h1 := mul_le_mul_of_nonneg_left hmax (show (0:ℝ) ≤ 1.398 by norm_num)
  have hinv : 0 ≤ (t ^ 4)⁻¹ := by positivity
  linarith [hgx, hε]

/-- `n^{-1/4} log((n+1)/n) ≤ 7 ((n-1)^{-1/4} - n^{-1/4})` for `n ≥ 2`. -/
theorem quarter_term_le {n : ℝ} (hn : 2 ≤ n) :
    n ^ (-1 / 4 : ℝ) * Real.log ((n + 1) / n) ≤ 7 * ((n - 1) ^ (-1 / 4 : ℝ) - n ^ (-1 / 4 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  set a := n ^ (-1 / 4 : ℝ) with ha
  set b := (n - 1) ^ (-1 / 4 : ℝ) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have ha4 : a ^ 4 = n⁻¹ := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num; rw [Real.rpow_neg_one]
  have hb4 : b ^ 4 = (n - 1)⁻¹ := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]; norm_num; rw [Real.rpow_neg_one]
  have hlog : Real.log ((n + 1) / n) ≤ a ^ 4 := by
    rw [ha4]
    have := Real.log_le_sub_one_of_pos (show 0 < (n + 1) / n by positivity)
    have e : (n + 1) / n - 1 = n⁻¹ := by field_simp; ring
    linarith
  -- `b⁴ - a⁴ ≥ a⁸` and `b⁴ ≤ 2 a⁴`
  have h1 : a ^ 8 ≤ b ^ 4 - a ^ 4 := by
    rw [hb4, ha4, show a ^ 8 = (a ^ 4) ^ 2 by ring, ha4]
    rw [inv_pow, ← sub_nonneg]
    have : (n - 1)⁻¹ - n⁻¹ - (n ^ 2)⁻¹ = 1 / (n ^ 2 * (n - 1)) := by field_simp; ring
    rw [this]; positivity
  have h2 : b ^ 4 ≤ 2 * a ^ 4 := by
    rw [hb4, ha4, inv_le_iff_one_le_mul₀ hn1]
    field_simp; nlinarith
  have hab : a ≤ b := by
    by_contra h; push Not at h
    have : b ^ 4 < a ^ 4 := by gcongr
    nlinarith [pow_pos ha0 8]
  -- `b ≤ 1.19 a`, so `b³ ≤ 1.69 a³`
  have h3 : b ≤ 1.19 * a := by
    by_contra h; push Not at h
    have : (1.19 * a) ^ 4 < b ^ 4 := by gcongr
    nlinarith [pow_pos ha0 4]
  have h4 : b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3 ≤ 6.73 * a ^ 3 := by
    have hb1 : b ^ 2 ≤ (1.19 * a) ^ 2 := pow_le_pow_left₀ hb0.le h3 2
    have hb3 : b ^ 3 ≤ (1.19 * a) ^ 3 := pow_le_pow_left₀ hb0.le h3 3
    nlinarith [pow_pos ha0 2, pow_pos ha0 3]
  have h5 : a ^ 8 ≤ (b - a) * (6.73 * a ^ 3) := by
    have e : b ^ 4 - a ^ 4 = (b - a) * (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) := by ring
    have := mul_le_mul_of_nonneg_left h4 (sub_nonneg.2 hab)
    linarith
  have h6 : a ^ 5 ≤ 6.73 * (b - a) := by
    have ha3 : 0 < a ^ 3 := by positivity
    have : a ^ 5 * a ^ 3 ≤ 6.73 * (b - a) * a ^ 3 := by nlinarith
    exact le_of_mul_le_mul_right this ha3
  calc a * Real.log ((n + 1) / n) ≤ a * a ^ 4 := mul_le_mul_of_nonneg_left hlog ha0.le
    _ = a ^ 5 := by ring
    _ ≤ 7 * (b - a) := by nlinarith [sub_nonneg.2 hab]

theorem sum_quarter_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ico N M, (n : ℝ) ^ (-1 / 4 : ℝ) * Real.log (((n : ℝ) + 1) / n) ≤
      7 * (((N : ℝ) - 1) ^ (-1 / 4 : ℝ) - ((M : ℝ) - 1) ^ (-1 / 4 : ℝ)) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk]
    have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hN.trans hk
    have := quarter_term_le hk2
    push_cast
    rw [show (k : ℝ) + 1 - 1 = k by ring]
    linarith

/-- `(s + c)^k e^{-ps} ≤ (s₁ + c)^k e^{-p s₁}` for `s ≥ s₁`, if `k ≤ p (s₁ + c)`. -/
theorem pow_mul_exp_le {c k p s₁ s : ℝ} (hp : 0 < p) (hc : 0 < s₁ + c)
    (hks : k ≤ p * (s₁ + c)) (hs : s₁ ≤ s) :
    (s + c) ^ k * rexp (-p * s) ≤ (s₁ + c) ^ k * rexp (-p * s₁) := by
  have hA := antitoneOn_mul_exp_neg (Q := fun s => (s + c) ^ k)
    (Q' := fun s => k * (s + c) ^ (k - 1)) (s₁ := s₁) (s₂ := s) (p := p)
    (fun u hu => by
      have h := ((hasDerivAt_id u).add_const c).rpow_const (p := k) (Or.inl (by
        have := hu.1; simp only [id]; linarith))
      convert h using 1
      · ext y; simp
      · simp)
    (fun u hu => by
      have hu0 : 0 < u + c := by linarith [hu.1]
      have e : (u + c) ^ k = (u + c) * (u + c) ^ (k - 1) := by
        have := Real.rpow_add hu0 1 (k - 1)
        rw [Real.rpow_one, show 1 + (k - 1) = k by ring] at this
        exact this
      rw [e]
      have : 0 ≤ (u + c) ^ (k - 1) := by positivity
      have : k ≤ p * (u + c) := by nlinarith [hu.1]
      nlinarith)
  exact hA ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs

theorem exp_neg_le_num {u : ℝ} (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (hu : (n : ℝ) + f ≤ u) :
    rexp (-u) ≤ 1 / (2.7182818283 ^ n * taylor6 f) := by
  have h := exp_ge_aux n h0
  have hpos : 0 < 2.7182818283 ^ n * taylor6 f := by unfold taylor6; positivity
  rw [Real.exp_neg, le_div_iff₀ hpos, ← div_eq_inv_mul, div_le_one (Real.exp_pos _)]
  exact h.trans (Real.exp_le_exp.2 hu)

/-! ## `y ≥ 10¹⁰⁰` -/

/-- `Ξ(y) = 3.8 y^{-1/6} + h(y)` is negligible: `(L + 3.9) Ξ(y) ≤ 10⁻¹⁰`, `L = log y ≥ 230.25`. -/
theorem Xi_le {y : ℝ} (hy : 1e100 ≤ y) :
    (Real.log y + 3.9) * (3.8 * y ^ (-1 / 6 : ℝ) + hfun y) ≤ 1e-10 := by
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  have hL230 : 230.25 ≤ L := by
    have := le_log_num (z := 1e100) 230 0.25 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hy
    norm_num at *; linarith
  set E := rexp (-(1 / 6) * L) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have e6 : y ^ (-1 / 6 : ℝ) = E := by
    rw [Real.rpow_def_of_pos hy0, ← hL, hE_def]; congr 1; ring
  have e3 : y ^ (-1 / 3 : ℝ) = E * E := by
    rw [Real.rpow_def_of_pos hy0, ← hL, hE_def, ← Real.exp_add]; congr 1; ring
  set W := L + 3.9 with hW
  have hW0 : 100 ≤ W := by linarith
  have hEv : rexp (-(1 / 6) * 230.25) ≤ 2.2e-17 := by
    have := exp_neg_le_num (u := 1 / 6 * 230.25) 38 0.375 (by norm_num) (by norm_num)
    rw [show -(1 / 6 : ℝ) * 230.25 = -(1 / 6 * 230.25) by ring]
    refine this.trans ?_
    rw [div_le_iff₀ (by unfold taylor6; positivity)]; unfold taylor6; norm_num
  have hm52 := pow_mul_exp_le (c := 3.9) (k := 5 / 2) (p := 1 / 6) (s₁ := 230.25) (s := L)
    (by norm_num) (by norm_num) (by norm_num) hL230
  have hm1 := pow_mul_exp_le (c := 3.9) (k := 1) (p := 1 / 6) (s₁ := 230.25) (s := L)
    (by norm_num) (by norm_num) (by norm_num) hL230
  rw [Real.rpow_one, Real.rpow_one] at hm1
  rw [← hW, ← hE_def] at hm52 hm1
  have h52 : (230.25 + 3.9 : ℝ) ^ (5 / 2 : ℝ) ≤ 840000 := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_two,
      ← Real.sqrt_eq_rpow]
    have : √(230.25 + 3.9 : ℝ) ≤ 15.31 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  have hW52 : W ^ (5 / 2 : ℝ) * E ≤ 840000 * 2.2e-17 := by
    have := mul_le_mul h52 hEv (Real.exp_pos _).le (by norm_num)
    linarith
  have hW1 : W * E ≤ 234.15 * 2.2e-17 := by
    have := mul_le_mul_of_nonneg_left hEv (show (0:ℝ) ≤ 230.25 + 3.9 by norm_num)
    norm_num at hm1 this ⊢; linarith
  -- `W^{3/2}` and the pieces
  have hW32 : (1000 : ℝ) ≤ W ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : (10 : ℝ) ≤ √W := by rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
    nlinarith
  have hW52e : W ^ (5 / 2 : ℝ) = W * W ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hLs : L ^ (3 / 2 : ℝ) ≤ W ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  unfold hfun
  rw [e6, e3, ← hL]
  -- `(W)(3.8E + 0.276 E L^{3/2} + 1234 E² L) ≤ 0.29 W^{5/2} E`
  have hL0 : 0 ≤ L := by linarith
  have hLs0 : 0 ≤ L ^ (3 / 2 : ℝ) := by positivity
  have t1 : 3.8 ≤ 0.004 * W ^ (3 / 2 : ℝ) := by linarith
  have t2 : 1234 * E * L ≤ 1e-11 * W ^ (3 / 2 : ℝ) := by
    have : E * L ≤ W * E := by nlinarith
    nlinarith
  have key : W * (3.8 * E + (0.276 * E * L ^ (3 / 2 : ℝ) + 1234 * (E * E) * L)) ≤
      0.29 * (W ^ (5 / 2 : ℝ) * E) := by
    rw [hW52e]
    have : 3.8 * E + (0.276 * E * L ^ (3 / 2 : ℝ) + 1234 * (E * E) * L) ≤
        0.29 * (W ^ (3 / 2 : ℝ) * E) := by
      have a1 : 3.8 * E ≤ 0.004 * W ^ (3 / 2 : ℝ) * E := mul_le_mul_of_nonneg_right t1 hE0.le
      have a2 : 0.276 * E * L ^ (3 / 2 : ℝ) ≤ 0.276 * E * W ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hLs (by positivity)
      have a3 : 1234 * (E * E) * L = (1234 * E * L) * E := by ring
      have a4 : (1234 * E * L) * E ≤ 1e-11 * W ^ (3 / 2 : ℝ) * E := mul_le_mul_of_nonneg_right t2 hE0.le
      nlinarith
    have hW0' : 0 ≤ W := by linarith
    calc W * (3.8 * E + (0.276 * E * L ^ (3 / 2 : ℝ) + 1234 * (E * E) * L))
        ≤ W * (0.29 * (W ^ (3 / 2 : ℝ) * E)) := mul_le_mul_of_nonneg_left this hW0'
      _ = 0.29 * (W * W ^ (3 / 2 : ℝ) * E) := by ring
  have : 0.29 * (W ^ (5 / 2 : ℝ) * E) ≤ 1e-10 := by nlinarith
  linarith

theorem Phi1_le {y : ℝ} (hy : 1e100 ≤ y) : (Real.log y + 3.9) * y ^ (-1 / 16 : ℝ) ≤ 1.4e-4 := by
  have hy0 : 0 < y := by linarith
  have hL230 : 230.25 ≤ Real.log y := by
    have := le_log_num (z := 1e100) 230 0.25 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hy
    norm_num at *; linarith
  have e : y ^ (-1 / 16 : ℝ) = rexp (-(1 / 16) * Real.log y) := by
    rw [Real.rpow_def_of_pos hy0]; congr 1; ring
  rw [e]
  have hm := pow_mul_exp_le (c := 3.9) (k := 1) (p := 1 / 16) (s₁ := 230.25) (s := Real.log y)
    (by norm_num) (by norm_num) (by norm_num) hL230
  rw [Real.rpow_one, Real.rpow_one] at hm
  have hEv : rexp (-(1 / 16) * 230.25) ≤ 5.7e-7 := by
    have := exp_neg_le_num (u := 1 / 16 * 230.25) 14 0.39 (by norm_num) (by norm_num)
    rw [show -(1 / 16 : ℝ) * 230.25 = -(1 / 16 * 230.25) by ring]
    refine this.trans ?_
    rw [div_le_iff₀ (by unfold taylor6; positivity)]; unfold taylor6; norm_num
  have := mul_le_mul_of_nonneg_left hEv (show (0:ℝ) ≤ 230.25 + 3.9 by norm_num)
  linarith

set_option maxHeartbeats 4000000 in
/-- **The numerics for `x ≥ 4.9·10¹⁰¹`** (`y ≥ 10¹⁰⁰`), with `r₂ = ⌊y^{1/4}⌋`. -/
theorem asymp_goal {x : ℝ} (hx : 4.9e101 ≤ x) : NumericsGoal x := by
  have hκ : (κ : ℝ) = 49 := rfl
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy_def
  have hy : 1e100 ≤ y := by rw [hy_def, hκ, le_div_iff₀ (by norm_num)]; linarith
  have hy0 : 0 < y := by linarith
  set q := y ^ (1 / 4 : ℝ) with hq_def
  have hq0 : 0 < q := by positivity
  have hq4 : q ^ 4 = y := by
    rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hq25 : 1e25 ≤ q := by
    by_contra h; push Not at h
    have : q ^ 4 < (1e25 : ℝ) ^ 4 := by gcongr
    rw [hq4] at this; norm_num at this; linarith
  set r₂ := ⌊q⌋₊ with hr₂_def
  have hr₂q : (r₂ : ℝ) ≤ q := Nat.floor_le hq0.le
  have hr₂q' : q / 2 ≤ r₂ := by
    have := Nat.lt_floor_add_one q; rw [← hr₂_def] at this; linarith
  have hr₂N : (82861350433499550 : ℝ) ≤ r₂ := by linarith
  have hr₂Nn : 82861350433499550 ≤ r₂ := by exact_mod_cast hr₂N
  have hr₂1 : 1 ≤ r₂ := by omega
  -- logs
  have hL230 : 230.25 ≤ Real.log y := by
    have := le_log_num (z := 1e100) 230 0.25 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hy
    norm_num at *; linarith
  have hlogx : Real.log x = Real.log 49 + Real.log y := by
    rw [hy_def, hκ, Real.log_div hx0.ne' (by norm_num)]; ring
  have hl49 : Real.log 49 ≤ 3.892 := by
    have := log_le_num (z := 49) 3 0.892 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  have hl49' : 3.891 ≤ Real.log 49 := by
    have := le_log_num (z := 49) 3 0.891 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  have hlogq : Real.log q = Real.log y / 4 := by
    rw [hq_def, Real.log_rpow hy0]; ring
  have hL₀ : (234.14 : ℝ) ≤ Real.log x := by
    have := le_log_num (z := 4.9e101) 234 0.14 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have := Real.log_le_log (by norm_num) hx
    norm_num at *; linarith
  -- size conditions
  have hq2 : (65536 : ℝ) ≤ q ^ 2 := by nlinarith
  have hxq : x = 49 * q ^ 4 := by rw [hq4, hy_def, hκ]; field_simp
  obtain ⟨c1, c2, c3, c4, c5⟩ := cell_conditions (X := x) (ℓr := Real.log (2 * q)) (L₀ := Real.log x)
    (r₂ := r₂) le_rfl hx0 hr₂1
    (by
      have : (20000 * (r₂ : ℝ)) ^ 2 ≤ (20000 * q) ^ 2 := by gcongr
      rw [hxq]; nlinarith)
    (by
      have : (2 * (r₂ : ℝ)) ^ 10 ≤ (2 * q) ^ 10 := by gcongr
      rw [hxq]
      have e : (4 * (49 * q ^ 4) / 784) ^ 3 = (q ^ 2) ^ 6 / 64 := by ring
      have e2 : (2 * q) ^ 10 = 1024 * (q ^ 2) ^ 5 := by ring
      rw [e]; rw [e2] at this
      have : 1024 * (q ^ 2) ^ 5 ≤ (q ^ 2) ^ 6 / 64 := by
        have h5 : 0 < (q ^ 2) ^ 5 := by positivity
        have : (q ^ 2) ^ 6 = q ^ 2 * (q ^ 2) ^ 5 := by ring
        rw [this]; nlinarith
      linarith)
    (by
      have : (6 * (r₂ : ℝ)) ^ 3 ≤ (6 * q) ^ 3 := by gcongr
      rw [hxq]
      have : 216 * q ^ 3 ≤ q ^ 4 := by nlinarith [pow_pos hq0 3]
      nlinarith)
    (by rw [hxq]; nlinarith [pow_pos hq0 3])
    (Real.log_le_log (by positivity) (by linarith))
    (by
      rw [Real.log_mul (by norm_num) hq0.ne', hlogq, hlogx]
      have := Real.log_two_lt_d9
      linarith)
    le_rfl
  refine ⟨r₂, by omega, c1, c2, c3, c4, c5, ?_⟩
  -- the pieces of `Mexpr`
  have hx26 : (4.9e26 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hsD := sig_div_Dx_le hx26 (by norm_num) hL₀
  obtain ⟨h14a, h14b⟩ := log14_bounds
  have hcE : cE = 1.33258 := rfl
  set sD' : ℝ := 1.2947
  have hsD' : sig x / Dx x ≤ sD' := by
    refine hsD.trans ?_
    rw [div_le_iff₀ (by rw [hcE]; linarith)]; rw [hcE]; norm_num; linarith
  have hDpos : 0 < Dx x := by rw [Dx_eq hx0, hcE]; linarith
  have hsig0 : 0 ≤ sig x := by
    unfold sig
    have : 0 ≤ 366.91 / √x * Real.log x := by
      have := Real.log_nonneg (show (1:ℝ) ≤ x by linarith); positivity
    nlinarith
  have hsD0 : 0 ≤ sig x / Dx x := div_nonneg hsig0 hDpos.le
  have hsigx : sig x ≤ 0.6403 * (Real.log y + 3.9) := by
    have := sig_le_lin hx26; rw [hlogx] at this; nlinarith
  -- base
  have hgb := (ghatY_mono_y (Y := 1e58) (y := y) (M := ((150000 : ℕ) : ℝ)) (by norm_num) (by linarith) (by norm_num) (by
    have := le_rpow_third (Y := (1e58 : ℝ)) (u := 2.15e19) (by norm_num) (by norm_num)
    linarith)).trans c8_g0
  have hgb0 := ghatY_nonneg (y := y) (n := 150000) (by linarith) (by norm_num)
  have hcl0 : cL 150000 ≤ 14.61155 := by
    unfold cL
    have := log_le_num (z := 2 * (((150000 : ℕ) : ℝ) + 1)) 12 0.61155 (by norm_num) (by norm_num)
      (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  have hcl00 : 0 ≤ cL 150000 := by
    unfold cL; exact add_nonneg (Real.log_nonneg (by push_cast; norm_num)) (by norm_num)
  have hbase : ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294) ≤
      0.0510741 * (14.61155 * sD' - 8.6294) := by
    have h1 : cL 150000 * sig x / Dx x ≤ 14.61155 * sD' := by
      rw [mul_div_assoc]; exact mul_le_mul hcl0 hsD' hsD0 (by norm_num)
    have h2 : (0:ℝ) ≤ 14.61155 * sD' - 8.6294 := by norm_num
    calc ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294)
        ≤ ghatY y 150000 * (14.61155 * sD' - 8.6294) := mul_le_mul_of_nonneg_left (by linarith) hgb0
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hgb) h2
  -- the middle sum
  set Ξ := 3.8 * y ^ (-1 / 6 : ℝ) + hfun y with hΞ
  have hΞ0 : 0 ≤ Ξ := by
    have := hfun_nonneg (z := y) (by linarith); positivity
  have hXi := Xi_le hy
  rw [← hΞ] at hXi
  have hmid2 : ∑ n ∈ Finset.Ico 82861350433499550 r₂, ghatY y n * Real.log (((n : ℝ) + 1) / n) ≤
      8.4e-4 + 1.398 * Ξ * (Real.log y + 3.9) := by
    have hpt : ∀ n ∈ Finset.Ico 82861350433499550 r₂, ghatY y n * Real.log (((n : ℝ) + 1) / n) ≤
        2 * ((n : ℝ) ^ (-1 / 4 : ℝ) * Real.log (((n : ℝ) + 1) / n)) +
          1.398 * Ξ * Real.log (((n : ℝ) + 1) / n) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.1 hn
      have hn1' : (82861350433499550 : ℝ) ≤ n := by exact_mod_cast hn1
      have hn2' : (n : ℝ) ≤ q := (by exact_mod_cast hn2.le : (n : ℝ) ≤ r₂).trans hr₂q
      have hn4 : (n : ℝ) ^ 4 ≤ y := by rw [← hq4]; gcongr
      have h := ghatY_le_asym hy (by linarith) hn4
      have hl0 : 0 ≤ Real.log (((n : ℝ) + 1) / n) :=
        Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
      have := mul_le_mul_of_nonneg_right h hl0
      rw [← hΞ] at this
      linarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_Ico_log_eq (by norm_num) hr₂Nn]
    have h1 := sum_quarter_le (N := 82861350433499550) (M := r₂) (by norm_num) hr₂Nn
    have h2 : ((82861350433499550 : ℕ) - 1 : ℝ) ^ (-1 / 4 : ℝ) ≤ 6e-5 := by
      have e : ((82861350433499550 : ℕ) - 1 : ℝ) = 82861350433499549 := by norm_num
      rw [e]
      have h := Real.rpow_le_rpow_of_nonpos (x := (1 / 6e-5 : ℝ) ^ 4) (y := 82861350433499549)
        (z := -1 / 4) (by norm_num) (by norm_num) (by norm_num)
      have e2 : ((1 / 6e-5 : ℝ) ^ 4) ^ (-1 / 4 : ℝ) = 6e-5 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have h3 : 0 ≤ ((r₂ : ℝ) - 1) ^ (-1 / 4 : ℝ) := by
      have : (0:ℝ) ≤ r₂ - 1 := by linarith
      positivity
    have h4 : Real.log ((r₂ : ℝ) / (82861350433499550 : ℕ)) ≤ Real.log y + 3.9 := by
      have : Real.log ((r₂ : ℝ) / (82861350433499550 : ℕ)) ≤ Real.log r₂ :=
        Real.log_le_log (by positivity) (div_le_self (by positivity) (by norm_num))
      have : Real.log r₂ ≤ Real.log q := Real.log_le_log (by linarith) hr₂q
      linarith [hlogq]
    have := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 1.398 * Ξ by positivity)
    nlinarith
  have hmid1 := chain8 (y := y) (by linarith)
  have hmid : ∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) ≤
      sD' * (0.165282706731081808 + (8.4e-4 + 1.398 * 1e-10)) := by
    have e : ∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) =
        sig x / Dx x * (∑ n ∈ Finset.Ico (150001 : ℕ) 82861350433499550,
          ghatY y n * Real.log (((n : ℝ) + 1) / n) +
          ∑ n ∈ Finset.Ico 82861350433499550 r₂, ghatY y n * Real.log (((n : ℝ) + 1) / n)) := by
      rw [Finset.sum_Ico_consecutive _ (by norm_num) hr₂Nn, ← Finset.Ico_add_one_left_eq_Ioo,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    have hS0 : 0 ≤ ∑ n ∈ Finset.Ico (150001 : ℕ) 82861350433499550,
          ghatY y n * Real.log (((n : ℝ) + 1) / n) +
          ∑ n ∈ Finset.Ico 82861350433499550 r₂, ghatY y n * Real.log (((n : ℝ) + 1) / n) := by
      refine add_nonneg (Finset.sum_nonneg fun n hn => ?_) (Finset.sum_nonneg fun n hn => ?_)
      all_goals
        have hn1 : (1 : ℝ) ≤ n := by
          have := (Finset.mem_Ico.1 hn).1; exact_mod_cast (by omega : 1 ≤ n)
        exact mul_nonneg (ghatY_nonneg (by linarith) (by linarith))
          (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    have hXi' : 1.398 * Ξ * (Real.log y + 3.9) ≤ 1.398 * 1e-10 := by nlinarith
    calc sig x / Dx x * _ ≤ sD' * _ := mul_le_mul_of_nonneg_right hsD' hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  -- the tail
  have hr₂4 : (r₂ : ℝ) ^ 4 ≤ y := by rw [← hq4]; gcongr
  have hgt := ghatY_le_asym hy (by linarith) hr₂4
  rw [← hΞ] at hgt
  have hr14 : (r₂ : ℝ) ^ (-1 / 4 : ℝ) ≤ 1.1893 * y ^ (-1 / 16 : ℝ) := by
    have h1 : (r₂ : ℝ) ^ (-1 / 4 : ℝ) ≤ (q / 2) ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr₂q' (by norm_num)
    have h2 : (q / 2) ^ (-1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * y ^ (-1 / 16 : ℝ) := by
      rw [Real.div_rpow hq0.le (by norm_num), hq_def, ← Real.rpow_mul hy0.le,
        show (1 / 4 : ℝ) * (-1 / 4) = -1 / 16 by norm_num, show (-1 / 4 : ℝ) = -(1 / 4) by norm_num,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
      ring
    have h3 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.1893 := by
      rw [show (1.1893 : ℝ) = ((1.1893 : ℝ) ^ (4:ℕ)) ^ (1 / 4 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
      exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    rw [h2] at h1
    have : 0 ≤ y ^ (-1 / 16 : ℝ) := by positivity
    nlinarith
  have hP1 := Phi1_le hy
  have htail : ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x) ≤ 2.2e-4 := by
    have hgt0 := ghatY_nonneg (y := y) (n := r₂) (by linarith) (by linarith)
    have hc0 : 0 ≤ cL (r₂ - 1) := by
      unfold cL; exact add_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) (r₂ - 1); linarith)) (by norm_num)
    have h1 : sig x - cL (r₂ - 1) * sig x / Dx x ≤ sig x := by
      have : 0 ≤ cL (r₂ - 1) * sig x / Dx x := by positivity
      linarith
    have h2 : 0 ≤ sig x - cL (r₂ - 1) * sig x / Dx x := by
      have e : sig x - cL (r₂ - 1) * sig x / Dx x = sig x * (1 - cL (r₂ - 1) / Dx x) := by field_simp
      rw [e]; exact mul_nonneg hsig0 (by rw [sub_nonneg, div_le_one hDpos]; exact c5)
    have hW0 : 0 ≤ Real.log y + 3.9 := by linarith
    calc ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)
        ≤ ghatY y r₂ * sig x := mul_le_mul_of_nonneg_left h1 hgt0
      _ ≤ (2 * (1.1893 * y ^ (-1 / 16 : ℝ)) + 1.398 * Ξ) * (0.6403 * (Real.log y + 3.9)) := by
          refine mul_le_mul (hgt.trans (by linarith)) hsigx hsig0 (by positivity)
      _ = 0.6403 * (2.3786 * ((Real.log y + 3.9) * y ^ (-1 / 16 : ℝ)) +
            1.398 * ((Real.log y + 3.9) * Ξ)) := by ring
      _ ≤ 0.6403 * (2.3786 * 1.4e-4 + 1.398 * 1e-10) := by
          gcongr
      _ ≤ 2.2e-4 := by norm_num
  unfold Mexpr
  rw [← hy_def]
  have : 0.0510741 * (14.61155 * sD' - 8.6294) +
      sD' * (0.165282706731081808 + (8.4e-4 + 1.398 * 1e-10)) + 2.2e-4 ≤ 1.037 := by norm_num
  linarith

end TernaryGoldbach.MinorArcs
