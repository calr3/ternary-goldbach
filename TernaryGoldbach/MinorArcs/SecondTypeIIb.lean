import TernaryGoldbach.MinorArcs.SecondTypeIIaPieces

/-!
# Type II at the second parameters: cases (a2) and (b)

* (a2) `x/16U < q ≤ Q₀`: (6.39) via `typeII_639`, crude bounds: `≤ 1.413 L^{3/2} T^{5/2}`.
* (b) `q ≤ T/6`, `|δ| > 8`, `|δ|q > 8T/6`: (6.41) via `typeII_641` (`θ = 8`), reduced to
  `(√(12 F₀ X₀ᵇ B₀ᵇ) + SECᵇ(L)) T^{5/2}` as in case (a1).
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem log_e_le_one_sqrt {T : ℝ} (hT : 6e6 ≤ T) : (2449 : ℝ) ≤ √T := sqrt_ge_2449 hT

set_option maxHeartbeats 4000000 in
/-- **Case (a2)**: `x/16U < q ≤ Q₀`. -/
theorem typeII_a2 {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq16 : T ^ 3 / U2 T < 16 * (q : ℝ)) :
    ‖typeII α (T ^ 3) (U2 T) (V2 T)‖ ≤ 1.413 * (Real.log T * √(Real.log T)) * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨k, hα⟩ := approx2_abs (by positivity) h
  have hqQ : (q : ℝ) ≤ Q2 T := h.2.2.2.2
  have hq1 : 1 ≤ q := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have key := typeII_639 hq1 h.2.1 hα hqQ (by positivity) (one_le_U2 hT)
    (by linarith [V2_ge_50000 hT]) (V2_le_xU hT)
  refine key.trans ?_
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hsT := sqrt_ge_2449 hT
  have hss : √T * √T = T := Real.mul_self_sqrt hT0.le
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  have hU0 := U2_pos hT
  have hV := V2_ge' hT
  have hV0 : (0 : ℝ) < V2 T := by linarith
  have hκ := kap1_le_second hT
  have hsκ : √(kap1 (T ^ 3) (U2 T) (V2 T)) ≤ 0.49075 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsL : 0 < √L := Real.sqrt_pos.2 (by linarith)
  have hLL : 15.6 * √L ≤ L * √L := by gcongr
  have hL1 : 61.6 ≤ L * √L := by
    have : 3.9496 ≤ √L := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    nlinarith
  set P := T ^ 2 * √T
  have hP0 : 0 < P := by positivity
  -- `√(x²/8q + qx) ≤ 0.0739 P`.
  have hM : √((T ^ 3) ^ 2 / (8 * q) + q * T ^ 3) ≤ 0.0739 * P := by
    have h1 : (T ^ 3) ^ 2 / (8 * q) ≤ 2450 * T ^ 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : T ^ 3 < 16 * q * U2 T := by rwa [div_lt_iff₀ hU0] at hq16
      have h2 : T ^ 3 * T ^ 3 ≤ T ^ 3 * (16 * q * (1225 * T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      nlinarith
    have h2 : (q : ℝ) * T ^ 3 ≤ T ^ 5 / 349 := by
      have : (q : ℝ) ≤ T ^ 2 / 349 := hqQ
      rw [le_div_iff₀ (by norm_num)]
      have : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at this
      nlinarith [pow_pos hT0 3]
    have h3 : 2450 * T ^ 4 + T ^ 5 / 349 ≤ (0.0739 * P) ^ 2 := by
      simp only [P]
      rw [mul_pow, mul_pow, sq (√T), hss]
      nlinarith [pow_pos hT0 4, pow_pos hT0 5]
    rw [Real.sqrt_le_left (by positivity)]; linarith
  -- `(2/3)(a√a - b√b) ≤ 1.8857 L√L`.
  have hxU := xU2_le hT
  have hla : Real.log (T ^ 3 / U2 T) ≤ 2 * L := by
    have := Real.log_le_log (by positivity) (hxU.trans (show T ^ 2 / 1224.99 ≤ T ^ 2 by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]))
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hla0 : 0 ≤ Real.log (T ^ 3 / U2 T) := Real.log_nonneg (by
    rw [le_div_iff₀ hU0, one_mul]; nlinarith [pow_pos hT0 3])
  have hVl0 : 0 ≤ Real.log (V2 T) := Real.log_nonneg (by linarith)
  have hW : 2 / 3 * (Real.log (T ^ 3 / U2 T) * √(Real.log (T ^ 3 / U2 T)) -
      Real.log (V2 T) * √(Real.log (V2 T))) ≤ 1.8857 * (L * √L) := by
    have h1 : √(Real.log (T ^ 3 / U2 T)) ≤ √2 * √L := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hla
    have h2 : 0 ≤ Real.log (V2 T) * √(Real.log (V2 T)) := by positivity
    have h3 : Real.log (T ^ 3 / U2 T) * √(Real.log (T ^ 3 / U2 T)) ≤ 2 * L * (√2 * √L) :=
      mul_le_mul hla h1 (Real.sqrt_nonneg _) (by linarith)
    have := sqrt2_le
    nlinarith
  -- the `x/√V` term.
  have hVl1 : 1 ≤ Real.log (V2 T) := by
    rw [Real.le_log_iff_exp_le hV0]; linarith [Real.exp_one_lt_d9, V2_ge_50000 hT]
  have hVlL : Real.log (V2 T) ≤ L := Real.log_le_log hV0 (by linarith [V2_le hT0])
  have hX2 : √2 * T ^ 3 * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) / √(V2 T) ≤
      1.414214 * 1.73207 * (√L + 1) * P := by
    have hsV : 0 < √(V2 T : ℝ) := Real.sqrt_pos.2 hV0
    have h1 : T ^ 3 / √(V2 T) ≤ 1.73207 * P := by
      rw [div_le_iff₀ hsV]
      have h3 : √(0.33333 * T) ≤ √(V2 T) := Real.sqrt_le_sqrt hV
      have h4 : √(0.33333 * T) = √0.33333 * √T := Real.sqrt_mul (by norm_num) T
      have h5 : 1 ≤ 1.73207 * √0.33333 := by
        have : 0.577347 ≤ √0.33333 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        linarith
      have : T ^ 3 ≤ 1.73207 * P * √(0.33333 * T) := by
        rw [h4]; simp only [P]
        have : T ^ 3 = T ^ 2 * (√T * √T) := by rw [hss]; ring
        rw [this]
        have : 0 ≤ T ^ 2 * √T * √T := by positivity
        nlinarith
      calc T ^ 3 ≤ 1.73207 * P * √(0.33333 * T) := this
        _ ≤ _ := by gcongr
    have h2 : √(Real.log (V2 T)) + 1 / √(Real.log (V2 T)) ≤ √L + 1 := by
      have : √(Real.log (V2 T)) ≤ √L := Real.sqrt_le_sqrt hVlL
      have : 1 / √(Real.log (V2 T)) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      linarith
    have := sqrt2_le
    calc √2 * T ^ 3 * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) / √(V2 T)
        = √2 * (T ^ 3 / √(V2 T)) * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) := by ring
      _ ≤ 1.414214 * (1.73207 * P) * (√L + 1) := by gcongr
      _ = _ := by ring
  -- the `√x √log(x/U) √(x/U)` term.
  have hX3 : √(T ^ 3) * √(Real.log (T ^ 3 / U2 T)) * √(T ^ 3 / U2 T) ≤
      0.028572 * (1.414214 * √L) * P := by
    have h1 : √(T ^ 3) = T * √T := by
      rw [show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hT0.le]
    have h2 : √(T ^ 3 / U2 T) ≤ 0.028572 * T := by
      rw [Real.sqrt_le_left (by positivity)]
      have : T ^ 2 / 1224.99 ≤ (0.028572 * T) ^ 2 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
      linarith
    have h3 : √(Real.log (T ^ 3 / U2 T)) ≤ 1.414214 * √L := by
      have : √(Real.log (T ^ 3 / U2 T)) ≤ √2 * √L := by
        rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hla
      have := sqrt2_le
      nlinarith [Real.sqrt_nonneg L]
    rw [h1]
    calc T * √T * √(Real.log (T ^ 3 / U2 T)) * √(T ^ 3 / U2 T)
        ≤ T * √T * (1.414214 * √L) * (0.028572 * T) := by gcongr
      _ = _ := by simp only [P]; ring
  have h4 := a1_M4_le hT
  have hK4 : 8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) ≤ 6.8578 := by
    have := sqrtK4_le; nlinarith
  -- Assemble.
  have hW0 : 0 ≤ 2 / 3 * (Real.log (T ^ 3 / U2 T) * √(Real.log (T ^ 3 / U2 T)) -
      Real.log (V2 T) * √(Real.log (V2 T))) := by
    have : Real.log (V2 T) ≤ Real.log (T ^ 3 / U2 T) := Real.log_le_log hV0 (V2_le_xU hT)
    have : √(Real.log (V2 T)) ≤ √(Real.log (T ^ 3 / U2 T)) := Real.sqrt_le_sqrt this
    nlinarith [Real.sqrt_nonneg (Real.log (V2 T))]
  have hA : √((T ^ 3) ^ 2 / (8 * q) + q * T ^ 3) * (2 / 3 * (Real.log (T ^ 3 / U2 T) *
      √(Real.log (T ^ 3 / U2 T)) - Real.log (V2 T) * √(Real.log (V2 T)))) ≤
      0.0739 * P * (1.8857 * (L * √L)) := mul_le_mul hM hW hW0 (by positivity)
  have hin : 0 ≤ √((T ^ 3) ^ 2 / (8 * q) + q * T ^ 3) * (2 / 3 * (Real.log (T ^ 3 / U2 T) *
      √(Real.log (T ^ 3 / U2 T)) - Real.log (V2 T) * √(Real.log (V2 T)))) +
      √2 * T ^ 3 * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) / √(V2 T) +
      √(T ^ 3) * √(Real.log (T ^ 3 / U2 T)) * √(T ^ 3 / U2 T) := by positivity
  have hsum := add_le_add (add_le_add hA hX2) hX3
  have hk := mul_le_mul hsκ hsum hin (by norm_num)
  have hfin : 4 * (0.49075 * (0.0739 * P * (1.8857 * (L * √L)) + 1.414214 * 1.73207 * (√L + 1) * P +
      0.028572 * (1.414214 * √L) * P)) + 6.8578 * P ≤ 1.413 * (L * √L) * P := by
    have : 4 * (0.49075 * (0.0739 * (1.8857 * (L * √L)) + 1.414214 * 1.73207 * (√L + 1) +
        0.028572 * (1.414214 * √L))) + 6.8578 ≤ 1.413 * (L * √L) := by nlinarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hK4 hP0.le]

end TernaryGoldbach.MinorArcs
