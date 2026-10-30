import TernaryGoldbach.MinorArcs.SecondTypeI2
import TernaryGoldbach.MinorArcs.SecondTypeIIbPieces
import TernaryGoldbach.MinorArcs.SecondBridge
import TernaryGoldbach.MinorArcs.SecondChoice
import TernaryGoldbach.MinorArcs.Assembly

/-!
# [B, §6.3.2]: Theorem 3.1.1 for `q > x^{1/3}/6`

With `T = x^{1/3}`, `L = log T`:
`|S_{η₂}(α, x)| ≤ 1.4341 T^{5/2} L^{3/2} + 3702 L T²`, i.e.
`≤ 0.276 x^{5/6} (log x)^{3/2} + 1234 x^{2/3} log x` ([B]'s constants).

We re-approximate `2α` with `Q₀ = T²/349` (`exists_approx2`) and split as in
`second_case_split`: (a) `q' > T/6` (Type II via (6.38) if `16q' ≤ x/U`, else (6.39));
(b) `q' ≤ T/6`, `|δ'| > 8`, `|δ'|q' > 8T/6` (Type II via (6.41)); (c) the bridge case, where the
first case of the theorem applies to `a'/q'`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

/-- `√T ≥ (log T)²/16` (from `T = e^L`, `e^{L/4} ≥ 1 + L/4`). -/
theorem sqrt_ge_log_sq {T : ℝ} (hT : 1 ≤ T) : Real.log T ^ 2 / 16 ≤ √T := by
  have hT0 : 0 < T := by linarith
  have hL : 0 ≤ Real.log T := Real.log_nonneg hT
  have h1 : √T = rexp (Real.log T / 4) ^ 2 := by
    rw [← Real.exp_nat_mul, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT0]; ring_nf
  have h2 := Real.add_one_le_exp (Real.log T / 4)
  rw [h1]
  have : 0 ≤ Real.log T / 4 + 1 := by linarith
  nlinarith

/-- The Type II bound of the second choice in cases (a) and (b). -/
theorem typeII_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    ‖typeII α (T ^ 3) (U2 T) (V2 T)‖ ≤ 1.413 * (Real.log T * √(Real.log T)) * (T ^ 2 * √T) := by
  have hL := fifteen_six_le_log hT
  have hP : 0 ≤ T ^ 2 * √T := by positivity
  rcases hc with hc | ⟨hq, hδ8, hδq⟩
  · rcases le_or_gt (16 * (q : ℝ)) (T ^ 3 / U2 T) with h16 | h16
    · have h1 := typeII_a1 hT h hc h16
      have h2 := a1_numeric hL
      exact h1.trans (mul_le_mul_of_nonneg_right h2 hP)
    · exact typeII_a2 hT h h16
  · have h1 := typeII_b hT h hq hδ8 hδq
    have h2 := b_numeric hL
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hP)

set_option maxHeartbeats 4000000 in
/-- **[B, Theorem 3.1.1] for `q > x^{1/3}/6`** (in terms of `T = x^{1/3}`). -/
theorem theorem_3_1_1_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (3 / 4 * T ^ 2)) (hq : T / 6 < q) :
    ‖S eta2 (T ^ 3) α‖ ≤
      1.4341 * (T ^ 2 * √T) * (Real.log T * √(Real.log T)) + 3702 * Real.log T * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hL0 : 0 ≤ L := by linarith
  have hsL : 3.9496 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0]; linarith
  have hsT := sqrt_ge_2449 hT
  have hsT2 := sqrt_ge_log_sq (show 1 ≤ T by linarith)
  have hP : 0 ≤ T ^ 2 * √T := by positivity
  have hLL : 0 ≤ L * √L := by positivity
  -- Re-approximate.
  obtain ⟨δ', a', q', h'⟩ := exists_approx2 α (by positivity : 0 < T ^ 3)
    (show 1 ≤ Q2 T by unfold Q2; rw [le_div_iff₀ (by norm_num)]; nlinarith)
  -- The final inequality, given the Type I and Type II bounds.
  have hfin : ∀ X : ℝ, X ≤ (0.0716 * L ^ 2 + 3175.9 * L + 8399.2) * T ^ 2 +
      1.413 * (L * √L) * (T ^ 2 * √T) + 3 * (3 * L) →
      X ≤ 1.4341 * (T ^ 2 * √T) * (L * √L) + 3702 * L * T ^ 2 := by
    intro X hX
    refine hX.trans ?_
    -- `0.0716 L² + 8400 ≤ 526.1 L + 0.0211 L^{3/2} √T`.
    have hs : 0.0716 * L ^ 2 + 8399.2 + 9 * L / T ^ 2 ≤ 526.1 * L + 0.0211 * (L * √L) * √T := by
      have h9 : 9 * L / T ^ 2 ≤ 0.8 := by
        have hLT : L ≤ T := by have := Real.log_le_sub_one_of_pos hT0; linarith
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h1 : 0.0211 * (L * √L) * √T ≥ 0.08333 * L * √T := by
        have := mul_le_mul_of_nonneg_left hsL hL0
        nlinarith [Real.sqrt_nonneg T]
      have h2 : 0.08333 * L * √T ≥ 0.08333 * L * (2449 / 2 + L ^ 2 / 32) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      nlinarith [mul_nonneg hL0 (sq_nonneg L), sq_nonneg (L - 27)]
    have hT2 : 0 < T ^ 2 := by positivity
    have e9 : 3 * (3 * L) = 9 * L / T ^ 2 * T ^ 2 := by field_simp; ring
    have e1 : 0.0211 * (L * √L) * √T * T ^ 2 = 0.0211 * (L * √L) * (T ^ 2 * √T) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hs hT2.le]
  rcases second_case_split (show 1 ≤ T by linarith) h hq h' with ha | hb | hc
  · have hsc : SecondCase T δ' q' := Or.inl ha
    have hparts := norm_S_le_parts α (x := T ^ 3) (by nlinarith) (U2 T) (V2 T) (V2_le_x4 hT)
    have hI := typeI_second hT h' hsc
    have hII := typeII_second hT h' hsc
    have hl : Real.log (T ^ 3) = 3 * L := by rw [Real.log_pow]; push_cast; ring
    rw [hl] at hparts
    exact hfin _ (by linarith)
  · have hsc : SecondCase T δ' q' := Or.inr hb
    have hparts := norm_S_le_parts α (x := T ^ 3) (by nlinarith) (U2 T) (V2 T) (V2_le_x4 hT)
    have hI := typeI_second hT h' hsc
    have hII := typeII_second hT h' hsc
    have hl : Real.log (T ^ 3) = 3 * L := by rw [Real.log_pow]; push_cast; ring
    rw [hl] at hparts
    exact hfin _ (by linarith)
  · obtain ⟨hq', happ, hlow⟩ := hc
    have hbr := bridge_le hT happ hq' hlow
    have : 0 ≤ 3702 * L * T ^ 2 := by positivity
    have : 1.434 * (T ^ 2 * √T) * (L * √L) ≤ 1.4341 * (T ^ 2 * √T) * (L * √L) := by
      have := mul_nonneg hP hLL
      nlinarith
    linarith

end TernaryGoldbach.MinorArcs
