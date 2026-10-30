import TernaryGoldbach.MinorArcs.SecondNumerics

/-!
# The second choice of parameters [B, (6.65)], modified

With `T = x^{1/3} ≥ 6·10⁶`: `U = ⌊1225 T⌋` ([B]: `500√6 T = 1224.74… T`), `V = ⌊T/3⌋`, and the
re-approximation parameter `Q₀ = T²/349 ≥ 3.5 x/U` ([B]: `Q = x/U`; see `NOTES.md`).
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `U = ⌊1225 T⌋`. -/
noncomputable def U2 (T : ℝ) : ℕ := ⌊1225 * T⌋₊

/-- `V = ⌊T/3⌋`. -/
noncomputable def V2 (T : ℝ) : ℕ := ⌊T / 3⌋₊

/-- `Q₀ = T²/349`. -/
noncomputable def Q2 (T : ℝ) : ℝ := T ^ 2 / 349

section
variable {T : ℝ}

theorem U2_ge (hT : 0 < T) : 1225 * T - 1 ≤ (U2 T : ℝ) := by
  unfold U2; have := Nat.lt_floor_add_one (1225 * T); linarith

theorem U2_le (hT : 0 < T) : (U2 T : ℝ) ≤ 1225 * T := by
  unfold U2; exact Nat.floor_le (by positivity)

theorem V2_ge (hT : 0 < T) : T / 3 - 1 ≤ (V2 T : ℝ) := by
  unfold V2; have := Nat.lt_floor_add_one (T / 3); linarith

theorem V2_le (hT : 0 < T) : (V2 T : ℝ) ≤ T / 3 := by
  unfold V2; exact Nat.floor_le (by positivity)

theorem U2_ge' (hT : 6e6 ≤ T) : 1224.99 * T ≤ (U2 T : ℝ) := by
  have := U2_ge (by linarith : 0 < T); linarith

theorem V2_ge' (hT : 6e6 ≤ T) : 0.33333 * T ≤ (V2 T : ℝ) := by
  have := V2_ge (by linarith : 0 < T); linarith

theorem one_le_U2 (hT : 6e6 ≤ T) : 1 ≤ U2 T := by
  have := U2_ge' hT
  exact_mod_cast (show (1 : ℝ) ≤ U2 T by linarith)

theorem V2_ge_50000 (hT : 6e6 ≤ T) : (50000 : ℝ) ≤ V2 T := by
  have := V2_ge' hT; linarith

theorem two_le_V2 (hT : 6e6 ≤ T) : 2 ≤ V2 T := by
  have := V2_ge_50000 hT
  exact_mod_cast (show (2 : ℝ) ≤ V2 T by linarith)

theorem U2_pos (hT : 6e6 ≤ T) : (0 : ℝ) < U2 T := by have := U2_ge' hT; linarith

/-- `x/U ≤ T²/1224.99`. -/
theorem xU2_le (hT : 6e6 ≤ T) : T ^ 3 / U2 T ≤ T ^ 2 / 1224.99 := by
  have h := U2_ge' hT
  have hT0 : 0 < T := by linarith
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [pow_pos hT0 3]

/-- `x/U ≥ T²/1225`. -/
theorem xU2_ge (hT : 6e6 ≤ T) : T ^ 2 / 1225 ≤ T ^ 3 / U2 T := by
  have h := U2_le (by linarith : 0 < T)
  have hT0 : 0 < T := by linarith
  rw [div_le_div_iff₀ (by norm_num) (U2_pos hT)]
  nlinarith [pow_pos hT0 2]

/-- `3.5 x/U ≤ Q₀`. -/
theorem Q2_ge (hT : 6e6 ≤ T) : 3.5 * (T ^ 3 / U2 T) ≤ Q2 T := by
  have h := xU2_le hT
  unfold Q2
  have : 3.5 * (T ^ 2 / 1224.99) ≤ T ^ 2 / 349 := by
    have : 0 ≤ T ^ 2 := sq_nonneg T
    rw [mul_div_assoc', div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  linarith

/-- `V ≤ x/U`. -/
theorem V2_le_xU (hT : 6e6 ≤ T) : (V2 T : ℝ) ≤ T ^ 3 / U2 T := by
  have h1 := V2_le (by linarith : 0 < T)
  have h2 := xU2_ge hT
  have : T / 3 ≤ T ^ 2 / 1225 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  linarith

theorem V2_le_x4 (hT : 6e6 ≤ T) : (V2 T : ℝ) ≤ T ^ 3 / 4 := by
  have h1 := V2_le (by linarith : 0 < T)
  have : T / 3 ≤ T ^ 3 / 4 := by
    have hT0 : 0 < T := by linarith
    have h2 : 2 ≤ T ^ 2 := by nlinarith
    have : 2 * T ≤ T ^ 3 := by
      have : T ^ 3 = T * T ^ 2 := by ring
      rw [this]; nlinarith
    linarith
  linarith

/-- `x ≤ Q₀²`. -/
theorem x_le_Q2_sq (hT : 6e6 ≤ T) : T ^ 3 ≤ Q2 T ^ 2 := by
  unfold Q2
  have hT0 : 0 < T := by linarith
  rw [div_pow, le_div_iff₀ (by norm_num)]
  nlinarith [pow_pos hT0 3]

/-- `U ≤ Q₀/2`. -/
theorem U2_le_Q2 (hT : 6e6 ≤ T) : (U2 T : ℝ) ≤ Q2 T / 2 := by
  have h := U2_le (by linarith : 0 < T)
  unfold Q2
  have : 1225 * T ≤ T ^ 2 / 349 / 2 := by
    rw [div_div, le_div_iff₀ (by norm_num)]; nlinarith
  linarith

theorem two_e_le_Q2 (hT : 6e6 ≤ T) : 2 * rexp 1 ≤ Q2 T := by
  have := Real.exp_one_lt_d9
  unfold Q2
  rw [le_div_iff₀ (by norm_num)]; nlinarith

end

end TernaryGoldbach.MinorArcs
