import TernaryGoldbach.MinorArcs.FirstChoice

/-!
# [B, (6.49)]: the first choice of parameters

With `T = x^{1/3}`, `t = δ₀q ∈ [2, T/3]`: `U = ⌊T²/(9√t)⌋`, `V = ⌊9T/2⌋`, `Q = 3T²/4`
(so `UV ≈ x/(2√t)`, [B]'s `κ = 1/2`).
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `δ₀ = max(2, |δ|/4)`. -/
noncomputable def delta0 (δ : ℝ) : ℝ := max 2 (|δ| / 4)

/-- `U = ⌊T²/(9√t)⌋` [B, (6.49)] (rounded down). -/
noncomputable def U1 (T t : ℝ) : ℕ := ⌊T ^ 2 / (9 * √t)⌋₊

/-- `V = ⌊9T/2⌋` [B, (6.49)] (rounded down). -/
noncomputable def V1 (T : ℝ) : ℕ := ⌊9 * T / 2⌋₊

section
variable {T t : ℝ}

theorem sqrt_mul_self_eq (hT : 0 ≤ T) : T * √T * √T = T ^ 2 := by
  rw [mul_assoc, Real.mul_self_sqrt hT]; ring

theorem U1_real_ge (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    √3 / 9 * (T * √T) ≤ T ^ 2 / (9 * √t) := by
  have hT0 : 0 < T := by linarith
  have hsT : 0 < √T := Real.sqrt_pos.2 hT0
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have h1 : √t ≤ √T / √3 := by
    rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h3 : 0 < √3 := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc √3 / 9 * (T * √T) * (9 * √t) ≤ √3 / 9 * (T * √T) * (9 * (√T / √3)) := by gcongr
    _ = T * √T * √T := by field_simp
    _ = T ^ 2 := sqrt_mul_self_eq hT0.le

theorem sqrt3_div9 : 0.19245 ≤ √3 / 9 := by
  rw [le_div_iff₀ (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

theorem sqrt_ge_2449 (hT : 6e6 ≤ T) : 2449 ≤ √T := by
  rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith

/-- `U ≥ 0.1924 T√T`. -/
theorem U1_ge (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    0.1924 * (T * √T) ≤ (U1 T t : ℝ) := by
  have h1 := U1_real_ge hT ht htT
  have h2 := sqrt3_div9
  have h3 := sqrt_ge_2449 hT
  have hfl : T ^ 2 / (9 * √t) - 1 ≤ (U1 T t : ℝ) := by
    unfold U1; have := Nat.lt_floor_add_one (T ^ 2 / (9 * √t)); linarith
  have : 0.00005 * (T * √T) ≥ 1 := by nlinarith
  have : 0.19245 * (T * √T) ≤ √3 / 9 * (T * √T) := by
    have : 0 ≤ T * √T := by positivity
    nlinarith
  linarith

theorem U1_le (ht : 0 < t) : (U1 T t : ℝ) ≤ T ^ 2 / (9 * √t) := by
  unfold U1; exact Nat.floor_le (by positivity)

theorem V1_ge (hT : 0 < T) : 9 * T / 2 - 1 ≤ (V1 T : ℝ) := by
  unfold V1; have := Nat.lt_floor_add_one (9 * T / 2); linarith

theorem V1_le (hT : 0 < T) : (V1 T : ℝ) ≤ 9 * T / 2 := by
  unfold V1; exact Nat.floor_le (by positivity)

/-- `UV ≤ x/(2√t)`. -/
theorem U1V1_le (hT : 0 < T) (ht : 0 < t) :
    (U1 T t : ℝ) * V1 T ≤ T ^ 3 / (2 * √t) := by
  have h1 := U1_le (T := T) ht
  have h2 := V1_le hT
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  calc (U1 T t : ℝ) * V1 T ≤ T ^ 2 / (9 * √t) * (9 * T / 2) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    _ = T ^ 3 / (2 * √t) := by field_simp

/-- `UV ≥ (1 - 1/T) x/(2√t)`. -/
theorem U1V1_ge (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    (1 - 1 / T) * (T ^ 3 / (2 * √t)) ≤ (U1 T t : ℝ) * V1 T := by
  have hT0 : 0 < T := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  set Ur := T ^ 2 / (9 * √t) with hUr
  have hUr0 : 0 < Ur := by positivity
  have hfl : Ur - 1 ≤ (U1 T t : ℝ) := by
    unfold U1; have := Nat.lt_floor_add_one Ur; linarith
  have hV := V1_ge hT0
  have hUrge : 0.19245 * (T * √T) ≤ Ur := (sqrt3_div9.trans le_rfl |> fun h => by
    have := U1_real_ge hT ht htT
    have : 0 ≤ T * √T := by positivity
    nlinarith)
  have h3 := sqrt_ge_2449 hT
  -- `1/Ur ≤ 7/(9T)`.
  have hUrT : 9 * T ≤ 7 * Ur := by nlinarith
  have e : Ur * (9 * T / 2) = T ^ 3 / (2 * √t) := by simp only [hUr]; field_simp
  have hprod : (Ur - 1) * (9 * T / 2 - 1) ≤ (U1 T t : ℝ) * V1 T :=
    mul_le_mul hfl hV (by nlinarith) (Nat.cast_nonneg _)
  -- `(Ur - 1)(9T/2 - 1) ≥ (1 - 1/T) Ur (9T/2)`.
  have key : (1 - 1 / T) * (Ur * (9 * T / 2)) ≤ (Ur - 1) * (9 * T / 2 - 1) := by
    have e2 : (1 - 1 / T) * (Ur * (9 * T / 2)) = Ur * (9 * T / 2) - 9 / 2 * Ur := by
      field_simp
    rw [e2]; nlinarith
  rw [← e]; linarith

/-- `x/U ≤ 9.0001 T√t`. -/
theorem div_U1_le (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    T ^ 3 / (U1 T t : ℝ) ≤ 9.0001 * (T * √t) := by
  have hT0 : 0 < T := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hU := U1_ge hT ht htT
  have h3 := sqrt_ge_2449 hT
  have hU0 : 0 < (U1 T t : ℝ) := lt_of_lt_of_le (by positivity) hU
  set Ur := T ^ 2 / (9 * √t) with hUr
  have hfl : Ur - 1 ≤ (U1 T t : ℝ) := by
    unfold U1; have := Nat.lt_floor_add_one Ur; linarith
  have hUrge : 0.19245 * (T * √T) ≤ Ur := by
    have := U1_real_ge hT ht htT; have := sqrt3_div9
    have : 0 ≤ T * √T := by positivity
    nlinarith
  have hUr1 : 1 ≤ 0.00001 * Ur := by nlinarith
  rw [div_le_iff₀ hU0]
  have e : 9 * (T * √t) * Ur = T ^ 3 := by simp only [hUr]; field_simp
  have : 9 * (T * √t) * Ur ≤ 9.0001 * (T * √t) * (U1 T t : ℝ) := by
    have : 0 < T * √t := by positivity
    nlinarith
  linarith

/-- `8 ζ³ √(x/V)/U ≤ 0.2355`. -/
theorem zeta_term_le (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    8 * zeta3 * √(T ^ 3 / V1 T) / U1 T t ≤ 0.2355 := by
  have hT0 : 0 < T := by linarith
  have hU := U1_ge hT ht htT
  have h3 := sqrt_ge_2449 hT
  have hU0 : 0 < (U1 T t : ℝ) := lt_of_lt_of_le (by positivity) hU
  have hV := V1_ge hT0
  have hV0 : 0 < (V1 T : ℝ) := by linarith
  have hζ := zeta3_le
  have hζ0 := zeta3_nonneg
  -- `√(x/V) ≤ 0.4767 T`.
  have h1 : √(T ^ 3 / V1 T) ≤ 0.4767 * T := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hV0]
    nlinarith
  rw [div_le_iff₀ hU0]
  have hsT : 0 < √T := by positivity
  calc 8 * zeta3 * √(T ^ 3 / V1 T) ≤ 8 * 27 * (0.4767 * T) := by gcongr
    _ ≤ 0.2355 * (0.1924 * (T * √T)) := by nlinarith
    _ ≤ 0.2355 * (U1 T t : ℝ) := by gcongr

end

end TernaryGoldbach.MinorArcs
