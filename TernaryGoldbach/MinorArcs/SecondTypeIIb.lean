import TernaryGoldbach.Prelim.MertensProduct
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

/-! ### Case (b): constants and definitions -/

theorem log_13066_ge : (9.4778 : ℝ) ≤ Real.log 13066.56 := by
  have := le_log_num (z := 13066.56) 9 0.4778 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_2_6259_ge : (0.9654 : ℝ) ≤ Real.log 2.6259 := by
  have := le_log_num (z := 2.6259) 0 0.9654 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_466_ge : (6.1452 : ℝ) ≤ Real.log 466.49 := by
  have := le_log_num (z := 466.49) 6 0.1452 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_28_ge : (3.3325 : ℝ) ≤ Real.log 28.0099 := by
  have := le_log_num (z := 28.0099) 3 0.3325 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_3_3325_ge : (1.2037 : ℝ) ≤ Real.log 3.3325 := by
  have := le_log_num (z := 3.3325) 1 0.2037 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_32_3_le : Real.log (32 / 3) ≤ 2.3672 := by
  have := log_le_num (z := 32 / 3) 2 0.3672 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_32_le : Real.log 32.0004 ≤ 3.4658 := by
  have := log_le_num (z := 32.0004) 3 0.4658 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

theorem log_99_le : Real.log 99.68 ≤ 4.603 := by
  have := log_le_num (z := 99.68) 4 0.603 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at this ⊢; linarith

noncomputable def bG (L : ℝ) : ℝ := Real.log (L - 6.1452) - 1.2037
noncomputable def bX0 (L : ℝ) : ℝ := (L - 9.4778) + (L - 0.9654) * bG L
noncomputable def bB0 (L : ℝ) : ℝ := 0.15107 * (L - 9.4778) + 0.0135

/-- The secondary terms of case (b), divided by `T^{5/2}`. -/
noncomputable def bSEC (L : ℝ) : ℝ :=
  4 * (0.49075 * (0.612373 * (3.4658 * √(L + 2.3672)) +
    0.0019072 * (√(2 * L - 7.1106) * (L - 6.0119)) +
    0.70712 * 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) + 0.02158 * √(2 * L - 7.1106))) +
  8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) +
  4 * √(0.24083 * a1F0 L / 2) * (0.057144 + 0.0848 * √(L + 4.603))

/-- `q/φ(q) ≤ F₀(L)` for `q ≤ T/6`. -/
theorem div_totient_le_F0 {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 6e6 ≤ T) (hqT : (q : ℝ) ≤ T / 6) :
    (q : ℝ) / Nat.totient q ≤ a1F0 (Real.log T) := by
  have hT0 : 0 < T := by linarith
  have h1 := Prelim.div_totient_lt hq (by linarith) hqT
  have hl : 13.81 ≤ Real.log (T / 6) := log_1e6_ge.trans (Real.log_le_log (by norm_num) (by linarith))
  have hll : 2.625 ≤ Real.log (Real.log (T / 6)) :=
    log_1381_ge.trans (Real.log_le_log (by norm_num) hl)
  have hg := exp_gamma_le_sharp
  have h2 : 2.50637 / Real.log (Real.log (T / 6)) ≤ 0.9549 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : rexp eulerMascheroniConstant * Real.log (Real.log (T / 6)) ≤
      1.7882 * Real.log (Real.log (T / 6)) := mul_le_mul_of_nonneg_right hg (by linarith)
  have h4 : Real.log (Real.log (T / 6)) ≤ Real.log (Real.log T - 1.7917) := by
    rw [Real.log_div hT0.ne' (by norm_num)] at hl ⊢
    exact Real.log_le_log (by linarith) (by linarith [log6_ge])
  unfold a1F0; linarith

/-- `(c + ℓ)²(L'' + ℓ) ≤ c² L'' e^ℓ` for `c = 3.4658`, `L'' ≥ 17`. -/
theorem decay_M3b {L' ℓ : ℝ} (hL : 17 ≤ L') (hℓ : 0 ≤ ℓ) :
    (3.4658 + ℓ) ^ 2 * (L' + ℓ) ≤ 3.4658 ^ 2 * L' * rexp ℓ := by
  have he := Real.sum_le_exp_of_nonneg hℓ 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have h3 : 0 ≤ ℓ ^ 3 := by positivity
  have h2 : 0 ≤ ℓ ^ 2 := by positivity
  have hL0 : 0 ≤ L' := by linarith
  nlinarith [mul_nonneg hL0 hℓ, mul_nonneg hL0 h2, mul_nonneg hL0 h3, mul_le_mul_of_nonneg_left he
    (by positivity : (0 : ℝ) ≤ 3.4658 ^ 2 * L')]

/-- Common facts for case (b): `4T/3 < |δ|q ≤ 349T`. -/
theorem b_facts {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hδq : 8 * (T / 6) < |δ| * q) :
    4 * T / 3 < |δ| * q ∧ |δ| * q ≤ 349 * T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hq1, -, -, hδQ, -⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨by linarith, ?_⟩
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < T ^ 3), div_le_div_iff₀ (by positivity)
    (by unfold Q2; positivity), one_mul] at hδQ
  unfold Q2 at hδQ
  have : |δ| * q * T ^ 2 ≤ 349 * T * T ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

/-- `ε₁ = x/2UQ₀ ∈ [0.142448, 0.142451]`. -/
theorem eps1_bounds {T : ℝ} (hT : 6e6 ≤ T) :
    0.142448 ≤ T ^ 3 / (2 * U2 T * Q2 T) ∧ T ^ 3 / (2 * U2 T * Q2 T) ≤ 0.142451 := by
  have hT0 : 0 < T := by linarith
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  have hU0 := U2_pos hT
  have e : T ^ 3 / (2 * U2 T * Q2 T) = 349 * T / (2 * U2 T) := by unfold Q2; field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

set_option maxHeartbeats 4000000 in
theorem b_M1_le {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq : (q : ℝ) ≤ T / 6) (hδq : 8 * (T / 6) < |δ| * q) :
    4 * T ^ 3 * √(2 / |δ| / (2 * Nat.totient q)) *
      √((Real.log (T ^ 3 / (U2 T * (8 * |δ| * q))) +
        Real.log (|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4) *
          (Real.log (Real.log (T ^ 3 / U2 T / (|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4))) -
            Real.log (Real.log (8 * |δ| * q / (|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4))))) *
        (0.15107 * Real.log (T ^ 3 / (U2 T * (8 * |δ| * q))) +
          2 * zeta3 * √(T ^ 3 / (8 * |δ| * q)) / U2 T)) ≤
    √(12 * a1F0 (Real.log T) * bX0 (Real.log T) * bB0 (Real.log T)) * (T ^ 2 * √T) := by
  obtain ⟨hD1, hD2⟩ := b_facts hT h hδq
  obtain ⟨he1, he2⟩ := eps1_bounds hT
  have hT0 : 0 < T := by linarith
  have hU := U2_ge' hT
  have hU0 : (0 : ℝ) < U2 T := by linarith
  have hxU := xU2_le hT
  have hq1 : 1 ≤ q := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
  have hδ0 : 0 < |δ| := by
    by_contra hh; push Not at hh
    have : |δ| * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh hq0.le
    linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  set ε := T ^ 3 / (2 * U2 T * Q2 T) with hεdef
  set D := |δ| * q with hDdef
  have hD0 : 0 < D := by linarith
  -- `u = 3D/4T ≥ 1`.
  set u := 3 * D / (4 * T) with hudef
  have hu1 : 1 ≤ u := by rw [hudef, le_div_iff₀ (by positivity)]; linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log u with hℓdef
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hu1
  have hexp : rexp ℓ = u := Real.exp_log hu0
  have hDu : D = 4 * T / 3 * u := by rw [hudef]; field_simp
  -- `8D ≤ x/U`.
  have h8D : 8 * D ≤ T ^ 3 / U2 T := by
    have : 8 * D ≤ 2792 * T := by linarith
    have : 2792 * T ≤ T ^ 2 / 1225 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith [xU2_ge hT]
  have h8D' : 8 * |δ| * q = 8 * D := by rw [hDdef]; ring
  -- `Λ`.
  set Λ := Real.log (T ^ 3 / (U2 T * (8 * |δ| * q)))
  have hΛ0 : 0 ≤ Λ := by
    apply Real.log_nonneg
    rw [h8D', le_div_iff₀ (by positivity), one_mul]
    rw [le_div_iff₀ hU0] at h8D; linarith
  have hΛ : Λ ≤ L - 9.4778 - ℓ := by
    have h1 : T ^ 3 / (U2 T * (8 * |δ| * q)) ≤ T / (13066.56 * u) := by
      rw [h8D', div_le_div_iff₀ (by positivity) (by positivity), hDu]
      have : 13066.56 * T ^ 2 * u ≤ U2 T * (8 * (4 * T / 3 * u)) := by
        have := mul_le_mul_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 8 * (4 * T / 3 * u))
        nlinarith
      have hT3 : T ^ 3 = T * T ^ 2 := by ring
      rw [hT3]; nlinarith [mul_le_mul_of_nonneg_left this hT0.le]
    have h2 : Real.log (T / (13066.56 * u)) = L - Real.log 13066.56 - ℓ := by
      rw [Real.log_div hT0.ne' (by positivity), Real.log_mul (by norm_num) hu0.ne']; ring
    have : Λ ≤ Real.log (T / (13066.56 * u)) := Real.log_le_log (by positivity) h1
    linarith [log_13066_ge]
  -- `c`.
  set c := D * (1 + ε) / 4 with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; nlinarith
  have hcup : c ≤ T * u / 2.6259 := by
    rw [hcdef, hDu, le_div_iff₀ (by norm_num)]; nlinarith [mul_pos hT0 hu0]
  have hclo : 0.380816 * (T * u) ≤ c := by rw [hcdef, hDu]; nlinarith [mul_pos hT0 hu0]
  have hlc : Real.log c ≤ L + ℓ - 0.9654 := by
    have := Real.log_le_log (by linarith) hcup
    rw [Real.log_div (show T * u ≠ 0 by positivity) (show (2.6259 : ℝ) ≠ 0 by norm_num),
      Real.log_mul hT0.ne' hu0.ne'] at this
    linarith [log_2_6259_ge]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hinU : T ^ 3 / U2 T / c ≤ T / (466.49 * u) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 466.49 * T ^ 2 * u ≤ U2 T * c := by
      have h1 := mul_le_mul hU hclo (by positivity) (by positivity)
      nlinarith [mul_pos hT0 hu0]
    have hT3 : T ^ 3 = T * T ^ 2 := by ring
    rw [hT3]; nlinarith [mul_le_mul_of_nonneg_left this hT0.le]
  have hlin : Real.log (T ^ 3 / U2 T / c) ≤ L - 6.1452 := by
    have h1 := Real.log_le_log (by positivity) hinU
    have h2 : Real.log (T / (466.49 * u)) = L - Real.log 466.49 - ℓ := by
      rw [Real.log_div hT0.ne' (by positivity), Real.log_mul (by norm_num) hu0.ne']; ring
    linarith [log_466_ge]
  have h8c : 8 * |δ| * q / c = 32 / (1 + ε) := by rw [h8D', hcdef]; field_simp; ring
  have h8c' : 28.0099 ≤ 8 * |δ| * q / c := by
    rw [h8c, le_div_iff₀ (by linarith)]; nlinarith
  have hll8 : 1.2037 ≤ Real.log (Real.log (8 * |δ| * q / c)) := by
    have h1 : 3.3325 ≤ Real.log (8 * |δ| * q / c) :=
      log_28_ge.trans (Real.log_le_log (by norm_num) h8c')
    exact log_3_3325_ge.trans (Real.log_le_log (by norm_num) h1)
  have hcin : 8 * |δ| * q / c ≤ T ^ 3 / U2 T / c :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hbr0 : 0 ≤ Real.log (Real.log (T ^ 3 / U2 T / c)) - Real.log (Real.log (8 * |δ| * q / c)) := by
    have h1 : 0 < Real.log (8 * |δ| * q / c) := Real.log_pos (by linarith)
    exact sub_nonneg.2 (Real.log_le_log h1 (Real.log_le_log (by linarith) hcin))
  have hbr : Real.log (Real.log (T ^ 3 / U2 T / c)) - Real.log (Real.log (8 * |δ| * q / c)) ≤
      bG L := by
    have h1 : 0 < Real.log (T ^ 3 / U2 T / c) :=
      Real.log_pos (by linarith)
    have := Real.log_le_log h1 hlin
    unfold bG; linarith
  have hG0 : 0 ≤ bG L := hbr0.trans hbr
  set Φ := Real.log c * (Real.log (Real.log (T ^ 3 / U2 T / c)) -
    Real.log (Real.log (8 * |δ| * q / c)))
  have hΦ0 : 0 ≤ Φ := mul_nonneg hlc0 hbr0
  have hΦ : Φ ≤ (L - 0.9654 + ℓ) * bG L := mul_le_mul (by linarith) hbr hbr0 (by linarith)
  have hX0def : bX0 L = (L - 9.4778) + (L - 0.9654) * bG L := rfl
  have hX : Λ + Φ ≤ bX0 L + bG L * ℓ := by rw [hX0def]; nlinarith
  have hX0G : 14 * bG L ≤ bX0 L := by rw [hX0def]; nlinarith
  have hX0 : 0 ≤ bX0 L := by linarith
  -- `B`.
  have hz := zeta3_le
  have hz0 := zeta3_nonneg
  have hBz : 2 * zeta3 * √(T ^ 3 / (8 * |δ| * q)) / U2 T ≤ 0.0135 := by
    have h1 : √(T ^ 3 / (8 * |δ| * q)) ≤ 0.30619 * T := by
      rw [Real.sqrt_le_left (by positivity), h8D', div_le_iff₀ (by positivity)]
      have hT3 : T ^ 3 = T * T ^ 2 := by ring
      rw [hT3]; nlinarith [mul_pos hT0 (mul_pos hT0 hT0)]
    rw [div_le_iff₀ hU0]
    have := mul_le_mul hz h1 (Real.sqrt_nonneg _) (by norm_num)
    nlinarith
  set B := 0.15107 * Λ + 2 * zeta3 * √(T ^ 3 / (8 * |δ| * q)) / U2 T
  have hB0def : bB0 L = 0.15107 * (L - 9.4778) + 0.0135 := rfl
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have hB : B ≤ bB0 L := by simp only [B]; rw [hB0def]; nlinarith
  have hBB0 : 0 ≤ bB0 L := hB0.trans hB
  -- `F`.
  have hF := div_totient_le_F0 hq1 hT hq
  have hF0 : 0 ≤ a1F0 L := le_trans (by positivity) hF
  -- Assemble.
  have hdec : bX0 L + bG L * ℓ ≤ bX0 L * u := by
    rw [← hexp]
    have := Real.add_one_le_exp ℓ
    nlinarith
  have hkey : 16 * (1 / (|δ| * Nat.totient q)) * ((Λ + Φ) * B) ≤
      12 * a1F0 L * bX0 L * bB0 L / T := by
    have h2 : ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) ≤ a1F0 L * (bX0 L * u) * bB0 L := by
      have h3 : (Λ + Φ) * B ≤ (bX0 L * u) * bB0 L :=
        mul_le_mul (hX.trans hdec) hB hB0 (by positivity)
      calc ((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B) ≤ a1F0 L * ((bX0 L * u) * bB0 L) :=
            mul_le_mul hF h3 (mul_nonneg (by linarith) hB0) hF0
        _ = _ := by ring
    calc 16 * (1 / (|δ| * Nat.totient q)) * ((Λ + Φ) * B)
        = 16 * (((q : ℝ) / Nat.totient q) * ((Λ + Φ) * B)) / D := by rw [hDdef]; field_simp
      _ ≤ 16 * (a1F0 L * (bX0 L * u) * bB0 L) / D := by gcongr
      _ = 12 * a1F0 L * bX0 L * bB0 L / T := by rw [hDu]; field_simp; ring
  have e1 : 4 * T ^ 3 * √(2 / |δ| / (2 * Nat.totient q)) * √((Λ + Φ) * B) =
      T ^ 3 * √(16 * (1 / (|δ| * Nat.totient q)) * ((Λ + Φ) * B)) := by
    have e0 : 2 / |δ| / (2 * Nat.totient q) = 1 / (|δ| * Nat.totient q) := by field_simp
    rw [e0, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16 * (1 / (|δ| * Nat.totient q)))
      ((Λ + Φ) * B), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) (1 / (|δ| * Nat.totient q)),
      show √(16 : ℝ) = 4 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [e1]
  have hsT : 0 < √T := Real.sqrt_pos.2 hT0
  calc T ^ 3 * √(16 * (1 / (|δ| * Nat.totient q)) * ((Λ + Φ) * B))
      ≤ T ^ 3 * √(12 * a1F0 L * bX0 L * bB0 L / T) := by gcongr
    _ = √(12 * a1F0 L * bX0 L * bB0 L) * (T ^ 2 * √T) := by
        rw [Real.sqrt_div' _ hT0.le]
        have : T ^ 3 = T ^ 2 * √T * √T := by rw [mul_assoc, Real.mul_self_sqrt hT0.le]; ring
        rw [this]; field_simp

set_option maxHeartbeats 4000000 in
theorem b_M2_le {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq : (q : ℝ) ≤ T / 6) (hδq : 8 * (T / 6) < |δ| * q) :
    4 * √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) *
      (2 * √(T ^ 3 / U2 T) + √(Real.log (|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4)) *
        (2 * rexp 1 * √(|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4) +
          4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T /
            (|δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4))))) ≤
    4 * √(0.24083 * a1F0 (Real.log T) / 2) * (0.057144 + 0.0848 * √(Real.log T + 4.603)) *
      (T ^ 2 * √T) := by
  obtain ⟨hD1, hD2⟩ := b_facts hT h hδq
  obtain ⟨he1, he2⟩ := eps1_bounds hT
  have hT0 : 0 < T := by linarith
  have hU0 := U2_pos hT
  have hxU := xU2_le hT
  have hq1 : 1 ≤ q := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
  set L := Real.log T
  have hL := fifteen_six_le_log hT
  have hsT := sqrt_ge_2449 hT
  have hκ := kap1_le_second hT
  have hκ0 : 0 ≤ kap1 (T ^ 3) (U2 T) (V2 T) := by unfold kap1; have := zeta3_nonneg; positivity
  have hF := div_totient_le_F0 hq1 hT hq
  have hF0 : 0 ≤ a1F0 L := le_trans (by positivity) hF
  set ε := T ^ 3 / (2 * U2 T * Q2 T)
  set D := |δ| * q
  have hD0 : 0 < D := by linarith
  set c := D * (1 + ε) / 4 with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; nlinarith
  have hcup : c ≤ 99.68 * T := by rw [hcdef]; nlinarith
  -- first factor.
  have hA : √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) ≤
      √(0.24083 * a1F0 L / 2) * (T * √T) := by
    have e : kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q) =
        kap1 (T ^ 3) (U2 T) (V2 T) * ((q : ℝ) / Nat.totient q) / 2 * T ^ 3 := by field_simp
    rw [e, Real.sqrt_mul (by positivity)]
    have hT3 : √(T ^ 3) = T * √T := by
      rw [show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hT0.le]
    rw [hT3]; gcongr
  -- second factor.
  have hB1 : 2 * √(T ^ 3 / U2 T) ≤ 0.057144 * T := by
    have : √(T ^ 3 / U2 T) ≤ 0.028572 * T := by
      rw [Real.sqrt_le_left (by positivity)]
      have : T ^ 2 / 1224.99 ≤ (0.028572 * T) ^ 2 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
      linarith
    linarith
  have hB2 : √(Real.log c) ≤ √(L + 4.603) := by
    apply Real.sqrt_le_sqrt
    have := Real.log_le_log (by linarith) hcup
    rw [Real.log_mul (by norm_num) hT0.ne'] at this
    linarith [log_99_le]
  have hB3 : 2 * rexp 1 * √c ≤ 0.02217 * T := by
    have h1 : √c ≤ 9.9841 * √T := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hT0.le]; nlinarith
    have he := Real.exp_one_lt_d9
    have h2 : √T * √T = T := Real.mul_self_sqrt hT0.le
    have : 0 ≤ √c := Real.sqrt_nonneg _
    nlinarith
  have h8c : 28.0099 ≤ 8 * D / c := by
    rw [hcdef, show 8 * D / (D * (1 + ε) / 4) = 32 / (1 + ε) by field_simp; ring,
      le_div_iff₀ (by linarith)]; nlinarith
  have h8D : 8 * D ≤ T ^ 3 / U2 T := by
    have : 8 * D ≤ 2792 * T := by linarith
    have : 2792 * T ≤ T ^ 2 / 1225 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith [xU2_ge hT]
  have hlin0 : 3.3325 ≤ Real.log (T ^ 3 / U2 T / c) :=
    log_28_ge.trans (Real.log_le_log (by norm_num) (h8c.trans
      (div_le_div_of_nonneg_right h8D (by linarith))))
  have hB4 : 4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / c)) ≤ 0.06263 * T := by
    have : √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / c)) ≤ 0.015657 * T := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
      have : T ^ 3 / U2 T ≤ (0.015657 * T) ^ 2 * 3.3325 := by
        have : T ^ 2 / 1224.99 ≤ (0.015657 * T) ^ 2 * 3.3325 := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
        linarith
      nlinarith [sq_nonneg (0.015657 * T)]
    linarith
  have hsum : 2 * √(T ^ 3 / U2 T) + √(Real.log c) * (2 * rexp 1 * √c +
      4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / c))) ≤
      (0.057144 + 0.0848 * √(L + 4.603)) * T := by
    have h1 : √(Real.log c) * (2 * rexp 1 * √c + 4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / c))) ≤
        √(L + 4.603) * (0.0848 * T) :=
      mul_le_mul hB2 (by linarith) (by positivity) (Real.sqrt_nonneg _)
    nlinarith
  calc 4 * √(kap1 (T ^ 3) (U2 T) (V2 T) * q * T ^ 3 / (2 * Nat.totient q)) *
        (2 * √(T ^ 3 / U2 T) + √(Real.log c) * (2 * rexp 1 * √c +
          4 * √(T ^ 3 / U2 T / Real.log (T ^ 3 / U2 T / c))))
      ≤ 4 * (√(0.24083 * a1F0 L / 2) * (T * √T)) * ((0.057144 + 0.0848 * √(L + 4.603)) * T) := by
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
theorem b_M3_le {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq : (q : ℝ) ≤ T / 6) (hδq : 8 * (T / 6) < |δ| * q) :
    4 * (√(kap1 (T ^ 3) (U2 T) (V2 T)) * (√((T ^ 3) ^ 2 / (2 * |δ| * q) +
      (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) * (2 / 3 *
      (Real.log (8 * |δ| * q) * √(Real.log (8 * |δ| * q)) - Real.log (V2 T) * √(Real.log (V2 T)))) +
      √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√(Real.log (V2 T)) + 1 / √(Real.log (V2 T))) /
        √(V2 T) +
      √(T ^ 3) * √(Real.log (8 * |δ| * q)) * √(8 * |δ| * q))) ≤
    4 * (0.49075 * (0.612373 * (3.4658 * √(Real.log T + 2.3672)) +
      0.0019072 * (√(2 * Real.log T - 7.1106) * (Real.log T - 6.0119)) +
      0.70712 * 1.73207 * (√(Real.log T - 1.0986) + 1 / √(Real.log T - 1.0986)) +
      0.02158 * √(2 * Real.log T - 7.1106))) * (T ^ 2 * √T) := by
  obtain ⟨hD1, hD2⟩ := b_facts hT h hδq
  have hT0 : 0 < T := by linarith
  have hsT := sqrt_ge_2449 hT
  have hss : √T * √T = T := Real.mul_self_sqrt hT0.le
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hV := V2_ge' hT
  have hVle := V2_le hT0
  have hV0 : (0 : ℝ) < V2 T := by linarith
  have hxU := xU2_le hT
  set D := |δ| * q with hDdef
  have hD0 : 0 < D := by linarith
  set u := 3 * D / (4 * T) with hudef
  have hu1 : 1 ≤ u := by rw [hudef, le_div_iff₀ (by positivity)]; linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log u with hℓdef
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hu1
  have hexp : rexp ℓ = u := Real.exp_log hu0
  have hDu : D = 4 * T / 3 * u := by rw [hudef]; field_simp
  have h8D' : 8 * |δ| * q = 8 * D := by rw [hDdef]; ring
  have h8D : 8 * D ≤ T ^ 3 / U2 T := by
    have : 8 * D ≤ 2792 * T := by linarith
    have : 2792 * T ≤ T ^ 2 / 1225 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith [xU2_ge hT]
  have hpos8 : 0 < 8 * |δ| * q := by rw [h8D']; linarith
  -- logs.
  set A := Real.log (8 * |δ| * q) with hAdef
  set Vl := Real.log (V2 T) with hVldef
  have hVl1 : 1 ≤ Vl := by
    rw [hVldef, Real.le_log_iff_exp_le hV0]; linarith [Real.exp_one_lt_d9, V2_ge_50000 hT]
  have hVlL : Vl ≤ L - 1.0986 := by
    have := Real.log_le_log hV0 hVle
    rw [Real.log_div hT0.ne' (by norm_num)] at this; rw [hVldef, hLdef]; linarith [log3_ge]
  have hVA : Vl ≤ A := Real.log_le_log hV0 (by rw [h8D']; linarith)
  have hA1 : A ≤ L + 2.3672 + ℓ := by
    have : 8 * |δ| * q = T * (32 / 3) * u := by rw [h8D', hDu]; ring
    rw [hAdef, this, Real.log_mul (by positivity) hu0.ne', Real.log_mul hT0.ne' (by norm_num)]
    linarith [log_32_3_le]
  have hA2 : A ≤ 2 * L - 7.1106 := by
    have h1 : 8 * |δ| * q ≤ T ^ 2 / 1224.99 := by rw [h8D']; linarith
    have := Real.log_le_log hpos8 h1
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at this
    push_cast at this; rw [hAdef, hLdef]; linarith [log_1224_ge]
  have hAV1 : A - Vl ≤ 3.4658 + ℓ := by
    have h1 : 8 * |δ| * q / V2 T ≤ 32.0004 * u := by
      rw [div_le_iff₀ hV0, h8D', hDu]; nlinarith [mul_le_mul_of_nonneg_left hV hu0.le, mul_pos hu0 hT0]
    have := Real.log_le_log (div_pos hpos8 hV0) h1
    rw [Real.log_div hpos8.ne' hV0.ne', Real.log_mul (by norm_num) hu0.ne'] at this
    rw [hAdef, hVldef, hℓdef]; linarith [log_32_le]
  have hAV2 : A - Vl ≤ L - 6.0119 := by
    have h1 : 8 * |δ| * q / V2 T ≤ T / 408.32 := by
      rw [div_le_div_iff₀ hV0 (by norm_num)]
      have : 8 * |δ| * q * 1224.99 ≤ T ^ 2 := by
        have := h8D.trans hxU; rw [h8D']; rwa [le_div_iff₀ (by norm_num)] at this
      nlinarith [mul_le_mul_of_nonneg_left hV hT0.le]
    have := Real.log_le_log (div_pos hpos8 hV0) h1
    rw [Real.log_div hpos8.ne' hV0.ne', Real.log_div hT0.ne' (by norm_num)] at this
    rw [hAdef, hVldef, hLdef]; linarith [log_408326_ge]
  have hA0 : 0 ≤ A := by linarith
  have hκ := kap1_le_second hT
  have hsκ : √(kap1 (T ^ 3) (U2 T) (V2 T)) ≤ 0.49075 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  -- `ρ = 349/6T`.
  have hQ0 : 0 < Q2 T := by unfold Q2; positivity
  have hρQ : (1 - T / 6 / Q2 T) * Q2 T ≥ 0.99999 * Q2 T := by
    have : T / 6 / Q2 T ≤ 0.00001 := by
      unfold Q2; rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hρ0 : 0.99999 ≤ 1 - T / 6 / Q2 T := by
    have : T / 6 / Q2 T ≤ 0.00001 := by
      unfold Q2; rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hW : 2 / 3 * (A * √A - Vl * √Vl) ≤ √A * (A - Vl) :=
    three_halves_sub_le (by linarith) hVA
  have hW0 : 0 ≤ 2 / 3 * (A * √A - Vl * √Vl) := by
    have := Real.sqrt_le_sqrt hVA
    have : 0 ≤ √Vl := Real.sqrt_nonneg _
    nlinarith
  -- `√M ≤ x/√(2D) + x/(4√((1-ρ)Q₀))`.
  have hM : √((T ^ 3) ^ 2 / (2 * |δ| * q) + (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) ≤
      0.612373 * (T ^ 2 * √T) / √u + 0.0019072 * (T ^ 2 * √T) := by
    have h1 : √((T ^ 3) ^ 2 / (2 * |δ| * q)) ≤ 0.612373 * (T ^ 2 * √T) / √u := by
      have hsu : 0 < √u := Real.sqrt_pos.2 hu0
      rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, mul_pow, sq (√T), hss,
        Real.sq_sqrt hu0.le, show 2 * |δ| * q = 2 * D by rw [hDdef]; ring, hDu,
        div_le_div_iff₀ (by positivity) hu0]
      nlinarith [pow_pos hT0 5, mul_pos (pow_pos hT0 6) hu0]
    have h2 : √((T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) ≤ 0.0019072 * (T ^ 2 * √T) := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
      have h3 : 16 * (0.99999 * Q2 T) ≤ 16 * ((1 - T / 6 / Q2 T) * Q2 T) := by linarith
      have h4 : (0.0019072 * (T ^ 2 * √T)) ^ 2 = 0.0019072 ^ 2 * T ^ 5 := by
        rw [mul_pow, mul_pow, sq (√T), hss]; ring
      rw [h4]; unfold Q2 at h3 ⊢
      have hTT : 2449 ^ 2 ≤ T := by nlinarith
      nlinarith [pow_pos hT0 6, pow_pos hT0 7]
    have h12 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → √(a + b) ≤ √a + √b := fun a b ha hb => by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    refine (h12 _ _ (by positivity) (by positivity)).trans (by linarith)
  -- piece 1a.
  have hP1a : 0.612373 * (T ^ 2 * √T) / √u * (√A * (A - Vl)) ≤
      0.612373 * (3.4658 * √(L + 2.3672)) * (T ^ 2 * √T) := by
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    have hk : √A * (A - Vl) / √u ≤ 3.4658 * √(L + 2.3672) := by
      have h1 : √A * (A - Vl) ≤ √(L + 2.3672 + ℓ) * (3.4658 + ℓ) :=
        mul_le_mul (Real.sqrt_le_sqrt hA1) hAV1 (by linarith) (Real.sqrt_nonneg _)
      have h2 := decay_M3b (L' := L + 2.3672) (by linarith) hℓ
      rw [hexp] at h2
      rw [div_le_iff₀ hsu]
      have h3 : √(L + 2.3672 + ℓ) * (3.4658 + ℓ) ≤ 3.4658 * √(L + 2.3672) * √u := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 3.4658 + ℓ by linarith), ← Real.sqrt_mul (by positivity),
          ← Real.sqrt_sq (show (0 : ℝ) ≤ 3.4658 by norm_num), ← Real.sqrt_mul (by norm_num),
          ← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        nlinarith
      linarith
    calc 0.612373 * (T ^ 2 * √T) / √u * (√A * (A - Vl))
        = 0.612373 * (T ^ 2 * √T) * (√A * (A - Vl) / √u) := by ring
      _ ≤ 0.612373 * (T ^ 2 * √T) * (3.4658 * √(L + 2.3672)) := by gcongr
      _ = _ := by ring
  -- piece 1b.
  have hP1b : 0.0019072 * (T ^ 2 * √T) * (√A * (A - Vl)) ≤
      0.0019072 * (√(2 * L - 7.1106) * (L - 6.0119)) * (T ^ 2 * √T) := by
    have h2 : √A * (A - Vl) ≤ √(2 * L - 7.1106) * (L - 6.0119) :=
      mul_le_mul (Real.sqrt_le_sqrt hA2) hAV2 (by linarith) (Real.sqrt_nonneg _)
    have : 0 ≤ T ^ 2 * √T := by positivity
    nlinarith
  -- piece 2.
  have hP2 : √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) ≤
      0.70712 * 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) * (T ^ 2 * √T) := by
    have h0 : √(1 / (2 * (1 - T / 6 / Q2 T))) ≤ 0.70712 := by
      rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
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
    calc √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T)
        = √(1 / (2 * (1 - T / 6 / Q2 T))) * (T ^ 3 / √(V2 T)) * (√Vl + 1 / √Vl) := by ring
      _ ≤ 0.70712 * (1.73207 * (T ^ 2 * √T)) * (√(L - 1.0986) + 1 / √(L - 1.0986)) := by
          gcongr
      _ = _ := by ring
  -- piece 3.
  have hP3 : √(T ^ 3) * √A * √(8 * |δ| * q) ≤ 0.02158 * √(2 * L - 7.1106) * (T ^ 2 * √T) := by
    have h1 : √(T ^ 3) = T * √T := by
      rw [show T ^ 3 = T ^ 2 * T by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hT0.le]
    have h2 : √(8 * |δ| * q) ≤ 0.02158 * T := by
      rw [Real.sqrt_le_left (by positivity), h8D']
      have : 8 * D ≤ 2792 * T := by linarith
      nlinarith
    rw [h1]
    calc T * √T * √A * √(8 * |δ| * q) ≤ T * √T * √(2 * L - 7.1106) * (0.02158 * T) := by
          gcongr
      _ = _ := by ring
  -- Assemble.
  have hsum : √((T ^ 3) ^ 2 / (2 * |δ| * q) + (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) *
      (2 / 3 * (A * √A - Vl * √Vl)) ≤
      0.612373 * (T ^ 2 * √T) / √u * (√A * (A - Vl)) + 0.0019072 * (T ^ 2 * √T) * (√A * (A - Vl)) := by
    calc _ ≤ (0.612373 * (T ^ 2 * √T) / √u + 0.0019072 * (T ^ 2 * √T)) * (√A * (A - Vl)) :=
          mul_le_mul hM hW hW0 (by positivity)
      _ = _ := by ring
  have hin0 : 0 ≤ √((T ^ 3) ^ 2 / (2 * |δ| * q) + (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) *
      (2 / 3 * (A * √A - Vl * √Vl)) +
      √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) +
      √(T ^ 3) * √A * √(8 * |δ| * q) := by positivity
  have hin : √((T ^ 3) ^ 2 / (2 * |δ| * q) + (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) *
      (2 / 3 * (A * √A - Vl * √Vl)) +
      √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) +
      √(T ^ 3) * √A * √(8 * |δ| * q) ≤
      (0.612373 * (3.4658 * √(L + 2.3672)) +
      0.0019072 * (√(2 * L - 7.1106) * (L - 6.0119)) +
      0.70712 * 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) +
      0.02158 * √(2 * L - 7.1106)) * (T ^ 2 * √T) := by nlinarith
  calc 4 * (√(kap1 (T ^ 3) (U2 T) (V2 T)) *
        (√((T ^ 3) ^ 2 / (2 * |δ| * q) + (T ^ 3) ^ 2 / (16 * (1 - T / 6 / Q2 T) * Q2 T)) *
          (2 / 3 * (A * √A - Vl * √Vl)) +
        √(1 / (2 * (1 - T / 6 / Q2 T))) * T ^ 3 * (√Vl + 1 / √Vl) / √(V2 T) +
        √(T ^ 3) * √A * √(8 * |δ| * q)))
      ≤ 4 * (0.49075 * ((0.612373 * (3.4658 * √(L + 2.3672)) +
          0.0019072 * (√(2 * L - 7.1106) * (L - 6.0119)) +
          0.70712 * 1.73207 * (√(L - 1.0986) + 1 / √(L - 1.0986)) +
          0.02158 * √(2 * L - 7.1106)) * (T ^ 2 * √T))) := by gcongr
    _ = _ := by ring

/-- **Case (b) of the second choice**: `q ≤ T/6`, `|δ| > 8`, `|δ|q > 8T/6`:
`|S_{II}| ≤ (√(12 F₀ X₀ᵇ B₀ᵇ) + SECᵇ(L)) T^{5/2}`. -/
theorem typeII_b {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hq : (q : ℝ) ≤ T / 6) (hδ8 : 8 < |δ|)
    (hδq : 8 * (T / 6) < |δ| * q) :
    ‖typeII α (T ^ 3) (U2 T) (V2 T)‖ ≤
      (√(12 * a1F0 (Real.log T) * bX0 (Real.log T) * bB0 (Real.log T)) + bSEC (Real.log T)) *
        (T ^ 2 * √T) := by
  obtain ⟨hD1, hD2⟩ := b_facts hT h hδq
  obtain ⟨he1, he2⟩ := eps1_bounds hT
  have hT0 : 0 < T := by linarith
  obtain ⟨hq1, hcop, ⟨k, h2α⟩, hδQ, hqQ⟩ := h
  have hQ0 : 0 < Q2 T := by unfold Q2; positivity
  have he := Real.exp_one_lt_d9
  have hxU := xU2_ge hT
  have hρ1 : T / 6 / Q2 T < 1 := by
    unfold Q2; rw [div_lt_one (by positivity)]; nlinarith
  have hqρ : (q : ℝ) ≤ T / 6 / Q2 T * Q2 T := by rw [div_mul_cancel₀ _ hQ0.ne']; exact hq
  have hδq0 : 0 < |δ| * q := by linarith
  have key := typeII_641 (θ := 8) (ρ := T / 6 / Q2 T) (U := U2 T) (V := V2 T) hq1 hcop h2α hδQ hδ8.le (by positivity)
    (x_le_Q2_sq hT) hρ1 hqρ (one_le_U2 hT) (by linarith [V2_ge_50000 hT])
    (by have := V2_le hT0; nlinarith)
    (by
      have : 8 * |δ| * q ≤ 2792 * T := by nlinarith
      have : 2792 * T ≤ T ^ 2 / 1225 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
      nlinarith)
    (by
      have h1 : (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4 * rexp 1 ≤ 8 := by nlinarith [Real.exp_pos 1]
      have h2 := mul_le_mul_of_nonneg_left h1 hδq0.le
      have e : |δ| * q * (1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4 * rexp 1 =
          |δ| * q * ((1 + T ^ 3 / (2 * U2 T * Q2 T)) / 4 * rexp 1) := by ring
      rw [e]; linarith)
  have hh : Approx2 α (T ^ 3) δ a q (Q2 T) := ⟨hq1, hcop, ⟨k, h2α⟩, hδQ, hqQ⟩
  have h1 := b_M1_le hT hh hq hδq
  have h2 := b_M2_le hT hh hq hδq
  have h3 := b_M3_le hT hh hq hδq
  have h4 := a1_M4_le hT
  simp only at key
  refine key.trans ?_
  have e : (√(12 * a1F0 (Real.log T) * bX0 (Real.log T) * bB0 (Real.log T)) +
      bSEC (Real.log T)) * (T ^ 2 * √T) =
      √(12 * a1F0 (Real.log T) * bX0 (Real.log T) * bB0 (Real.log T)) * (T ^ 2 * √T) +
      4 * √(0.24083 * a1F0 (Real.log T) / 2) * (0.057144 + 0.0848 * √(Real.log T + 4.603)) *
        (T ^ 2 * √T) +
      4 * (0.49075 * (0.612373 * (3.4658 * √(Real.log T + 2.3672)) +
        0.0019072 * (√(2 * Real.log T - 7.1106) * (Real.log T - 6.0119)) +
        0.70712 * 1.73207 * (√(Real.log T - 1.0986) + 1 / √(Real.log T - 1.0986)) +
        0.02158 * √(2 * Real.log T - 7.1106))) * (T ^ 2 * √T) +
      8 * 1.4262 * 1.73207 * √(0.24083 * 0.50001) * (T ^ 2 * √T) := by
    unfold bSEC; ring
  rw [e]
  linarith

end TernaryGoldbach.MinorArcs
