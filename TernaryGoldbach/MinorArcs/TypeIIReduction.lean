import TernaryGoldbach.MinorArcs.Decomposition
import TernaryGoldbach.MinorArcs.TypeIIS1
import TernaryGoldbach.Prelim.LambdaMu

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Type II sums: reduction to `S₁`, `S₂` [H, (5.2)–(5.5)]

* `eta2_eq_integral`: `η₂(mn/x) = 4 ∫ 1[x/2W < m ≤ x/W, W/2 < n ≤ W] dW/W` [H, (5.2)];
* `typeII_eq_integral`: `S_{II} = 4 ∫_V^{x/U} IIsum(W) dW/W` [H, (5.3)];
* `norm_IIsum_le`: Cauchy–Schwarz, `|IIsum(W)| ≤ √S₁ (√S₂ + √S₃)` [H, (5.4)–(5.5)], with
  the trusted [RS62, Thm. 13] `ψ(y) - θ(y) < 1.4262 √y` for `S₃`;
* `norm_typeII_le`: `|S_{II}| ≤ 4 ∫_V^{x/U} g(W) dW/W` for any integrable majorant `g`.
-/

open Real Finset MeasureTheory
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open TernaryGoldbach.Helfgott (eta2)

namespace TernaryGoldbach.MinorArcs

/-- `η₂(y) = 4 log(hi/lo)` with `lo = max(1/(2y), 1)`, `hi = min(1/y, 2)` (scaled by `n`). -/
theorem eta2_eq_log {x : ℝ} (hx : 0 < x) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (max (x / (2 * m)) n < min (x / m) (2 * n) →
      eta2 (m * n / x) = 4 * (Real.log (min (x / m) (2 * n)) - Real.log (max (x / (2 * m)) n))) ∧
    (min (x / m) (2 * n) ≤ max (x / (2 * m)) n → eta2 (m * n / x) = 0) := by
  set y := m * n / x with hy
  have hy0 : 0 < y := by positivity
  have hxm : x / m = n / y := by rw [hy]; field_simp
  have hx2m : x / (2 * m) = n / (2 * y) := by rw [hy]; field_simp
  rw [hxm, hx2m]
  constructor
  · intro h
    have hy1 : y < 1 := by
      by_contra h'; push Not at h'
      have : n / y ≤ n := div_le_self hn.le h'
      have := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le h (min_le_left _ _)); linarith
    have hy4 : 1 / 4 < y := by
      by_contra h'; push Not at h'
      have h1 : 2 * n ≤ n / (2 * y) := by rw [le_div_iff₀ (by positivity)]; nlinarith
      have := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le h (min_le_right _ _)); linarith
    unfold eta2
    rw [if_pos hy0]
    rcases le_total y (1 / 2) with h2 | h2
    · have e1 : max (n / (2 * y)) n = n / (2 * y) :=
        max_eq_left (by rw [le_div_iff₀ (by positivity)]; nlinarith)
      have e2 : min (n / y) (2 * n) = 2 * n :=
        min_eq_right (by rw [le_div_iff₀ hy0]; nlinarith)
      have hl : Real.log (2 * y) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
      have l1 : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
      have l2 : Real.log (2 * n) = Real.log 2 + Real.log n := Real.log_mul two_ne_zero hn.ne'
      have l3 : Real.log (n / (2 * y)) = Real.log n - (Real.log 2 + Real.log y) := by
        rw [Real.log_div hn.ne' (by positivity), l1]
      have l4 : Real.log (1 / 4) = -2 * Real.log 2 := by
        rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      have l5 := Real.log_lt_log (by norm_num) hy4
      rw [e1, e2, abs_of_nonpos hl, l1, l2, l3, max_eq_left (by linarith)]; ring
    · have e1 : max (n / (2 * y)) n = n :=
        max_eq_right (by rw [div_le_iff₀ (by positivity)]; nlinarith)
      have e2 : min (n / y) (2 * n) = n / y :=
        min_eq_left (by rw [div_le_iff₀ hy0]; nlinarith)
      have hl : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
      have l1 : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
      have l3 : Real.log (n / y) = Real.log n - Real.log y := Real.log_div hn.ne' hy0.ne'
      have : Real.log y < 0 := Real.log_neg hy0 hy1
      rw [e1, e2, abs_of_nonneg hl, l1, l3, max_eq_left (by linarith)]; ring
  · intro h
    apply Helfgott.eta2_eq_zero
    rintro ⟨h1, h2⟩
    have a1 : n / (2 * y) < n / y := div_lt_div_of_pos_left hn hy0 (by linarith)
    have a2 : n < n / y := by rw [lt_div_iff₀ hy0]; nlinarith
    have a3 : n / (2 * y) < 2 * n := by rw [div_lt_iff₀ (by positivity)]; nlinarith
    have : max (n / (2 * y)) n < min (n / y) (2 * n) :=
      max_lt (lt_min a1 a3) (lt_min a2 (by linarith))
    linarith

/-- **[H, (5.2)–(5.3)]**: `η₂(mn/x) = 4 ∫ 1[x/2W < m ≤ x/W, W/2 < n ≤ W] dW/W` (over any
`[A, B] ⊇ [max(x/2m, n), min(x/m, 2n)]`, `A > 0`). -/
theorem eta2_eq_integral {x : ℝ} (hx : 0 < x) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hAlo : A ≤ max (x / (2 * m)) n)
    (hhiB : min (x / m) (2 * n) ≤ B) :
    eta2 (m * n / x) = 4 * ∫ W in A..B,
      (if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 / W else 0) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set lo := max (x / (2 * m)) (n : ℝ) with hlo
  set hi := min (x / m) (2 * (n : ℝ)) with hhi
  have hlo0 : 0 < lo := lt_of_lt_of_le hn0 (le_max_right _ _)
  -- Change the integrand off the countable set `{x/2m, x/m}`.
  have hae : ∫ W in A..B,
      (if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 / W else 0) =
      ∫ W in A..B, (if lo ≤ W ∧ W < hi then 1 / W else 0) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hc : ({x / (2 * m), x / m} : Set ℝ).Countable := (Set.toFinite _).countable
    filter_upwards [hc.ae_notMem volume] with W hW hWI
    rw [Set.uIoc_of_le hAB] at hWI
    have hW0 : 0 < W := lt_trans hA hWI.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hW
    have c1 : x / (2 * W) < m ↔ x / (2 * m) ≤ W := by
      rw [div_lt_iff₀ (by positivity), div_le_iff₀ (by positivity)]
      constructor
      · intro h; linarith
      · intro h
        rcases h.lt_or_eq with h | h
        · linarith
        · exfalso; apply hW.1; field_simp; linarith
    have c2 : (m : ℝ) ≤ x / W ↔ W < x / m := by
      rw [le_div_iff₀ hW0, lt_div_iff₀ hm0]
      constructor
      · intro h
        rcases h.lt_or_eq with h | h
        · linarith
        · exfalso; apply hW.2; field_simp; linarith
      · intro h; linarith
    have c3 : W / 2 < n ↔ W < 2 * n := by constructor <;> intro h <;> linarith
    have hiff : (x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W) ↔
        (lo ≤ W ∧ W < hi) := by
      rw [c1, c2, c3, hlo, hhi, max_le_iff, lt_min_iff]; tauto
    exact if_congr hiff rfl rfl
  rw [hae]
  rcases lt_or_ge lo hi with hlh | hlh
  · rw [(eta2_eq_log hx hm0 hn0).1 hlh]
    congr 1
    set F : ℝ → ℝ := fun W => Real.log (max lo (min W hi))
    have hint : IntervalIntegrable (fun W => if lo ≤ W ∧ W < hi then 1 / W else 0) volume A B := by
      have : (fun W : ℝ => if lo ≤ W ∧ W < hi then 1 / W else 0) =
          (Set.Ico lo hi).indicator (fun W => 1 / W) := by
        ext W; simp [Set.indicator, Set.mem_Ico]
      rw [this, intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
      refine IntegrableOn.indicator ?_ measurableSet_Ico
      refine ContinuousOn.integrableOn_Icc ?_
      exact continuousOn_const.div continuousOn_id fun W hW => (lt_of_lt_of_le hA hW.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hAB (f := F) ?_ ?_ hint]
    · simp only [F]
      rw [min_eq_right hhiB, max_eq_right hlh.le, max_eq_left (min_le_of_left_le hAlo)]
    · refine ContinuousOn.log ?_ fun W _ => (lt_of_lt_of_le hlo0 (le_max_left _ _)).ne'
      exact (continuous_const.max (continuous_id.min continuous_const)).continuousOn
    · intro W hW
      rcases lt_or_ge W lo with h1 | h1
      · rw [if_neg (by rintro ⟨h, -⟩; linarith)]
        refine (hasDerivWithinAt_const W _ (Real.log lo)).congr_of_eventuallyEq ?_ ?_
        · filter_upwards [Ioo_mem_nhdsGT h1] with W' hW'
          simp only [F]; rw [max_eq_left (min_le_of_left_le hW'.2.le)]
        · simp only [F]; rw [max_eq_left (min_le_of_left_le h1.le)]
      rcases lt_or_ge W hi with h2 | h2
      · rw [if_pos ⟨h1, h2⟩]
        have hW0 : 0 < W := lt_of_lt_of_le hlo0 h1
        refine ((Real.hasDerivAt_log hW0.ne').hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_).congr_deriv
          (one_div W).symm
        · filter_upwards [Ioo_mem_nhdsGT h2] with W' hW'
          simp only [F]; rw [min_eq_left hW'.2.le, max_eq_right (le_trans h1 hW'.1.le)]
        · simp only [F]; rw [min_eq_left h2.le, max_eq_right h1]
      · rw [if_neg (by rintro ⟨-, h⟩; linarith)]
        refine (hasDerivWithinAt_const W _ (Real.log hi)).congr_of_eventuallyEq ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with W' hW'
          simp only [F]; rw [min_eq_right (le_trans h2 (le_of_lt hW')), max_eq_right hlh.le]
        · simp only [F]; rw [min_eq_right h2, max_eq_right hlh.le]
  · rw [(eta2_eq_log hx hm0 hn0).2 hlh]
    have : (fun W : ℝ => if lo ≤ W ∧ W < hi then 1 / W else 0) = fun _ => 0 := by
      ext W; rw [if_neg]; rintro ⟨h1, h2⟩; linarith
    rw [this]; simp


/-- The indicator weight `1[x/2W < m ≤ x/W, W/2 < n ≤ W]/W`. -/
noncomputable def indW (x : ℝ) (m n : ℕ) (W : ℝ) : ℝ :=
  if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 / W else 0

theorem indW_intervalIntegrable (x : ℝ) (m n : ℕ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (indW x m n) volume A B := by
  have : indW x m n = {W : ℝ | x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W}.indicator
      (fun W => 1 / W) := by
    ext W; simp [indW, Set.indicator]
  rw [this, intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
  refine IntegrableOn.indicator ?_ ?_
  · exact ContinuousOn.integrableOn_Icc
      (continuousOn_const.div continuousOn_id fun W hW => (lt_of_lt_of_le hA hW.1).ne')
  · refine MeasurableSet.inter (measurableSet_lt
      (measurable_const.div (measurable_const.mul measurable_id)) measurable_const) ?_
    refine MeasurableSet.inter (measurableSet_le measurable_const
      (measurable_const.div measurable_id)) ?_
    exact MeasurableSet.inter (measurableSet_lt (measurable_id.div_const 2) measurable_const)
      (measurableSet_le measurable_const measurable_id)

theorem intervalIntegrable_ofReal_mul {f : ℝ → ℝ} {A B : ℝ} (h : IntervalIntegrable f volume A B)
    (c : ℂ) : IntervalIntegrable (fun W => c * (f W : ℂ)) volume A B :=
  ⟨h.1.ofReal.const_mul c, h.2.ofReal.const_mul c⟩

theorem intervalIntegrable_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun W => ∑ i ∈ s, f i W) volume a b := by
  have := IntervalIntegrable.sum s h
  convert this using 1; ext W; simp [Finset.sum_apply]

/-- `∑_{d | m, d > U} μ(d)`. -/
noncomputable def coefM (U m : ℕ) : ℂ := ∑ d ∈ m.divisors.filter (U < ·), (μ d : ℂ)

theorem coefM_eq_zero {U m : ℕ} (hm : m ≤ U) : coefM U m = 0 := by
  refine sum_eq_zero fun d hd => ?_
  simp only [mem_filter, Nat.mem_divisors] at hd
  have := Nat.le_of_dvd (by omega) hd.1.1; omega

open Classical in
/-- The integrand of [H, (5.3)]: `∑_{x/2W < m ≤ x/W odd} c_m ∑_{max(V, W/2) < n ≤ W odd}
Λ(n) e(αmn)`, `c_m = ∑_{d | m, d > U} μ(d)`. -/
noncomputable def IIsum (α x : ℝ) (U V : ℕ) (W : ℝ) : ℂ :=
  ∑ m ∈ Ioc ⌊x / (2 * W)⌋₊ ⌊x / W⌋₊, if Odd m then coefM U m *
    ∑ n ∈ Ioc ⌊max (V : ℝ) (W / 2)⌋₊ ⌊W⌋₊, (if Odd n then (Λ n : ℂ) * e (α * m * n) else 0) else 0

/-- **[H, (5.3)]**: `S_{II} = 4 ∫_V^{x/U} IIsum(W) dW/W`. -/
theorem typeII_eq_integral (α : ℝ) {x : ℝ} (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hVU : (V : ℝ) ≤ x / U) :
    typeII α x U V = 4 * ∫ W in (V : ℝ)..x / U, IIsum α x U V W / W := by
  set N := ⌊x⌋₊
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hint : ∀ m n : ℕ, IntervalIntegrable (indW x m n) volume V (x / U) :=
    fun m n => indW_intervalIntegrable x m n hV0 hVU
  -- Step 1: insert the integral formula for `η₂`.
  have h1 : typeII α x U V = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      ∫ W in (V : ℝ)..x / U, ((if Odd m ∧ Odd n ∧ V < n then
        4 * coefM U m * (Λ n : ℂ) * e (α * m * n) else 0) * ((indW x m n W : ℝ) : ℂ)) := by
    rw [typeII]
    refine sum_congr rfl fun m hm => ?_
    have hm1 := (mem_Icc.1 hm).1
    split_ifs with hmo
    · rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn1 := (mem_Icc.1 hn).1
      rw [intervalIntegral.integral_const_mul]
      by_cases hc : Odd n ∧ V < n
      · rw [if_pos hc, if_pos ⟨hmo, hc⟩]
        by_cases hmU : m ≤ U
        · have h0 : (∑ d ∈ m.divisors.filter (U < ·), (μ d : ℂ)) = 0 := coefM_eq_zero hmU
          simp [h0, coefM_eq_zero hmU]
        · push Not at hmU
          have hmU' : (U : ℝ) < m := by exact_mod_cast hmU
          have hnV : (V : ℝ) < n := by exact_mod_cast hc.2
          rw [eta2_eq_integral hx hm1 hn1 hV0 hVU (le_trans hnV.le (le_max_right _ _))
            (le_trans (min_le_left _ _) (div_le_div_of_nonneg_left hx.le hU0 hmU'.le)),
            intervalIntegral.integral_ofReal]
          simp only [coefM, indW]; push_cast; ring
      · rw [if_neg hc, if_neg (fun h => hc h.2)]; simp
    · refine (sum_eq_zero fun n _ => ?_).symm
      rw [if_neg (fun h => hmo h.1)]; simp
  -- Step 2: swap sums and integral.
  rw [h1]
  have hF : ∀ m n : ℕ, IntervalIntegrable (fun W => (if Odd m ∧ Odd n ∧ V < n then
      4 * coefM U m * (Λ n : ℂ) * e (α * m * n) else 0) * ((indW x m n W : ℝ) : ℂ))
      volume V (x / U) := fun m n => intervalIntegrable_ofReal_mul (hint m n) _
  rw [sum_congr rfl fun m _ => (intervalIntegral.integral_finsetSum fun n _ => hF m n).symm,
    ← intervalIntegral.integral_finsetSum fun m _ => intervalIntegrable_sum' _ fun n _ => hF m n,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun W hW => ?_
  rw [Set.uIcc_of_le hVU] at hW
  have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
  have hWx : W ≤ x := hW.2.trans (div_le_self hx.le (by exact_mod_cast hU))
  rw [IIsum, sum_div, mul_sum]
  have hIoc₁ : Ioc ⌊x / (2 * W)⌋₊ ⌊x / W⌋₊ ⊆ Icc 1 N := by
    intro m hm
    simp only [mem_Ioc] at hm
    refine mem_Icc.2 ⟨by omega, hm.2.trans (Nat.floor_le_floor ?_)⟩
    rw [div_le_iff₀ hW0]
    nlinarith [hW.1, show (1 : ℝ) ≤ V by exact_mod_cast hV]
  rw [← sum_subset hIoc₁]
  swap
  · intro m hm hm'
    refine sum_eq_zero fun n _ => ?_
    have : ¬ (x / (2 * W) < m ∧ (m : ℝ) ≤ x / W) := by
      rintro ⟨h1, h2⟩
      exact hm' (mem_Ioc.2 ⟨(Nat.floor_lt (by positivity)).2 h1, Nat.le_floor h2⟩)
    rw [show indW x m n W = 0 from if_neg (fun h => this ⟨h.1, h.2.1⟩)]; simp
  refine sum_congr rfl fun m hm => ?_
  simp only [mem_Ioc] at hm
  have hm1 : x / (2 * W) < m := (Nat.floor_lt (by positivity)).1 hm.1
  have hm2 : (m : ℝ) ≤ x / W := (Nat.le_floor_iff (by positivity)).1 hm.2
  have hIoc₂ : Ioc ⌊max (V : ℝ) (W / 2)⌋₊ ⌊W⌋₊ ⊆ Icc 1 N := by
    intro n hn
    simp only [mem_Ioc] at hn
    exact mem_Icc.2 ⟨by omega, hn.2.trans (Nat.floor_le_floor hWx)⟩
  split_ifs with hmo
  · rw [mul_sum, sum_div, mul_sum, ← sum_subset hIoc₂]
    · refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 := (Nat.floor_lt (by positivity)).1 hn.1
      have hn2 : (n : ℝ) ≤ W := (Nat.le_floor_iff hW0.le).1 hn.2
      have hnV : V < n := by
        have : (V : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn1
        exact_mod_cast this
      have hnW : W / 2 < n := lt_of_le_of_lt (le_max_right _ _) hn1
      rw [show indW x m n W = 1 / W from if_pos ⟨hm1, hm2, hnW, hn2⟩]
      by_cases hno : Odd n
      · rw [if_pos ⟨hmo, hno, hnV⟩, if_pos hno]; push_cast; field_simp
      · rw [if_neg (fun h => hno h.2.1), if_neg hno]; simp
    · intro n hn hn'
      have : ¬ (V < n ∧ W / 2 < n ∧ (n : ℝ) ≤ W) := by
        rintro ⟨h1, h2, h3⟩
        refine hn' (mem_Ioc.2 ⟨(Nat.floor_lt (by positivity)).2 (max_lt ?_ h2), Nat.le_floor h3⟩)
        exact_mod_cast h1
      by_cases hc : Odd m ∧ Odd n ∧ V < n
      · rw [if_pos hc, show indW x m n W = 0 from if_neg (fun h => this ⟨hc.2.2, h.2.2⟩)]; simp
      · rw [if_neg hc]; simp
  · rw [sum_eq_zero fun n _ => by rw [if_neg (fun h => hmo h.1)]; simp]; simp


/-! ### Cauchy–Schwarz [H, (5.4)–(5.5)] -/

theorem sum_Ioc_int_eq_nat {A B : ℝ} (hA : 0 ≤ A) (f : ℤ → ℝ) :
    ∑ m ∈ Ioc ⌊A⌋ ⌊B⌋, f m = ∑ m ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f m := by
  have h1 : (⌊A⌋₊ : ℤ) = ⌊A⌋ := Int.natCast_floor_eq_floor hA
  have h2 : ⌊B⌋ ≤ (⌊B⌋₊ : ℤ) := by
    rcases le_or_gt 0 B with hB | hB
    · rw [Int.natCast_floor_eq_floor hB]
    · have : ⌊B⌋ < 0 := Int.floor_lt.2 (by simpa using hB)
      omega
  have h3 : ∀ n : ℕ, ⌊A⌋₊ < n → n ≤ ⌊B⌋₊ → (n : ℤ) ≤ ⌊B⌋ := by
    intro n hn1 hn2
    have hB : 0 ≤ B := by
      by_contra h; push Not at h
      rw [Nat.floor_of_nonpos h.le] at hn2; omega
    rw [← Int.natCast_floor_eq_floor hB]; exact_mod_cast hn2
  refine sum_nbij' (fun m => m.toNat) (fun n => (n : ℤ)) (fun m hm => ?_) (fun n hn => ?_)
    (fun m hm => ?_) (fun n _ => by simp) (fun m hm => ?_)
  · simp only [mem_Ioc] at hm ⊢; omega
  · simp only [mem_Ioc] at hn ⊢; exact ⟨by omega, h3 n hn.1 hn.2⟩
  · simp only [mem_Ioc] at hm; omega
  · simp only [mem_Ioc] at hm
    rw [Int.toNat_of_nonneg (by omega)]

/-- [H, (5.4)–(5.5)]: `|IIsum(W)| ≤ √S₁(U, W) (√S₂(U', W', W) + √S₃(W))` with
`U' = max(U, x/2W)`, `W' = max(V, W/2)`, `S₃(W) ≤ (x/2W + 1)(1.4262 √W)²` ([RS62, Thm. 13]). -/
theorem norm_IIsum_le (α : ℝ) {x : ℝ} (hx : 0 < x) {U V : ℕ} (hV : 2 ≤ V) {W : ℝ} (hW : 0 < W) :
    ‖IIsum α x U V W‖ ≤ √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
      √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) := by
  set W' := max (V : ℝ) (W / 2)
  set U' := max (U : ℝ) (x / (2 * W))
  set R := (Ioc ⌊U'⌋₊ ⌊x / W⌋₊).filter Odd
  set P : ℕ → ℂ := fun m => primeExpSum W' W (α * m)
  set Q : ℕ → ℂ := fun m => ∑ n ∈ Ioc ⌊W'⌋₊ ⌊W⌋₊,
    (if n.Prime then 0 else if Odd n then (Λ n : ℂ) * e (α * m * n) else 0)
  set c : ℕ → ℝ := fun m => ∑ d ∈ m.divisors.filter (U < ·), (μ d : ℝ)
  have hW'2 : (2 : ℝ) ≤ W' := le_trans (by exact_mod_cast hV) (le_max_left _ _)
  -- `IIsum = ∑_{m ∈ R} c_m (P_m + Q_m)`.
  have hT : ∀ m : ℕ, (∑ n ∈ Ioc ⌊W'⌋₊ ⌊W⌋₊, (if Odd n then (Λ n : ℂ) * e (α * m * n) else 0)) =
      P m + Q m := by
    intro m
    simp only [P, Q, primeExpSum]
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    by_cases hp : n.Prime
    · have hn2 : 2 < n := by
        have := (Nat.floor_lt (by linarith)).1 (mem_Ioc.1 hn).1
        have : (2 : ℝ) < n := by linarith
        exact_mod_cast this
      have hodd : Odd n := hp.odd_of_ne_two (by omega)
      rw [if_pos hodd, if_pos hp, if_pos hp, add_zero, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · rw [if_neg hp, if_neg hp, zero_add]
  have hII : IIsum α x U V W = ∑ m ∈ R, (c m : ℂ) * (P m + Q m) := by
    rw [IIsum, sum_filter]
    have hsub : Ioc ⌊U'⌋₊ ⌊x / W⌋₊ ⊆ Ioc ⌊x / (2 * W)⌋₊ ⌊x / W⌋₊ :=
      Ioc_subset_Ioc_left (Nat.floor_le_floor (le_max_right _ _))
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun m _ => ?_
      split_ifs
      · rw [hT m]; simp only [coefM, c]; push_cast; rfl
      · rfl
    · intro m hm hm'
      have hmU : m ≤ U := by
        simp only [mem_Ioc] at hm hm'
        by_contra h; push Not at h
        apply hm' ⟨?_, hm.2⟩
        rw [Nat.floor_lt (by positivity)]
        exact max_lt (by exact_mod_cast h) ((Nat.floor_lt (by positivity)).1 hm.1)
      rw [coefM_eq_zero hmU]; simp
  -- Cauchy–Schwarz.
  have hS1 : ∑ m ∈ R, c m ^ 2 = S1 x U W := by
    rw [S1, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    simp only [c, Nat.cast_lt]
  have hS2 : ∑ m ∈ R, ‖P m‖ ^ 2 = S2 α x U' W' W := by
    rw [S2, oddSqSum, sum_Ioc_int_eq_nat (le_trans (Nat.cast_nonneg U) (le_max_left _ _)),
      sum_filter]
    refine sum_congr rfl fun m _ => ?_
    simp only [P, Int.odd_coe_nat, Int.cast_natCast]
  have hQ : ∀ m, ‖Q m‖ ≤ 1.4262 * √W := by
    intro m
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (Prelim.sum_vonMangoldt_nonprime_lt hW).le
    have hsub : Ioc ⌊W'⌋₊ ⌊W⌋₊ ⊆ Icc 1 ⌊W⌋₊ := fun n hn => by
      simp only [mem_Ioc] at hn; exact mem_Icc.2 ⟨by omega, hn.2⟩
    refine le_trans (sum_le_sum fun n _ => ?_) (sum_le_sum_of_subset_of_nonneg hsub
      fun n _ _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg])
    split_ifs with h1 h2
    · simp
    · rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    · simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hcard : (#R : ℝ) ≤ x / (2 * W) + 1 := by
    have h1 : #R ≤ #(Ioc ⌊x / (2 * W)⌋₊ ⌊x / W⌋₊) :=
      (card_filter_le _ _).trans (card_le_card (Ioc_subset_Ioc_left
        (Nat.floor_le_floor (le_max_right _ _))))
    rw [Nat.card_Ioc] at h1
    have h2 : (#R : ℝ) ≤ (⌊x / W⌋₊ : ℝ) - ⌊x / (2 * W)⌋₊ := by
      have := Nat.cast_le (α := ℝ) |>.2 h1
      push_cast [Nat.cast_sub (Nat.floor_le_floor (by
        rw [div_le_div_iff₀ (by positivity) hW]; nlinarith : x / (2 * W) ≤ x / W))] at this
      exact this
    have h3 := Nat.floor_le (div_nonneg hx.le hW.le)
    have h4 := Nat.lt_floor_add_one (x / (2 * W))
    have : x / W - x / (2 * W) = x / (2 * W) := by field_simp; ring
    linarith
  have hS3 : ∑ m ∈ R, ‖Q m‖ ^ 2 ≤ (x / (2 * W) + 1) * (1.4262 ^ 2 * W) := by
    calc ∑ m ∈ R, ‖Q m‖ ^ 2 ≤ ∑ m ∈ R, (1.4262 * √W) ^ 2 :=
          sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (hQ m) 2
      _ = #R * (1.4262 ^ 2 * W) := by rw [sum_const, nsmul_eq_mul, mul_pow, sq_sqrt hW.le]
      _ ≤ _ := by gcongr
  rw [hII]
  calc ‖∑ m ∈ R, (c m : ℂ) * (P m + Q m)‖
      ≤ ∑ m ∈ R, |c m| * (‖P m‖ + ‖Q m‖) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr; exact norm_add_le _ _
    _ = ∑ m ∈ R, |c m| * ‖P m‖ + ∑ m ∈ R, |c m| * ‖Q m‖ := by
        rw [← sum_add_distrib]; refine sum_congr rfl fun m _ => by ring
    _ ≤ √(∑ m ∈ R, |c m| ^ 2) * √(∑ m ∈ R, ‖P m‖ ^ 2) +
          √(∑ m ∈ R, |c m| ^ 2) * √(∑ m ∈ R, ‖Q m‖ ^ 2) :=
        add_le_add (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
    _ ≤ _ := by
        simp only [sq_abs]
        rw [hS1, hS2, ← mul_add]
        gcongr


/-- **[H, (5.3)–(5.5)]**: `|S_{II}| ≤ 4 ∫_V^{x/U} g(W) dW/W` for any integrable `g` with
`√S₁(U, W) (√S₂(U', W', W) + √S₃(W)) ≤ g(W)` on `[V, x/U]` (`U' = max(U, x/2W)`,
`W' = max(V, W/2)`, `S₃(W) ≤ (x/2W + 1)(1.4262² W)`). -/
theorem norm_typeII_le (α : ℝ) {x : ℝ} (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U) (hV : 2 ≤ V)
    (hVU : (V : ℝ) ≤ x / U) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun W => g W / W) volume V (x / U))
    (hbound : ∀ W ∈ Set.Icc (V : ℝ) (x / U),
      √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
        √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ g W) :
    ‖typeII α x U V‖ ≤ 4 * ∫ W in (V : ℝ)..x / U, g W / W := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  rw [typeII_eq_integral α hx hU (by omega) hVU, norm_mul, Complex.norm_ofNat]
  gcongr
  refine intervalIntegral.norm_integral_le_of_norm_le hVU (Filter.Eventually.of_forall ?_) hg
  intro W hW
  have hW0 : 0 < W := lt_trans hV0 hW.1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW0]
  gcongr
  exact (norm_IIsum_le α hx hV hW0).trans (hbound W ⟨hW.1.le, hW.2⟩)

end TernaryGoldbach.MinorArcs
