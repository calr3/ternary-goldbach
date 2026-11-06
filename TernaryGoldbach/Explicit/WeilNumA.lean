import TernaryGoldbach.Explicit.WeilPhiBound

/-!
# Closed-form pieces for the Weil-window bound

* `aN_le_aC`: `A_N(y) ≤ ½ log(y/2π) + ½ log((N+¼)/(N−¾)) + 1/(2y) + 1/(16y²)` for `y ≥ ½`. The sum in
  `ψ_N` is compared with `∫ x/(x²+z²) dx`, a unimodal integrand (peak `1/(2z)` at `x = z`).
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-! ### The sum in `ψ_N` against its integral -/

/-- The summand of `ψ_N` as a function of `x`. -/
noncomputable def fz (z x : ℝ) : ℝ := x / (x ^ 2 + z ^ 2)

theorem fz_le {z : ℝ} (hz : 0 < z) (x : ℝ) : fz z x ≤ 1 / (2 * z) := by
  unfold fz
  have hd : 0 < x ^ 2 + z ^ 2 := by positivity
  rw [div_le_div_iff₀ hd (by positivity)]
  nlinarith [sq_nonneg (x - z)]

theorem fz_nonneg (z : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fz z x := by
  unfold fz; positivity

theorem continuous_fz {z : ℝ} (hz : 0 < z) : Continuous (fz z) := by
  unfold fz
  exact continuous_id.div (by fun_prop) fun x => by positivity

theorem monotoneOn_fz {z : ℝ} (hz : 0 < z) : MonotoneOn (fz z) (Icc 0 z) := by
  intro x hx y hy hxy
  unfold fz
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : x * y ≤ z ^ 2 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 hxy)]

theorem antitoneOn_fz {z : ℝ} (hz : 0 < z) : AntitoneOn (fz z) (Ici z) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold fz
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  have : z ^ 2 ≤ x * y := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 hxy)]

theorem integral_fz {z : ℝ} (hz : 0 < z) (a b : ℝ) :
    ∫ x in a..b, fz z x = 1 / 2 * Real.log (b ^ 2 + z ^ 2) - 1 / 2 * Real.log (a ^ 2 + z ^ 2) := by
  have hd : ∀ x : ℝ, 0 < x ^ 2 + z ^ 2 := fun x => by positivity
  have hderiv : ∀ x ∈ [[a, b]], HasDerivAt (fun x => 1 / 2 * Real.log (x ^ 2 + z ^ 2)) (fz z x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + z ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (z ^ 2)
    have h2 := (h1.log (hd x).ne').const_mul (1 / 2 : ℝ)
    convert h2 using 1
    unfold fz; field_simp
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_fz hz).intervalIntegrable _ _)

/-- **The sum in `ψ_N` is at least its integral, less the peak.** -/
theorem integral_fz_le_sum {z : ℝ} (hz : 1 / 4 ≤ z) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (1 / 4 : ℝ)..((N : ℝ) - 3 / 4), fz z x ≤
      ∑ k ∈ range N, fz z ((k : ℝ) + 1 / 4) + 1 / (2 * z) := by
  have hz0 : 0 < z := by linarith
  have hfi : ∀ a b : ℝ, IntervalIntegrable (fz z) volume a b :=
    fun a b => (continuous_fz hz0).intervalIntegrable a b
  have hS0 : ∀ k : ℕ, 0 ≤ fz z ((k : ℝ) + 1 / 4) := fun k => fz_nonneg z (by positivity)
  have hpeak : 0 ≤ 1 / (2 * z) := by positivity
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hNx : ((M + 1 : ℕ) : ℝ) - 3 / 4 = 1 / 4 + (M : ℝ) := by push_cast; ring
  rw [hNx]
  have hshift : ∀ i : ℕ, (1 / 4 : ℝ) + ((i + 1 : ℕ) : ℝ) = ((i + 1 : ℕ) : ℝ) + 1 / 4 := fun i => by ring
  by_cases hcase : (1 / 4 : ℝ) + M ≤ z
  · -- monotone on the whole range
    have hmono : MonotoneOn (fz z) (Icc (1 / 4) (1 / 4 + (M : ℝ))) :=
      (monotoneOn_fz hz0).mono (Icc_subset_Icc (by norm_num) hcase)
    have h1 := hmono.integral_le_sum
    simp only [hshift] at h1
    have h2 : ∑ i ∈ range M, fz z (((i + 1 : ℕ) : ℝ) + 1 / 4) ≤ ∑ k ∈ range (M + 1), fz z ((k : ℝ) + 1 / 4) := by
      rw [Finset.sum_range_succ']
      linarith [hS0 0]
    linarith
  · push Not at hcase
    set a := ⌊z - 1 / 4⌋₊ with ha
    have ha1 : (a : ℝ) ≤ z - 1 / 4 := Nat.floor_le (by linarith)
    have ha2 : z - 1 / 4 < (a : ℝ) + 1 := Nat.lt_floor_add_one _
    have haM : a < M := by
      have : (a : ℝ) < M := by linarith
      exact_mod_cast this
    obtain ⟨b, hb⟩ : ∃ b, M = a + 1 + b := ⟨M - a - 1, by omega⟩
    have hbM : (M : ℝ) = a + 1 + b := by rw [hb]; push_cast; ring
    -- the three pieces
    have e1 : ∫ x in (1 / 4 : ℝ)..(1 / 4 + (M : ℝ)), fz z x =
        (∫ x in (1 / 4 : ℝ)..(1 / 4 + (a : ℝ)), fz z x) +
        (∫ x in (1 / 4 + (a : ℝ))..(1 / 4 + (a : ℝ) + 1), fz z x) +
        (∫ x in (1 / 4 + (a : ℝ) + 1)..(1 / 4 + (a : ℝ) + 1 + b), fz z x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _),
        intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
      congr 1; rw [hbM]; ring
    have hA : ∫ x in (1 / 4 : ℝ)..(1 / 4 + (a : ℝ)), fz z x ≤
        ∑ i ∈ range a, fz z (((i + 1 : ℕ) : ℝ) + 1 / 4) := by
      have hmono : MonotoneOn (fz z) (Icc (1 / 4) (1 / 4 + (a : ℝ))) :=
        (monotoneOn_fz hz0).mono (Icc_subset_Icc (by norm_num) (by linarith))
      have h1 := hmono.integral_le_sum
      simp only [hshift] at h1
      exact h1
    have hB : ∫ x in (1 / 4 + (a : ℝ))..(1 / 4 + (a : ℝ) + 1), fz z x ≤ 1 / (2 * z) := by
      have := intervalIntegral.integral_mono_on (μ := volume) (f := fz z) (g := fun _ => 1 / (2 * z))
        (show (1 / 4 + (a : ℝ)) ≤ 1 / 4 + a + 1 by linarith) (hfi _ _) intervalIntegrable_const
        (fun x _ => fz_le hz0 x)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    have hC : ∫ x in (1 / 4 + (a : ℝ) + 1)..(1 / 4 + (a : ℝ) + 1 + b), fz z x ≤
        ∑ i ∈ range b, fz z ((((a + 1 + i : ℕ) : ℝ)) + 1 / 4) := by
      have hanti : AntitoneOn (fz z) (Icc (1 / 4 + (a : ℝ) + 1) (1 / 4 + (a : ℝ) + 1 + b)) :=
        (antitoneOn_fz hz0).mono fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1]
      have h1 := hanti.integral_le_sum
      refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      congr 1; push_cast; ring
    have hsum : ∑ i ∈ range a, fz z (((i + 1 : ℕ) : ℝ) + 1 / 4) +
        ∑ i ∈ range b, fz z ((((a + 1 + i : ℕ) : ℝ)) + 1 / 4) ≤ ∑ k ∈ range (M + 1), fz z ((k : ℝ) + 1 / 4) := by
      have e : M + 1 = (1 + a) + (b + 1) := by omega
      rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_succ _ b, Finset.sum_range_one]
      have h1 : ∑ i ∈ range a, fz z (((i + 1 : ℕ) : ℝ) + 1 / 4) = ∑ x ∈ range a, fz z (((1 + x : ℕ) : ℝ) + 1 / 4) :=
        Finset.sum_congr rfl fun i _ => by rw [add_comm i 1]
      have h2 : ∑ i ∈ range b, fz z ((((a + 1 + i : ℕ) : ℝ)) + 1 / 4) =
          ∑ x ∈ range b, fz z (((1 + a + x : ℕ) : ℝ) + 1 / 4) :=
        Finset.sum_congr rfl fun i _ => by rw [add_comm a 1]
      rw [h1, h2]
      linarith [hS0 0, hS0 (1 + a + b)]
    linarith

/-- **`ψ_N(y) ≤ log((N+¼)/(N−¾)) + log y + 1/(2y) + 1/(32y²)`** for `y ≥ ¼`. -/
theorem psiN_le_log {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 1 / 4 ≤ y) :
    psiN N y ≤ Real.log (((N : ℝ) + 1 / 4) / ((N : ℝ) - 3 / 4)) + Real.log y + 1 / (2 * y) +
      1 / (32 * y ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) - 3 / 4 := by linarith
  have h := integral_fz_le_sum hy hN
  rw [integral_fz hy0] at h
  have hS : ∑ k ∈ range N, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) =
      ∑ k ∈ range N, fz y ((k : ℝ) + 1 / 4) := rfl
  have e1 : Real.log (1 + y ^ 2 / ((N : ℝ) - 3 / 4) ^ 2) =
      Real.log (((N : ℝ) - 3 / 4) ^ 2 + y ^ 2) - 2 * Real.log ((N : ℝ) - 3 / 4) := by
    set c := (N : ℝ) - 3 / 4 with hcdef
    have hc2 : c ^ 2 ≠ 0 := by positivity
    rw [show 1 + y ^ 2 / c ^ 2 = (c ^ 2 + y ^ 2) / c ^ 2 by rw [add_div, div_self hc2],
      Real.log_div (by positivity) hc2, Real.log_pow]; push_cast; ring
  have e2 : Real.log ((1 / 4 : ℝ) ^ 2 + y ^ 2) = 2 * Real.log y + Real.log (1 + 1 / (16 * y ^ 2)) := by
    rw [show (1 / 4 : ℝ) ^ 2 + y ^ 2 = y ^ 2 * (1 + 1 / (16 * y ^ 2)) by field_simp; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have e3 : Real.log (((N : ℝ) + 1 / 4) / ((N : ℝ) - 3 / 4)) =
      Real.log ((N : ℝ) + 1 / 4) - Real.log ((N : ℝ) - 3 / 4) :=
    Real.log_div (by positivity) hc.ne'
  have h4 : Real.log (1 + 1 / (16 * y ^ 2)) ≤ 1 / (16 * y ^ 2) := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (16 * y ^ 2)); linarith
  unfold psiN
  rw [hS, e1, e3]
  have e5 : ((N : ℝ) - 3 / 4) = ((N : ℝ) - 3 / 4) := rfl
  rw [e2] at h
  have : 1 / (32 * y ^ 2) = 1 / 2 * (1 / (16 * y ^ 2)) := by field_simp; ring
  rw [this]
  linarith

/-- The closed-form majorant of `A_N`. -/
noncomputable def aC (N : ℕ) (y : ℝ) : ℝ :=
  1 / 2 * Real.log y - 1 / 2 * Real.log (2 * π) + 1 / 2 * Real.log (((N : ℝ) + 1 / 4) / ((N : ℝ) - 3 / 4)) +
    1 / (2 * y) + 1 / (16 * y ^ 2)

/-- **`A_N(y) ≤ ½ log(y/2π) + ½ log((N+¼)/(N−¾)) + 1/(2y) + 1/(16y²)`** for `y ≥ ½`. -/
theorem aN_le_aC {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 1 / 2 ≤ y) : aN N y ≤ aC N y := by
  have hy0 : 0 < y := by linarith
  have h := psiN_le_log hN (y := y / 2) (by linarith)
  unfold aN aC
  have e : Real.log (y / 2) = Real.log y - Real.log 2 := Real.log_div hy0.ne' (by norm_num)
  have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) Real.pi_pos.ne'
  rw [e] at h
  have e3 : 1 / (2 * (y / 2)) = 1 / y := by field_simp
  have e4 : 1 / (32 * (y / 2) ^ 2) = 1 / (8 * y ^ 2) := by field_simp; ring
  rw [e3, e4] at h
  rw [e2]
  have : 1 / (2 * y) = 1 / 2 * (1 / y) := by field_simp
  have h' : 1 / (16 * y ^ 2) = 1 / 2 * (1 / (8 * y ^ 2)) := by field_simp; ring
  rw [this, h']
  linarith

/-! ### `B_R` from below -/

theorem sincC_ofReal_eq (x : ℝ) : sincC (x : ℂ) = (((sincC (x : ℂ)).re : ℝ) : ℂ) :=
  Complex.ext (by rw [Complex.ofReal_re]) (by rw [sincC_ofReal_im, Complex.ofReal_im])

theorem sincC_re_ge (x : ℝ) : 1 - x ^ 2 / 6 ≤ (sincC (x : ℂ)).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sincC_zero]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [sincC_of_ne hxc, ← Complex.ofReal_sin, ← Complex.ofReal_div, Complex.ofReal_re]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h := Real.sin_ge_sub_cube (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    rw [le_div_iff_of_neg hneg]
    nlinarith
  · have h := Real.sin_ge_sub_cube hpos.le
    rw [le_div_iff₀ hpos]
    nlinarith

/-- `B(u)² ≥ (2ℓ)^{2m} (1 − ℓ²u²/6)^{2m}` while `ℓ²u² ≤ 6`. -/
theorem Bsq_ge {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) {u : ℝ} (hu : ℓ ^ 2 * u ^ 2 ≤ 6) :
    (2 * ℓ) ^ (2 * m) * (1 - ℓ ^ 2 * u ^ 2 / 6) ^ (2 * m) ≤ Bsq ℓ m u := by
  have hs := sincC_re_ge (ℓ * u)
  have h0 : 0 ≤ 1 - ℓ ^ 2 * u ^ 2 / 6 := by linarith
  set s := (sincC ((ℓ * u : ℝ) : ℂ)).re with hsdef
  have hsr : sincC ((ℓ : ℂ) * (u : ℂ)) = ((s : ℝ) : ℂ) := by
    rw [show (ℓ : ℂ) * (u : ℂ) = ((ℓ * u : ℝ) : ℂ) by push_cast; ring]
    exact sincC_ofReal_eq _
  have e : WB ℓ m (u : ℂ) = (((2 * ℓ * s) ^ m : ℝ) : ℂ) := by
    unfold WB; rw [hsr]; push_cast; ring
  have hs' : 1 - ℓ ^ 2 * u ^ 2 / 6 ≤ s := by rw [show ℓ ^ 2 * u ^ 2 = (ℓ * u) ^ 2 by ring]; exact hs
  have hb : (2 * ℓ * (1 - ℓ ^ 2 * u ^ 2 / 6)) ^ 2 ≤ (2 * ℓ * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  unfold Bsq
  rw [e, Complex.ofReal_re]
  calc (2 * ℓ) ^ (2 * m) * (1 - ℓ ^ 2 * u ^ 2 / 6) ^ (2 * m) = ((2 * ℓ * (1 - ℓ ^ 2 * u ^ 2 / 6)) ^ 2) ^ m := by
        rw [← pow_mul, ← mul_pow, mul_comm 2 m]
    _ ≤ ((2 * ℓ * s) ^ 2) ^ m := pow_le_pow_left₀ (by positivity) hb m
    _ = ((2 * ℓ * s) ^ m) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm 2 m]

/-- The polynomial lower bound for `B_R` (`m = 2`): `k₀ = 2∫_0^R (1 − cu²)⁴ du`, `c = ℓ²/6`. -/
noncomputable def kB (ℓ R : ℝ) : ℝ :=
  2 * (R - 4 * (ℓ ^ 2 / 6) * R ^ 3 / 3 + 6 * (ℓ ^ 2 / 6) ^ 2 * R ^ 5 / 5 - 4 * (ℓ ^ 2 / 6) ^ 3 * R ^ 7 / 7 +
    (ℓ ^ 2 / 6) ^ 4 * R ^ 9 / 9)

theorem KRB_ge {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 ≤ R) (hlR : ℓ ^ 2 * R ^ 2 ≤ 6) :
    (2 * ℓ) ^ 4 * kB ℓ R ≤ KRB ℓ 2 R := by
  set c := ℓ ^ 2 / 6 with hc
  set F : ℝ → ℝ := fun u => (2 * ℓ) ^ 4 * (u - 4 * c * u ^ 3 / 3 + 6 * c ^ 2 * u ^ 5 / 5 - 4 * c ^ 3 * u ^ 7 / 7 +
    c ^ 4 * u ^ 9 / 9) with hF
  have hderiv : ∀ u ∈ [[-R, R]], HasDerivAt F ((2 * ℓ) ^ (2 * 2) * (1 - ℓ ^ 2 * u ^ 2 / 6) ^ (2 * 2)) u := by
    intro u _
    have d1 := hasDerivAt_id' u
    have d3 := ((hasDerivAt_pow 3 u).const_mul (4 * c)).div_const 3
    have d5 := ((hasDerivAt_pow 5 u).const_mul (6 * c ^ 2)).div_const 5
    have d7 := ((hasDerivAt_pow 7 u).const_mul (4 * c ^ 3)).div_const 7
    have d9 := ((hasDerivAt_pow 9 u).const_mul (c ^ 4)).div_const 9
    have h := ((((d1.sub d3).add d5).sub d7).add d9).const_mul ((2 * ℓ) ^ 4)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)).congr_deriv ?_
    · simp only [hF, Pi.add_apply, Pi.sub_apply]
    · simp only [hc]; push_cast; ring
  have hcont : IntervalIntegrable (fun u : ℝ => (2 * ℓ) ^ (2 * 2) * (1 - ℓ ^ 2 * u ^ 2 / 6) ^ (2 * 2))
      volume (-R) R := by
    apply Continuous.intervalIntegrable; fun_prop
  have hint : ∫ u in (-R)..R, (2 * ℓ) ^ (2 * 2) * (1 - ℓ ^ 2 * u ^ 2 / 6) ^ (2 * 2) = (2 * ℓ) ^ 4 * kB ℓ R := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    simp only [hF, kB, hc]; ring
  rw [← hint, KRB]
  refine intervalIntegral.integral_mono_on (by linarith) hcont
    ((continuous_Bsq ℓ 2).intervalIntegrable _ _) fun u hu => Bsq_ge hℓ 2 ?_
  have : u ^ 2 ≤ R ^ 2 := by nlinarith [hu.1, hu.2]
  nlinarith

/-! ### The tails `I₀`, `I₁` in closed form (`m = 2`) -/

theorem I0_two {R : ℝ} (hR : 0 < R) : I0 2 R = 32 / (3 * R ^ 3) := by
  have e : I0 2 R = ∫ x, (fun v : ℝ => if R < v then (2 / v) ^ (2 * 2) else 0) |x| := rfl
  rw [e, integral_comp_abs (f := fun v : ℝ => if R < v then (2 / v) ^ (2 * 2) else 0)]
  have h1 : ∫ x in Ioi (0 : ℝ), (if R < x then (2 / x) ^ (2 * 2) else 0) =
      ∫ x in Ioi (0 : ℝ), (Ioi R).indicator (fun x : ℝ => 16 * x ^ (-4 : ℝ)) x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · have hx0 : 0 < x := hx
      rw [Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [div_pow]; field_simp; ring
    · rfl
  rw [h1, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hR.le,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hR]
  rw [show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg hR.le,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp; norm_num

theorem I1_two {R : ℝ} (hR : 0 < R) : I1 2 R = 12.8 * R ^ (-(5 / 2) : ℝ) := by
  have e : I1 2 R = ∫ x, (fun v : ℝ => if R < v then √v * (2 / v) ^ (2 * 2) else 0) |x| := rfl
  rw [e, integral_comp_abs (f := fun v : ℝ => if R < v then √v * (2 / v) ^ (2 * 2) else 0)]
  have h1 : ∫ x in Ioi (0 : ℝ), (if R < x then √x * (2 / x) ^ (2 * 2) else 0) =
      ∫ x in Ioi (0 : ℝ), (Ioi R).indicator (fun x : ℝ => 16 * x ^ (-(7 / 2) : ℝ)) x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · have hx0 : 0 < x := hx
      rw [Real.sqrt_eq_rpow, show (-(7 / 2) : ℝ) = 1 / 2 - 4 by norm_num, Real.rpow_sub hx0,
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [div_pow]; field_simp; ring
    · rfl
  rw [h1, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hR.le,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hR]
  rw [show (-(7 / 2) : ℝ) + 1 = -(5 / 2) by norm_num]
  ring
