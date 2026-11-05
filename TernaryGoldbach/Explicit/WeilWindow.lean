import TernaryGoldbach.Explicit.WeilBridge
import TernaryGoldbach.Explicit.PsiPlateau

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# One window of the Weil formula (route D, step P7a)

For the on-line zeros `S` of `zerosRectD zetaF T` with `|γ| ≤ 3·10¹⁰` (all of them are on the line by
`rh_upto`) and a window centre `|T₀| ≤ 1.5·10¹⁰`:
`Σ_S m_ρ B(γ − T₀)² ≤ Φ(T₀) + Off` (`weil_window`), where
`Φ(T₀) = Re [H̃_{T₀}(1) + (1/2π) ∫ A(½ + iy) H̃_{T₀}(½ + iy) dy]` is the right-hand side of the Weil
formula, and `Off = 10⁻¹⁵ · 4^m e^{mℓ}` bounds the zeros with `|γ| > 3·10¹⁰` (`|H| ≤ 4^m e^{mℓ} · 64/γ⁴`,
counted in windows of width `4.4` by `count_tail_windowG`).
-/

open Complex Metric Set Filter Finset
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-! ### Zeros of `ξ` in the rectangle are zeros of `zetaF` -/

theorem xiF_eq_zero_of_mem_rectZerosXi {T : ℝ} {u : ℂ} (hu : u ∈ rectZerosXi T) : xiF u = 0 := by
  rw [rectZerosXi, Finset.mem_filter] at hu
  have hd := (mem_zerosIn hu.1).2
  by_contra hne
  apply hd
  by_cases hb : u ∈ closedBall (1 / 2 : ℂ) (6 * T)
  · rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF (closedBall (1 / 2 : ℂ) (6 * T))) hb,
      (differentiable_xiF.analyticAt u).analyticOrderAt_eq_zero.2 hne]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb

theorem strip_of_mem_rectZerosXi {T : ℝ} {u : ℂ} (hu : u ∈ rectZerosXi T) : 0 < u.re ∧ u.re < 1 := by
  have h := xiF_eq_zero_of_mem_rectZerosXi hu
  constructor
  · by_contra h0; exact xiF_ne_zero_of_re_nonpos (not_lt.1 h0) h
  · by_contra h1; exact xiF_ne_zero_of_one_le_re (not_lt.1 h1) h

theorem im_lt_of_mem_rectZerosXi {T : ℝ} {u : ℂ} (hu : u ∈ rectZerosXi T) : |u.im| < T := by
  rw [rectZerosXi, Finset.mem_filter] at hu
  obtain ⟨-, -, -, h3, h4⟩ := hu
  rw [zT_im] at h3; rw [wT_im] at h4
  exact abs_lt.2 ⟨h3, h4⟩

/-- **The reverse bridge**: a zero of `ξ` in `R_T` is a zero of `zetaF` in `R_T`, with the same
multiplicity. -/
theorem mem_zerosRectD_of_mem_rectZerosXi {T : ℝ} (hT : 1 ≤ T) {u : ℂ} (hu : u ∈ rectZerosXi T) :
    u ∈ zerosRectD zetaF T ∧ mult T u = multRectD zetaF T u := by
  obtain ⟨h0, h1⟩ := strip_of_mem_rectZerosXi hu
  have him := im_lt_of_mem_rectZerosXi hu
  have hb := mem_closedBall_two_RT h0 h1 him
  have hb' := mem_closedBall_half_six hT h0 h1 him
  have heq := divB_eq_of_analyticOrderAt_eq differentiable_zetaF differentiable_xiF hb.1 hb'.1
    (analyticOrderAt_xiF_eq h0).symm
  refine ⟨?_, by rw [mult, multRectD, heq]⟩
  rw [rectZerosXi, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support] at hu
  rw [zerosRectD, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support]
  exact ⟨⟨by rw [heq]; exact hu.1.1, hb.2⟩, hu.2⟩

/-! ### Zeros above `3·10¹⁰` -/

/-- `Σ_{k<K} 1/(H + 4.4k)² ≤ 1/H² + 1/(4.4H)`. -/
theorem sum_inv_sq_lin_le {H : ℝ} (hH : 0 < H) (K : ℕ) :
    ∑ k ∈ range K, 1 / (H + 4.4 * k) ^ 2 ≤ 1 / H ^ 2 + 1 / (4.4 * H) := by
  have key : ∀ K : ℕ, ∑ k ∈ range (K + 1), 1 / (H + 4.4 * k) ^ 2 ≤
      1 / H ^ 2 + (1 / H - 1 / (H + 4.4 * K)) / 4.4 := by
    intro K
    induction K with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have ha : 0 < H + 4.4 * n := by positivity
      have hb : 0 < H + 4.4 * (n + 1) := by positivity
      have hstep : 1 / (H + 4.4 * (n + 1)) ^ 2 ≤ (1 / (H + 4.4 * n) - 1 / (H + 4.4 * (n + 1))) / 4.4 := by
        rw [div_sub_div _ _ ha.ne' hb.ne', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [e1]
      calc (∑ k ∈ range (n + 1), 1 / (H + 4.4 * (k : ℝ)) ^ 2) + 1 / (H + 4.4 * ((n : ℝ) + 1)) ^ 2 ≤
          (1 / H ^ 2 + (1 / H - 1 / (H + 4.4 * n)) / 4.4) +
            (1 / (H + 4.4 * n) - 1 / (H + 4.4 * ((n : ℝ) + 1))) / 4.4 := add_le_add ih hstep
        _ = 1 / H ^ 2 + (1 / H - 1 / (H + 4.4 * ((n : ℝ) + 1))) / 4.4 := by ring
  rcases K with _ | K
  · simp; positivity
  · refine (key K).trans ?_
    have : 0 ≤ 1 / (H + 4.4 * K) := by positivity
    have e : (1 / H - 1 / (H + 4.4 * K)) / 4.4 ≤ 1 / (4.4 * H) := by
      rw [div_le_iff₀ (by norm_num)]; field_simp; linarith
    linarith

/-- The off-line constant. -/
noncomputable def OffC (ℓ : ℝ) (m : ℕ) : ℝ := 4 ^ m * Real.exp (m * ℓ) * 1e-15

theorem OffC_nonneg (ℓ : ℝ) (m : ℕ) : 0 ≤ OffC ℓ m := by unfold OffC; positivity

/-- **The zeros above `3·10¹⁰`** contribute at most `OffC` to the Weil sum. -/
theorem off_line_le {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m) {T₀ : ℝ}
    (hT₀ : |T₀| ≤ 1.5e10) {T : ℝ} (hT : 1 ≤ T) :
    ∑ u ∈ (rectZerosXi T).filter (fun u => ¬ |u.im| ≤ 3e10), (mult T u : ℝ) * ‖WH ℓ m T₀ u‖ ≤ OffC ℓ m := by
  set Z := (rectZerosXi T).filter (fun u => ¬ |u.im| ≤ 3e10) with hZ
  set H : ℝ := 3e10 with hH
  have hZD : ∀ u ∈ Z, u ∈ rectZerosXi T ∧ H < |u.im| := fun u hu =>
    ⟨(Finset.mem_filter.1 hu).1, not_le.1 (Finset.mem_filter.1 hu).2⟩
  -- the pointwise bound `|H(u)| ≤ 4^m e^{mℓ} · 64/(H + 4.4 idx)⁴`
  set idx : ℂ → ℕ := fun u => ⌊(|u.im| - H) / 4.4⌋₊ with hidx
  set E := 4 ^ m * Real.exp (m * ℓ) * 64 with hE
  have hpt : ∀ u ∈ Z, ‖WH ℓ m T₀ u‖ ≤ E * (1 / (H + 4.4 * idx u) ^ 2) ^ 2 := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hZD u hu
    obtain ⟨h0, h1⟩ := strip_of_mem_rectZerosXi hu1
    have h := norm_WH_le_lor_sq hℓ0 hℓ1 hm T₀ u
    have hre : |u.re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have he : Real.exp (2 * m * ℓ * |u.re - 1 / 2|) ≤ Real.exp (m * ℓ) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ (m : ℝ) * ℓ := by positivity
      nlinarith
    have hid : H + 4.4 * idx u ≤ |u.im| := by
      have := Nat.floor_le (a := (|u.im| - H) / 4.4) (by apply div_nonneg <;> linarith)
      rw [hidx]; simp only; rw [le_div_iff₀ (by norm_num)] at this; linarith
    have hγ : |u.im| / 2 ≤ |u.im - T₀| := by
      have := abs_sub_abs_le_abs_sub u.im T₀
      linarith
    have hlor : lor (u.im - T₀) ≤ 8 * (1 / (H + 4.4 * idx u) ^ 2) := by
      unfold lor
      have hpos : 0 < H + 4.4 * idx u := by positivity
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (H + 4.4 * idx u) ^ 2 ≤ 4 * (u.im - T₀) ^ 2 := by
        rw [← sq_abs (u.im - T₀)]
        nlinarith [abs_nonneg u.im, hpos.le]
      nlinarith
    calc ‖WH ℓ m T₀ u‖ ≤ 4 ^ m * Real.exp (2 * m * ℓ * |u.re - 1 / 2|) * lor (u.im - T₀) ^ 2 := h
      _ ≤ 4 ^ m * Real.exp (m * ℓ) * (8 * (1 / (H + 4.4 * idx u) ^ 2)) ^ 2 := by
          gcongr; exact (lor_pos _).le
      _ = E * (1 / (H + 4.4 * idx u) ^ 2) ^ 2 := by rw [hE]; ring
  -- the window counts
  have hZsub : Z ⊆ zerosRectD zetaF T := fun u hu => (mem_zerosRectD_of_mem_rectZerosXi hT (hZD u hu).1).1
  have hmult : ∀ u ∈ Z, (mult T u : ℝ) = multRectD zetaF T u := fun u hu => by
    exact_mod_cast (mem_zerosRectD_of_mem_rectZerosXi hT (hZD u hu).1).2
  have hcnt : ∀ k : ℕ, ∑ u ∈ Z.filter (fun u => idx u = k), (mult T u : ℝ) ≤
      2 * Z3g BPz2 H + 2 * c3g 10 H * (k + 1) := by
    intro k
    rw [Finset.sum_congr rfl fun u hu => hmult u (Finset.mem_filter.1 hu).1]
    exact count_tail_windowG polyDatum_zeta2 (by norm_num) Z hZsub
      (fun u hu => strip_of_mem_rectZerosXi (hZD u hu).1) (fun u hu => (hZD u hu).2) k
  have hZ3 : Z3g BPz2 H ≤ 210.6 := Z3g_H_le
  have hc3 : c3g 10 H ≤ 1.22e-9 := c3g_H_le
  have hc30 : 0 ≤ c3g 10 H := c3g_H_nonneg
  -- fiberwise
  set K := (Z.image idx).sup id + 1 with hK
  have hmaps : ∀ u ∈ Z, idx u ∈ range K := by
    intro u hu
    rw [Finset.mem_range, hK, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem idx hu)
  set f : ℕ → ℝ := fun k => 1 / (H + 4.4 * k) ^ 2 with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have hfle : ∀ k, f k ≤ 1 / H ^ 2 := fun k => by
    simp only [hf]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by
      have : (0 : ℝ) ≤ 4.4 * k := by positivity
      linarith) 2)
  calc ∑ u ∈ Z, (mult T u : ℝ) * ‖WH ℓ m T₀ u‖ ≤ ∑ u ∈ Z, (mult T u : ℝ) * (E * f (idx u) ^ 2) :=
        Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hpt u hu) (Nat.cast_nonneg _)
    _ = ∑ k ∈ range K, ∑ u ∈ Z.filter (fun u => idx u = k), (mult T u : ℝ) * (E * f (idx u) ^ 2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ range K, (E * f k ^ 2) * ∑ u ∈ Z.filter (fun u => idx u = k), (mult T u : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [(Finset.mem_filter.1 hu).2]; ring
    _ ≤ ∑ k ∈ range K, (E * f k ^ 2) * (421.2 + 2.44e-9 * (k + 1)) := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (hcnt k).trans ?_
        have : (0 : ℝ) ≤ k + 1 := by positivity
        nlinarith
    _ ≤ ∑ k ∈ range K, E * (421.2 / H ^ 2 + 2.44e-9 * (1 / (8.8 * H) + 1 / H ^ 2)) * f k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hHk : 0 < H + 4.4 * k := by positivity
        have hfk : f k * (H + 4.4 * k) ^ 2 = 1 := by simp only [hf]; field_simp
        have hk0 : (0 : ℝ) ≤ k := by positivity
        -- `f(k)² ≤ f(k)/H²` and `(k + 1) f(k)² ≤ (1/(8.8H) + 1/H²) f(k)`
        have h1 : f k ^ 2 ≤ (1 / H ^ 2) * f k := by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hfle k) (hf0 k)
        have h2 : ((k : ℝ) + 1) * f k ^ 2 ≤ (1 / (8.8 * H) + 1 / H ^ 2) * f k := by
          have hle : (k : ℝ) + 1 ≤ (1 / (8.8 * H) + 1 / H ^ 2) * (H + 4.4 * k) ^ 2 := by
            have hH0 : 0 < H := by norm_num
            have e : (1 / (8.8 * H) + 1 / H ^ 2) * (H + 4.4 * k) ^ 2 =
                (H + 4.4 * k) ^ 2 / (8.8 * H) + (H + 4.4 * k) ^ 2 / H ^ 2 := by ring
            rw [e]
            have a1 : (k : ℝ) ≤ (H + 4.4 * k) ^ 2 / (8.8 * H) := by
              rw [le_div_iff₀ (by positivity)]; nlinarith
            have a2 : (1 : ℝ) ≤ (H + 4.4 * k) ^ 2 / H ^ 2 := by
              rw [le_div_iff₀ (by positivity)]; nlinarith
            linarith
          calc ((k : ℝ) + 1) * f k ^ 2 = ((k : ℝ) + 1) * f k * f k := by ring
            _ ≤ ((1 / (8.8 * H) + 1 / H ^ 2) * (H + 4.4 * k) ^ 2) * f k * f k := by
                gcongr
            _ = (1 / (8.8 * H) + 1 / H ^ 2) * f k * (f k * (H + 4.4 * k) ^ 2) := by ring
            _ = (1 / (8.8 * H) + 1 / H ^ 2) * f k := by rw [hfk, mul_one]
        have hE0 : 0 ≤ E := by positivity
        calc E * f k ^ 2 * (421.2 + 2.44e-9 * ((k : ℝ) + 1)) =
            E * (421.2 * f k ^ 2 + 2.44e-9 * (((k : ℝ) + 1) * f k ^ 2)) := by ring
          _ ≤ E * (421.2 * ((1 / H ^ 2) * f k) + 2.44e-9 * ((1 / (8.8 * H) + 1 / H ^ 2) * f k)) := by
              gcongr
          _ = E * (421.2 / H ^ 2 + 2.44e-9 * (1 / (8.8 * H) + 1 / H ^ 2)) * f k := by ring
    _ = E * (421.2 / H ^ 2 + 2.44e-9 * (1 / (8.8 * H) + 1 / H ^ 2)) * ∑ k ∈ range K, f k := by
        rw [Finset.mul_sum]
    _ ≤ E * (421.2 / H ^ 2 + 2.44e-9 * (1 / (8.8 * H) + 1 / H ^ 2)) * (1 / H ^ 2 + 1 / (4.4 * H)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_lin_le (by norm_num) K) (by positivity)
    _ ≤ OffC ℓ m := by
        rw [hE, OffC, hH]
        have : (0 : ℝ) ≤ 4 ^ m * Real.exp (m * ℓ) := by positivity
        norm_num
        nlinarith

/-! ### One window -/

/-- The right-hand side of the Weil formula at `T₀`. -/
noncomputable def WPhi (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) : ℝ :=
  (WHt ℓ m T₀ 1 + (1 / (2 * π) : ℂ) *
    ∫ y : ℝ, archF (((1 / 2 : ℝ) : ℂ) + y * I) * WHt ℓ m T₀ (((1 / 2 : ℝ) : ℂ) + y * I)).re

/-- A zero of `ξ` in the strip with `|γ| ≤ 3·10¹⁰` is on the critical line. -/
theorem re_eq_half_of_mem_rectZerosXi {T : ℝ} {u : ℂ} (hu : u ∈ rectZerosXi T) (him : |u.im| ≤ 3e10) :
    u.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := strip_of_mem_rectZerosXi hu
  have hz : riemannZeta u = 0 := (xiF_eq_zero_iff h0 h1).1 (xiF_eq_zero_of_mem_rectZerosXi hu)
  exact rh_upto u hz h0 h1 him

theorem WH_re_nonneg_of_line (ℓ : ℝ) (m : ℕ) (T₀ : ℝ) {u : ℂ} (hu : u.re = 1 / 2) :
    0 ≤ (WH ℓ m T₀ u).re := by
  have e : u = 1 / 2 + (u.im : ℂ) * I := by
    apply Complex.ext <;> simp [hu]
  rw [e]; exact WH_line_re_nonneg ℓ m T₀ u.im

/-- **One window of the Weil formula**: `Σ_{|γ| ≤ 3·10¹⁰} m_ρ Re H_{T₀}(ρ) ≤ Φ(T₀) + Off`. -/
theorem weil_window {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) {T₀ : ℝ} (hT₀ : |T₀| ≤ 1.5e10) (T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ 3e10), (multRectD zetaF T u : ℝ) * (WH ℓ m T₀ u).re ≤
      WPhi ℓ m T₀ + OffC ℓ m := by
  set S := (zerosRectD zetaF T).filter (fun u => |u.im| ≤ 3e10) with hS
  set Z : ℕ → Finset ℂ := fun k => rectZerosXi (goodT k) with hZ
  have hlim := weil_formula hℓ0 hℓ1 hm h2 T₀
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hlimR : Tendsto (fun k : ℕ => (∑ u ∈ Z k, (mult (goodT k) u : ℂ) * WH ℓ m T₀ u).re) atTop
      (𝓝 (WPhi ℓ m T₀)) := by
    have hπ : (0 : ℝ) < 2 * π := by positivity
    have h := hre.div_const (2 * π)
    have hc : (2 : ℂ) * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    have hc' : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
    have e1 : ∀ X : ℂ, (2 * (π : ℂ) * X).re / (2 * π) = X.re := by
      intro X; rw [hc, Complex.re_ofReal_mul]; field_simp
    have e2 : ∀ X Y : ℂ, (2 * (π : ℂ) * X + Y).re / (2 * π) = (X + (1 / (2 * π) : ℂ) * Y).re := by
      intro X Y
      rw [Complex.add_re, Complex.add_re, hc', Complex.re_ofReal_mul, hc, Complex.re_ofReal_mul]
      field_simp
    simp only [Function.comp_def, e1, e2] at h
    exact h
  refine ge_of_tendsto (hlimR.add_const (OffC ℓ m)) ?_
  filter_upwards [eventually_ge_atTop (⌈max T 3e10⌉₊ + 1)] with k hk
  set T' := goodT k with hT'
  have hkT : max T 3e10 + 1 ≤ (k : ℝ) := by
    have := Nat.le_ceil (max T 3e10)
    have : ((⌈max T 3e10⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this; linarith
  have hT'k : (k : ℝ) ≤ T' := (goodT_mem k).1
  have hT'1 : 1 ≤ T' := by linarith [le_max_right T 3e10]
  have hT'3 : 3e10 < T' := by linarith [le_max_right T 3e10]
  -- `S` sits inside the on-line part of `Z k`, with the same multiplicities
  have hmemS : ∀ u ∈ S, u ∈ zerosRectD zetaF T ∧ |u.im| ≤ 3e10 := fun u hu => Finset.mem_filter.1 hu
  have hstrip : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu => by
    obtain ⟨-, h0, h1, -⟩ := zerosRectD_zetaF_strip (hmemS u hu).1; exact ⟨h0, h1⟩
  have himT : ∀ u ∈ S, |u.im| < T := by
    intro u hu
    have h := (hmemS u hu).1
    rw [zerosRectD, Finset.mem_filter] at h
    obtain ⟨-, -, -, h3, h4⟩ := h
    rw [zT_im] at h3; rw [wT_im] at h4
    exact abs_lt.2 ⟨h3, h4⟩
  have hsub : S ⊆ (Z k).filter (fun u => |u.im| ≤ 3e10) := by
    intro u hu
    refine Finset.mem_filter.2 ⟨mem_rectZerosXi_of_mem hT'1 (hmemS u hu).1 (hstrip u hu).1
      (hstrip u hu).2 (by linarith [(hmemS u hu).2]), (hmemS u hu).2⟩
  have hmul : ∀ u ∈ S, (multRectD zetaF T u : ℝ) = mult T' u := fun u hu => by
    exact_mod_cast multRectD_eq_mult hT'1 (hstrip u hu).1 (hstrip u hu).2 (himT u hu)
      (by linarith [(hmemS u hu).2])
  -- real parts
  have hre_sum : (∑ u ∈ Z k, (mult T' u : ℂ) * WH ℓ m T₀ u).re =
      ∑ u ∈ Z k, (mult T' u : ℝ) * (WH ℓ m T₀ u).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [Complex.mul_re]
  rw [hre_sum, ← Finset.sum_filter_add_sum_filter_not (Z k) (fun u => |u.im| ≤ 3e10)]
  have hon : ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (WH ℓ m T₀ u).re ≤
      ∑ u ∈ (Z k).filter (fun u => |u.im| ≤ 3e10), (mult T' u : ℝ) * (WH ℓ m T₀ u).re := by
    rw [Finset.sum_congr rfl fun u hu => by rw [hmul u hu]]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun u hu _ => ?_
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    exact mul_nonneg (Nat.cast_nonneg _) (WH_re_nonneg_of_line ℓ m T₀ (re_eq_half_of_mem_rectZerosXi hu1 hu2))
  have hoff := off_line_le hℓ0 hℓ1 hm hT₀ hT'1
  have hoff' : -(OffC ℓ m) ≤ ∑ u ∈ (Z k).filter (fun u => ¬ |u.im| ≤ 3e10), (mult T' u : ℝ) * (WH ℓ m T₀ u).re := by
    have : ∑ u ∈ (Z k).filter (fun u => ¬ |u.im| ≤ 3e10), -((mult T' u : ℝ) * ‖WH ℓ m T₀ u‖) ≤
        ∑ u ∈ (Z k).filter (fun u => ¬ |u.im| ≤ 3e10), (mult T' u : ℝ) * (WH ℓ m T₀ u).re :=
      Finset.sum_le_sum fun u _ => by
        have h1 : -‖WH ℓ m T₀ u‖ ≤ (WH ℓ m T₀ u).re := by
          have := Complex.abs_re_le_norm (WH ℓ m T₀ u); linarith [neg_abs_le (WH ℓ m T₀ u).re]
        have h0 : (0 : ℝ) ≤ mult T' u := Nat.cast_nonneg _
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left h1 h0
    rw [Finset.sum_neg_distrib] at this
    linarith
  linarith

end TernaryGoldbach.Explicit
