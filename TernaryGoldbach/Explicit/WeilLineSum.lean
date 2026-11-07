import TernaryGoldbach.Explicit.WeilPhiBound
import TernaryGoldbach.Explicit.ZetaLowZeroFree

/-!
# The line zeros of the explicit formula for `ψ`, by the Weil formula

On the critical line `‖Mg(½ + iγ)‖ ≤ C e^{−δ²γ²/2}/|γ|` with `C = e^{δ²/8}(e^{a/2} + e^{b/2})`
(`norm_Mg_line_gauss`). Given `RHBelow H`, every zero has `|γ| ≥ t₀ = 2.39` (`abs_im_ge_of_zeroH`),
so with the nonincreasing weight `ĝ(u) = e^{−δ² max(u,t₀)²/2}/max(u, t₀)` and `weil_weightedH`,
`WPhi_le_PhiUp`: `Σ_{|γ| ≤ Y₁} m_ρ ‖Mg(ρ)‖ ≤ C · B_R⁻¹ ∫_{|t| ≤ Y₁+R} ĝ(max(0, |t| − R)) Φ⁺(t) dt`
(`line_sum_weilH`).
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-- `‖Mg(½ + iγ)‖ ≤ e^{δ²/8}(e^{a/2} + e^{b/2}) e^{−δ²γ²/2}/|γ|`. -/
theorem norm_Mg_line_gauss (a b δ : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ‖Mg a b δ (((1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) * Real.exp (-(δ ^ 2 * y ^ 2 / 2)) / |y| := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hs] at this
  have hg : ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ = Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 * y ^ 2 / 2)) := by
    rw [norm_cexp_gauss, hsre, hsim, ← Real.exp_add]; congr 1; ring
  have h1 := norm_intExp_le' (a := a) (b := b) hs0
  rw [hsre] at h1
  have hsn : |y| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; rwa [hsim] at this
  have hy0 : 0 < |y| := abs_pos.2 hy
  have h2 : ‖∫ w in b..a, cexp (s * w)‖ ≤ (Real.exp (a / 2) + Real.exp (b / 2)) / |y| := by
    refine h1.trans ?_
    rw [mul_one_div, mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) hy0 hsn
  rw [Mg, norm_mul, hg]
  calc Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 * y ^ 2 / 2)) * ‖∫ w in b..a, cexp (s * w)‖ ≤
      Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 * y ^ 2 / 2)) * ((Real.exp (a / 2) + Real.exp (b / 2)) / |y|) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The weight `ĝ(u) = e^{−δ² max(u,t₀)²/2}/max(u, t₀)`. -/
noncomputable def gW (δ t₀ : ℝ) (u : ℝ) : ℝ := Real.exp (-(δ ^ 2 * max u t₀ ^ 2 / 2)) / max u t₀

theorem gW_nonneg (δ : ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) (u : ℝ) : 0 ≤ gW δ t₀ u := by
  unfold gW
  have : 0 < max u t₀ := lt_of_lt_of_le ht₀ (le_max_right _ _)
  positivity

theorem continuous_gW (δ : ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) : Continuous (gW δ t₀) := by
  unfold gW
  refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
  exact (lt_of_lt_of_le ht₀ (le_max_right _ _)).ne'

theorem antitoneOn_gW (δ : ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) : AntitoneOn (gW δ t₀) (Ici 0) := by
  intro u _ v _ huv
  unfold gW
  have hm : max u t₀ ≤ max v t₀ := max_le_max huv le_rfl
  have hu0 : 0 < max u t₀ := lt_of_lt_of_le ht₀ (le_max_right _ _)
  have hsq : max u t₀ ^ 2 ≤ max v t₀ ^ 2 := pow_le_pow_left₀ hu0.le hm 2
  have he : Real.exp (-(δ ^ 2 * max v t₀ ^ 2 / 2)) ≤ Real.exp (-(δ ^ 2 * max u t₀ ^ 2 / 2)) := by
    apply Real.exp_le_exp.2
    have : δ ^ 2 * max u t₀ ^ 2 ≤ δ ^ 2 * max v t₀ ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg δ)
    linarith
  calc Real.exp (-(δ ^ 2 * max v t₀ ^ 2 / 2)) / max v t₀ ≤ Real.exp (-(δ ^ 2 * max u t₀ ^ 2 / 2)) / max v t₀ :=
        div_le_div_of_nonneg_right he (by linarith)
    _ ≤ Real.exp (-(δ ^ 2 * max u t₀ ^ 2 / 2)) / max u t₀ :=
        div_le_div_of_nonneg_left (by positivity) hu0 hm

/-- The line zeros `|γ| ≤ Y₁` by `weil_weightedH`, under RH up to `H ∈ [10⁸, 3·10¹⁰]`, `Y₁ + R ≤ H/2`. -/
theorem line_sum_weilH {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) {N : ℕ} (hN : 3 ≤ N) {H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H)
    (hH2 : H ≤ 3e10) {R : ℝ} (hR : 1 ≤ R) (hY₁0 : 0 ≤ Y₁) (hY₁ : Y₁ + R ≤ H / 2)
    (hK : 0 < KRB ℓ m R) (a b δ : ℝ) (T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ Y₁), (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) *
        ((∫ t in (-(Y₁ + R))..(Y₁ + R), gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ m N R t) / KRB ℓ m R) := by
  set C := Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) with hC
  have hC0 : 0 ≤ C := by positivity
  have ht₀ : (0 : ℝ) < 2.39 := by norm_num
  have hW := weil_weightedH hℓ0 hℓ1 hm h2 hRH hH1 hH2 (R := R) (by linarith) hY₁0 hY₁ (gW_nonneg δ ht₀)
    (antitoneOn_gW δ ht₀) (continuous_gW δ ht₀) hK (continuous_PhiUp ℓ m N R)
    (fun t _ => WPhi_le_PhiUp hℓ0 hℓ1 hm hN hR t) T
  rw [KRB]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hW hC0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
  obtain ⟨hz, h0, h1, -⟩ := zerosRectD_zetaF_strip hu1
  have hre := hRH u hz h0 h1 (by linarith)
  have hγ := abs_im_ge_of_zeroH hRH (by linarith) hz h0 h1
  have hy0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hγ; norm_num at hγ
  have e : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
  have hM := norm_Mg_line_gauss a b δ hy0
  rw [← e] at hM
  have hg : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) / |u.im| = gW δ 2.39 |u.im| := by
    unfold gW; rw [max_eq_left hγ, sq_abs]
  calc (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤ (multRectD zetaF T u : ℝ) * (C * gW δ 2.39 |u.im|) := by
        refine mul_le_mul_of_nonneg_left (hM.trans (le_of_eq ?_)) (Nat.cast_nonneg _)
        rw [hC, ← hg]; ring
    _ = C * ((multRectD zetaF T u : ℝ) * gW δ 2.39 |u.im|) := by ring

/-- The Jensen-window constant of `LineB2H` at height `H`. -/
noncomputable def LWH (H : ℝ) : ℝ :=
  2 * ∑ m ∈ Finset.range (JlH 6 H), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
    Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ)))

/-- **The line zeros with `Y₁ < |γ| ≤ H`** under RH up to `H`: Jensen windows, with the Gaussian factor. -/
theorem line_sum_midH {H Y₁ : ℝ} (hRH : RHBelow H) (hH : 0 ≤ H) (hY₁ : 1 / 2 ≤ Y₁) (a b δ T : ℝ) :
    ∑ u ∈ ((zerosRectD zetaF T).filter (fun u => |u.im| ≤ H)).filter (fun u => ¬ |u.im| ≤ Y₁),
        (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) * Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) *
        LWH H := by
  set S := ((zerosRectD zetaF T).filter (fun u => |u.im| ≤ H)).filter (fun u => ¬ |u.im| ≤ Y₁) with hS
  have hSZ : S ⊆ zerosRectD zetaF T := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmem : ∀ u ∈ S, |u.im| ≤ H ∧ Y₁ < |u.im| := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    exact ⟨(Finset.mem_filter.1 hu1).2, not_le.1 hu2⟩
  have hre : ∀ u ∈ S, u.re = 1 / 2 := by
    intro u hu
    obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip (hSZ hu)
    exact hRH u hz hr1 hr2 (hmem u hu).1
  rw [LWH]
  refine line_sum_leH (H := H) (h := 6) (r := 3.36) hH (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) S hSZ hre (fun u hu => (hmem u hu).1) (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _)
    (by positivity) (fun u hu => ?_)
  obtain ⟨-, hγ⟩ := hmem u hu
  have hy0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hγ; linarith
  have e : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by apply Complex.ext <;> simp [hre u hu]
  have hM := norm_Mg_line_gauss a b δ hy0
  rw [← e] at hM
  have hpos : 0 < |u.im| := by linarith
  rw [max_eq_right (by linarith)]
  have hg : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) ≤ Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) := by
    apply Real.exp_le_exp.2
    have : Y₁ ^ 2 ≤ u.im ^ 2 := by
      rw [← sq_abs u.im]; exact pow_le_pow_left₀ (by linarith) hγ.le 2
    have := mul_le_mul_of_nonneg_left this (sq_nonneg δ)
    linarith
  calc ‖Mg a b δ u‖ * |u.im| ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) * Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) / |u.im| *
        |u.im| := mul_le_mul_of_nonneg_right hM hpos.le
    _ = Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) * Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) := by
        field_simp
    _ ≤ _ := by gcongr

/-- **All line zeros `|γ| ≤ H`** under RH up to `H ∈ [10⁸, 3·10¹⁰]`: `weil_weightedH` below `Y₁`
(`Y₁ + R ≤ H/2`), Jensen windows above. -/
theorem line_sum_weil_allH {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) {N : ℕ} (hN : 3 ≤ N) {H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H)
    (hH2 : H ≤ 3e10) {R : ℝ} (hR : 1 ≤ R) (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + R ≤ H / 2)
    (hK : 0 < KRB ℓ m R) (a b δ : ℝ) (T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ H), (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) *
        ((∫ t in (-(Y₁ + R))..(Y₁ + R), gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ m N R t) / KRB ℓ m R +
          Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u => |u.im| ≤ Y₁)]
  have e : ((zerosRectD zetaF T).filter (fun u => |u.im| ≤ H)).filter (fun u => |u.im| ≤ Y₁) =
      (zerosRectD zetaF T).filter (fun u => |u.im| ≤ Y₁) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨h.trans (by linarith), h⟩⟩
  rw [e, mul_add]
  refine add_le_add (line_sum_weilH hℓ0 hℓ1 hm h2 hN hRH hH1 hH2 hR (by linarith) hY₁ hK a b δ T) ?_
  rw [← mul_assoc]
  exact line_sum_midH hRH (by linarith) hY₁0 a b δ T

end TernaryGoldbach.Explicit
