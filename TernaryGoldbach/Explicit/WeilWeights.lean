import TernaryGoldbach.Explicit.WeilWindow


/-!
# Weighted zero sums from the windows

For a weight `g ≥ 0`, nonincreasing on `[0, ∞)`, and `R > 0`, with `B_R = ∫_{−R}^{R} B(u)² du`:
`g(|γ|) B_R ≤ ∫_{γ−R}^{γ+R} g(max(0, |t| − R)) B(γ − t)² dt`. Summing over the on-line zeros
`|γ| ≤ Y₁` and using one window per `t` (`weil_windowH`, given `RHBelow H`), for any continuous
`Φ⁺ ≥ Φ + Off` on `|t| ≤ H/2` (`weil_weightedH`):
`Σ_{|γ| ≤ Y₁} m_ρ g(|γ|) ≤ B_R⁻¹ ∫_{−(Y₁+R)}^{Y₁+R} g(max(0, |t| − R)) Φ⁺(t) dt`.
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-- `B(y)²` on the real line. -/
noncomputable def Bsq (ℓ : ℝ) (m : ℕ) (y : ℝ) : ℝ := (WB ℓ m (y : ℂ)).re ^ 2

theorem Bsq_nonneg (ℓ : ℝ) (m : ℕ) (y : ℝ) : 0 ≤ Bsq ℓ m y := sq_nonneg _

theorem continuous_Bsq (ℓ : ℝ) (m : ℕ) : Continuous (Bsq ℓ m) := by
  unfold Bsq
  exact (Complex.continuous_re.comp ((differentiable_WB ℓ m).continuous.comp
    Complex.continuous_ofReal)).pow 2

/-- On the line, `Re H_t(½ + iγ) = B(γ − t)²`. -/
theorem WH_re_line_eq (ℓ : ℝ) (m : ℕ) (t : ℝ) {u : ℂ} (hu : u.re = 1 / 2) :
    (WH ℓ m t u).re = Bsq ℓ m (u.im - t) := by
  have e : u = 1 / 2 + (u.im : ℂ) * I := by apply Complex.ext <;> simp [hu]
  rw [e, WH_line, Bsq, sq, Complex.mul_re, WB_ofReal_im]
  simp only [mul_zero, sub_zero]
  rw [sq]; congr 3 <;> simp

/-- `∫_{γ−R}^{γ+R} B(γ − t)² dt = ∫_{−R}^{R} B²`. -/
theorem integral_Bsq_shift (ℓ : ℝ) (m : ℕ) (γ R : ℝ) :
    ∫ t in (γ - R)..(γ + R), Bsq ℓ m (γ - t) = ∫ u in (-R)..R, Bsq ℓ m u := by
  have h := intervalIntegral.integral_comp_sub_left (fun u => Bsq ℓ m u) (a := γ - R) (b := γ + R) γ
  rw [h, show γ - (γ + R) = -R by ring, show γ - (γ - R) = R by ring]

/-- **The weighted zero sum** under RH up to `H ∈ [10⁸, 3·10¹⁰]`, for the line zeros `|γ| ≤ Y₁` with
`Y₁ + R ≤ H/2`. -/
theorem weil_weightedH {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 2 ≤ m)
    (h2 : Real.exp (2 * m * ℓ) < 2) {H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10)
    {R : ℝ} (hR : 0 < R) (hY₁0 : 0 ≤ Y₁) (hY₁ : Y₁ + R ≤ H / 2)
    {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hganti : AntitoneOn g (Ici 0)) (hgc : Continuous g)
    (hK : 0 < ∫ u in (-R)..R, Bsq ℓ m u)
    {Φ : ℝ → ℝ} (hΦc : Continuous Φ) (hΦ : ∀ t, |t| ≤ H / 2 → WPhi ℓ m t + OffC ℓ m ≤ Φ t) (T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ Y₁), (multRectD zetaF T u : ℝ) * g |u.im| ≤
      (∫ t in (-(Y₁ + R))..(Y₁ + R), g (max 0 (|t| - R)) * Φ t) / ∫ u in (-R)..R, Bsq ℓ m u := by
  set S := (zerosRectD zetaF T).filter (fun u => |u.im| ≤ Y₁) with hS
  set KR := ∫ u in (-R)..R, Bsq ℓ m u with hKR
  set Y := Y₁ + R with hY
  set G : ℝ → ℝ := fun t => g (max 0 (|t| - R)) with hG
  have hGc : Continuous G := hgc.comp (continuous_const.max (continuous_abs.sub continuous_const))
  have hG0 : ∀ t, 0 ≤ G t := fun t => hg0 _
  have hmemS : ∀ u ∈ S, u ∈ zerosRectD zetaF T ∧ |u.im| ≤ Y₁ := fun u hu => Finset.mem_filter.1 hu
  have hline : ∀ u ∈ S, u.re = 1 / 2 := by
    intro u hu
    obtain ⟨hz, h0, h1, -⟩ := zerosRectD_zetaF_strip (hmemS u hu).1
    exact hRH u hz h0 h1 (by linarith [(hmemS u hu).2])
  -- (1) `g(|γ|) K_R ≤ ∫_{−Y}^{Y} G(t) B(γ − t)² dt`
  have hpt : ∀ u ∈ S, g |u.im| * KR ≤ ∫ t in (-Y)..Y, G t * Bsq ℓ m (u.im - t) := by
    intro u hu
    set γ := u.im with hγ
    have hγY : |γ| ≤ Y₁ := (hmemS u hu).2
    have hcont : Continuous fun t => G t * Bsq ℓ m (γ - t) :=
      hGc.mul ((continuous_Bsq ℓ m).comp (continuous_const.sub continuous_id))
    have hsub : ∫ t in (γ - R)..(γ + R), G t * Bsq ℓ m (γ - t) ≤ ∫ t in (-Y)..Y, G t * Bsq ℓ m (γ - t) := by
      have h1 : -Y ≤ γ - R := by rw [abs_le] at hγY; linarith [hγY.1]
      have h2 : γ + R ≤ Y := by rw [abs_le] at hγY; linarith [hγY.2]
      exact intervalIntegral.integral_mono_interval h1 (by linarith) h2
        (Eventually.of_forall fun t => mul_nonneg (hG0 t) (Bsq_nonneg ℓ m _)) (hcont.intervalIntegrable _ _)
    refine le_trans ?_ hsub
    rw [hKR, ← integral_Bsq_shift ℓ m γ R, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) ((continuous_const.mul
      ((continuous_Bsq ℓ m).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun t ht => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Bsq_nonneg ℓ m _)
    -- `max(0, |t| − R) ≤ |γ|`, so `G(t) ≥ g(|γ|)`
    have hle : max 0 (|t| - R) ≤ |γ| := by
      refine max_le (abs_nonneg _) ?_
      have := abs_sub_abs_le_abs_sub t γ
      have : |t - γ| ≤ R := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      linarith
    exact hganti (le_max_left _ _ : (0 : ℝ) ≤ max 0 (|t| - R)) (abs_nonneg γ) hle
  -- (2) sum and swap
  have hsum : (∑ u ∈ S, (multRectD zetaF T u : ℝ) * g |u.im|) * KR ≤
      ∫ t in (-Y)..Y, G t * ∑ u ∈ S, (multRectD zetaF T u : ℝ) * Bsq ℓ m (u.im - t) := by
    rw [Finset.sum_mul]
    have hint : ∀ u ∈ S, IntervalIntegrable (fun t => (multRectD zetaF T u : ℝ) * (G t * Bsq ℓ m (u.im - t)))
        volume (-Y) Y := fun u _ => (continuous_const.mul (hGc.mul ((continuous_Bsq ℓ m).comp
          (continuous_const.sub continuous_id)))).intervalIntegrable _ _
    calc ∑ u ∈ S, (multRectD zetaF T u : ℝ) * g |u.im| * KR ≤
        ∑ u ∈ S, (multRectD zetaF T u : ℝ) * ∫ t in (-Y)..Y, G t * Bsq ℓ m (u.im - t) :=
          Finset.sum_le_sum fun u hu => by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hpt u hu) (Nat.cast_nonneg _)
      _ = ∫ t in (-Y)..Y, ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (G t * Bsq ℓ m (u.im - t)) := by
          rw [intervalIntegral.integral_finsetSum hint]
          exact Finset.sum_congr rfl fun u _ => (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ t in (-Y)..Y, G t * ∑ u ∈ S, (multRectD zetaF T u : ℝ) * Bsq ℓ m (u.im - t) := by
          congr 1; ext t; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
  -- (3) one window per `t`
  have hwin : ∀ t ∈ Icc (-Y) Y, ∑ u ∈ S, (multRectD zetaF T u : ℝ) * Bsq ℓ m (u.im - t) ≤ Φ t := by
    intro t ht
    have htY : |t| ≤ H / 2 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hw := weil_windowH hℓ0 hℓ1 hm h2 hRH hH1 hH2 htY T
    refine le_trans ?_ (hw.trans (hΦ t htY))
    have hsub : S ⊆ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ H) := by
      intro u hu
      exact Finset.mem_filter.2 ⟨(hmemS u hu).1, by linarith [(hmemS u hu).2]⟩
    calc ∑ u ∈ S, (multRectD zetaF T u : ℝ) * Bsq ℓ m (u.im - t) =
        ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (WH ℓ m t u).re :=
          Finset.sum_congr rfl fun u hu => by rw [WH_re_line_eq ℓ m t (hline u hu)]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun u hu _ => ?_
          obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
          obtain ⟨hz, h0, h1, -⟩ := zerosRectD_zetaF_strip hu1
          exact mul_nonneg (Nat.cast_nonneg _)
            (WH_re_nonneg_of_line ℓ m t (hRH u hz h0 h1 hu2))
  have hmono : ∫ t in (-Y)..Y, G t * ∑ u ∈ S, (multRectD zetaF T u : ℝ) * Bsq ℓ m (u.im - t) ≤
      ∫ t in (-Y)..Y, G t * Φ t := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ((hGc.mul hΦc).intervalIntegrable _ _)
      fun t ht => mul_le_mul_of_nonneg_left (hwin t ht) (hG0 t)
    exact (hGc.mul (continuous_finsetSum _ fun u _ => continuous_const.mul
      ((continuous_Bsq ℓ m).comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
  rw [le_div_iff₀ hK]
  exact hsum.trans hmono

end TernaryGoldbach.Explicit
