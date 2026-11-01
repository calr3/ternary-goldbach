import TernaryGoldbach.Explicit.PsiPlateau

/-!
# The explicit bound for large `x`: zeros above `H` via the zero-free region

Zeros with `H < |γ| ≤ Γ` have `x^β ≤ x·e^{−log x/(11 log Γ)}` (`zero_free`); those above `Γ` are killed by the
Gaussian (`tail_sum_gauss` anchored at `Γ`).
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- The window count for zeros in `(H, Γ]`. -/
theorem count_mid {T H Γ : ℝ} (hH : 0 < H) (S : Finset ℂ) (hS : S ⊆ zerosRectD zetaF T)
    (him : ∀ u ∈ S, H < |u.im| ∧ |u.im| ≤ Γ) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) ≤
      (⌊(Γ - H) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 H + 2 * c3g 10 H * (⌊(Γ - H) / 4.4⌋₊ + 1)) := by
  set idx : ℂ → ℕ := fun u => ⌊(|u.im| - H) / 4.4⌋₊ with hidx
  set K := ⌊(Γ - H) / 4.4⌋₊ with hK
  have hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu =>
    ⟨(zerosRectD_zetaF_strip (hS hu)).2.1, (zerosRectD_zetaF_strip (hS hu)).2.2.1⟩
  have hmaps : ∀ u ∈ S, idx u ∈ Finset.range (K + 1) := by
    intro u hu
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_mono (div_le_div_of_nonneg_right (by linarith [(him u hu).2]) (by norm_num))
  have hc0 : 0 ≤ c3g 10 H := by
    unfold c3g; exact div_nonneg (by positivity) (log_ratio_pos (by norm_num) (by norm_num)).le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.range (K + 1), ∑ u ∈ S.filter (fun u => idx u = k), (multRectD zetaF T u : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (2 * Z3g BPz2 H + 2 * c3g 10 H * (k + 1)) :=
        Finset.sum_le_sum fun k _ => count_tail_windowG polyDatum_zeta2 hH S hS hre
          (fun u hu => (him u hu).1) k
    _ ≤ ∑ k ∈ Finset.range (K + 1), (2 * Z3g BPz2 H + 2 * c3g 10 H * (K + 1)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        nlinarith
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- `x^β ≤ x e^{−log x/(11 log Γ)}` for zeros with `10⁹ ≤ |γ| ≤ Γ`. -/
theorem rpow_re_le_zf {x Γ : ℝ} (hx : 1 < x) {u : ℂ} (hu : xiF u = 0) (h1 : 1e9 ≤ |u.im|) (h2 : |u.im| ≤ Γ) :
    x ^ u.re ≤ x * Real.exp (-(Real.log x / (11 * Real.log Γ))) := by
  have hzf := zero_free hu h1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlg : 0 < Real.log |u.im| := Real.log_pos (by linarith)
  have hlΓ : Real.log |u.im| ≤ Real.log Γ := Real.log_le_log (by linarith) h2
  have hle : x ^ u.re ≤ x ^ (1 - 1 / (11 * Real.log |u.im|)) := Real.rpow_le_rpow_of_exponent_le hx.le hzf
  have e : x ^ (1 - 1 / (11 * Real.log |u.im|)) = x * Real.exp (-(Real.log x / (11 * Real.log |u.im|))) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, div_eq_mul_inv x, ← Real.exp_neg]
    congr 2; ring
  rw [e] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0.le)
  apply neg_le_neg
  apply div_le_div_of_nonneg_left hlx.le (by positivity)
  linarith

/-- The Gaussian tail anchored at `Γ`. -/
noncomputable def TailBG (a δ Γ : ℝ) : ℝ :=
  EBg a δ Γ * (2 * Z3g BPz2 Γ / (1 - rhoG δ Γ) + 2 * c3g 10 Γ / (1 - rhoG δ Γ) ^ 2)

/-- The zeros in `(H, Γ]`, with the zero-free region. -/
noncomputable def MidB (a δ Γ x : ℝ) : ℝ :=
  2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log Γ))) *
    ((⌊(Γ - 3e12) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 3e12 + 2 * c3g 10 3e12 * (⌊(Γ - 3e12) / 4.4⌋₊ + 1)))

/-- **The explicit-formula bound with the zero-free region.** -/
theorem SsumG_gsm_err_zf {a b δ x Γ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x)
    (hΓ : 3e12 ≤ Γ) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * LineB a δ + x * MidB a δ Γ x + x * TailBG a δ Γ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineB a δ + x * MidB a δ Γ x + x * TailBG a δ Γ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ 3e12),
      ← Finset.sum_filter_add_sum_filter_not (Z.filter fun u => ¬ |u.im| ≤ 3e12) (fun u => |u.im| ≤ Γ)]
    rw [add_assoc]
    refine add_le_add ?_ (add_le_add ?_ ?_)
    · -- the line zeros (as in `SsumG_gsm_err`)
      set S := Z.filter (fun u => |u.im| ≤ 3e12) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact rh_upto u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ 3e12 := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_le (by norm_num) S hSZ hre him (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _)
        (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le (δ := δ) hab hb u.im
      simpa using this
    · -- zeros in `(H, Γ]`
      set S := (Z.filter fun u => ¬ |u.im| ≤ 3e12).filter (fun u => |u.im| ≤ Γ) with hS
      have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have him : ∀ u ∈ S, 3e12 < |u.im| ∧ |u.im| ≤ Γ := fun u hu =>
        ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
      have hcount := count_mid (by norm_num) S hSZ him
      have hpt : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
          m u * (2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x) := by
        intro u hu
        obtain ⟨hz, hr1, hr2, hxi⟩ := zerosRectD_zetaF_strip (hSZ hu)
        obtain ⟨hH, hG⟩ := him u hu
        have hγ0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hH; linarith
        have hMs := norm_Mg_strip_le (a := a) (δ := δ) hb hr1 hr2 hγ0
        have hγ : 0 < |u.im| := abs_pos.2 hγ0
        have hMb : ‖Mg a b δ u‖ ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 := by
          have hg1 : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have := sq_nonneg (δ * u.im); nlinarith)
          have : ‖Mg a b δ u‖ * |u.im| ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) := by
            have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0:ℝ) ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|))
            linarith
          rw [le_div_iff₀ (by norm_num)]
          calc ‖Mg a b δ u‖ * 3e12 ≤ ‖Mg a b δ u‖ * |u.im| := mul_le_mul_of_nonneg_left hH.le (norm_nonneg _)
            _ ≤ _ := this
        have hxr := rpow_re_le_zf hx hxi (by linarith) hG
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖Mg a b δ u‖ * x ^ u.re ≤ (2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12) *
            (x * Real.exp (-(Real.log x / (11 * Real.log Γ)))) :=
              mul_le_mul hMb hxr (by positivity) (by positivity)
          _ = _ := by ring
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [← Finset.sum_mul]
      unfold MidB
      have hC0 : 0 ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x := by
        positivity
      calc (∑ u ∈ S, m u) * (2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x)
          ≤ ((⌊(Γ - 3e12) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 3e12 + 2 * c3g 10 3e12 * (⌊(Γ - 3e12) / 4.4⌋₊ + 1))) *
            (2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x) :=
            mul_le_mul_of_nonneg_right hcount hC0
        _ = _ := by ring
    · -- zeros above `Γ`
      set S := (Z.filter fun u => ¬ |u.im| ≤ 3e12).filter (fun u => ¬ |u.im| ≤ Γ) with hS
      have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have him : ∀ u ∈ S, Γ < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by linarith) hδ hb hx.le S hSZ him
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineB a δ + x * MidB a δ Γ x + x * TailBG a δ Γ :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hbound (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_gsm hδ hab hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) φ x - Mg a b δ 1 * x =
      -((mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by rw [hM]; ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end TernaryGoldbach.Explicit
