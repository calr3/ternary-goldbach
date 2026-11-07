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

/-- `x^β ≤ x e^{−log x/(11 log Γ)}` for zeros with `10⁸ ≤ |γ| ≤ Γ`. -/
theorem rpow_re_le_zf {x Γ : ℝ} (hx : 1 < x) {u : ℂ} (hu : xiF u = 0) (h1 : 1e8 ≤ |u.im|) (h2 : |u.im| ≤ Γ) :
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

/-- The zeros in `(H₁, Γ]`, with the zero-free region. -/
noncomputable def MidB0 (a δ H₁ Γ x : ℝ) : ℝ :=
  2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (11 * Real.log Γ))) *
    ((⌊(Γ - H₁) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 H₁ + 2 * c3g 10 H₁ * (⌊(Γ - H₁) / 4.4⌋₊ + 1)))

/-- The zeros in `(H, Γ]` (`H = 3·10¹⁰`), in two ranges: `(H, 3·10¹²]` and `(3·10¹², Γ]`. (One range
anchored at `H` would count the zeros near `Γ` with `log B(H) + 10 (Γ − H)/H`, far too crudely.) -/
noncomputable def MidB (a δ Γ x : ℝ) : ℝ := MidB0 a δ 3e10 3e12 x + MidB0 a δ 3e12 Γ x

/-- `LineB` with the line zeros `|γ| ≤ H`. -/
noncomputable def LineBH (a δ H : ℝ) : ℝ :=
  ZLg BPz2 H * (2 * Real.exp (δ ^ 2 / 2 + |a|)) * (4 * (1 + (1 + Real.log (Jl H)) / 3.48))

/-- `MidB` for the zeros in `(H, Γ]`: `(H, 3·10¹²]` and `(3·10¹², Γ]`. -/
noncomputable def MidBH (a δ H Γ x : ℝ) : ℝ := MidB0 a δ H 3e12 x + MidB0 a δ 3e12 Γ x

/-- The zero-free-region estimate for the zeros with `H₁ < |γ| ≤ Γ`, `H₁ ≥ 10⁸`. -/
theorem mid_sum_le {a b δ x H₁ Γ T : ℝ} (hb : b ≤ 0) (hx : 1 < x) (hH₁ : 1e8 ≤ H₁) (S : Finset ℂ)
    (hS : S ⊆ zerosRectD zetaF T) (him : ∀ u ∈ S, H₁ < |u.im| ∧ |u.im| ≤ Γ) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (‖Mg a b δ u‖ * x ^ u.re) ≤ x * MidB0 a δ H₁ Γ x := by
  have hH0 : 0 < H₁ := by linarith
  set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
  have hcount := count_mid hH0 S hS him
  have hpt : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
      m u * (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x) := by
    intro u hu
    obtain ⟨hz, hr1, hr2, hxi⟩ := zerosRectD_zetaF_strip (hS hu)
    obtain ⟨hH, hG⟩ := him u hu
    have hγ0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hH; linarith
    have hMs := norm_Mg_strip_le (a := a) (δ := δ) hb hr1 hr2 hγ0
    have hγ : 0 < |u.im| := abs_pos.2 hγ0
    have hMb : ‖Mg a b δ u‖ ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ := by
      have hg1 : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have := sq_nonneg (δ * u.im); nlinarith)
      have : ‖Mg a b δ u‖ * |u.im| ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) := by
        have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0:ℝ) ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|))
        linarith
      rw [le_div_iff₀ hH0]
      calc ‖Mg a b δ u‖ * H₁ ≤ ‖Mg a b δ u‖ * |u.im| := mul_le_mul_of_nonneg_left hH.le (norm_nonneg _)
        _ ≤ _ := this
    have hxr := rpow_re_le_zf hx hxi (by linarith) hG
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖Mg a b δ u‖ * x ^ u.re ≤ (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁) *
        (x * Real.exp (-(Real.log x / (11 * Real.log Γ)))) :=
          mul_le_mul hMb hxr (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_mul]
  unfold MidB0
  have hC0 : 0 ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x := by
    positivity
  calc (∑ u ∈ S, m u) * (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x)
      ≤ ((⌊(Γ - H₁) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 H₁ + 2 * c3g 10 H₁ * (⌊(Γ - H₁) / 4.4⌋₊ + 1))) *
        (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (11 * Real.log Γ))) * x) :=
        mul_le_mul_of_nonneg_right hcount hC0
    _ = _ := by ring

/-- **The explicit-formula bound with the zero-free region**, under RH up to `H ∈ [10⁸, 3·10¹²]`. -/
theorem SsumG_gsm_err_zfH {a b δ x Γ H : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e12)
    (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x) (hΓ : 3e12 ≤ Γ) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * LineBH a δ H + x * MidBH a δ H Γ x + x * TailBG a δ Γ +
        x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineBH a δ H + x * MidBH a δ H Γ x + x * TailBG a δ Γ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    set Z1 := Z.filter fun u => ¬ |u.im| ≤ H with hZ1
    set Z2 := Z1.filter fun u => ¬ |u.im| ≤ 3e12 with hZ2
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H),
      ← Finset.sum_filter_add_sum_filter_not Z1 (fun u => |u.im| ≤ 3e12),
      ← Finset.sum_filter_add_sum_filter_not Z2 (fun u => |u.im| ≤ Γ)]
    have hZ1Z : Z1 ⊆ Z := Finset.filter_subset _ _
    have hZ2Z : Z2 ⊆ Z := (Finset.filter_subset _ _).trans hZ1Z
    have hA : ∑ u ∈ Z.filter (fun u => |u.im| ≤ H), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤ √x * LineBH a δ H := by
      -- the line zeros (as in `SsumG_gsm_errH`)
      set S := Z.filter (fun u => |u.im| ≤ H) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact hRH u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ H := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_le (by linarith) S hSZ hre him (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _)
        (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le (δ := δ) hab hb u.im
      simpa using this
    have hB : ∑ u ∈ Z1.filter (fun u => |u.im| ≤ 3e12), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0 a δ H 3e12 x := by
      refine mid_sum_le hb hx hH1 _ ((Finset.filter_subset _ _).trans hZ1Z) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hC : ∑ u ∈ Z2.filter (fun u => |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0 a δ 3e12 Γ x := by
      refine mid_sum_le hb hx (by norm_num) _ ((Finset.filter_subset _ _).trans hZ2Z) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hD : ∑ u ∈ Z2.filter (fun u => ¬ |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * TailBG a δ Γ := by
      have hSZ := (Finset.filter_subset (fun u => ¬ |u.im| ≤ Γ) Z2).trans hZ2Z
      have him : ∀ u ∈ Z2.filter (fun u => ¬ |u.im| ≤ Γ), Γ < |u.im| := fun u hu =>
        not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by linarith) hδ hb hx.le _ hSZ him
    rw [MidBH, mul_add]
    linarith
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineBH a δ H + x * MidBH a δ H Γ x + x * TailBG a δ Γ :=
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

/-- **The explicit-formula bound with the zero-free region**, under RH up to `H`, with the zeros
in `(H, Γ]` in three ranges `(H, H₂]`, `(H₂, 3·10¹²]`, `(3·10¹², Γ]`. -/
theorem SsumG_gsm_err_zf3H {a b δ x Γ H H₂ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH₂ : H ≤ H₂)
    (hH₂' : H₂ ≤ 3e12) (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x) (hΓ : 3e12 ≤ Γ) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * LineBH a δ H + x * (MidB0 a δ H H₂ x + MidBH a δ H₂ Γ x) + x * TailBG a δ Γ +
        x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineBH a δ H + x * (MidB0 a δ H H₂ x + MidBH a δ H₂ Γ x) + x * TailBG a δ Γ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    set Z1 := Z.filter fun u => ¬ |u.im| ≤ H with hZ1
    set Z1b := Z1.filter fun u => ¬ |u.im| ≤ H₂ with hZ1b
    set Z2 := Z1b.filter fun u => ¬ |u.im| ≤ 3e12 with hZ2
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H),
      ← Finset.sum_filter_add_sum_filter_not Z1 (fun u => |u.im| ≤ H₂),
      ← Finset.sum_filter_add_sum_filter_not Z1b (fun u => |u.im| ≤ 3e12),
      ← Finset.sum_filter_add_sum_filter_not Z2 (fun u => |u.im| ≤ Γ)]
    have hZ1Z : Z1 ⊆ Z := Finset.filter_subset _ _
    have hZ1bZ : Z1b ⊆ Z := (Finset.filter_subset _ _).trans hZ1Z
    have hZ2Z : Z2 ⊆ Z := (Finset.filter_subset _ _).trans hZ1bZ
    have hA : ∑ u ∈ Z.filter (fun u => |u.im| ≤ H), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤ √x * LineBH a δ H := by
      -- the line zeros (as in `SsumG_gsm_errH`)
      set S := Z.filter (fun u => |u.im| ≤ H) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact hRH u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ H := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_le (by linarith) S hSZ hre him (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _)
        (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le (δ := δ) hab hb u.im
      simpa using this
    have hB0 : ∑ u ∈ Z1.filter (fun u => |u.im| ≤ H₂), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0 a δ H H₂ x := by
      refine mid_sum_le hb hx hH1 _ ((Finset.filter_subset _ _).trans hZ1Z) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hB : ∑ u ∈ Z1b.filter (fun u => |u.im| ≤ 3e12), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0 a δ H₂ 3e12 x := by
      refine mid_sum_le hb hx (hH1.trans hH₂) _ ((Finset.filter_subset _ _).trans hZ1bZ) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hC : ∑ u ∈ Z2.filter (fun u => |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0 a δ 3e12 Γ x := by
      refine mid_sum_le hb hx (by norm_num) _ ((Finset.filter_subset _ _).trans hZ2Z) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hD : ∑ u ∈ Z2.filter (fun u => ¬ |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * TailBG a δ Γ := by
      have hSZ := (Finset.filter_subset (fun u => ¬ |u.im| ≤ Γ) Z2).trans hZ2Z
      have him : ∀ u ∈ Z2.filter (fun u => ¬ |u.im| ≤ Γ), Γ < |u.im| := fun u hu =>
        not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by linarith) hδ hb hx.le _ hSZ him
    rw [MidBH, mul_add, mul_add]
    linarith
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineBH a δ H + x * (MidB0 a δ H H₂ x + MidBH a δ H₂ Γ x) + x * TailBG a δ Γ :=
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

/-! ## `ψ` bounds from a general error term -/

theorem psi_upper_of_err {δ K y0 x E : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1)
    (hy0 : 0 < y0) (hx : 1 ≤ x) (hYx : y0 * Real.exp (K * δ) ≤ x)
    (hE : |∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) -
      Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x| ≤ E) :
    psiR x ≤ 4 * (y0 * Real.exp (K * δ)) +
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + E) / (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx0).2
    (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
  have hab : Real.log (y0 / x) ≤ K * δ := hb.trans (by positivity)
  have hS := sandwich_upper hδ hK hy0 hx0 hYx (summable_gsm hδ hab hx0)
  have hc : 0 < 1 - 2 * Real.exp (-(K ^ 2 / 2)) := by linarith
  have hmain : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x := by
    rw [Real.exp_add]
    have hp : 0 < Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x :=
      mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hx0
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (K * δ) * x - Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x := by
      ring
    rw [e]; linarith
  have hsum : ∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x + E := by
    have := (abs_le.1 hE).2; linarith
  have hY := psiR_le (y := y0 * Real.exp (K * δ)) (by positivity)
  have h1 : psiR x - psiR (y0 * Real.exp (K * δ)) ≤
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + E) / (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
    rw [le_div_iff₀ hc]; nlinarith
  linarith

theorem psi_lower_of_err {δ K y0 x E : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hKδ : δ ≤ K) (hy0 : 0 < y0)
    (hx : 1 ≤ x) (hb : Real.log (y0 / x) ≤ -(K * δ))
    (hE : |∑' n : ℕ, Λ n * gsm (-(K * δ)) (Real.log (y0 / x)) δ (n / x) -
      Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - Real.exp (Real.log (y0 / x))) * x| ≤ E) :
    Real.exp (-(K * δ)) * x - 2 * y0 - E - 4 * x * Real.exp (-(K ^ 2 / 2)) ≤ psiR x := by
  have hx0 : 0 < x := by linarith
  have hS := sandwich_lower hδ hKδ hx0 hb
  have he : Real.exp (Real.log (y0 / x)) = y0 / x := Real.exp_log (by positivity)
  rw [he] at hE
  have hd : Real.exp (δ ^ 2 / 2) ≤ 2 := by
    have : Real.exp (δ ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    linarith
  have hd1 : 1 ≤ Real.exp (δ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hmain : Real.exp (-(K * δ)) * x - 2 * y0 ≤
      Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x := by
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x - Real.exp (δ ^ 2 / 2) * y0 := by
      field_simp
    rw [e]
    have hq : 0 ≤ Real.exp (-(K * δ)) * x := (mul_pos (Real.exp_pos _) hx0).le
    have h1 : 1 * (Real.exp (-(K * δ)) * x) ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) :=
      mul_le_mul_of_nonneg_right hd1 hq
    have h2 : Real.exp (δ ^ 2 / 2) * y0 ≤ 2 * y0 := mul_le_mul_of_nonneg_right hd hy0.le
    have e2 : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) = Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x := by ring
    rw [e2, one_mul] at h1
    linarith
  have := (abs_le.1 hE).1
  linarith

/-- The tsum version of `SsumG_gsm_err_zfH`. -/
theorem tsum_gsm_le_zfH {a b δ x Γ H : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e12)
    (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x) (hΓ : 3e12 ≤ Γ) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤
      √x * LineBH a δ H + x * MidBH a δ H Γ x + x * TailBG a δ Γ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have h := SsumG_gsm_err_zfH hRH hH1 hH2 hδ hab hb hx hΓ
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The tsum version of `SsumG_gsm_err_zf3H`. -/
theorem tsum_gsm_le_zf3H {a b δ x Γ H H₂ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH₂ : H ≤ H₂)
    (hH₂' : H₂ ≤ 3e12)
    (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x) (hΓ : 3e12 ≤ Γ) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤
      √x * LineBH a δ H + x * (MidB0 a δ H H₂ x + MidBH a δ H₂ Γ x) + x * TailBG a δ Γ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have h := SsumG_gsm_err_zf3H hRH hH1 hH₂ hH₂' hδ hab hb hx hΓ
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end TernaryGoldbach.Explicit
