import TernaryGoldbach.Prelim.MertensProduct

/-!
# `∑_{n ≤ x} Λ(n)/n − log x → −γ`

* The limit `ℓ = lim E₁Λ(x)` exists: `|E₁Λ(t) − E₁Λ(x)| ≤ D(x)` for `t ≥ x ≥ 10¹²` (`E1_var`) and
  `D(x) → 0` (`E1_tendsto_exists`).
* Its value: with `L(t) = ∑_{k ≤ t} Λ(k)/k` and `H(t) = ∑_{k ≤ t} 1/k`, partial summation
  (`LSeries_eq_mul_integral'`) gives, for `s > 0`,
  `s ∫₁^∞ (L(t) − H(t)) t^{−s−1} dt = −ζ'/ζ(1 + s) − ζ(1 + s)`, which tends to `−2γ` as `s → 0⁺`
  (`ζ = (s − 1)⁻¹ ζ₁`, `ζ₁(1) = 1`, `ζ₁'(1) = γ`, `ζ₀(1) = γ`). The left side tends to
  `lim (L − H) = ℓ − γ` (`abel_lim`), so `ℓ = −γ` (`E1_tendsto`).
-/

open MeasureTheory Set Filter Finset Asymptotics
open scoped ArithmeticFunction.vonMangoldt Topology

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-! ### Existence of the limit -/

theorem Dvar_tendsto : Tendsto Dvar atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℕ => 1443 / √(x : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun x : ℕ => 13 / (x : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun x : ℕ => 16 / Real.log x ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hlog)
  have h4 : Tendsto (fun x : ℕ => 2 / Real.log x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hlog)
  have h5 : Tendsto (fun x : ℕ => if Real.log x < 20000 then (8.5e-6 : ℝ) else 2 / Real.log x ^ 2)
      atTop (𝓝 0) := by
    refine h4.congr' ?_
    filter_upwards [hlog.eventually_ge_atTop 20000] with x hx
    rw [if_neg (not_lt.2 hx)]
  have := ((h1.add h2).add h3).add h5
  simp only [add_zero] at this
  exact this.congr fun x => by unfold Dvar; ring

variable [Fact TernaryGoldbach.PlattGRH] in
/-- `E₁Λ` has a limit at `∞`, approached within `2 D(n)` beyond `n ≥ 10¹²`. -/
theorem E1_tendsto_exists : ∃ ℓ : ℝ, Tendsto E₁Λ atTop (𝓝 ℓ) ∧
    ∀ n : ℕ, 10 ^ 12 ≤ n → ∀ t : ℝ, (n : ℝ) ≤ t → |E₁Λ t - ℓ| ≤ 2 * Dvar n := by
  set a : ℕ → ℝ := fun n => E₁Λ n with ha
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Dvar_tendsto.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨max N (10 ^ 12), fun n hn => ?_⟩
    have hle : ((max N (10 ^ 12) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (E1_var (le_max_right _ _) hle) (hN _ (le_max_left _ _))
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcau
  have hclose : ∀ n : ℕ, 10 ^ 12 ≤ n → |a n - ℓ| ≤ Dvar n := by
    intro n hn
    have h : Tendsto (fun m => |a m - a n|) atTop (𝓝 |ℓ - a n|) :=
      ((continuous_abs.tendsto _).comp (hℓ.sub_const _))
    rw [abs_sub_comm]
    refine le_of_tendsto h ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact E1_var hn (by exact_mod_cast hm)
  have hbd : ∀ n : ℕ, 10 ^ 12 ≤ n → ∀ t : ℝ, (n : ℝ) ≤ t → |E₁Λ t - ℓ| ≤ 2 * Dvar n := by
    intro n hn t ht
    have h1 := E1_var hn ht
    have h2 := hclose n hn
    calc |E₁Λ t - ℓ| = |(E₁Λ t - E₁Λ n) + (a n - ℓ)| := by simp only [ha]; ring_nf
      _ ≤ |E₁Λ t - E₁Λ n| + |a n - ℓ| := abs_add_le _ _
      _ ≤ 2 * Dvar n := by linarith
  refine ⟨ℓ, ?_, hbd⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Dvar_tendsto.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
  set n := max N (10 ^ 12)
  refine ⟨n, fun t ht => ?_⟩
  rw [Real.dist_eq]
  have := hbd n (le_max_right _ _) t ht
  have := hN n (le_max_left _ _)
  linarith

/-! ### An Abelian lemma -/

/-- If `g` is bounded and measurable on `[1, ∞)` and `g(t) → ℓ`, then `s ∫₁^∞ g(t) t^{−s−1} dt → ℓ`
as `s → 0⁺`. -/
theorem abel_lim {g : ℝ → ℝ} {ℓ B : ℝ} (hg : Measurable g) (hB : ∀ t, 1 ≤ t → |g t| ≤ B)
    (hlim : Tendsto g atTop (𝓝 ℓ)) :
    Tendsto (fun s : ℝ => s * ∫ t in Ioi (1 : ℝ), g t * t ^ (-s - 1)) (𝓝[>] 0) (𝓝 ℓ) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 le_rfl)
  -- `s ∫₁^∞ t^{−s−1} = 1`
  have hone : ∀ s : ℝ, 0 < s → s * ∫ t in Ioi (1 : ℝ), t ^ (-s - 1) = 1 := by
    intro s hs
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show (-s - 1 + 1 : ℝ) = -s by ring, neg_div_neg_eq]
    field_simp
  have hint : ∀ s : ℝ, 0 < s → IntegrableOn (fun t : ℝ => t ^ (-s - 1)) (Ioi 1) := fun s hs =>
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hgint : ∀ s : ℝ, 0 < s → IntegrableOn (fun t : ℝ => g t * t ^ (-s - 1)) (Ioi 1) := by
    intro s hs
    refine Integrable.mono' ((hint s hs).const_mul B)
      ((hg.mul (by fun_prop)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact mul_le_mul_of_nonneg_right (hB t ht1) (Real.rpow_pos_of_pos (by linarith) _).le
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 2) (half_pos hε)
  set T' := max T 1 with hT'
  have hT'1 : 1 ≤ T' := le_max_right _ _
  set K := (B + |ℓ|) * Real.log T' with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (Real.log_nonneg hT'1)
  refine ⟨ε / (2 * (K + 1)), by positivity, fun s hs hsd => ?_⟩
  have hs0 : 0 < s := hs
  have hsd' : s < ε / (2 * (K + 1)) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd; exact hsd
  rw [Real.dist_eq]
  -- `s ∫ g t^{−s−1} − ℓ = s ∫ (g − ℓ) t^{−s−1}`
  have e : s * (∫ t in Ioi (1 : ℝ), g t * t ^ (-s - 1)) - ℓ =
      s * ∫ t in Ioi (1 : ℝ), (g t - ℓ) * t ^ (-s - 1) := by
    have h1 : ∫ t in Ioi (1 : ℝ), (g t - ℓ) * t ^ (-s - 1) =
        (∫ t in Ioi (1 : ℝ), g t * t ^ (-s - 1)) - ℓ * ∫ t in Ioi (1 : ℝ), t ^ (-s - 1) := by
      rw [← integral_const_mul, ← integral_sub (hgint s hs0) ((hint s hs0).const_mul ℓ)]
      congr 1; ext t; ring
    rw [h1, mul_sub, ← mul_assoc, mul_comm s ℓ, mul_assoc, hone s hs0, mul_one]
  rw [e]
  -- split at `T'`
  set f : ℝ → ℝ := fun t => (g t - ℓ) * t ^ (-s - 1) with hf
  have hfint : IntegrableOn f (Ioi 1) := by
    have := (hgint s hs0).sub ((hint s hs0).const_mul ℓ)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hf, Pi.sub_apply]; ring
  have hsplit : ∫ t in Ioi (1 : ℝ), f t = (∫ t in Ioc (1 : ℝ) T', f t) + ∫ t in Ioi T', f t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hfint.mono_set Ioc_subset_Ioi_self) (hfint.mono_set (Ioi_subset_Ioi hT'1)),
      Ioc_union_Ioi_eq_Ioi hT'1]
  have hA : |∫ t in Ioc (1 : ℝ) T', f t| ≤ K := by
    have hb : ∀ t ∈ Ioc (1 : ℝ) T', ‖f t‖ ≤ (B + |ℓ|) * t⁻¹ := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, hf, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      have h1 : |g t - ℓ| ≤ B + |ℓ| := (abs_sub _ _).trans (by linarith [hB t ht1])
      have h2 : t ^ (-s - 1) ≤ t⁻¹ := by
        rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos ht0 _).le (by positivity)
    have hgi : IntegrableOn (fun t : ℝ => (B + |ℓ|) * t⁻¹) (Ioc 1 T') := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1])
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall hb))).trans (le_of_eq ?_)
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hT'1, integral_inv_of_pos one_pos
      (by linarith), div_one]
  have hC : |∫ t in Ioi T', f t| ≤ ε / 2 / s := by
    have hb : ∀ t ∈ Ioi T', ‖f t‖ ≤ ε / 2 * t ^ (-s - 1) := by
      intro t ht
      have ht0 : 0 < t := by linarith [show T' < t from ht]
      rw [Real.norm_eq_abs, hf, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      have h1 : |g t - ℓ| ≤ ε / 2 := by
        have := hT t (le_trans (le_max_left _ _) (le_of_lt ht))
        rw [Real.dist_eq] at this; exact this.le
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos ht0 _).le
    have hT'0 : 0 < T' := by linarith
    have hgi : IntegrableOn (fun t : ℝ => ε / 2 * t ^ (-s - 1)) (Ioi T') :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hT'0).const_mul _
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall hb))).trans ?_
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hT'0]
    have e : -s - 1 + 1 = -s := by ring
    rw [e]
    have hp : T' ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT'1 (by linarith)
    have hp0 : 0 ≤ T' ^ (-s) := (Real.rpow_pos_of_pos hT'0 _).le
    rw [neg_div_neg_eq]
    calc ε / 2 * (T' ^ (-s) / s) ≤ ε / 2 * (1 / s) := by gcongr
      _ = ε / 2 / s := by ring
  rw [hsplit, abs_mul, abs_of_pos hs0]
  have hsK : s * K < ε / 2 := by
    have h1 : s * K ≤ s * (K + 1) := by nlinarith
    have h2 : s * (K + 1) < ε / 2 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (K + 1))] at hsd'
      nlinarith
    linarith
  calc s * |(∫ t in Ioc (1 : ℝ) T', f t) + ∫ t in Ioi T', f t|
      ≤ s * (K + ε / 2 / s) := mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hA hC)) hs0.le
    _ = s * K + ε / 2 := by field_simp
    _ < ε := by linarith

/-! ### The value of the limit -/

/-- `L(t) − H(t) = ∑_{k ≤ t} (Λ(k) − 1)/k`. -/
noncomputable def gLH (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((Λ k : ℝ) / k - 1 / k)

theorem sum_Lambda_div_eq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (Λ k : ℝ) / k = Real.log n + E₁Λ n := by
  have e : Finset.Icc 1 n = Finset.Ioc 0 n := by ext k; simp; omega
  rw [E₁Λ, Nat.floor_natCast, ← e]; ring

theorem harmonic_eq_sum (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]

theorem gLH_eq (t : ℝ) : gLH t = Real.log ⌊t⌋₊ + E₁Λ ⌊t⌋₊ - ((harmonic ⌊t⌋₊ : ℚ) : ℝ) := by
  rw [gLH, Finset.sum_sub_distrib, sum_Lambda_div_eq, harmonic_eq_sum]

theorem abs_gLH_le (t : ℝ) : |gLH t| ≤ Real.log 4 + 5 := by
  rw [gLH_eq]
  set n := ⌊t⌋₊
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]; simp [E₁Λ]; positivity
  have hE := E₁Λ.bounded'.choose_spec
  have hE' : |E₁Λ n| ≤ Real.log 4 + 4 := sum_mangoldt_div_eq_log (by exact_mod_cast hn)
  have h1 := harmonic_le_one_add_log n
  have h2 := log_add_one_le_harmonic n
  have h3 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  rw [abs_le] at hE' ⊢
  constructor <;> linarith [hE'.1, hE'.2]

theorem measurable_gLH : Measurable gLH :=
  (measurable_from_nat (f := fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, ((Λ k : ℝ) / k - 1 / k))).comp
    Nat.measurable_floor

/-- `L(t) − H(t) → ℓ − γ`. -/
theorem gLH_tendsto {ℓ : ℝ} (h : Tendsto E₁Λ atTop (𝓝 ℓ)) :
    Tendsto gLH atTop (𝓝 (ℓ - Real.eulerMascheroniConstant)) := by
  have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have h1 : Tendsto (fun t : ℝ => E₁Λ ⌊t⌋₊) atTop (𝓝 ℓ) :=
    h.comp (tendsto_natCast_atTop_atTop.comp hfl)
  have h2 : Tendsto (fun t : ℝ => ((harmonic ⌊t⌋₊ : ℚ) : ℝ) - Real.log ⌊t⌋₊) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log.comp hfl
  have := h1.sub h2
  refine this.congr fun t => ?_
  rw [gLH_eq]; ring

/-- The partial sums of `Λ(k)/k` and `1/k` grow at most like `n^r`. -/
theorem sum_norm_bigO {r : ℝ} (hr : 0 < r) (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ Real.log n + C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
  refine IsBigO.of_bound (1 / r + |C|) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_rpow_div (x := n) (by positivity) hr
  have hp : 1 ≤ (n : ℝ) ^ r := Real.one_le_rpow hn1 hr.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
  have := hf n hn
  have hC : C ≤ |C| * (n : ℝ) ^ r := by
    have := le_abs_self C; nlinarith [abs_nonneg C]
  calc _ ≤ Real.log n + C := this
    _ ≤ (n : ℝ) ^ r / r + |C| * (n : ℝ) ^ r := by linarith
    _ = (1 / r + |C|) * (n : ℝ) ^ r := by ring

/-- **Partial summation**: `s ∫₁^∞ (L(t) − H(t)) t^{−s−1} dt = −ζ'/ζ(1 + s) − ζ(1 + s)` for `s > 0`. -/
theorem integral_gLH_eq {σ : ℝ} (hσ : 0 < σ) :
    (((σ * ∫ t in Ioi (1 : ℝ), gLH t * t ^ (-σ - 1) : ℝ)) : ℂ) =
      -deriv riemannZeta (1 + σ) / riemannZeta (1 + σ) - riemannZeta (1 + σ) := by
  set s : ℂ := (σ : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  set f₁ : ℕ → ℂ := fun k => (((Λ k : ℝ) / k : ℝ) : ℂ) with hf₁
  set f₂ : ℕ → ℂ := fun k => (((1 : ℝ) / k : ℝ) : ℂ) with hf₂
  have hr : (0 : ℝ) < σ / 2 := by positivity
  have hO₁ : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖f₁ k‖) =O[atTop] fun n ↦ (n : ℝ) ^ (σ / 2) := by
    refine sum_norm_bigO hr f₁ (Real.log 4 + 4) fun n hn => ?_
    have e : ∑ k ∈ Finset.Icc 1 n, ‖f₁ k‖ = ∑ k ∈ Finset.Icc 1 n, (Λ k : ℝ) / k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf₁, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
    rw [e, sum_Lambda_div_eq]
    have := sum_mangoldt_div_eq_log (x := (n : ℝ)) (by exact_mod_cast hn)
    linarith [(abs_le.1 this).2]
  have hO₂ : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖f₂ k‖) =O[atTop] fun n ↦ (n : ℝ) ^ (σ / 2) := by
    refine sum_norm_bigO hr f₂ 1 fun n hn => ?_
    have e : ∑ k ∈ Finset.Icc 1 n, ‖f₂ k‖ = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf₂, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [e, ← harmonic_eq_sum]
    linarith [harmonic_le_one_add_log n]
  have hS₁ : LSeriesSummable f₁ s :=
    LSeriesSummable_of_sum_norm_bigO hO₁ hr.le (by rw [hsre]; linarith)
  have hS₂ : LSeriesSummable f₂ s :=
    LSeriesSummable_of_sum_norm_bigO hO₂ hr.le (by rw [hsre]; linarith)
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (f₁ - f₂) k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    refine IsBigO.of_bound (Real.log 4 + 5) (Eventually.of_forall fun n => ?_)
    have e : ∑ k ∈ Finset.Icc 1 n, (f₁ - f₂) k = ((gLH n : ℝ) : ℂ) := by
      rw [gLH, Nat.floor_natCast]; push_cast; simp [hf₁, hf₂]
    rw [e, Complex.norm_real, Real.rpow_zero, norm_one, mul_one]
    exact abs_gLH_le n
  have hI := LSeries_eq_mul_integral (f₁ - f₂) le_rfl (by rw [hsre]; exact hσ) (hS₁.sub hS₂) hO
  rw [LSeries_sub hS₁ hS₂] at hI
  -- the two L-series
  have hL₁ : LSeries f₁ s = LSeries (fun n => (Λ n : ℂ)) (s + 1) := by
    simp only [LSeries]
    congr 1; ext n
    simp only [LSeries.term]
    split_ifs with hn
    · rfl
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_add _ _ hn0, Complex.cpow_one, hf₁]
    push_cast
    field_simp
  have hL₂ : LSeries f₂ s = LSeries 1 (s + 1) := by
    simp only [LSeries]
    congr 1; ext n
    simp only [LSeries.term]
    split_ifs with hn
    · rfl
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_add _ _ hn0, Complex.cpow_one, hf₂]
    push_cast
    simp only [Pi.one_apply]
    field_simp
  have hre1 : 1 < (s + 1).re := by simp [hs]; linarith
  rw [hL₁, hL₂, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre1,
    LSeries_one_eq_riemannZeta hre1] at hI
  -- the integral, as a real integral
  have hint : ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (f₁ - f₂) k) * (t : ℂ) ^ (-(s + 1)) =
      ((∫ t in Ioi (1 : ℝ), gLH t * t ^ (-σ - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := by linarith [show (1 : ℝ) < t from ht]
    have e1 : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (f₁ - f₂) k = ((gLH t : ℝ) : ℂ) := by
      rw [gLH]; push_cast; simp [hf₁, hf₂]
    rw [e1, Complex.ofReal_mul, Complex.ofReal_cpow ht0]
    congr 2
    rw [hs]; push_cast; ring
  rw [hint] at hI
  have e2 : (1 : ℂ) + σ = s + 1 := by rw [hs]; ring
  rw [e2, hI, hs]
  push_cast; ring

/-- `−ζ'/ζ(1 + s) − ζ(1 + s) → −2γ` as `s → 0⁺`. -/
theorem zeta_combo_tendsto :
    Tendsto (fun σ : ℝ => -deriv riemannZeta (1 + σ) / riemannZeta (1 + σ) - riemannZeta (1 + σ))
      (𝓝[>] 0) (𝓝 (-2 * (Real.eulerMascheroniConstant : ℂ))) := by
  have hz : Tendsto (fun σ : ℝ => (1 : ℂ) + σ) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun σ : ℝ => (1 : ℂ) + σ) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  set G : ℂ → ℂ := fun z => -deriv riemannZeta₁ z / riemannZeta₁ z - riemannZeta₀ z with hG
  have hGc : ContinuousAt G 1 := by
    have h1 : ContinuousAt (deriv riemannZeta₁) 1 :=
      differentiable_riemannZeta₁.deriv.continuous.continuousAt
    have h2 : ContinuousAt riemannZeta₁ 1 := differentiable_riemannZeta₁.continuous.continuousAt
    have h3 : ContinuousAt riemannZeta₀ 1 := differentiable_riemannZeta₀.continuous.continuousAt
    exact (h1.neg.div h2 (by simp)).sub h3
  have hlim : Tendsto (fun σ : ℝ => G (1 + σ)) (𝓝[>] 0) (𝓝 (G 1)) := hGc.tendsto.comp hz
  have hG1 : G 1 = -2 * (Real.eulerMascheroniConstant : ℂ) := by
    simp only [hG, deriv_riemannZeta₁_one, riemannZeta₁_one, riemannZeta₀_one]; ring
  rw [hG1] at hlim
  refine hlim.congr' ?_
  have hne : ∀ᶠ σ : ℝ in 𝓝[>] 0, riemannZeta₁ (1 + σ) ≠ 0 := hz.eventually riemannZeta₁_ne_zero_of_near_one
  filter_upwards [hne, self_mem_nhdsWithin] with σ h1 hσ
  have hσ0 : (0 : ℝ) < σ := hσ
  have hz1 : (1 : ℂ) + σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsub : (1 : ℂ) + σ - 1 ≠ 0 := sub_ne_zero.2 hz1
  simp only [hG]
  have hB : riemannZeta₀ (1 + σ) = (riemannZeta₁ (1 + σ) - 1) / ((1 : ℂ) + σ - 1) := by
    rw [riemannZeta₁]; field_simp; ring
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hz1, riemannZeta_eq_inv_sub_mul hz1, hB]
  field_simp
  ring

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`∑_{n ≤ x} Λ(n)/n − log x → −γ`**, approached within `2 D(n)` beyond `n ≥ 10¹²`. -/
theorem E1_tendsto : Tendsto E₁Λ atTop (𝓝 (-Real.eulerMascheroniConstant)) ∧
    ∀ n : ℕ, 10 ^ 12 ≤ n → ∀ t : ℝ, (n : ℝ) ≤ t →
      |E₁Λ t + Real.eulerMascheroniConstant| ≤ 2 * Dvar n := by
  obtain ⟨ℓ, hℓ, hbd⟩ := E1_tendsto_exists
  have hA := abel_lim measurable_gLH (fun t _ => abs_gLH_le t) (gLH_tendsto hℓ)
  have hA' : Tendsto (fun σ : ℝ => ((σ * ∫ t in Ioi (1 : ℝ), gLH t * t ^ (-σ - 1) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((ℓ - Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hA
  have hB : Tendsto (fun σ : ℝ => ((σ * ∫ t in Ioi (1 : ℝ), gLH t * t ^ (-σ - 1) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (-2 * (Real.eulerMascheroniConstant : ℂ))) := by
    refine zeta_combo_tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (integral_gLH_eq hσ).symm
  have heq := tendsto_nhds_unique hA' hB
  have hℓ' : ℓ = -Real.eulerMascheroniConstant := by
    have := congrArg Complex.re heq
    simp at this; linarith
  subst hℓ'
  refine ⟨hℓ, fun n hn t ht => ?_⟩
  have := hbd n hn t ht
  rwa [sub_neg_eq_add] at this

end TernaryGoldbach.Prelim
