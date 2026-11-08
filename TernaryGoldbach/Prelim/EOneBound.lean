import TernaryGoldbach.Prelim.MertensZeros
import TernaryGoldbach.Prelim.MertensLimit

/-!
# Pointwise bounds for `E(y) = ∑_{n ≤ y} Λ(n)/n − log y + γ`

* `E1_diff_gen`: summation by parts, `|E₁Λ(t) − E₁Λ(M)| ≤ 3/M + err(N)/N + err(M)/M +
  ∑_{M<n<N} err(n)/(n(n+1))` if `|ψ(n) − n| ≤ err(n)` on `[M, N]`, `N = ⌊t⌋`; with
  `err(n) = C√n` this is `3/M + 3C/√M` (`E1_diff_sqrt`).
* `abs_smoothed_E_le`: `|∫₀^∞ E(Yv) φ(v) dv| ≤ Z(Y)` for `φ = gsm a 0 δ`, from the integrated
  explicit formula (`abs_integral_psi_gsm_le`) between `Y` and `Y₂ → ∞`, where
  `∫₀^∞ E(Y₂v) φ(v) dv → 0` by dominated convergence (`E1_tendsto`).
-/

open MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt Topology

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

/-! ### Summation by parts -/

/-- **Summation by parts for `E₁Λ`** with any pointwise error `err` for `ψ` on `[M, ⌊t⌋]`. -/
theorem E1_diff_gen {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : (M : ℝ) ≤ t) (err : ℕ → ℝ)
    (herr0 : ∀ n, 0 ≤ err n) (herr : ∀ n, M ≤ n → n ≤ ⌊t⌋₊ → |psiN n - n| ≤ err n) :
    |E₁Λ t - E₁Λ M| ≤ 3 / M + err ⌊t⌋₊ / ⌊t⌋₊ + err M / M +
      ∑ n ∈ Finset.Ioo M ⌊t⌋₊, err n / (n * (n + 1)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set N := ⌊t⌋₊ with hN
  have hMN : M ≤ N := Nat.le_floor ht
  have ht0 : 0 < t := lt_of_lt_of_le hM0 ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le ht0.le
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 (by exact_mod_cast hMN)
  have hlt1 : Real.log N ≤ Real.log t := Real.log_le_log hN0 hNt
  have hlt2 : Real.log t ≤ Real.log (N + 1) := Real.log_le_log ht0 htN.le
  have hdiff : E₁Λ t - E₁Λ M = ∑ n ∈ Finset.Ioc M N, (Λ n : ℝ) * (fun n : ℕ => 1 / (n : ℝ)) n -
      Real.log t + Real.log M := by
    simp only [E₁Λ, Nat.floor_natCast, mul_one_div]
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]; ring
  have hl1 : Real.log (M + 1) - Real.log M ≤ 1 / M := by
    have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at this
    have e : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
    linarith
  have hl2 : Real.log (M + 2) - Real.log M ≤ 2 / M := by
    have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 2) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at this
    have e : ((M : ℝ) + 2) / M - 1 = 2 / M := by field_simp; ring
    linarith
  have hlogMM : Real.log M ≤ Real.log (M + 1) := Real.log_le_log hM0 (by linarith)
  have heN0 : 0 ≤ err N / N := div_nonneg (herr0 N) hN0.le
  have heM0 : 0 ≤ err M / M := div_nonneg (herr0 M) hM0.le
  have hS0 : 0 ≤ ∑ n ∈ Finset.Ioo M N, err n / (n * (n + 1)) :=
    Finset.sum_nonneg fun n _ => div_nonneg (herr0 n) (by positivity)
  rcases eq_or_lt_of_le hMN with hEq | hlt
  · rw [hdiff, ← hEq, Finset.Ioc_self, Finset.sum_empty, Finset.Ioo_self, Finset.sum_empty]
    have : Real.log t ≤ Real.log (M + 1) := by rw [hEq]; exact hlt2
    have h3 : Real.log M ≤ Real.log t := by rw [hEq]; exact hlt1
    have h30 : 0 ≤ 3 / (M : ℝ) := by positivity
    rw [abs_le]; constructor
    · have : 1 / (M : ℝ) ≤ 3 / M := div_le_div_of_nonneg_right (by norm_num) hM0.le
      linarith
    · linarith
  rw [hdiff, abel_Ioc _ M N hlt]
  set Sall := ∑ n ∈ Finset.Ioo M N, err n / (n * (n + 1)) with hSall
  have hint : |∑ n ∈ Finset.Ioo M N, (psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) -
      1 / ((n : ℝ) + 1))| ≤ Sall := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have e : psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) - 1 / ((n : ℝ) + 1) =
        (psiN n - n) * (1 / (n * (n + 1))) := by push_cast; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n * (n + 1))), mul_one_div]
    exact div_le_div_of_nonneg_right (herr n h1.le h2.le) (by positivity)
  rw [Finset.sum_sub_distrib] at hint
  have hH1 := sum_inv_succ_ge hlt
  have hH2 := sum_inv_succ_le hlt
  have hbN : |psiN N * (1 / (N : ℝ)) - 1| ≤ err N / N := by
    have e : psiN N * (1 / (N : ℝ)) - 1 = (psiN N - N) * (1 / (N : ℝ)) := by field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)), mul_one_div]
    exact div_le_div_of_nonneg_right (herr N hMN le_rfl) hN0.le
  have hbM : |psiN M * (1 / ((M + 1 : ℕ) : ℝ)) - (1 - 1 / ((M : ℝ) + 1))| ≤ err M / M := by
    have e : psiN M * (1 / ((M + 1 : ℕ) : ℝ)) - (1 - 1 / ((M : ℝ) + 1)) =
        (psiN M - M) * (1 / ((M : ℝ) + 1)) := by push_cast; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1)), mul_one_div]
    exact (div_le_div_of_nonneg_right (herr M le_rfl hMN) (by positivity)).trans
      (div_le_div_of_nonneg_left (herr0 M) hM0 (by linarith))
  have hM1 : 1 / ((M : ℝ) + 1) ≤ 1 / M := div_le_div_of_nonneg_left (by norm_num) hM0 (by linarith)
  have hM1' : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
  have hlN : Real.log (N + 1) - Real.log t ≥ 0 := by linarith
  have e3 : (3 : ℝ) / M = 1 / M + 2 / M := by ring
  rw [abs_le] at hint hbN hbM ⊢
  constructor <;> linarith [hint.1, hint.2, hbN.1, hbN.2, hbM.1, hbM.2]

/-- **Summation by parts with `|ψ(n) − n| ≤ C√n`**: `|E₁Λ(t) − E₁Λ(M)| ≤ 3/M + 3C/√M`. -/
theorem E1_diff_sqrt {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : (M : ℝ) ≤ t) {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ n : ℕ, M ≤ n → n ≤ ⌊t⌋₊ → |psiN n - n| ≤ C * √(n : ℝ)) :
    |E₁Λ t - E₁Λ M| ≤ 3 / M + 3 * C / √(M : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h := E1_diff_gen hM ht (fun n => C * √(n : ℝ)) (fun n => by positivity) herr
  set N := ⌊t⌋₊ with hN
  have hMN : M ≤ N := Nat.le_floor ht
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 (by exact_mod_cast hMN)
  have hsq : ∀ n : ℕ, 0 < n → C * √(n : ℝ) / n = C / √(n : ℝ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs := Real.mul_self_sqrt hn0.le
    have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    field_simp; nlinarith [hs]
  rw [hsq N (by omega), hsq M (by omega)] at h
  have hsum : ∑ n ∈ Finset.Ioo M N, C * √(n : ℝ) / (n * (n + 1)) ≤ C * (2 / √(M : ℝ) - 2 / √(N : ℝ)) := by
    rcases eq_or_lt_of_le hMN with hEq | hlt
    · rw [← hEq, Finset.Ioo_self, Finset.sum_empty]; simp
    have e : ∀ n ∈ Finset.Ioo M N, C * √(n : ℝ) / (n * (n + 1)) = C * (1 / (√(n : ℝ) * (n + 1))) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (Finset.mem_Ioo.1 hn).1; omega)
      have hs := Real.mul_self_sqrt hn0.le
      have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
      field_simp; nlinarith [hs]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((sum_inv_sqrt_le hlt).trans ?_) hC
    have : 2 / √((M : ℝ) + 1) ≤ 2 / √(M : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hM0) (Real.sqrt_le_sqrt (by linarith))
    linarith
  have hNM : C / √(N : ℝ) ≤ C / √(M : ℝ) :=
    div_le_div_of_nonneg_left hC (Real.sqrt_pos.2 hM0) (Real.sqrt_le_sqrt (by exact_mod_cast hMN))
  have e3 : 3 * C / √(M : ℝ) = C / √(M : ℝ) + C * (2 / √(M : ℝ)) := by ring
  have hpos : 0 ≤ C * (2 / √(N : ℝ)) := by positivity
  have hCN : C / √(N : ℝ) = C * (2 / √(N : ℝ)) - C / √(N : ℝ) := by ring
  nlinarith

/-! ### The smoothed bound -/

/-- The error `Z(Y)` of the smoothed bound (RH up to `10⁸`). -/
noncomputable def Zsm (a δ Y : ℝ) : ℝ :=
  Y ^ (-(1 / 2) : ℝ) * LQW a 0 δ 1e8 + 2 * TailBH a δ 1e8 / 1e8 +
    2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi)

/-- `|E₁Λ(u)| ≤ log 4 + 4 + |log v|` for `u = Yv`, `Y ≥ 1`. -/
theorem abs_E1_scaled_le {Y v : ℝ} (hY : 1 ≤ Y) (hv : 0 < v) :
    |E₁Λ (Y * v)| ≤ Real.log 4 + 4 + |Real.log v| := by
  have hYv : 0 < Y * v := by positivity
  have h4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases le_or_gt 1 (Y * v) with h | h
  · have := E₁Λ.le h; have := E₁Λ.ge h
    rw [abs_le]; constructor <;> linarith [abs_nonneg (Real.log v)]
  · rw [E₁Λ_of_lt_one h, abs_neg, abs_of_neg (Real.log_neg hYv h), Real.log_mul (by linarith) hv.ne']
    have h1 := Real.log_nonneg hY
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have := neg_abs_le (Real.log v)
    linarith

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The smoothed bound**: `|∫₀^∞ (E₁Λ(Yv) + γ) φ(v) dv| ≤ Z(Y)` for `φ = gsm a 0 δ`, `Y ≥ 1`. -/
theorem abs_smoothed_E_le {a δ Y : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hY : 1 ≤ Y) :
    |∫ v in Ioi 0, (E₁Λ (Y * v) + Real.eulerMascheroniConstant) * gsm a 0 δ v| ≤ Zsm a δ Y := by
  set γ := Real.eulerMascheroniConstant with hγ
  have hY0 : 0 < Y := by linarith
  have hRH := rh_upto_1e8
  set M := Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp 0) with hM
  set Ψ : ℝ → ℝ := fun y => ∑' n : ℕ, Λ n * gsm a 0 δ (n / y) with hΨ
  have hg := integrableOn_gsm hδ ha
  have hE : ∀ Z : ℝ, 0 < Z → IntegrableOn (fun v => E₁Λ (Z * v) * gsm a 0 δ v) (Ioi 0) :=
    fun Z hZ => integrableOn_E₁Λ_mul_gsm hδ ha hZ
  -- the variation between `Y` and `Y₂`
  have hvar : ∀ Y2 : ℝ, Y ≤ Y2 → |∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y * v)) * gsm a 0 δ v| ≤
      (Y ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a 0 δ 1e8 + 2 * TailBH a δ 1e8 / 1e8 +
        2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi) := by
    intro Y2 hY2
    have hY20 : 0 < Y2 := by linarith
    have h1 := integral_dE1_gsm hδ ha hY0 hY2
    have h2 := abs_integral_psi_gsm_le (by norm_num) hRH hδ ha le_rfl hY hY2
    have hFi := integrableOn_psi_gsm_sub (Y2 := Y2) (by norm_num) hRH hδ ha le_rfl hY
    have hinv : IntegrableOn (fun y : ℝ => M * (1 / y)) (Ioc Y Y2) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_const.div continuousOn_id fun y hy =>
        (lt_of_lt_of_le hY0 hy.1).ne')
    have hΨi : IntegrableOn (fun y => Ψ y / y ^ 2) (Ioc Y Y2) := by
      refine (hFi.add hinv).congr_fun (fun y hy => ?_) measurableSet_Ioc
      have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1.le
      simp only [Pi.add_apply, hΨ, hM]; field_simp; ring
    have e : ∫ y in Ioc Y Y2, (Ψ y - M * y) / y ^ 2 = (∫ y in Ioc Y Y2, Ψ y / y ^ 2) -
        M * Real.log (Y2 / Y) := by
      have hlog : ∫ y in Ioc Y Y2, M * (1 / y) = M * Real.log (Y2 / Y) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hY2, integral_one_div_of_pos hY0 hY20]
      rw [← hlog, ← integral_sub hΨi hinv]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1.le
      field_simp
    rw [h1, ← e]
    exact h2
  -- the far end tends to `0`
  have hfar : Tendsto (fun Y2 : ℝ => ∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v) atTop (𝓝 0) := by
    have hlim := E1_tendsto.1
    set bound : ℝ → ℝ := fun v => (Real.log 4 + 4 + |γ|) * gsm a 0 δ v +
      2 * (v ^ (3 / 2 - 1 : ℝ) * gsm a 0 δ v + v ^ (1 / 2 - 1 : ℝ) * gsm a 0 δ v) with hbound
    have hbi : Integrable bound (volume.restrict (Ioi 0)) :=
      (hg.const_mul _).add (((integrableOn_rpow_mul_gsm hδ ha (3 / 2)).add
        (integrableOn_rpow_mul_gsm hδ ha (1 / 2))).const_mul 2)
    suffices h : Tendsto (fun Y2 : ℝ => ∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v) atTop
        (𝓝 (∫ _ in Ioi (0 : ℝ), (0 : ℝ))) by simpa using h
    refine tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun Y2 v => (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v) (f := fun _ => (0 : ℝ)) bound ?_ ?_ hbi ?_
    · refine Eventually.of_forall fun Y2 => ?_
      exact (((measurable_E₁Λ.comp (measurable_const_mul Y2)).add_const γ).aestronglyMeasurable).mul
        (continuousOn_gsm.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [eventually_ge_atTop 1] with Y2 hY2
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
      have hv0 : (0 : ℝ) < v := hv
      have hgv := gsm_nonneg (a := a) (b := 0) hδ ha v
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgv]
      have h1 := abs_E1_scaled_le hY2 hv0
      have h3 := abs_log_le_rpow hv0
      have e1 : (3 / 2 - 1 : ℝ) = 1 / 2 := by norm_num
      have e2 : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
      simp only [hbound, e1, e2]
      have : |E₁Λ (Y2 * v) + γ| ≤ Real.log 4 + 4 + |γ| + 2 * (v ^ (1 / 2 : ℝ) + v ^ (-(1 / 2) : ℝ)) := by
        have := abs_add_le (E₁Λ (Y2 * v)) γ; linarith
      calc |E₁Λ (Y2 * v) + γ| * gsm a 0 δ v ≤
            (Real.log 4 + 4 + |γ| + 2 * (v ^ (1 / 2 : ℝ) + v ^ (-(1 / 2) : ℝ))) * gsm a 0 δ v :=
            mul_le_mul_of_nonneg_right this hgv
        _ = _ := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
      have hv0 : (0 : ℝ) < v := hv
      have h := (hlim.comp (tendsto_id.atTop_mul_const hv0)).add_const γ
      simp only [Function.comp_def, id] at h
      rw [hγ, neg_add_cancel] at h
      simpa using h.mul_const (gsm a 0 δ v)
  -- combine
  have hsplit : ∀ Y2 : ℝ, 0 < Y2 → ∫ v in Ioi 0, (E₁Λ (Y * v) + γ) * gsm a 0 δ v =
      (∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v) -
        ∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y * v)) * gsm a 0 δ v := by
    intro Y2 hY20
    have i1 : IntegrableOn (fun v => (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v) (Ioi 0) :=
      ((hE Y2 hY20).add (hg.const_mul γ)).congr_fun (fun v _ => by simp only [Pi.add_apply]; ring)
        measurableSet_Ioi
    have i2 : IntegrableOn (fun v => (E₁Λ (Y2 * v) - E₁Λ (Y * v)) * gsm a 0 δ v) (Ioi 0) :=
      ((hE Y2 hY20).sub (hE Y hY0)).congr_fun (fun v _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioi
    rw [← integral_sub i1 i2]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => by ring
  have hbd : ∀ᶠ Y2 in atTop, |∫ v in Ioi 0, (E₁Λ (Y * v) + γ) * gsm a 0 δ v| ≤
      |∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v| +
        ((Y ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a 0 δ 1e8 + 2 * TailBH a δ 1e8 / 1e8 +
          2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi)) := by
    filter_upwards [eventually_ge_atTop Y] with Y2 hY2
    rw [hsplit Y2 (by linarith)]
    exact (abs_sub _ _).trans (add_le_add le_rfl (hvar Y2 hY2))
  have hR : Tendsto (fun Y2 : ℝ => |∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v| +
      ((Y ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a 0 δ 1e8 + 2 * TailBH a δ 1e8 / 1e8 +
        2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi))) atTop (𝓝 (0 + Zsm a δ Y)) := by
    have hp : Tendsto (fun Y2 : ℝ => Y2 ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h1 : Tendsto (fun Y2 : ℝ => |∫ v in Ioi 0, (E₁Λ (Y2 * v) + γ) * gsm a 0 δ v|) atTop (𝓝 0) := by
      have := (continuous_abs.tendsto 0).comp hfar
      rw [abs_zero] at this
      exact this
    have h2 : Tendsto (fun Y2 : ℝ => (Y ^ (-(1 / 2) : ℝ) + Y2 ^ (-(1 / 2) : ℝ)) * LQW a 0 δ 1e8 +
        2 * TailBH a δ 1e8 / 1e8 + 2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi)) atTop
        (𝓝 (Zsm a δ Y)) := by
      have := (((tendsto_const_nhds (x := Y ^ (-(1 / 2) : ℝ))).add hp).mul_const (LQW a 0 δ 1e8)).add
        (tendsto_const_nhds (x := 2 * TailBH a δ 1e8 / 1e8 +
          2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg a 0 δ / (2 * Real.pi)))
      unfold Zsm
      simpa [add_assoc] using this
    exact h1.add h2
  rw [zero_add] at hR
  exact ge_of_tendsto hR hbd

/-! ### From the smoothed bound to a pointwise bound -/

/-- `φ(v) ≤ e^{1/2} (e^a/v)^{1/δ}` for `v > 0` (`b = 0`); it is used for `v > e^a`. -/
theorem gsm_le_rpow_hi {a δ v : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hv0 : 0 < v) :
    gsm a 0 δ v ≤ Real.exp (1 / 2) * (Real.exp a / v) ^ (1 / δ) := by
  set z₀ := (0 - Real.log v) / δ with hz₀
  set z₁ := (a - Real.log v) / δ with hz₁
  have hz : z₀ ≤ z₁ := div_le_div_of_nonneg_right (by linarith) hδ.le
  have hint : Integrable (fun z : ℝ => gpdf z * Real.exp ((-1) * z)) := integrable_gpdf_mul_exp (-1)
  have hint' : Integrable (fun z : ℝ => gpdf z * Real.exp (z₁ - z)) := by
    refine (hint.mul_const (Real.exp z₁)).congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h1 : gsm a 0 δ v ≤ ∫ z in z₀..z₁, gpdf z * Real.exp (z₁ - z) := by
    unfold gsm
    refine intervalIntegral.integral_mono_on hz (continuous_gpdf.intervalIntegrable _ _)
      (hint'.intervalIntegrable) fun z hz' => ?_
    have : 1 ≤ Real.exp (z₁ - z) := Real.one_le_exp (by linarith [hz'.2])
    nlinarith [gpdf_nonneg z]
  have h2 : ∫ z in z₀..z₁, gpdf z * Real.exp (z₁ - z) ≤ ∫ z, gpdf z * Real.exp (z₁ - z) := by
    rw [intervalIntegral.integral_of_le hz]
    exact setIntegral_le_integral hint' (Eventually.of_forall fun z => by
      have := gpdf_nonneg z; positivity)
  have h3 : ∫ z, gpdf z * Real.exp (z₁ - z) = Real.exp z₁ * Real.exp (1 / 2) := by
    have e : ∀ z : ℝ, gpdf z * Real.exp (z₁ - z) = Real.exp z₁ * (gpdf z * Real.exp ((-1) * z)) := by
      intro z; rw [mul_left_comm, ← Real.exp_add]; ring_nf
    simp_rw [e]
    rw [integral_const_mul, integral_gpdf_mul_exp]; norm_num
  have h4 : Real.exp z₁ = (Real.exp a / v) ^ (1 / δ) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div (Real.exp_pos a).ne' hv0.ne', Real.log_exp,
      hz₁]
    congr 1; ring
  calc gsm a 0 δ v ≤ Real.exp z₁ * Real.exp (1 / 2) := h1.trans (h2.trans h3.le)
    _ = Real.exp (1 / 2) * (Real.exp a / v) ^ (1 / δ) := by rw [h4, mul_comm]

/-- **The edge term in a window**: if `|E₁Λ(Yv) − E₁Λ(Y)| ≤ A` for `e^{−κ} ≤ v ≤ e^{a+κ}`, then
`∫₀^∞ |E₁Λ(Yv) − E₁Λ(Y)| φ(v) dv ≤ A M(1) + (22 + 36 e^{a+κ}) δ e^{−κ/δ}` (`δ ≤ 1/2`). -/
theorem edge_le_win {a δ κ Y A : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (ha : 0 ≤ a) (hκ : 0 < κ)
    (hY : 1 ≤ Y) (hA : 0 ≤ A)
    (hwin : ∀ v : ℝ, Real.exp (-κ) ≤ v → v ≤ Real.exp (a + κ) → |E₁Λ (Y * v) - E₁Λ Y| ≤ A) :
    ∫ v in Ioi 0, |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v ≤
      A * (Real.exp (δ ^ 2 / 2) * (Real.exp a - 1)) +
        (22 + 36 * Real.exp (a + κ)) * δ * Real.exp (-(κ / δ)) := by
  have hY0 : 0 < Y := by linarith
  set f : ℝ → ℝ := fun v => |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v with hf
  have hg := integrableOn_gsm (a := a) (b := 0) hδ ha
  have hfint : IntegrableOn f (Ioi 0) := by
    have : IntegrableOn (fun v => |E₁Λ (Y * v) * gsm a 0 δ v - E₁Λ Y * gsm a 0 δ v|) (Ioi 0) :=
      ((integrableOn_E₁Λ_mul_gsm (a := a) (b := 0) hδ ha hY0).sub (hg.const_mul (E₁Λ Y))).abs
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only [hf]
    rw [← sub_mul, abs_mul, abs_of_nonneg (gsm_nonneg hδ ha v)]
  set v₀ := Real.exp (-κ) with hv₀
  set v₁ := Real.exp (a + κ) with hv₁
  have hv₀0 : 0 < v₀ := Real.exp_pos _
  have hv₀1 : v₀ ≤ v₁ := Real.exp_le_exp.2 (by linarith)
  -- split `(0, ∞) = (0, v₀] ∪ (v₀, v₁] ∪ (v₁, ∞)`
  have hsplit : ∫ v in Ioi 0, f v = (∫ v in Ioc 0 v₀, f v) + (∫ v in Ioc v₀ v₁, f v) + ∫ v in Ioi v₁, f v := by
    rw [← Ioc_union_Ioi_eq_Ioi hv₀0.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hfint.mono_set Ioc_subset_Ioi_self) (hfint.mono_set (Ioi_subset_Ioi hv₀0.le)),
      ← Ioc_union_Ioi_eq_Ioi hv₀1, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((hfint.mono_set (Ioi_subset_Ioi hv₀0.le)).mono_set Ioc_subset_Ioi_self)
      (hfint.mono_set (Ioi_subset_Ioi (hv₀0.le.trans hv₀1)))]
    ring
  have hr : -1 < 1 / δ - 1 / 2 := by have : 0 < 1 / δ := by positivity
                                     linarith
  have hdinv : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hexpκ : Real.exp (-(κ / δ)) = v₀ ^ (1 / δ) := by
    rw [hv₀, ← Real.exp_mul]; congr 1; field_simp
  -- `(0, v₀]`
  have hlow : ∫ v in Ioc 0 v₀, f v ≤ 22 * δ * Real.exp (-(κ / δ)) := by
    set C := (2 * Real.log 4 + 10) * Real.exp (1 / 2) with hC
    have hv₀le : v₀ ≤ 1 := by rw [hv₀]; exact Real.exp_le_one_iff.2 (by linarith)
    have hgint : IntegrableOn (fun v : ℝ => C * v ^ (1 / δ - 1 / 2)) (Ioc 0 v₀) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hv₀0.le).1
        ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul C)
    have hpt : ∀ v ∈ Ioc (0 : ℝ) v₀, f v ≤ C * v ^ (1 / δ - 1 / 2) := by
      intro v hv
      have hv0 : 0 < v := hv.1
      have hE := abs_E1_sub_le_small hY hv0 (hv.2.trans hv₀le)
      have hG := gsm_le_rpow (a := a) hδ ha hv0
      have hG0 := gsm_nonneg (a := a) (b := 0) hδ ha v
      have e : v ^ (1 / δ - 1 / 2) = v ^ (-(1 / 2) : ℝ) * v ^ (1 / δ) := by
        rw [← Real.rpow_add hv0]; ring_nf
      rw [e]
      calc f v = |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v := rfl
        _ ≤ ((2 * Real.log 4 + 10) * v ^ (-(1 / 2) : ℝ)) * (Real.exp (1 / 2) * v ^ (1 / δ)) :=
          mul_le_mul hE hG hG0 (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity)
        _ = _ := by rw [hC]; ring
    have hcalc : ∫ v in Ioc (0 : ℝ) v₀, C * v ^ (1 / δ - 1 / 2) =
        C * (v₀ ^ (1 / δ - 1 / 2 + 1) / (1 / δ - 1 / 2 + 1)) := by
      rw [← intervalIntegral.integral_of_le hv₀0.le, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl hr), Real.zero_rpow (by linarith)]
      ring
    refine (setIntegral_mono_on (hfint.mono_set Ioc_subset_Ioi_self) hgint measurableSet_Ioc hpt).trans ?_
    rw [hcalc]
    have hl4 := log_four_le
    have he := exp_half_le
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hC21 : C ≤ 21.1 := by rw [hC]; nlinarith [Real.exp_pos (1 / 2)]
    have hden : 0 < 1 / δ - 1 / 2 + 1 := by linarith
    have hpow : v₀ ^ (1 / δ - 1 / 2 + 1) ≤ v₀ ^ (1 / δ) :=
      Real.rpow_le_rpow_of_exponent_ge hv₀0 hv₀le (by linarith)
    have hq : v₀ ^ (1 / δ - 1 / 2 + 1) / (1 / δ - 1 / 2 + 1) ≤ δ * v₀ ^ (1 / δ) := by
      rw [div_le_iff₀ hden]
      have hp0 : 0 ≤ v₀ ^ (1 / δ) := (Real.rpow_pos_of_pos hv₀0 _).le
      have : δ * (1 / δ - 1 / 2 + 1) = 1 + δ / 2 := by field_simp; ring
      nlinarith
    rw [hexpκ]
    have hC0 : 0 ≤ C := by positivity
    calc C * (v₀ ^ (1 / δ - 1 / 2 + 1) / (1 / δ - 1 / 2 + 1)) ≤ C * (δ * v₀ ^ (1 / δ)) :=
          mul_le_mul_of_nonneg_left hq hC0
      _ ≤ 22 * (δ * v₀ ^ (1 / δ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 22 * δ * v₀ ^ (1 / δ) := by ring
  -- `(v₀, v₁]`
  have hmid : ∫ v in Ioc v₀ v₁, f v ≤ A * (Real.exp (δ ^ 2 / 2) * (Real.exp a - 1)) := by
    have hpt : ∀ v ∈ Ioc v₀ v₁, f v ≤ A * gsm a 0 δ v := by
      intro v hv
      exact mul_le_mul_of_nonneg_right (hwin v hv.1.le hv.2) (gsm_nonneg hδ ha v)
    refine (setIntegral_mono_on (hfint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hv₀0.le)))
      ((hg.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hv₀0.le))).const_mul A)
      measurableSet_Ioc hpt).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA
    have := integral_gsm (a := a) (b := 0) hδ ha
    rw [Real.exp_zero] at this
    rw [← this]
    exact setIntegral_mono_set hg (Eventually.of_forall fun v => gsm_nonneg hδ ha v)
      (Eventually.of_forall (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hv₀0.le)))
  -- `(v₁, ∞)`
  have hhigh : ∫ v in Ioi v₁, f v ≤ 36 * Real.exp (a + κ) * δ * Real.exp (-(κ / δ)) := by
    have hv₁0 : 0 < v₁ := Real.exp_pos _
    set C := 2 * (Real.log 4 + 4) * Real.exp (1 / 2) * Real.exp a ^ (1 / δ) with hC
    have hr' : -(1 / δ) < -1 := by linarith
    have hgint : IntegrableOn (fun v : ℝ => C * v ^ (-(1 / δ))) (Ioi v₁) :=
      (integrableOn_Ioi_rpow_of_lt hr' hv₁0).const_mul C
    have hpt : ∀ v ∈ Ioi v₁, f v ≤ C * v ^ (-(1 / δ)) := by
      intro v hv
      have hv1 : v₁ < v := hv
      have hv0 : 0 < v := by linarith
      have hYv : 1 ≤ Y * v := by
        have : (1 : ℝ) ≤ v := le_trans (Real.one_le_exp (by linarith)) hv1.le
        nlinarith
      have hE : |E₁Λ (Y * v) - E₁Λ Y| ≤ 2 * (Real.log 4 + 4) := by
        have a1 := E₁Λ.le hYv; have a2 := E₁Λ.ge hYv; have a3 := E₁Λ.le hY; have a4 := E₁Λ.ge hY
        have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        rw [abs_le]; constructor <;> linarith
      have hG := gsm_le_rpow_hi (a := a) hδ ha hv0
      have hG0 := gsm_nonneg (a := a) (b := 0) hδ ha v
      have e : (Real.exp a / v) ^ (1 / δ) = Real.exp a ^ (1 / δ) * v ^ (-(1 / δ)) := by
        rw [Real.div_rpow (Real.exp_pos a).le hv0.le, Real.rpow_neg hv0.le, div_eq_mul_inv]
      rw [e] at hG
      calc f v = |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v := rfl
        _ ≤ (2 * (Real.log 4 + 4)) * (Real.exp (1 / 2) * (Real.exp a ^ (1 / δ) * v ^ (-(1 / δ)))) :=
          mul_le_mul hE hG hG0 (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity)
        _ = _ := by rw [hC]; ring
    refine (setIntegral_mono_on (hfint.mono_set (Ioi_subset_Ioi (hv₀0.le.trans hv₀1))) hgint
      measurableSet_Ioi hpt).trans ?_
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hr' hv₁0]
    -- `C · v₁^{1 − 1/δ}/(1/δ − 1) = 2(log 4 + 4) e^{1/2} e^{a+κ} e^{−κ/δ}/(1/δ − 1)`
    have hv₁pow : Real.exp a ^ (1 / δ) * v₁ ^ (-(1 / δ) + 1) = v₁ * Real.exp (-(κ / δ)) := by
      rw [hv₁, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; field_simp; ring
    have hden : 0 < 1 / δ - 1 := by linarith
    have e : C * (-v₁ ^ (-(1 / δ) + 1) / (-(1 / δ) + 1)) =
        2 * (Real.log 4 + 4) * Real.exp (1 / 2) * (v₁ * Real.exp (-(κ / δ))) / (1 / δ - 1) := by
      rw [hC, ← hv₁pow]
      have : (-(1 / δ) + 1) = -(1 / δ - 1) := by ring
      rw [this]; field_simp
    rw [e, div_le_iff₀ hden]
    have hl4 := log_four_le
    have he := exp_half_le
    have hpos : 0 ≤ v₁ * Real.exp (-(κ / δ)) := by positivity
    have hK : 2 * (Real.log 4 + 4) * Real.exp (1 / 2) ≤ 18 := by
      have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith [Real.exp_pos (1 / 2)]
    have hδ' : 18 ≤ 36 * δ * (1 / δ - 1) := by
      have : δ * (1 / δ - 1) = 1 - δ := by field_simp
      nlinarith
    rw [← hv₁]
    nlinarith
  rw [hsplit]
  have e1 : (22 + 36 * Real.exp (a + κ)) * δ * Real.exp (-(κ / δ)) =
      22 * δ * Real.exp (-(κ / δ)) + 36 * Real.exp (a + κ) * δ * Real.exp (-(κ / δ)) := by ring
  rw [e1]
  linarith

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The pointwise bound from a window**: if `|E₁Λ(Yv) − E₁Λ(Y)| ≤ A` for `e^{−κ} ≤ v ≤ e^{a+κ}`,
then `|E₁Λ(Y) + γ| ≤ A + (Z(Y) + (22 + 36 e^{a+κ}) δ e^{−κ/δ})/M(1)`. -/
theorem E_bound_win {a δ κ Y A : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (ha : 0 < a) (hκ : 0 < κ)
    (hY : 1 ≤ Y) (hA : 0 ≤ A)
    (hwin : ∀ v : ℝ, Real.exp (-κ) ≤ v → v ≤ Real.exp (a + κ) → |E₁Λ (Y * v) - E₁Λ Y| ≤ A) :
    |E₁Λ Y + Real.eulerMascheroniConstant| ≤
      A + (Zsm a δ Y + (22 + 36 * Real.exp (a + κ)) * δ * Real.exp (-(κ / δ))) /
        (Real.exp (δ ^ 2 / 2) * (Real.exp a - 1)) := by
  set γ := Real.eulerMascheroniConstant with hγ
  have hY0 : 0 < Y := by linarith
  set M1 := Real.exp (δ ^ 2 / 2) * (Real.exp a - 1) with hM1
  have hM10 : 0 < M1 := by
    have : 1 < Real.exp a := Real.one_lt_exp_iff.2 ha
    rw [hM1]; exact mul_pos (Real.exp_pos _) (by linarith)
  have hg := integrableOn_gsm (a := a) (b := 0) hδ ha.le
  have hgM : ∫ v in Ioi 0, gsm a 0 δ v = M1 := by
    rw [integral_gsm hδ ha.le, Real.exp_zero]
  have hS := abs_smoothed_E_le hδ ha.le hY
  have hedge := edge_le_win hδ hδ2 ha.le hκ hY hA hwin
  have hE := integrableOn_E₁Λ_mul_gsm (a := a) (b := 0) hδ ha.le hY0
  have i1 : IntegrableOn (fun v => (E₁Λ (Y * v) + γ) * gsm a 0 δ v) (Ioi 0) :=
    (hE.add (hg.const_mul γ)).congr_fun (fun v _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have i2 : IntegrableOn (fun v => (E₁Λ (Y * v) - E₁Λ Y) * gsm a 0 δ v) (Ioi 0) :=
    (hE.sub (hg.const_mul (E₁Λ Y))).congr_fun (fun v _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hid : M1 * (E₁Λ Y + γ) = (∫ v in Ioi 0, (E₁Λ (Y * v) + γ) * gsm a 0 δ v) -
      ∫ v in Ioi 0, (E₁Λ (Y * v) - E₁Λ Y) * gsm a 0 δ v := by
    rw [← integral_sub i1 i2, ← hgM, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => by ring
  have h2 : |∫ v in Ioi 0, (E₁Λ (Y * v) - E₁Λ Y) * gsm a 0 δ v| ≤
      ∫ v in Ioi 0, |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [abs_mul, abs_of_nonneg (gsm_nonneg hδ ha.le v)]
  have hmain : M1 * |E₁Λ Y + γ| ≤ Zsm a δ Y + (A * M1 +
      (22 + 36 * Real.exp (a + κ)) * δ * Real.exp (-(κ / δ))) := by
    rw [← abs_of_pos hM10, ← abs_mul, hid, abs_of_pos hM10]
    exact (abs_sub _ _).trans (add_le_add hS (h2.trans hedge))
  rw [add_div' _ _ _ hM10.ne', le_div_iff₀ hM10]
  linarith

end TernaryGoldbach.Prelim
