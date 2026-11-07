import TernaryGoldbach.Prelim.PNTMertens
import TernaryGoldbach.Explicit.PsiExplicit

/-!
# `E₁Λ` over long ranges from the smoothed explicit formula

`E₁Λ(t) = Σ_{n ≤ t} Λ(n)/n − log t`. Its variation `E₁Λ(Y₂) − E₁Λ(Y₁)` is controlled by the
explicit formula for the Gaussian-smoothed sum `Ψ(y) = Σ Λ(n) φ(n/y)`, `φ = gsm a b δ`, integrated
against `dy/y²`. With `S(u) = Σ_{n ≤ u} Λ(n)/n` and `M = ∫₀^∞ φ = e^{δ²/2}(e^a − e^b)`:
* `∫₀^∞ (S(Y₂v) − S(Y₁v)) φ(v) dv = ∫_{Y₁}^{Y₂} Ψ(y)/y² dy` (`integral_dS_gsm`: both sides are
  `Σ_n Λ(n)/n ∫_{n/Y₂}^{n/Y₁} φ`);
* hence `∫₀^∞ (E₁Λ(Y₂v) − E₁Λ(Y₁v)) φ(v) dv = ∫_{Y₁}^{Y₂} (Ψ(y) − M y)/y² dy`, and
  `M |E₁Λ(Y₂) − E₁Λ(Y₁)| ≤ 2α/√Y₁ + β log(Y₂/Y₁) + edge(Y₁) + edge(Y₂)` if
  `|Ψ(y) − M y| ≤ α√y + βy` on `[Y₁, Y₂]` (`E1_window`), where
  `edge(Y) = ∫₀^∞ |E₁Λ(Yv) − E₁Λ(Y)| φ(v) dv`;
* for `b = 0`, `edge(Y) ≤ (2A + 2B/⌊Y⌋)M + 2B M(3/2) + 21.1δ` if
  `|E₁Λ(t) − E₁Λ(⌊Y⌋)| ≤ A + B log(t/⌊Y⌋)` for `t ≥ ⌊Y⌋` (`edge_le`; below `v = 1` the
  Chernoff bound `φ(v) ≤ e^{1/2} v^{1/δ}`, `gsm_le_rpow`).

The zeros of `ζ` enter only through `α` and `β`, and the pointwise errors of `ψ` only through `A`
and `B` at the two ends: nothing is integrated over `[Y₁, Y₂]`.
-/

open MeasureTheory Set Filter Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

/-! ### The smoothing `gsm a b δ` on `(0, ∞)` -/

theorem gsm_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (u : ℝ) : 0 ≤ gsm a b δ u := by
  unfold gsm
  exact intervalIntegral.integral_nonneg (div_le_div_of_nonneg_right (by linarith) hδ.le)
    fun z _ => gpdf_nonneg z

theorem continuousOn_gsm {a b δ : ℝ} : ContinuousOn (gsm a b δ) (Ioi 0) :=
  fun _ hu => (continuous_gsm hu).continuousWithinAt

/-- `v ↦ v^{s−1} φ(v)` is integrable on `(0, ∞)` for every real `s`. -/
theorem integrableOn_rpow_mul_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (s : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ (s - 1) * gsm a b δ v) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((s : ℂ) - 1) • ((gsm a b δ t : ℝ) : ℂ)‖) (Ioi 0) :=
    (mellinConvergent_gsm hδ hab (s : ℂ)).norm
  refine h.congr_fun (fun v hv => ?_) measurableSet_Ioi
  have hv0 : (0 : ℝ) < v := hv
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gsm_nonneg hδ hab v)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv0]
  simp

theorem integrableOn_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) :
    IntegrableOn (gsm a b δ) (Ioi 0) := by
  refine (integrableOn_rpow_mul_gsm hδ hab 1).congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp

/-- `∫₀^∞ v^{s−1} φ(v) dv = e^{δ²s²/2}(e^{as} − e^{bs})/s` for real `s ≠ 0`. -/
theorem integral_rpow_mul_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) {s : ℝ} (hs : s ≠ 0) :
    ∫ v in Ioi 0, v ^ (s - 1) * gsm a b δ v =
      Real.exp (δ ^ 2 * s ^ 2 / 2) * (Real.exp (a * s) - Real.exp (b * s)) / s := by
  have h := mellin_gsm hδ hab (s : ℂ)
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [Mg, integral_exp_mul_complex hs'] at h
  rw [mellin] at h
  have e1 : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((s : ℂ) - 1) • ((gsm a b δ t : ℝ) : ℂ) =
      ((∫ v in Ioi 0, v ^ (s - 1) * gsm a b δ v : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [smul_eq_mul]
    rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0.le]
    push_cast; ring
  rw [e1] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  rw [mul_comm (s : ℂ) (a : ℂ), mul_comm (s : ℂ) (b : ℂ)]
  ring_nf

/-- `∫₀^∞ φ = e^{δ²/2}(e^a − e^b)`. -/
theorem integral_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) :
    ∫ v in Ioi 0, gsm a b δ v = Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) := by
  have h := integral_rpow_mul_gsm hδ hab (s := 1) one_ne_zero
  simp only [sub_self, Real.rpow_zero, one_mul, one_pow, mul_one, div_one] at h
  exact h

/-! ### The Chernoff bound below `v = 1` (`b = 0`) -/

/-- `φ(v) ≤ e^{1/2} v^{1/δ}` for `v > 0` (`b = 0`, `a ≥ 0`); it is used for `v ≤ 1`. -/
theorem gsm_le_rpow {a δ v : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hv0 : 0 < v) :
    gsm a 0 δ v ≤ Real.exp (1 / 2) * v ^ (1 / δ) := by
  set z₀ := (0 - Real.log v) / δ with hz₀
  set z₁ := (a - Real.log v) / δ with hz₁
  have hz : z₀ ≤ z₁ := div_le_div_of_nonneg_right (by linarith) hδ.le
  have hint : Integrable (fun z : ℝ => gpdf z * Real.exp (1 * z)) := integrable_gpdf_mul_exp 1
  have hint' : Integrable (fun z : ℝ => gpdf z * Real.exp (z - z₀)) := by
    refine (hint.mul_const (Real.exp (-z₀))).congr (Eventually.of_forall fun z => ?_)
    simp only [one_mul]
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h1 : gsm a 0 δ v ≤ ∫ z in z₀..z₁, gpdf z * Real.exp (z - z₀) := by
    unfold gsm
    refine intervalIntegral.integral_mono_on hz (continuous_gpdf.intervalIntegrable _ _)
      (hint'.intervalIntegrable) fun z hz' => ?_
    have : 1 ≤ Real.exp (z - z₀) := Real.one_le_exp (by linarith [hz'.1])
    nlinarith [gpdf_nonneg z]
  have h2 : ∫ z in z₀..z₁, gpdf z * Real.exp (z - z₀) ≤ ∫ z, gpdf z * Real.exp (z - z₀) := by
    rw [intervalIntegral.integral_of_le hz]
    exact setIntegral_le_integral hint' (Eventually.of_forall fun z => by
      have := gpdf_nonneg z; positivity)
  have h3 : ∫ z, gpdf z * Real.exp (z - z₀) = Real.exp (-z₀) * Real.exp (1 / 2) := by
    have e : ∀ z : ℝ, gpdf z * Real.exp (z - z₀) = Real.exp (-z₀) * (gpdf z * Real.exp (1 * z)) := by
      intro z; rw [one_mul, mul_left_comm, ← Real.exp_add]; ring_nf
    simp_rw [e]
    rw [integral_const_mul, integral_gpdf_mul_exp]; norm_num
  have h4 : Real.exp (-z₀) = v ^ (1 / δ) := by
    rw [Real.rpow_def_of_pos hv0, hz₀]; congr 1; ring
  calc gsm a 0 δ v ≤ Real.exp (-z₀) * Real.exp (1 / 2) := h1.trans (h2.trans h3.le)
    _ = Real.exp (1 / 2) * v ^ (1 / δ) := by rw [h4, mul_comm]

/-! ### `E₁Λ` is measurable, with logarithmic growth -/

theorem measurable_E₁Λ : Measurable E₁Λ := by
  have h : Measurable fun x : ℝ => ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / (d : ℝ) :=
    (measurable_from_nat (f := fun N : ℕ => ∑ d ∈ Ioc 0 N, (Λ d) / (d : ℝ))).comp Nat.measurable_floor
  exact h.sub Real.measurable_log

theorem E₁Λ_of_lt_one {u : ℝ} (hu : u < 1) : E₁Λ u = -Real.log u := by
  have : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.2 hu
  simp [E₁Λ, this]

/-- `|E₁Λ(u)| ≤ log 4 + 4 + |log u|` for `u > 0`. -/
theorem abs_E₁Λ_le {u : ℝ} (hu : 0 < u) : |E₁Λ u| ≤ Real.log 4 + 4 + |Real.log u| := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases le_or_gt 1 u with h1 | h1
  · have := E₁Λ.le h1; have := E₁Λ.ge h1
    rw [abs_le]; constructor <;> linarith [abs_nonneg (Real.log u)]
  · rw [E₁Λ_of_lt_one h1, abs_neg]; linarith

/-- `|log v| ≤ 2(v^{1/2} + v^{−1/2})` for `v > 0`. -/
theorem abs_log_le_rpow {v : ℝ} (hv : 0 < v) :
    |Real.log v| ≤ 2 * (v ^ (1 / 2 : ℝ) + v ^ (-(1 / 2) : ℝ)) := by
  have hp1 : 0 < v ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hv _
  have hp2 : 0 < v ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hv _
  rcases le_or_gt 1 v with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_rpow_div hv.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith [show v ^ (1 / 2 : ℝ) / (1 / 2) = 2 * v ^ (1 / 2 : ℝ) by ring]
  · rw [abs_of_neg (Real.log_neg hv h1)]
    have := Real.log_le_rpow_div (inv_pos.2 hv).le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_inv, Real.inv_rpow hv.le, ← Real.rpow_neg hv.le] at this
    linarith [show v ^ (-(1 / 2) : ℝ) / (1 / 2) = 2 * v ^ (-(1 / 2) : ℝ) by ring]

/-- `v ↦ E₁Λ(Yv) φ(v)` is integrable on `(0, ∞)`. -/
theorem integrableOn_E₁Λ_mul_gsm {a b δ Y : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hY : 0 < Y) :
    IntegrableOn (fun v => E₁Λ (Y * v) * gsm a b δ v) (Ioi 0) := by
  set C := Real.log 4 + 4 + |Real.log Y| with hC
  have hg1 := integrableOn_gsm hδ hab
  have hg2 := integrableOn_rpow_mul_gsm hδ hab (3 / 2)
  have hg3 := integrableOn_rpow_mul_gsm hδ hab (1 / 2)
  have hbound : IntegrableOn (fun v : ℝ => C * gsm a b δ v +
      2 * (v ^ (3 / 2 - 1 : ℝ) * gsm a b δ v + v ^ (1 / 2 - 1 : ℝ) * gsm a b δ v)) (Ioi 0) :=
    (hg1.const_mul C).add ((hg2.add hg3).const_mul 2)
  refine hbound.mono' ?_ ?_
  · exact ((measurable_E₁Λ.comp (measurable_const_mul Y)).aestronglyMeasurable).mul
      (continuousOn_gsm.aestronglyMeasurable measurableSet_Ioi)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have hg := gsm_nonneg (a := a) (b := b) hδ hab v
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg]
    have h1 := abs_E₁Λ_le (mul_pos hY hv0)
    have h2 : |Real.log (Y * v)| ≤ |Real.log Y| + |Real.log v| := by
      rw [Real.log_mul hY.ne' hv0.ne']; exact abs_add_le _ _
    have h3 := abs_log_le_rpow hv0
    have e1 : (3 / 2 - 1 : ℝ) = 1 / 2 := by norm_num
    have e2 : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
    rw [e1, e2]
    have : |E₁Λ (Y * v)| ≤ C + 2 * (v ^ (1 / 2 : ℝ) + v ^ (-(1 / 2) : ℝ)) := by rw [hC]; linarith
    calc |E₁Λ (Y * v)| * gsm a b δ v ≤ (C + 2 * (v ^ (1 / 2 : ℝ) + v ^ (-(1 / 2) : ℝ))) * gsm a b δ v :=
          mul_le_mul_of_nonneg_right this hg
      _ = _ := by ring

/-! ### The identity `∫₀^∞ (S(Y₂v) − S(Y₁v)) φ(v) dv = ∫_{Y₁}^{Y₂} Ψ(y)/y² dy` -/

/-- `S(u) = Σ_{n ≤ u} Λ(n)/n`, so that `E₁Λ(u) = S(u) − log u`. -/
noncomputable def Smv (u : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊u⌋₊, (Λ d) / (d : ℝ)

theorem E₁Λ_eq_Smv (u : ℝ) : E₁Λ u = Smv u - Real.log u := rfl

/-- The substitution `v = n/y`: `∫_{Y₁}^{Y₂} φ(n/y)/y² dy = (1/n) ∫_{n/Y₂}^{n/Y₁} φ`. -/
theorem integral_gsm_div_sq {a b δ Y1 Y2 : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y in Y1..Y2, gsm a b δ (n / y) / y ^ 2 = (1 / n) * ∫ v in (n / Y2)..(n / Y1), gsm a b δ v := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ y ∈ uIcc Y1 Y2, 0 < y := fun y hy => by
    rw [uIcc_of_le hY12] at hy; linarith [hy.1]
  have hderiv : ∀ y ∈ uIcc Y1 Y2, HasDerivAt (fun y : ℝ => (n : ℝ) / y) (-(n : ℝ) / y ^ 2) y := by
    intro y hy
    have hy0 := hpos y hy
    have := (hasDerivAt_inv hy0.ne').const_mul (n : ℝ)
    convert this using 1
    · funext y; rw [div_eq_mul_inv]
    · field_simp
  have hcont' : ContinuousOn (fun y : ℝ => -(n : ℝ) / y ^ 2) (uIcc Y1 Y2) :=
    ContinuousOn.div continuousOn_const (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hpos y hy).ne'
  have hg : ContinuousOn (gsm a b δ) ((fun y : ℝ => (n : ℝ) / y) '' uIcc Y1 Y2) := by
    refine continuousOn_gsm.mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact div_pos hn0 (hpos y hy)
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hg
  have e : ∫ y in Y1..Y2, gsm a b δ (n / y) / y ^ 2 =
      (-(1 / n)) * ∫ y in Y1..Y2, (gsm a b δ ∘ fun y : ℝ => (n : ℝ) / y) y * (-(n : ℝ) / y ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 := hpos y hy
    simp only [Function.comp]
    field_simp
  rw [e, h, intervalIntegral.integral_symm]
  ring

/-- The `n`-th term on the `v` side: `Λ(n)/n · φ(v)` on `[n/Y₂, n/Y₁)`. -/
noncomputable def Fv (a b δ Y1 Y2 : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  (Ico ((n : ℝ) / Y2) (n / Y1)).indicator (fun v => Λ n / n * gsm a b δ v) v

/-- The `n`-th term on the `y` side. -/
noncomputable def Gy (a b δ : ℝ) (n : ℕ) (y : ℝ) : ℝ := Λ n * gsm a b δ (n / y) / y ^ 2

theorem mem_Ico_iff_mem_Ioc {Y1 Y2 v : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) (hv : 0 < v) (n : ℕ) :
    v ∈ Ico ((n : ℝ) / Y2) (n / Y1) ↔ n ∈ Finset.Ioc ⌊Y1 * v⌋₊ ⌊Y2 * v⌋₊ := by
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  rw [Set.mem_Ico, Finset.mem_Ioc, div_le_iff₀ hY2, lt_div_iff₀ hY1,
    Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity), mul_comm Y1 v, mul_comm Y2 v]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem Fv_eq_zero {a b δ Y1 Y2 v : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) (hv : 0 < v) {n : ℕ}
    (hn : n ∉ Finset.Ioc ⌊Y1 * v⌋₊ ⌊Y2 * v⌋₊) : Fv a b δ Y1 Y2 n v = 0 := by
  rw [Fv, indicator_of_notMem fun h => hn ((mem_Ico_iff_mem_Ioc hY1 hY12 hv n).1 h)]

theorem tsum_Fv {a b δ Y1 Y2 v : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) (hv : 0 < v) :
    ∑' n : ℕ, Fv a b δ Y1 Y2 n v = (Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v := by
  rw [tsum_eq_sum (s := Finset.Ioc ⌊Y1 * v⌋₊ ⌊Y2 * v⌋₊) fun n hn => Fv_eq_zero hY1 hY12 hv hn]
  have hfl : ⌊Y1 * v⌋₊ ≤ ⌊Y2 * v⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hY12 hv.le)
  rw [Smv, Smv, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl, add_sub_cancel_left, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Fv, indicator_of_mem ((mem_Ico_iff_mem_Ioc hY1 hY12 hv n).2 hn)]

theorem Fv_nonneg {a b δ Y1 Y2 : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (n : ℕ) (v : ℝ) :
    0 ≤ Fv a b δ Y1 Y2 n v := by
  unfold Fv
  refine indicator_nonneg (fun v _ => ?_) v
  have := gsm_nonneg (a := a) (b := b) hδ hab v
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

theorem Gy_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (n : ℕ) (y : ℝ) : 0 ≤ Gy a b δ n y := by
  unfold Gy
  have := gsm_nonneg (a := a) (b := b) hδ hab (n / y)
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

theorem integrableOn_Fv {a b δ Y1 Y2 : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (n : ℕ) :
    IntegrableOn (Fv a b δ Y1 Y2 n) (Ioi 0) :=
  ((integrableOn_gsm hδ hab).const_mul (Λ n / n)).indicator measurableSet_Ico

theorem integrableOn_Gy {a b δ Y1 Y2 : ℝ} (hY1 : 0 < Y1) (n : ℕ) :
    IntegrableOn (Gy a b δ n) (Ioc Y1 Y2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Gy a b δ 0 = fun _ => 0 := funext fun y => by simp [Gy]
    rw [this]; exact integrableOn_zero
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  have hpos : ∀ y ∈ Icc Y1 Y2, 0 < y := fun y hy => lt_of_lt_of_le hY1 hy.1
  refine ContinuousOn.div (continuousOn_const.mul ?_) (continuousOn_pow 2)
    fun y hy => pow_ne_zero 2 (hpos y hy).ne'
  refine continuousOn_gsm.comp (continuousOn_const.div continuousOn_id fun y hy => (hpos y hy).ne') ?_
  intro y hy; exact div_pos hn0 (hpos y hy)

theorem integral_Fv_eq {a b δ Y1 Y2 : ℝ} (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) (n : ℕ) :
    ∫ v in Ioi 0, Fv a b δ Y1 Y2 n v = ∫ y in Ioc Y1 Y2, Gy a b δ n y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Fv, Gy]
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpq : (n : ℝ) / Y2 ≤ n / Y1 := div_le_div_of_nonneg_left hn0.le hY1 hY12
  have hsub : Ico ((n : ℝ) / Y2) (n / Y1) ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le (div_pos hn0 hY2) hv.1
  unfold Fv Gy
  rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.2 hsub, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpq,
    intervalIntegral.integral_const_mul, ← intervalIntegral.integral_of_le hY12]
  have e : ∀ y : ℝ, Λ n * gsm a b δ (n / y) / y ^ 2 = Λ n * (gsm a b δ (n / y) / y ^ 2) := fun y => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_gsm_div_sq hY1 hY12 hn]
  ring

/-- `v ↦ (S(Y₂v) − S(Y₁v)) φ(v)` is integrable on `(0, ∞)`. -/
theorem integrableOn_dS_gsm {a b δ Y1 Y2 : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) :
    IntegrableOn (fun v => (Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v) (Ioi 0) := by
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  have h := ((integrableOn_E₁Λ_mul_gsm (a := a) (b := b) hδ hab hY2).sub
    (integrableOn_E₁Λ_mul_gsm (a := a) (b := b) hδ hab hY1)).add
    ((integrableOn_gsm hδ hab).const_mul (Real.log Y2 - Real.log Y1))
  refine h.congr_fun (fun v hv => ?_) measurableSet_Ioi
  have hv0 : (0 : ℝ) < v := hv
  simp only [Pi.add_apply, Pi.sub_apply, E₁Λ_eq_Smv]
  rw [Real.log_mul hY2.ne' hv0.ne', Real.log_mul hY1.ne' hv0.ne']
  ring

/-- **`∫₀^∞ (S(Y₂v) − S(Y₁v)) φ(v) dv = ∫_{Y₁}^{Y₂} Ψ(y)/y² dy`**, `Ψ(y) = Σ Λ(n) φ(n/y)`. -/
theorem integral_dS_gsm {a b δ Y1 Y2 : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) :
    ∫ v in Ioi 0, (Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v =
      ∫ y in Ioc Y1 Y2, (∑' n : ℕ, Λ n * gsm a b δ (n / y)) / y ^ 2 := by
  have hdS := integrableOn_dS_gsm hδ hab hY1 hY12
  have hFint : ∀ n, IntegrableOn (Fv a b δ Y1 Y2 n) (Ioi 0) := integrableOn_Fv hδ hab
  have hGint : ∀ n, IntegrableOn (Gy a b δ n) (Ioc Y1 Y2) := integrableOn_Gy hY1
  have hsumF : Summable fun n => ∫ v in Ioi 0, Fv a b δ Y1 Y2 n v := by
    refine summable_of_sum_range_le
      (c := ∫ v in Ioi 0, (Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v)
      (fun n => setIntegral_nonneg measurableSet_Ioi fun v _ => Fv_nonneg hδ hab n v) fun N => ?_
    rw [← integral_finsetSum _ fun n _ => hFint n]
    refine setIntegral_mono_on (integrable_finsetSum _ fun n _ => hFint n) hdS measurableSet_Ioi
      fun v hv => ?_
    have hv0 : (0 : ℝ) < v := hv
    rw [← tsum_Fv hY1 hY12 hv0]
    exact Summable.sum_le_tsum _ (fun n _ => Fv_nonneg hδ hab n v)
      (summable_of_ne_finset_zero fun n hn => Fv_eq_zero hY1 hY12 hv0 hn)
  have hnormF : (fun n => ∫ v in Ioi 0, ‖Fv a b δ Y1 Y2 n v‖) = fun n => ∫ v in Ioi 0, Fv a b δ Y1 Y2 n v :=
    funext fun n => integral_congr_ae (Eventually.of_forall fun v => Real.norm_of_nonneg (Fv_nonneg hδ hab n v))
  have hnormG : (fun n => ∫ y in Ioc Y1 Y2, ‖Gy a b δ n y‖) = fun n => ∫ v in Ioi 0, Fv a b δ Y1 Y2 n v :=
    funext fun n => by
      rw [integral_Fv_eq hY1 hY12 n]
      exact integral_congr_ae (Eventually.of_forall fun y => Real.norm_of_nonneg (Gy_nonneg hδ hab n y))
  have h1 := integral_tsum_of_summable_integral_norm hFint (by rw [hnormF]; exact hsumF)
  have h2 := integral_tsum_of_summable_integral_norm hGint (by rw [hnormG]; exact hsumF)
  have eL : ∫ v in Ioi 0, (Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v =
      ∫ v in Ioi 0, ∑' n, Fv a b δ Y1 Y2 n v :=
    setIntegral_congr_fun measurableSet_Ioi fun v hv => (tsum_Fv hY1 hY12 hv).symm
  have eR : ∫ y in Ioc Y1 Y2, (∑' n : ℕ, Λ n * gsm a b δ (n / y)) / y ^ 2 =
      ∫ y in Ioc Y1 Y2, ∑' n, Gy a b δ n y :=
    setIntegral_congr_fun measurableSet_Ioc fun y _ => by simp only [Gy]; rw [tsum_div_const]
  rw [eL, eR, ← h1, ← h2]
  exact tsum_congr fun n => integral_Fv_eq hY1 hY12 n

/-! ### The variation of `E₁Λ` -/

/-- `∫₀^∞ (E₁Λ(Y₂v) − E₁Λ(Y₁v)) φ(v) dv = ∫_{Y₁}^{Y₂} Ψ(y)/y² dy − M log(Y₂/Y₁)`. -/
theorem integral_dE1_gsm {a b δ Y1 Y2 : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2) :
    ∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v =
      (∫ y in Ioc Y1 Y2, (∑' n : ℕ, Λ n * gsm a b δ (n / y)) / y ^ 2) -
        Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * Real.log (Y2 / Y1) := by
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  have e : ∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v =
      ∫ v in Ioi 0, ((Smv (Y2 * v) - Smv (Y1 * v)) * gsm a b δ v -
        Real.log (Y2 / Y1) * gsm a b δ v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv0 : (0 : ℝ) < v := hv
    simp only [E₁Λ_eq_Smv]
    rw [Real.log_mul hY2.ne' hv0.ne', Real.log_mul hY1.ne' hv0.ne', Real.log_div hY2.ne' hY1.ne']
    ring
  rw [e, integral_sub (integrableOn_dS_gsm hδ hab hY1 hY12) ((integrableOn_gsm hδ hab).const_mul _),
    integral_const_mul, integral_gsm hδ hab, integral_dS_gsm hδ hab hY1 hY12]
  ring

/-- **The variation of `E₁Λ` from the smoothed explicit formula.** If `|Ψ(y) − M y| ≤ α√y + βy` on
`[Y₁, Y₂]`, then `M |E₁Λ(Y₂) − E₁Λ(Y₁)| ≤ 2α/√Y₁ + β log(Y₂/Y₁) + edge(Y₂) + edge(Y₁)`. -/
theorem E1_window {a b δ Y1 Y2 α β : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hY1 : 0 < Y1) (hY12 : Y1 ≤ Y2)
    (hα : 0 ≤ α)
    (hA : ∀ y ∈ Icc Y1 Y2, |∑' n : ℕ, Λ n * gsm a b δ (n / y) -
      Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * y| ≤ α * √y + β * y) :
    Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * |E₁Λ Y2 - E₁Λ Y1| ≤
      2 * α / √Y1 + β * Real.log (Y2 / Y1) +
        (∫ v in Ioi 0, |E₁Λ (Y2 * v) - E₁Λ Y2| * gsm a b δ v) +
        ∫ v in Ioi 0, |E₁Λ (Y1 * v) - E₁Λ Y1| * gsm a b δ v := by
  have hY2 : 0 < Y2 := lt_of_lt_of_le hY1 hY12
  set M := Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) with hM
  have hM0 : 0 ≤ M := by
    have : Real.exp b ≤ Real.exp a := Real.exp_le_exp.2 hab
    rw [hM]; exact mul_nonneg (Real.exp_pos _).le (by linarith)
  set Ψ : ℝ → ℝ := fun y => ∑' n : ℕ, Λ n * gsm a b δ (n / y) with hΨ
  have hg := integrableOn_gsm hδ hab
  -- `Ψ/y²` is integrable on `(Y₁, Y₂]`
  have hΨint : IntegrableOn (fun y => Ψ y / y ^ 2) (Ioc Y1 Y2) := by
    have hmeas : AEStronglyMeasurable (fun y => Ψ y / y ^ 2) (volume.restrict (Ioc Y1 Y2)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun N y => ∑ n ∈ Finset.range N, Gy a b δ n y) (fun N => ?_) ?_
      · exact (integrable_finsetSum _ fun n _ => integrableOn_Gy hY1 n).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
        have hy0 : 0 < y := lt_trans hY1 hy.1
        have hs := (summable_gsm (a := a) (b := b) hδ hab hy0).div_const (y ^ 2)
        have := hs.hasSum.tendsto_sum_nat
        simp only [hΨ, ← tsum_div_const]
        simpa [Gy] using this
    set K := (M * Y2 + α * √Y2 + |β| * Y2) / Y1 ^ 2 with hK
    refine Integrable.mono' (g := fun _ => K) (integrableOn_const measure_Ioc_lt_top.ne) hmeas
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_))
    have hy0 : 0 < y := lt_trans hY1 hy.1
    have h := hA y (Ioc_subset_Icc_self hy)
    have hΨy : |Ψ y| ≤ M * y + α * √y + |β| * y := by
      have h1 := abs_sub_abs_le_abs_sub (Ψ y) (M * y)
      rw [abs_of_nonneg (by positivity : 0 ≤ M * y)] at h1
      have : β * y ≤ |β| * y := mul_le_mul_of_nonneg_right (le_abs_self β) hy0.le
      linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2), hK]
    have hsq : Y1 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hY1.le hy.1.le 2
    have hnum : M * y + α * √y + |β| * y ≤ M * Y2 + α * √Y2 + |β| * Y2 := by
      have := Real.sqrt_le_sqrt hy.2
      have := mul_le_mul_of_nonneg_left hy.2 hM0
      have := mul_le_mul_of_nonneg_left this hα
      have := mul_le_mul_of_nonneg_left hy.2 (abs_nonneg β)
      nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy.2) hα]
    calc |Ψ y| / y ^ 2 ≤ (M * Y2 + α * √Y2 + |β| * Y2) / y ^ 2 :=
          div_le_div_of_nonneg_right (hΨy.trans hnum) (by positivity)
      _ ≤ (M * Y2 + α * √Y2 + |β| * Y2) / Y1 ^ 2 :=
          div_le_div_of_nonneg_left (le_trans (abs_nonneg _) (hΨy.trans hnum)) (by positivity) hsq
  have hint1 : IntegrableOn (fun y : ℝ => M * (1 / y)) (Ioc Y1 Y2) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_const.div continuousOn_id fun y hy =>
      (lt_of_lt_of_le hY1 hy.1).ne')
  have hlog : ∫ y in Ioc Y1 Y2, M * (1 / y) = M * Real.log (Y2 / Y1) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hY12, integral_one_div_of_pos hY1 hY2]
  -- the `y` side
  have hy : |(∫ y in Ioc Y1 Y2, Ψ y / y ^ 2) - M * Real.log (Y2 / Y1)| ≤
      2 * α / √Y1 + β * Real.log (Y2 / Y1) := by
    rw [← hlog, ← integral_sub hΨint hint1]
    refine (abs_integral_le_integral_abs).trans ?_
    have hbd : ∀ y ∈ Ioc Y1 Y2, |Ψ y / y ^ 2 - M * (1 / y)| ≤ α * y ^ (-(3 / 2) : ℝ) + β * y⁻¹ := by
      intro y hy
      have hy0 : 0 < y := lt_trans hY1 hy.1
      have e : Ψ y / y ^ 2 - M * (1 / y) = (Ψ y - M * y) / y ^ 2 := by field_simp
      rw [e, abs_div, abs_of_pos (by positivity : 0 < y ^ 2), div_le_iff₀ (by positivity)]
      have e1 : y ^ (-(3 / 2) : ℝ) * y ^ 2 = √y := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast y 2, ← Real.rpow_add hy0]; norm_num
      have e2 : y⁻¹ * y ^ 2 = y := by field_simp
      calc |Ψ y - M * y| ≤ α * √y + β * y := hA y (Ioc_subset_Icc_self hy)
        _ = (α * y ^ (-(3 / 2) : ℝ) + β * y⁻¹) * y ^ 2 := by
            rw [add_mul, mul_assoc, e1, mul_assoc, e2]
    have h0 : (0 : ℝ) ∉ uIcc Y1 Y2 := by
      rw [uIcc_of_le hY12, Set.mem_Icc]; intro h; linarith [h.1]
    have hc1 : IntervalIntegrable (fun y : ℝ => y ^ (-(3 / 2) : ℝ)) volume Y1 Y2 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
    have hc2 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume Y1 Y2 :=
      intervalIntegral.intervalIntegrable_inv (fun y hy => by
        rw [uIcc_of_le hY12] at hy; exact (lt_of_lt_of_le hY1 hy.1).ne') continuousOn_id
    have hgint : IntegrableOn (fun y : ℝ => α * y ^ (-(3 / 2) : ℝ) + β * y⁻¹) (Ioc Y1 Y2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hY12).1 ((hc1.const_mul α).add (hc2.const_mul β))
    have hval : ∫ y in Ioc Y1 Y2, (α * y ^ (-(3 / 2) : ℝ) + β * y⁻¹) =
        α * (2 * (Y1 ^ (-(1 / 2) : ℝ) - Y2 ^ (-(1 / 2) : ℝ))) + β * Real.log (Y2 / Y1) := by
      rw [← intervalIntegral.integral_of_le hY12,
        intervalIntegral.integral_add (hc1.const_mul α) (hc2.const_mul β),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨by norm_num, h0⟩), integral_inv_of_pos hY1 hY2,
        show (-(3 / 2 : ℝ)) + 1 = -(1 / 2) by norm_num]
      ring
    have hY2p : 0 ≤ Y2 ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hY2.le _
    have hY1p : Y1 ^ (-(1 / 2) : ℝ) = 1 / √Y1 := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hY1.le, inv_eq_one_div]
    have habs : IntegrableOn (fun y => |Ψ y / y ^ 2 - M * (1 / y)|) (Ioc Y1 Y2) := (hΨint.sub hint1).abs
    calc ∫ y in Ioc Y1 Y2, |Ψ y / y ^ 2 - M * (1 / y)|
        ≤ ∫ y in Ioc Y1 Y2, (α * y ^ (-(3 / 2) : ℝ) + β * y⁻¹) :=
          setIntegral_mono_on habs hgint measurableSet_Ioc hbd
      _ = α * (2 * (Y1 ^ (-(1 / 2) : ℝ) - Y2 ^ (-(1 / 2) : ℝ))) + β * Real.log (Y2 / Y1) := hval
      _ ≤ 2 * α / √Y1 + β * Real.log (Y2 / Y1) := by
          rw [hY1p]
          have := mul_nonneg hα hY2p
          have e : 2 * α / √Y1 = α * (2 * (1 / √Y1)) := by ring
          rw [e]; nlinarith
  -- the decomposition
  have hD : ∀ Y c : ℝ, 0 < Y → IntegrableOn (fun v => (E₁Λ (Y * v) - c) * gsm a b δ v) (Ioi 0) :=
    fun Y c hY => ((integrableOn_E₁Λ_mul_gsm (a := a) (b := b) hδ hab hY).sub (hg.const_mul c)).congr_fun
      (fun v _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hD12 : IntegrableOn (fun v => (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v) (Ioi 0) :=
    ((integrableOn_E₁Λ_mul_gsm (a := a) (b := b) hδ hab hY2).sub
      (integrableOn_E₁Λ_mul_gsm (a := a) (b := b) hδ hab hY1)).congr_fun
      (fun v _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hkey : M * (E₁Λ Y2 - E₁Λ Y1) =
      (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v) -
        (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v) +
        ∫ v in Ioi 0, (E₁Λ (Y1 * v) - E₁Λ Y1) * gsm a b δ v := by
    have hsplit : ∫ v in Ioi 0, ((E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v -
          (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v + (E₁Λ (Y1 * v) - E₁Λ Y1) * gsm a b δ v) =
        (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v) -
          (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v) +
          ∫ v in Ioi 0, (E₁Λ (Y1 * v) - E₁Λ Y1) * gsm a b δ v := by
      have hsub : IntegrableOn (fun v => (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v -
          (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v) (Ioi 0) := hD12.sub (hD Y2 _ hY2)
      rw [integral_add hsub (hD Y1 _ hY1), integral_sub hD12 (hD Y2 _ hY2)]
    have e : ∫ v in Ioi 0, ((E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v -
          (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v + (E₁Λ (Y1 * v) - E₁Λ Y1) * gsm a b δ v) =
        ∫ v in Ioi 0, (E₁Λ Y2 - E₁Λ Y1) * gsm a b δ v :=
      setIntegral_congr_fun measurableSet_Ioi fun v _ => by ring
    rw [← hsplit, e, integral_const_mul, integral_gsm hδ hab, hM]; ring
  have hJ : ∀ Y : ℝ, |∫ v in Ioi 0, (E₁Λ (Y * v) - E₁Λ Y) * gsm a b δ v| ≤
      ∫ v in Ioi 0, |E₁Λ (Y * v) - E₁Λ Y| * gsm a b δ v := fun Y =>
    (abs_integral_le_integral_abs).trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun v _ => by
      rw [abs_mul, abs_of_nonneg (gsm_nonneg hδ hab v)]))
  have hI := integral_dE1_gsm hδ hab hY1 hY12
  rw [← hM] at hI
  change _ = (∫ y in Ioc Y1 Y2, Ψ y / y ^ 2) - M * Real.log (Y2 / Y1) at hI
  have hJ2 := hJ Y2
  have hJ1 := hJ Y1
  rw [← abs_of_nonneg hM0, ← abs_mul, hkey, hI]
  have htri := abs_add_le ((∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v) -
      ∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v)
    (∫ v in Ioi 0, (E₁Λ (Y1 * v) - E₁Λ Y1) * gsm a b δ v)
  have htri2 := abs_sub (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ (Y1 * v)) * gsm a b δ v)
      (∫ v in Ioi 0, (E₁Λ (Y2 * v) - E₁Λ Y2) * gsm a b δ v)
  rw [hI] at htri2 htri
  linarith

/-! ### The edge terms (`b = 0`) -/

theorem neg_log_le_rpow {v : ℝ} (hv : 0 < v) : -Real.log v ≤ 2 * v ^ (-(1 / 2) : ℝ) := by
  have := Real.log_le_rpow_div (inv_pos.2 hv).le (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_inv, Real.inv_rpow hv.le, ← Real.rpow_neg hv.le] at this
  linarith [show v ^ (-(1 / 2) : ℝ) / (1 / 2) = 2 * v ^ (-(1 / 2) : ℝ) by ring]

/-- `|E₁Λ(Yv) − E₁Λ(Y)| ≤ (2 log 4 + 10) v^{−1/2}` for `Y ≥ 1`, `0 < v ≤ 1`. -/
theorem abs_E1_sub_le_small {Y v : ℝ} (hY : 1 ≤ Y) (hv0 : 0 < v) (hv1 : v ≤ 1) :
    |E₁Λ (Y * v) - E₁Λ Y| ≤ (2 * Real.log 4 + 10) * v ^ (-(1 / 2) : ℝ) := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hYv : 0 < Y * v := by positivity
  have hp : 1 ≤ v ^ (-(1 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv0 hv1 (by norm_num)
  have hl := neg_log_le_rpow hv0
  have h1 : |E₁Λ (Y * v)| ≤ Real.log 4 + 4 - Real.log v := by
    have hlv : Real.log v ≤ 0 := Real.log_nonpos hv0.le hv1
    rcases le_or_gt 1 (Y * v) with h | h
    · have := E₁Λ.le h; have := E₁Λ.ge h
      rw [abs_le]; constructor <;> linarith
    · rw [E₁Λ_of_lt_one h, abs_neg, abs_of_neg (Real.log_neg hYv h), Real.log_mul (by linarith) hv0.ne']
      have := Real.log_nonneg hY; linarith
  have h2 : |E₁Λ Y| ≤ Real.log 4 + 4 := by
    have := E₁Λ.le hY; have := E₁Λ.ge hY
    rw [abs_le]; constructor <;> linarith
  calc |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v)| + |E₁Λ Y| := abs_sub _ _
    _ ≤ 2 * Real.log 4 + 8 + 2 * v ^ (-(1 / 2) : ℝ) := by linarith
    _ ≤ (2 * Real.log 4 + 10) * v ^ (-(1 / 2) : ℝ) := by nlinarith

theorem exp_half_le : Real.exp (1 / 2) ≤ 1.6488 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

theorem log_four_le : Real.log 4 ≤ 1.3863 := by
  have h := Real.log_two_lt_d9
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- **The edge term.** For `b = 0`, `Y ≥ 1`, `M = ⌊Y⌋` and `|E₁Λ(t) − E₁Λ(M)| ≤ A + B log(t/M)`
(`t ≥ M`): `∫₀^∞ |E₁Λ(Yv) − E₁Λ(Y)| φ(v) dv ≤ (2A + 2B/M) M(1) + 2B M(3/2) + 21.1δ`. -/
theorem edge_le {a δ Y A B : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hY : 1 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hloc : ∀ t : ℝ, (⌊Y⌋₊ : ℝ) ≤ t → |E₁Λ t - E₁Λ ⌊Y⌋₊| ≤ A + B * Real.log (t / ⌊Y⌋₊)) :
    ∫ v in Ioi 0, |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v ≤
      (2 * A + 2 * B / ⌊Y⌋₊) * (Real.exp (δ ^ 2 / 2) * (Real.exp a - 1)) +
        2 * B * (Real.exp (δ ^ 2 * (3 / 2) ^ 2 / 2) * (Real.exp (a * (3 / 2)) - 1) / (3 / 2)) +
          21.1 * δ := by
  have hY0 : 0 < Y := by linarith
  set M := ⌊Y⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hY)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hMY : (M : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hYM : Y < M + 1 := Nat.lt_floor_add_one Y
  set f : ℝ → ℝ := fun v => |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v with hf
  have hg := integrableOn_gsm (a := a) (b := 0) hδ ha
  have hfint : IntegrableOn f (Ioi 0) := by
    have : IntegrableOn (fun v => |E₁Λ (Y * v) * gsm a 0 δ v - E₁Λ Y * gsm a 0 δ v|) (Ioi 0) :=
      ((integrableOn_E₁Λ_mul_gsm (a := a) (b := 0) hδ ha hY0).sub (hg.const_mul (E₁Λ Y))).abs
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only [hf]
    rw [← sub_mul, abs_mul, abs_of_nonneg (gsm_nonneg hδ ha v)]
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hfint.mono_set Ioc_subset_Ioi_self) (hfint.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  -- `0 < v ≤ 1`: the Chernoff bound
  have hr : -1 < 1 / δ - 1 / 2 := by have : 0 < 1 / δ := by positivity
                                     linarith
  have h1 : ∫ v in Ioc 0 1, f v ≤ 21.1 * δ := by
    set C := (2 * Real.log 4 + 10) * Real.exp (1 / 2) with hC
    have hgint : IntegrableOn (fun v : ℝ => C * v ^ (1 / δ - 1 / 2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul C)
    have hpt : ∀ v ∈ Ioc (0 : ℝ) 1, f v ≤ C * v ^ (1 / δ - 1 / 2) := by
      intro v hv
      have hv0 : 0 < v := hv.1
      have hE := abs_E1_sub_le_small hY hv0 hv.2
      have hG := gsm_le_rpow (a := a) hδ ha hv0
      have hG0 := gsm_nonneg (a := a) (b := 0) hδ ha v
      have e : v ^ (1 / δ - 1 / 2) = v ^ (-(1 / 2) : ℝ) * v ^ (1 / δ) := by
        rw [← Real.rpow_add hv0]; ring_nf
      rw [e]
      calc f v = |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v := rfl
        _ ≤ ((2 * Real.log 4 + 10) * v ^ (-(1 / 2) : ℝ)) * (Real.exp (1 / 2) * v ^ (1 / δ)) :=
          mul_le_mul hE hG hG0 (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity)
        _ = _ := by rw [hC]; ring
    have hcalc : ∫ v in Ioc (0 : ℝ) 1, C * v ^ (1 / δ - 1 / 2) = C / (1 / δ - 1 / 2 + 1) := by
      rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith)]
      ring
    refine (setIntegral_mono_on (hfint.mono_set Ioc_subset_Ioi_self) hgint measurableSet_Ioc hpt).trans ?_
    rw [hcalc]
    have hl4 := log_four_le
    have he := exp_half_le
    have hden : 0 < 1 / δ - 1 / 2 + 1 := by linarith
    rw [div_le_iff₀ hden]
    have e : 21.1 * δ * (1 / δ - 1 / 2 + 1) = 21.1 + 10.55 * δ := by field_simp; ring
    rw [e, hC]
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith [Real.exp_pos (1 / 2)]
  -- `v > 1`: the local bound at both ends
  have h2 : ∫ v in Ioi 1, f v ≤ (2 * A + 2 * B / M) * (Real.exp (δ ^ 2 / 2) * (Real.exp a - 1)) +
      2 * B * (Real.exp (δ ^ 2 * (3 / 2) ^ 2 / 2) * (Real.exp (a * (3 / 2)) - 1) / (3 / 2)) := by
    set c := 2 * A + 2 * B / M with hc
    have hc0 : 0 ≤ c := by positivity
    have hgint : IntegrableOn (fun v : ℝ => c * gsm a 0 δ v + 2 * B * (v ^ ((3 / 2 : ℝ) - 1) * gsm a 0 δ v))
        (Ioi 0) := (hg.const_mul c).add ((integrableOn_rpow_mul_gsm hδ ha (3 / 2)).const_mul (2 * B))
    have hpt : ∀ v ∈ Ioi (1 : ℝ), f v ≤ c * gsm a 0 δ v + 2 * B * (v ^ ((3 / 2 : ℝ) - 1) * gsm a 0 δ v) := by
      intro v hv
      have hv1 : (1 : ℝ) < v := hv
      have hv0 : (0 : ℝ) < v := by linarith
      have hG0 := gsm_nonneg (a := a) (b := 0) hδ ha v
      have hYv : (M : ℝ) ≤ Y * v := hMY.trans (le_mul_of_one_le_right hY0.le hv1.le)
      have l1 := hloc (Y * v) hYv
      have l2 := hloc Y hMY
      have hlogYM : Real.log (Y / M) ≤ 1 / M := by
        have h := Real.log_le_sub_one_of_pos (x := Y / M) (by positivity)
        have : Y / M - 1 ≤ 1 / M := by
          rw [div_sub_one hM0.ne', div_le_div_iff_of_pos_right hM0]; linarith
        linarith
      have hsplit : Real.log (Y * v / M) = Real.log v + Real.log (Y / M) := by
        rw [show Y * v / M = v * (Y / M) by ring, Real.log_mul hv0.ne' (by positivity)]
      have hlv : Real.log v ≤ 2 * v ^ (1 / 2 : ℝ) := by
        have := Real.log_le_rpow_div hv0.le (by norm_num : (0 : ℝ) < 1 / 2)
        linarith [show v ^ (1 / 2 : ℝ) / (1 / 2) = 2 * v ^ (1 / 2 : ℝ) by ring]
      have hE : |E₁Λ (Y * v) - E₁Λ Y| ≤ c + 2 * B * v ^ (1 / 2 : ℝ) := by
        have ht : |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v) - E₁Λ M| + |E₁Λ Y - E₁Λ M| := by
          have := abs_sub_le (E₁Λ (Y * v)) (E₁Λ M) (E₁Λ Y)
          rwa [abs_sub_comm (E₁Λ M) (E₁Λ Y)] at this
        rw [hsplit] at l1
        have k1 : B * Real.log (Y / M) ≤ B * (1 / M) := mul_le_mul_of_nonneg_left hlogYM hB
        have k2 : B * Real.log v ≤ B * (2 * v ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hlv hB
        have e : c = 2 * A + 2 * (B * (1 / M)) := by rw [hc]; ring
        rw [e]; nlinarith
      rw [show ((3 / 2 : ℝ) - 1) = 1 / 2 by norm_num]
      calc f v = |E₁Λ (Y * v) - E₁Λ Y| * gsm a 0 δ v := rfl
        _ ≤ (c + 2 * B * v ^ (1 / 2 : ℝ)) * gsm a 0 δ v := mul_le_mul_of_nonneg_right hE hG0
        _ = _ := by ring
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        fun v : ℝ => c * gsm a 0 δ v + 2 * B * (v ^ ((3 / 2 : ℝ) - 1) * gsm a 0 δ v) :=
      (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => by
        have := gsm_nonneg (a := a) (b := 0) hδ ha v
        have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < v from hv)) ((3 / 2 : ℝ) - 1)
        positivity)
    calc ∫ v in Ioi 1, f v
        ≤ ∫ v in Ioi 1, (c * gsm a 0 δ v + 2 * B * (v ^ ((3 / 2 : ℝ) - 1) * gsm a 0 δ v)) :=
          setIntegral_mono_on (hfint.mono_set (Set.Ioi_subset_Ioi zero_le_one))
            (hgint.mono_set (Set.Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi hpt
      _ ≤ ∫ v in Ioi 0, (c * gsm a 0 δ v + 2 * B * (v ^ ((3 / 2 : ℝ) - 1) * gsm a 0 δ v)) :=
          setIntegral_mono_set hgint hnn (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
      _ = _ := by
          rw [integral_add (hg.const_mul c) ((integrableOn_rpow_mul_gsm hδ ha _).const_mul _),
            integral_const_mul, integral_const_mul, integral_gsm hδ ha,
            integral_rpow_mul_gsm hδ ha (by norm_num : (3 / 2 : ℝ) ≠ 0)]
          simp only [Real.exp_zero, zero_mul]
  linarith

end TernaryGoldbach.Prelim
