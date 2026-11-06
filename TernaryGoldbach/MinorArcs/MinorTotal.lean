import TernaryGoldbach.MinorArcs.BaseGap2
import TernaryGoldbach.MinorArcs.EBound
import TernaryGoldbach.MinorArcs.Thm1321

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# The minor-arc total (14.49), via repair 3

Assembles (NOTES, "Ch. 13: scale erratum", repair 3):
* `thm_13_2_1_repaired` (mixed family, ℓ² from (12.42) with `δ₀ = 392`);
* the ℓ∞ inputs `norm_S_etaStar_le_ghat` (off `𝔐_{8,n}(y)`) and `norm_S_etaStar_le_gap` (base gap);
* the split `S_{η₊} = S₁ + S₂` (`S₁`: primes `> √x`), with `|a + b|² ≤ (1+t)|a|² + (1+1/t)|b|²`;
* the Part II inputs `l2_major_14_7` (J), `prop_7_1_5` (S) (`PartIICited.lean`); `E_le_14_28` (E, `EBound.lean`
  with the constant `8·10⁻¹¹` in place of [H]'s `8.4029·10⁻¹²`);
* the numerics `NumericsGoal` (proved in `NumericsFinal.lean`).
-/

open Real Set MeasureTheory Filter
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum)

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs S etaStar etaPlus eta2 phi κ r₀)

/-! ## A uniform bound for `S_{η_*}` -/

theorem integral_phi_Ici_one_le : ∫ w in Ici (1:ℝ), phi w ≤ 1.0044 := by
  rw [integral_Ici_eq_integral_Ioi, integral_phi_Ioi_one]
  have hg := integral_gaussian_Ioi (1 / 2)
  have hg' : ∫ w in Ioi (0:ℝ), rexp (-w ^ 2 / 2) = √(π / (1 / 2)) / 2 := by
    rw [← hg]; congr 1; ext w; ring_nf
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi integrable_exp_neg_sq_half.integrableOn
    integrable_exp_neg_sq_half.integrableOn] at hg'
  have h2 := integral_exp_Ioc_ge
  have hpi : √(π / (1 / 2)) ≤ 2.50664 := by
    rw [Real.sqrt_le_left (by norm_num), div_div_eq_mul_div]
    have := Real.pi_lt_d6; nlinarith
  have he : rexp (-(1 / 2)) ≤ 0.6066 := by
    have h := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.sum_le_exp_of_nonneg (x := 1 / 2) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  linarith

/-- `|S_{η_*}(α, x)| ≤ 22.75 x/κ` for all `α`. -/
theorem norm_S_etaStar_le_uniform {x : ℝ} (hx : 0 < x) (α : ℝ) :
    ‖S etaStar x α‖ ≤ 22.75 * (x / κ) := by
  have hκ : (0:ℝ) < κ := by rw [Helfgott.κ]; norm_num
  have hy0 : 0 < x / κ := div_pos hx hκ
  have hGi : IntegrableOn (fun w => (17 : ℝ) * phi w) (Ici 1) :=
    (integrable_phi.const_mul 17).integrableOn
  have key := norm_S_etaStar_le_of_pointwise_Ici (G := fun _ => 17) (α := α) hx one_pos
    (fun w (hw : 1 ≤ w) => norm_S_eta2_le_trivial (mul_pos (by linarith) hy0) α) hGi
  have h1 := integral_phi_Ici_one_le
  have h2 := integral_phi_Ioo_le (w₀ := 1) zero_le_one
  rw [integral_const_mul] at key
  refine key.trans ?_
  have h3 : (17 * ∫ w in Ici (1:ℝ), phi w) + 17 * ∫ w in Ioo (0:ℝ) 1, phi w ≤ 22.75 := by
    norm_num at h2; linarith
  calc x / κ * ((17 * ∫ w in Ici (1:ℝ), phi w) + 17 * ∫ w in Ioo (0:ℝ) 1, phi w)
      ≤ x / κ * 22.75 := mul_le_mul_of_nonneg_left h3 hy0.le
    _ = 22.75 * (x / κ) := by ring

/-! ## The numerical core -/

/-- `σ(x)`: `Σ_{p > √x} (log p)² η₊(p/x)² ≤ σ(x) x` (from Prop 7.1.5). -/
noncomputable def sig (x : ℝ) : ℝ := (0.640208 + 366.91 / √x) * Real.log x - 0.021095

/-- The denominator of (12.42) with `δ₀ = 392`. -/
noncomputable def Dx (x : ℝ) : ℝ := Real.log (2 * √(x / 784)) + cE

noncomputable def cL (n : ℕ) : ℝ := Real.log (2 * ((n : ℝ) + 1)) + 2

/-- The bound for `Z₁/(x · x/κ)` produced by `thm_13_2_1_repaired`. -/
noncomputable def Mexpr (x : ℝ) (r₂ : ℕ) : ℝ :=
  ghatY (x / κ) 150000 * (cL 150000 * sig x / Dx x - 8.6294) +
    ∑ n ∈ Finset.Ioo 150000 r₂, ghatY (x / κ) n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) +
    ghatY (x / κ) r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)

/-- **The numerical statement** (proved in `NumericsFinal.lean: numerics_M`). -/
def NumericsGoal (x : ℝ) : Prop :=
  ∃ r₂ : ℕ, 150000 < r₂ ∧ (20000 * (r₂ : ℝ)) ^ 2 ≤ x / 784 ∧
    2 * (r₂ : ℝ) ≤ (2 * √(x / 784)) ^ (0.6 : ℝ) ∧ (r₂ : ℝ) ≤ (x / κ) ^ (1 / 3 : ℝ) / 6 ∧
    2.16e20 * r₂ ≤ 670 * (x / κ) ∧ cL (r₂ - 1) ≤ Dx x ∧ Mexpr x r₂ ≤ 1.037

/-! ## The split `S_{η₊} = S₁ + S₂` -/

/-- Coefficients of `S₁`: primes `p > √x`. -/
noncomputable def a₁ (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ √x < n then ((Λ n * etaPlus (n / x) : ℝ) : ℂ) else 0

/-- Coefficients of `S₂ = S_{η₊} - S₁`. -/
noncomputable def a₂ (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ √x < n then 0 else ((Λ n * etaPlus (n / x) : ℝ) : ℂ)

theorem summable_a₁ {x : ℝ} (hx : 0 < x) : Summable fun n => ‖a₁ x n‖ :=
  (Helfgott.summable_etaPlus hx).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    unfold a₁; split_ifs <;> simp [abs_nonneg, mul_nonneg]

theorem summable_a₂ {x : ℝ} (hx : 0 < x) : Summable fun n => ‖a₂ x n‖ :=
  (Helfgott.summable_etaPlus hx).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    unfold a₂; split_ifs <;> simp [abs_nonneg, mul_nonneg]

theorem primeSupported_a₁ {x : ℝ} (hx : 0 < x) : PrimeSupported x (a₁ x) :=
  ⟨fun n hn => by
    unfold a₁ at hn; split_ifs at hn with h
    · exact h
    · exact absurd rfl hn, summable_a₁ hx⟩

theorem S_etaPlus_eq {x : ℝ} (hx : 0 < x) (α : ℝ) :
    S etaPlus x α = expTsum (a₁ x) α + expTsum (a₂ x) α := by
  unfold S expTsum
  have s1 : Summable fun n : ℕ => a₁ x n * e (n * α) :=
    Summable.of_norm ((summable_a₁ hx).congr fun n => by rw [TernaryGoldbach.norm_mul_e])
  have s2 : Summable fun n : ℕ => a₂ x n * e (n * α) :=
    Summable.of_norm ((summable_a₂ hx).congr fun n => by rw [TernaryGoldbach.norm_mul_e])
  rw [← s1.tsum_add s2]
  congr 1; ext n
  unfold a₁ a₂; split_ifs <;> ring

theorem norm_add_sq_le (u v : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖u + v‖ ^ 2 ≤ (1 + t) * ‖u‖ ^ 2 + (1 + 1 / t) * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  have h0 : 0 ≤ ‖u + v‖ := norm_nonneg _
  have h1 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  have h2 : 2 * ‖u‖ * ‖v‖ ≤ t * ‖u‖ ^ 2 + 1 / t * ‖v‖ ^ 2 := by
    have := sq_nonneg (t * ‖u‖ - ‖v‖)
    rw [div_mul_eq_mul_div, one_mul, ← sub_nonneg]
    have e : t * ‖u‖ ^ 2 + ‖v‖ ^ 2 / t - 2 * ‖u‖ * ‖v‖ = (t * ‖u‖ - ‖v‖) ^ 2 / t := by
      field_simp; ring
    rw [e]; positivity
  nlinarith

theorem norm_sq_sum_a₂_le {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n, ‖a₂ x n‖ ^ 2 ≤ 8e-11 * x := by
  refine le_trans (le_of_eq ?_) (E_le_14_28 hx)
  congr 1; ext n
  unfold a₂; split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Properties of `ĝ` -/

theorem ghatY_nonneg {y n : ℝ} (hy : 1 ≤ y) (hn : 0 < n) : 0 ≤ ghatY y n := by
  unfold ghatY
  have := hfun_nonneg hy
  have : 0 ≤ max (gx y n) (hfun y) := this.trans (le_max_right _ _)
  positivity

theorem ghatY_antitone {y n m : ℝ} (hy : 2.16e20 ≤ y) (hn : 670 ≤ n) (hnm : n ≤ m)
    (hm : m ≤ y ^ (1 / 3 : ℝ) / 6) : ghatY y m ≤ ghatY y n := by
  unfold ghatY
  have h1 := gx_antitoneOn hy ⟨hn, hnm.trans hm⟩ ⟨hn.trans hnm, hm⟩ hnm
  have hn0 : 0 < n := by linarith
  have h2 : 17 * (670 / m) ^ 3 / 3 ≤ 17 * (670 / n) ^ 3 / 3 := by
    have : 670 / m ≤ 670 / n := div_le_div_of_nonneg_left (by norm_num) hn0 hnm
    have := pow_le_pow_left₀ (div_nonneg (by norm_num) (by linarith)) this 3
    linarith
  have h3 : max (gx y m) (hfun y) ≤ max (gx y n) (hfun y) := max_le_max h1 le_rfl
  linarith

theorem gx_r0_ge {y : ℝ} (hy : 1e25 ≤ y) : 0.01 ≤ gx y 150000 := by
  have hy' : 2.16e20 ≤ y := by linarith
  obtain ⟨hT, hT3, -, -⟩ := cube_root_facts hy'
  have hy0 : 0 < y := by linarith
  have hT' : (2 * 150000 : ℝ) ≤ y ^ (1 / 3 : ℝ) / 3 := by
    have : (1e8 : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
      by_contra h; push Not at h
      have : (y ^ (1 / 3 : ℝ)) ^ 3 < (1e8 : ℝ) ^ 3 := by gcongr
      rw [hT3] at this; norm_num at this; linarith
    linarith
  have hR := R_nonneg (x := y) (t := 2 * 150000) (by norm_num) hT'
  have hl : 12.6 ≤ Real.log (2 * 150000) := by
    have := le_log_num (z := 2 * 150000) 12 0.6 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  have hF : 3.8 ≤ Fr 150000 := by
    rw [Fr_eq_Fs]; refine Fs_ge ?_
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hsF : 1.949 ≤ √(Fr 150000) := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hs : √(2 * 150000 : ℝ) ≤ 548 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hFl : 3.8 ≤ Fr (2 * 150000 / 2) := by norm_num; norm_num at hF; exact hF
  have hLg : 394 ≤ Lg (2 * 150000) := by
    unfold Lg
    have : 3.8 * (13 / 4 * 12.6 + 7.82) ≤ Fr (2 * 150000 / 2) * (13 / 4 * Real.log (2 * 150000) + 7.82) :=
      mul_le_mul hFl (by linarith) (by norm_num) (by linarith)
    linarith
  have h1 : (0.8764 * 1.949 + 2.526) / 548 ≤
      ((R y (2 * 150000) * Real.log (2 * 150000) + 0.8764) * √(Fr 150000) + 2.526) / √(2 * 150000) := by
    apply div_le_div₀ (by positivity) _ (by positivity) hs
    have hl0 : (0:ℝ) ≤ Real.log (2 * 150000) := le_trans (by norm_num) hl
    have hRl : 0 ≤ R y (2 * 150000) * Real.log (2 * 150000) := mul_nonneg hR hl0
    have : 0.8764 * 1.949 ≤ (R y (2 * 150000) * Real.log (2 * 150000) + 0.8764) * √(Fr 150000) :=
      mul_le_mul (le_add_of_nonneg_left hRl) hsF (by norm_num) (by positivity)
    linarith
  have h2 : 394 / 150000 ≤ Lg (2 * 150000) / 150000 := div_le_div_of_nonneg_right hLg (by norm_num)
  have h3 : 0 ≤ 3.8 * y ^ (-1 / 6 : ℝ) := by positivity
  unfold gx
  norm_num at h1 h2 ⊢
  linarith

theorem ghatY_r0_ge {y : ℝ} (hy : 1e25 ≤ y) : 0.0121 ≤ ghatY y 150000 := by
  have := gx_r0_ge hy
  unfold ghatY
  have : 0.01 ≤ max (gx y 150000) (hfun y) := this.trans (le_max_left _ _)
  have : 0 ≤ 17 * (670 / (150000:ℝ)) ^ 3 / 3 := by positivity
  linarith

/-! ## `T = Σ|a₁|²` and `I₀` -/

theorem T_le {x : ℝ} (hx : 4.9e26 ≤ x) : ∑' n, ‖a₁ x n‖ ^ 2 ≤ sig x * x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨E₂, hE₂, heq⟩ := prop_7_1_5 (x := x) (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hpt : ∀ n : ℕ, ‖a₁ x n‖ ^ 2 ≤ Λ n * Real.log n * etaPlus (n / x) ^ 2 := by
    intro n
    unfold a₁
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
        ArithmeticFunction.vonMangoldt_apply_prime h.1, sq]
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      positivity
  have hs1 : Summable fun n => ‖a₁ x n‖ ^ 2 :=
    TernaryGoldbach.summable_norm_sq_of_summable_norm (summable_a₁ hx0)
  have hs2 : Summable fun n : ℕ => Λ n * Real.log n * etaPlus (n / x) ^ 2 := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at heq
    -- the main term is positive
    have : 0 < 0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x := by
      have hl : 60 ≤ Real.log x := by
        rw [Real.le_log_iff_exp_le hx0]
        have := Real.exp_one_lt_d9
        calc rexp 60 = rexp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 60 := by gcongr
          _ ≤ 4.9e26 := by norm_num
          _ ≤ x := hx
      have hE : -(2e-6 + 366.91 / √x) ≤ E₂ := (abs_le.1 hE₂).1
      have hsx : 0 < √x := Real.sqrt_pos.2 hx0
      have : 366.91 / √x ≤ 1e-6 := by
        rw [div_le_iff₀ hsx]
        have : (1e13 : ℝ) ≤ √x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
        linarith
      have h1 : 0.64 ≤ 0.640206 + E₂ := by linarith
      have h2 : 0.64 * 60 ≤ (0.640206 + E₂) * Real.log x := mul_le_mul h1 hl (by norm_num) (by linarith)
      have h3 : 0 < ((0.640206 + E₂) * Real.log x - 0.021095) * x := mul_pos (by linarith) hx0
      linarith [h3]
    linarith
  calc ∑' n, ‖a₁ x n‖ ^ 2 ≤ ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 :=
        Summable.tsum_le_tsum hpt hs1 hs2
    _ = 0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x := heq
    _ ≤ sig x * x := by
        unfold sig
        have := (abs_le.1 hE₂).2
        have : E₂ * x * Real.log x ≤ (2e-6 + 366.91 / √x) * x * Real.log x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hx0.le) hlx
        nlinarith

/-! ## The minor-arc total -/

theorem continuous_norm_sq_expTsum {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Continuous fun α => ‖expTsum a α‖ ^ 2 :=
  (TernaryGoldbach.continuous_expTsum ha).norm.pow 2

theorem integrableOn_Ioc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (A : Set ℝ)
    (hA : A ⊆ Ioc 0 1) : IntegrableOn f A :=
  (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set (hA.trans Ioc_subset_Icc_self)

/-- `I₀ = ∫_{(0,1] ∩ 𝔐_{8,r₀}(x)} |S₁|² ≥ 8.6294 x`. -/
theorem I0_ge {x : ℝ} (hx : 4.9e26 ≤ x) :
    8.6294 * x ≤ ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, ‖expTsum (a₁ x) α‖ ^ 2 := by
  have hx0 : 0 < x := by linarith
  set B := Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x
  have hB : MeasurableSet B := measurableSet_Ioc.inter (Helfgott.measurableSet_majorArcs _ _ _)
  have hBsub : B ⊆ Ioc 0 1 := inter_subset_left
  have hJ := l2_major_14_7 hx
  have hJ' : 8.6296 * x ≤ ∫ α in B, ‖S etaPlus x α‖ ^ 2 := by
    have := (abs_le.1 hJ).1; linarith
  set t : ℝ := 1e-5
  have ht : 0 < t := by norm_num
  have c1 := continuous_norm_sq_expTsum (summable_a₁ hx0)
  have c2 := continuous_norm_sq_expTsum (summable_a₂ hx0)
  have hpt : ∀ α, ‖S etaPlus x α‖ ^ 2 ≤
      (1 + t) * ‖expTsum (a₁ x) α‖ ^ 2 + (1 + 1 / t) * ‖expTsum (a₂ x) α‖ ^ 2 := fun α => by
    rw [S_etaPlus_eq hx0]; exact norm_add_sq_le _ _ ht
  have hcS : Continuous fun α => ‖S etaPlus x α‖ ^ 2 :=
    (TernaryGoldbach.continuous_expTsum (Helfgott.summable_etaPlus hx0)).norm.pow 2
  have h1 : ∫ α in B, ‖S etaPlus x α‖ ^ 2 ≤
      (1 + t) * (∫ α in B, ‖expTsum (a₁ x) α‖ ^ 2) + (1 + 1 / t) * ∫ α in B, ‖expTsum (a₂ x) α‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((integrableOn_Ioc_of_continuous c1 B hBsub).const_mul _)
        ((integrableOn_Ioc_of_continuous c2 B hBsub).const_mul _)]
    exact setIntegral_mono_on (integrableOn_Ioc_of_continuous hcS B hBsub)
      (((integrableOn_Ioc_of_continuous c1 B hBsub).const_mul _).add
        ((integrableOn_Ioc_of_continuous c2 B hBsub).const_mul _)) hB fun α _ => hpt α
  have h2 : ∫ α in B, ‖expTsum (a₂ x) α‖ ^ 2 ≤ 8e-11 * x := by
    refine le_trans ?_ ((TernaryGoldbach.setIntegral_norm_sq_expTsum (summable_a₂ hx0)).le.trans
      (norm_sq_sum_a₂_le hx))
    exact setIntegral_mono_set (integrableOn_Ioc_of_continuous c2 _ le_rfl)
      (Eventually.of_forall fun α => by positivity) (Eventually.of_forall hBsub)
  have h3 : 0 ≤ ∫ α in B, ‖expTsum (a₂ x) α‖ ^ 2 := setIntegral_nonneg hB fun α _ => by positivity
  have : (1 + 1 / t) * ∫ α in B, ‖expTsum (a₂ x) α‖ ^ 2 ≤ (1 + 1 / t) * (8e-11 * x) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 8.6296 * x - (1 + 1 / t) * (8e-11 * x) ≤
      (1 + t) * ∫ α in B, ‖expTsum (a₁ x) α‖ ^ 2 := by linarith
  have h5 : 8.6294 * x * (1 + t) ≤ 8.6296 * x - (1 + 1 / t) * (8e-11 * x) := by
    simp only [t]; nlinarith
  have := le_trans h5 h4
  rw [mul_comm (1 + t)] at this
  exact le_of_mul_le_mul_right this (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **(14.49), repaired**: for `x ≥ 4.9·10²⁶`,
`∫_{(0,1] \ 𝔐_{8,r₀}} |S_{η_*}(α, x)| |S_{η₊}(α, x)|² dα ≤ 1.0376 x²/κ`. -/
theorem minor_total {x : ℝ} (hx : 4.9e26 ≤ x) (hnum : NumericsGoal x) :
    ∫ α in Ioc (0:ℝ) 1 \ majorArcs 8 r₀ x, ‖S etaStar x α‖ * ‖S etaPlus x α‖ ^ 2 ≤
      1.0376 * x ^ 2 / κ := by
  have hκ : (κ : ℝ) = 49 := rfl
  have hr₀ : (r₀ : ℝ) = ((150000 : ℕ) : ℝ) := by norm_num [Helfgott.r₀]
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy_def
  have hy : 1e25 ≤ y := by rw [hy_def, hκ, le_div_iff₀ (by norm_num)]; linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨r₂, h150, hx1, hρ, hry, hry', hcD, hM⟩ := hnum
  set A := Ioc (0:ℝ) 1 \ majorArcs 8 r₀ x
  have hA : MeasurableSet A := measurableSet_Ioc.diff (Helfgott.measurableSet_majorArcs _ _ _)
  have hAsub : A ⊆ Ioc 0 1 := sdiff_subset
  set v : ℝ → ℝ := fun α => ‖S etaStar x α‖
  have hv : Continuous v :=
    (TernaryGoldbach.continuous_expTsum (Helfgott.summable_etaStar hx0)).norm
  have c1 := continuous_norm_sq_expTsum (summable_a₁ hx0)
  have c2 := continuous_norm_sq_expTsum (summable_a₂ hx0)
  set t : ℝ := 5e-4
  have ht : 0 < t := by norm_num
  -- step 1: the split
  have hstep1 : ∫ α in A, ‖S etaStar x α‖ * ‖S etaPlus x α‖ ^ 2 ≤
      (1 + t) * (∫ α in A, ‖expTsum (a₁ x) α‖ ^ 2 * v α) +
        (1 + 1 / t) * ∫ α in A, v α * ‖expTsum (a₂ x) α‖ ^ 2 := by
    have i1 : IntegrableOn (fun α => ‖expTsum (a₁ x) α‖ ^ 2 * v α) A :=
      integrableOn_Ioc_of_continuous (c1.mul hv) A hAsub
    have i2 : IntegrableOn (fun α => v α * ‖expTsum (a₂ x) α‖ ^ 2) A :=
      integrableOn_Ioc_of_continuous (hv.mul c2) A hAsub
    have hcS : Continuous fun α => ‖S etaStar x α‖ * ‖S etaPlus x α‖ ^ 2 :=
      hv.mul ((TernaryGoldbach.continuous_expTsum (Helfgott.summable_etaPlus hx0)).norm.pow 2)
    have e : (1 + t) * (∫ α in A, ‖expTsum (a₁ x) α‖ ^ 2 * v α) +
        (1 + 1 / t) * ∫ α in A, v α * ‖expTsum (a₂ x) α‖ ^ 2 =
        ∫ α in A, ((1 + t) * (‖expTsum (a₁ x) α‖ ^ 2 * v α) +
          (1 + 1 / t) * (v α * ‖expTsum (a₂ x) α‖ ^ 2)) := by
      rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
    rw [e]
    refine setIntegral_mono_on (integrableOn_Ioc_of_continuous hcS A hAsub)
      ((i1.const_mul _).add (i2.const_mul _)) hA fun α _ => ?_
    have h := norm_add_sq_le (expTsum (a₁ x) α) (expTsum (a₂ x) α) ht
    rw [← S_etaPlus_eq hx0] at h
    have hv0 : 0 ≤ v α := norm_nonneg _
    have := mul_le_mul_of_nonneg_left h hv0
    simp only [v] at this ⊢
    nlinarith
  -- step 2: `S₂`
  have hstep2 : ∫ α in A, v α * ‖expTsum (a₂ x) α‖ ^ 2 ≤ 22.75 * y * (8e-11 * x) := by
    have i2 := integrableOn_Ioc_of_continuous c2 A hAsub
    calc ∫ α in A, v α * ‖expTsum (a₂ x) α‖ ^ 2
        ≤ ∫ α in A, 22.75 * y * ‖expTsum (a₂ x) α‖ ^ 2 := by
          refine setIntegral_mono_on (integrableOn_Ioc_of_continuous (hv.mul c2) A hAsub)
            (i2.const_mul _) hA fun α _ => ?_
          exact mul_le_mul_of_nonneg_right (norm_S_etaStar_le_uniform hx0 α) (by positivity)
      _ = 22.75 * y * ∫ α in A, ‖expTsum (a₂ x) α‖ ^ 2 := integral_const_mul _ _
      _ ≤ 22.75 * y * (8e-11 * x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans ?_ ((TernaryGoldbach.setIntegral_norm_sq_expTsum (summable_a₂ hx0)).le.trans
            (norm_sq_sum_a₂_le hx))
          exact setIntegral_mono_set (integrableOn_Ioc_of_continuous c2 _ le_rfl)
            (Eventually.of_forall fun α => by positivity) (Eventually.of_forall hAsub)
  -- step 3: `S₁` via the repaired Thm 13.2.1
  have hy' : 2.16e20 ≤ y := by linarith
  have hr2y : (r₂ : ℝ) ≤ y ^ (1 / 3 : ℝ) / 6 := hry
  have h150r : (150000 : ℝ) < r₂ := by exact_mod_cast h150
  set g : ℕ → ℝ := fun n => y * ghatY y n with hg_def
  have hgmono : ∀ n, 150000 ≤ n → n < r₂ → g (n + 1) ≤ g n := by
    intro n hn hn2
    have hn' : (150000 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2' : ((n + 1 : ℕ) : ℝ) ≤ r₂ := by exact_mod_cast hn2
    simp only [hg_def]
    refine mul_le_mul_of_nonneg_left (ghatY_antitone hy' (by linarith) (by push_cast; linarith)
      (hn2'.trans hr2y)) hy0.le
  have hg0 : 0 ≤ g r₂ := mul_nonneg hy0.le (ghatY_nonneg (by linarith) (by linarith))
  have hv₀ : ∀ α ∉ majorArcs 8 ((150000 : ℕ) : ℝ) x, ‖S etaStar x α‖ ≤ g 150000 := by
    refine hv_of_split (y := x / κ) (fun α hα => ?_) (fun α hα => ?_)
    · exact norm_S_etaStar_le_ghat hx0 hy (by norm_num) (by rw [← hy_def]; push_cast; linarith)
        (by rw [← hy_def]; push_cast; linarith) hα
    · have h1 : α ∈ majorArcs 8 r₀ (x / κ) := by rw [hr₀]; exact hα.1
      have h2 : α ∉ majorArcs 8 r₀ x := by rw [hr₀]; exact hα.2
      refine (norm_S_etaStar_le_gap hx h1 h2).trans ?_
      have := ghatY_r0_ge hy
      simp only [hg_def]; push_cast
      nlinarith
  have hvn : ∀ n, 150000 < n → n ≤ r₂ → ∀ α ∉ majorArcs 8 n (x / κ), ‖S etaStar x α‖ ≤ g n := by
    intro n hn hn2 α hα
    have hn' : (150000 : ℝ) < n := by exact_mod_cast hn
    have hn2' : (n : ℝ) ≤ r₂ := by exact_mod_cast hn2
    exact norm_S_etaStar_le_ghat hx0 hy (by linarith) (by rw [← hy_def]; exact hn2'.trans hr2y)
      (by rw [← hy_def]; nlinarith) hα
  have key := thm_13_2_1_repaired hx0 (primeSupported_a₁ hx0) (g := g) (r₀ := 150000) (r₁ := r₂)
    h150.le (by norm_num) hx1 hρ hgmono hg0 hv₀ hvn
  -- bound the right side by `y x Mexpr`
  set T := ∑' n, ‖a₁ x n‖ ^ 2 with hT_def
  have hT := T_le hx
  have hT0 : 0 ≤ T := tsum_nonneg fun n => by positivity
  have hI := I0_ge hx
  rw [hr₀] at hI
  have hD : 0 < Dx x := by
    unfold Dx cE
    have : 0 ≤ Real.log (2 * √(x / 784)) := Real.log_nonneg (by
      have : (1:ℝ) ≤ √(x / 784) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; rw [le_div_iff₀ (by norm_num)]; linarith
      linarith)
    linarith
  have hHl : ∀ n : ℕ, n < r₂ → Hl2y x T r₂ n = cL n / Dx x * T := fun n hn => by
    simp only [Hl2y, ite_eq_left hn, cL, Dx]
  have hHr : Hl2y x T r₂ r₂ = T := by simp only [Hl2y, lt_irrefl, ite_false]
  have hgnn : ∀ n : ℕ, 150000 ≤ n → 0 ≤ g n := fun n hn =>
    mul_nonneg hy0.le (ghatY_nonneg (by linarith) (by
      have : (150000 : ℝ) ≤ n := by exact_mod_cast hn
      linarith))
  have hsig0 : 0 ≤ sig x := by
    have := T_le hx
    by_contra h; push Not at h
    have : sig x * x < 0 := mul_neg_of_neg_of_pos h hx0
    linarith
  have hcL : ∀ n : ℕ, 0 ≤ cL n := fun n => by
    unfold cL
    have : 0 ≤ Real.log (2 * ((n : ℝ) + 1)) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  -- base term
  have hbase : g 150000 * (Hl2y x T r₂ 150000 - ∫ α in Ioc 0 1 ∩ majorArcs 8 ((150000 : ℕ) : ℝ) x,
      ‖expTsum (a₁ x) α‖ ^ 2) ≤ y * x * (ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294)) := by
    rw [hHl 150000 h150]
    have h1 : cL 150000 / Dx x * T ≤ cL 150000 / Dx x * (sig x * x) :=
      mul_le_mul_of_nonneg_left hT (div_nonneg (hcL _) hD.le)
    have h2 : cL 150000 / Dx x * T - ∫ α in Ioc 0 1 ∩ majorArcs 8 ((150000 : ℕ) : ℝ) x,
        ‖expTsum (a₁ x) α‖ ^ 2 ≤ x * (cL 150000 * sig x / Dx x - 8.6294) := by
      have e : x * (cL 150000 * sig x / Dx x - 8.6294) = cL 150000 / Dx x * (sig x * x) - 8.6294 * x := by
        field_simp
      rw [e]; push_cast at hI ⊢; linarith
    have := mul_le_mul_of_nonneg_left h2 (hgnn 150000 le_rfl)
    simp only [hg_def] at this ⊢
    push_cast at this ⊢
    linarith [this]
  -- the sum
  have hIoc : Finset.Ioc 150000 r₂ = insert r₂ (Finset.Ioo 150000 r₂) :=
    (Finset.Ioo_insert_right h150).symm
  have hsum : ∑ n ∈ Finset.Ioc 150000 r₂, g n * (Hl2y x T r₂ n - Hl2y x T r₂ (n - 1)) ≤
      y * x * (∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) +
        ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)) := by
    rw [hIoc, Finset.sum_insert Finset.right_notMem_Ioo, mul_add, Finset.mul_sum, add_comm]
    refine add_le_add (Finset.sum_le_sum fun n hn => ?_) ?_
    · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
      have hn0 : (0:ℝ) < n := by
        have : (150000 : ℝ) < n := by exact_mod_cast hn1
        linarith
      rw [hHl n hn2, hHl (n - 1) (by omega)]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hdiff : cL n - cL (n - 1) = Real.log (((n : ℝ) + 1) / n) := by
        unfold cL; rw [hcast, Real.log_div (by linarith) hn0.ne']
        rw [Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) hn0.ne']; ring
      have hlog0 : 0 ≤ Real.log (((n : ℝ) + 1) / n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
      have e : cL n / Dx x * T - cL (n - 1) / Dx x * T = Real.log (((n : ℝ) + 1) / n) / Dx x * T := by
        rw [← hdiff]; ring
      rw [e]
      have h1 : Real.log (((n : ℝ) + 1) / n) / Dx x * T ≤
          x * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) := by
        have := mul_le_mul_of_nonneg_left hT (div_nonneg hlog0 hD.le)
        have e2 : x * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) =
            Real.log (((n : ℝ) + 1) / n) / Dx x * (sig x * x) := by ring
        linarith
      have := mul_le_mul_of_nonneg_left h1 (hgnn n hn1.le)
      simp only [hg_def] at this ⊢
      linarith
    · rw [hHr, hHl (r₂ - 1) (by omega)]
      have h1 : T - cL (r₂ - 1) / Dx x * T ≤ x * (sig x - cL (r₂ - 1) * sig x / Dx x) := by
        have hc : 0 ≤ 1 - cL (r₂ - 1) / Dx x := by
          rw [sub_nonneg, div_le_one hD]; exact hcD
        have := mul_le_mul_of_nonneg_left hT hc
        have e1 : T - cL (r₂ - 1) / Dx x * T = (1 - cL (r₂ - 1) / Dx x) * T := by ring
        have e2 : x * (sig x - cL (r₂ - 1) * sig x / Dx x) = (1 - cL (r₂ - 1) / Dx x) * (sig x * x) := by
          field_simp
        linarith
      have := mul_le_mul_of_nonneg_left h1 (hgnn r₂ h150.le)
      simp only [hg_def] at this ⊢
      linarith
  have hZ1 : ∫ α in A, ‖expTsum (a₁ x) α‖ ^ 2 * v α ≤ y * x * Mexpr x r₂ := by
    have hAeq : A = Ioc 0 1 \ majorArcs 8 ((150000 : ℕ) : ℝ) x := by simp only [A, hr₀]
    rw [hAeq]
    refine key.trans ?_
    unfold Mexpr
    rw [← hy_def]
    have : y * x * (ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294) +
        ∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) +
        ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)) =
        y * x * (ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294)) +
        y * x * (∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) +
        ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)) := by ring
    push_cast at hbase hsum ⊢
    rw [this]
    exact add_le_add hbase hsum
  -- conclude
  have hxy : 1.0376 * x ^ 2 / κ = 1.0376 * (x * y) := by rw [hy_def]; ring
  rw [hxy]
  have hM' : y * x * Mexpr x r₂ ≤ y * x * 1.037 := mul_le_mul_of_nonneg_left hM (by positivity)
  have hfin : (1 + t) * (y * x * 1.037) + (1 + 1 / t) * (22.75 * y * (8e-11 * x)) ≤
      1.0376 * (x * y) := by
    simp only [t]; nlinarith [mul_pos hx0 hy0]
  have h1 : (1 + t) * (∫ α in A, ‖expTsum (a₁ x) α‖ ^ 2 * v α) ≤ (1 + t) * (y * x * 1.037) :=
    mul_le_mul_of_nonneg_left (hZ1.trans hM') (by norm_num)
  have h2 : (1 + 1 / t) * (∫ α in A, v α * ‖expTsum (a₂ x) α‖ ^ 2) ≤
      (1 + 1 / t) * (22.75 * y * (8e-11 * x)) :=
    mul_le_mul_of_nonneg_left hstep2 (by norm_num)
  linarith [hstep1]

end TernaryGoldbach.MinorArcs
