import TernaryGoldbach.Explicit.WeilNumA
import TernaryGoldbach.Explicit.WeilLineSum

/-!
# The Weil-window integral in closed form

With `m = 2` and `B_R ≥ K0 ℓ R = (2ℓ)⁴ k₀` (`KRB_ge`), `Φ⁺(t)/B_R ≤ Ψ(|t|)` (`PhiUp_div_le`), where
`Ψ(s) = p₀/max(1, ℓs)⁴ + κ₁ log(s + R) + κ₀ + (1/π)(1/(2(s+R)) + 1/(16(s+R)²))`.
-/

open Complex MeasureTheory Set Filter Finset
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-! ### The majorant `Ψ` -/

noncomputable def K0 (ℓ R : ℝ) : ℝ := (2 * ℓ) ^ 4 * kB ℓ R
noncomputable def kap1 (ℓ R : ℝ) : ℝ := (1 + I0 2 R / K0 ℓ R) / (2 * π)
noncomputable def kap0 (ℓ : ℝ) (N : ℕ) (R : ℝ) : ℝ :=
  1 / π * (-(1 / 2) * Real.log (2 * π) + 1 / 2 * Real.log (((N : ℝ) + 1 / 4) / ((N : ℝ) - 3 / 4)) +
    (cN N * I0 2 R + I1 2 R) / K0 ℓ R) + OffC ℓ 2 / K0 ℓ R
noncomputable def p0 (ℓ R : ℝ) : ℝ := 2 * Real.exp (2 * ℓ) / kB ℓ R
noncomputable def smallT (y : ℝ) : ℝ := 1 / π * (1 / (2 * y) + 1 / (16 * y ^ 2))
/-- `Ψ` with constants `p₀, κ₁, κ₀` (upper bounds for `p0`, `kap1`, `kap0`). -/
noncomputable def PsiG (ℓ p₀ κ₁ κ₀ R s : ℝ) : ℝ :=
  p₀ / max 1 (ℓ * s) ^ 4 + κ₁ * Real.log (s + R) + κ₀ + smallT (s + R)
noncomputable def PsiB (ℓ : ℝ) (N : ℕ) (R s : ℝ) : ℝ := PsiG ℓ (p0 ℓ R) (kap1 ℓ R) (kap0 ℓ N R) R s

theorem I0_two_nonneg {R : ℝ} (hR : 0 < R) : 0 ≤ I0 2 R := by rw [I0_two hR]; positivity
theorem I1_two_nonneg {R : ℝ} (hR : 0 < R) : 0 ≤ I1 2 R := by rw [I1_two hR]; positivity

theorem kap1_nonneg {ℓ R : ℝ} (hR : 0 < R) (hK0 : 0 < K0 ℓ R) : 0 ≤ kap1 ℓ R := by
  unfold kap1
  have := I0_two_nonneg hR
  have : 0 ≤ I0 2 R / K0 ℓ R := div_nonneg this hK0.le
  have := Real.pi_pos
  positivity

theorem smallT_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ smallT y := by unfold smallT; positivity

theorem smallT_anti {y y' : ℝ} (hy : 0 < y) (h : y ≤ y') : smallT y' ≤ smallT y := by
  unfold smallT
  have hy' : 0 < y' := by linarith
  have h1 : 1 / (2 * y') ≤ 1 / (2 * y) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 / (16 * y' ^ 2) ≤ 1 / (16 * y ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have := Real.pi_pos
  gcongr

theorem polarUp_two (ℓ t : ℝ) :
    polarUp ℓ 2 t = (2 * ℓ) ^ 4 * (2 * Real.exp (2 * ℓ)) / max 1 (ℓ * |t|) ^ 4 := by
  unfold polarUp; push_cast; ring

/-- **`Φ⁺(t)/B_R ≤ Ψ(|t|)`.** -/
theorem PhiUp_div_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 3 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hkB : 0 < kB ℓ R) (hKK : K0 ℓ R ≤ KRB ℓ 2 R) (t : ℝ) :
    PhiUp ℓ 2 N R t / KRB ℓ 2 R ≤ PsiB ℓ N R |t| := by
  have hR0 : 0 < R := by linarith
  have hK0 : 0 < K0 ℓ R := by unfold K0; positivity
  have hK : 0 < KRB ℓ 2 R := lt_of_lt_of_le hK0 hKK
  have hI0 := I0_two_nonneg hR0
  have hI1 := I1_two_nonneg hR0
  have hcN := cN_nonneg hN
  have hpi := Real.pi_pos
  have hs : 0 ≤ |t| := abs_nonneg t
  -- the pieces
  have hpol0 : 0 ≤ polarUp ℓ 2 t := by
    rw [polarUp_two]; have : 0 < max 1 (ℓ * |t|) := lt_of_lt_of_le one_pos (le_max_left _ _); positivity
  have hpol : polarUp ℓ 2 t / KRB ℓ 2 R ≤ p0 ℓ R / max 1 (ℓ * |t|) ^ 4 := by
    calc polarUp ℓ 2 t / KRB ℓ 2 R ≤ polarUp ℓ 2 t / K0 ℓ R := div_le_div_of_nonneg_left hpol0 hK0 hKK
      _ = _ := by
        rw [polarUp_two]; unfold p0 K0
        have : 0 < max 1 (ℓ * |t|) := lt_of_lt_of_le one_pos (le_max_left _ _)
        field_simp
  have haN : aN N (|t| + R) ≤ aC N (|t| + R) := aN_le_aC (by omega) (by linarith)
  have hlog : Real.log (1 + |t|) ≤ Real.log (|t| + R) := Real.log_le_log (by positivity) (by linarith)
  have htail0 : 0 ≤ (cN N + 1 / 2 * Real.log (1 + |t|)) * I0 2 R + I1 2 R := by
    have : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith)
    positivity
  have htail : ((cN N + 1 / 2 * Real.log (1 + |t|)) * I0 2 R + I1 2 R) / KRB ℓ 2 R ≤
      ((cN N + 1 / 2 * Real.log (|t| + R)) * I0 2 R + I1 2 R) / K0 ℓ R := by
    calc _ ≤ ((cN N + 1 / 2 * Real.log (1 + |t|)) * I0 2 R + I1 2 R) / K0 ℓ R :=
          div_le_div_of_nonneg_left htail0 hK0 hKK
      _ ≤ _ := by gcongr
  have hoff : OffC ℓ 2 / KRB ℓ 2 R ≤ OffC ℓ 2 / K0 ℓ R :=
    div_le_div_of_nonneg_left (by unfold OffC; positivity) hK0 hKK
  -- assemble
  have e : PhiUp ℓ 2 N R t / KRB ℓ 2 R = polarUp ℓ 2 t / KRB ℓ 2 R + 1 / π * aN N (|t| + R) +
      1 / π * (((cN N + 1 / 2 * Real.log (1 + |t|)) * I0 2 R + I1 2 R) / KRB ℓ 2 R) + OffC ℓ 2 / KRB ℓ 2 R := by
    unfold PhiUp; field_simp; ring
  rw [e]
  have e2 : PsiB ℓ N R |t| = p0 ℓ R / max 1 (ℓ * |t|) ^ 4 + 1 / π * aC N (|t| + R) +
      1 / π * (((cN N + 1 / 2 * Real.log (|t| + R)) * I0 2 R + I1 2 R) / K0 ℓ R) + OffC ℓ 2 / K0 ℓ R := by
    unfold PsiB PsiG kap1 kap0 smallT aC
    field_simp
    ring
  rw [e2]
  have h1 : 1 / π * aN N (|t| + R) ≤ 1 / π * aC N (|t| + R) :=
    mul_le_mul_of_nonneg_left haN (by positivity)
  have h2 : 1 / π * (((cN N + 1 / 2 * Real.log (1 + |t|)) * I0 2 R + I1 2 R) / KRB ℓ 2 R) ≤
      1 / π * (((cN N + 1 / 2 * Real.log (|t| + R)) * I0 2 R + I1 2 R) / K0 ℓ R) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  linarith

theorem PsiB_le_PsiG {ℓ : ℝ} {N : ℕ} {R : ℝ} (hR : 1 ≤ R) {p₀ κ₁ κ₀ : ℝ} (hp : p0 ℓ R ≤ p₀)
    (hk : kap1 ℓ R ≤ κ₁) (hk0 : kap0 ℓ N R ≤ κ₀) {s : ℝ} (hs : 0 ≤ s) :
    PsiB ℓ N R s ≤ PsiG ℓ p₀ κ₁ κ₀ R s := by
  unfold PsiB PsiG
  have h0 : 0 < max 1 (ℓ * s) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : p0 ℓ R / max 1 (ℓ * s) ^ 4 ≤ p₀ / max 1 (ℓ * s) ^ 4 := by gcongr
  have hl : 0 ≤ Real.log (s + R) := Real.log_nonneg (by linarith)
  have h2 : kap1 ℓ R * Real.log (s + R) ≤ κ₁ * Real.log (s + R) := mul_le_mul_of_nonneg_right hk hl
  linarith

/-! ### Evenness and Riemann sums -/

theorem integral_symm_abs {h : ℝ → ℝ} (hc : Continuous fun t => h |t|) (Y : ℝ) :
    ∫ t in (-Y)..Y, h |t| = 2 * ∫ t in (0 : ℝ)..Y, h |t| := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => h |t|) volume a b := fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-Y) 0) (hi 0 Y)]
  have h1 : ∫ t in (-Y)..0, h |t| = ∫ t in (0 : ℝ)..Y, h |t| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := Y) (fun t => h |t|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [h1]; ring

/-- **Riemann upper sums**: if `f ≤ c_k w` on each `[p_k, p_{k+1}]`, then
`∫_{p_0}^{p_n} f ≤ Σ c_k ∫_{p_k}^{p_{k+1}} w`. -/
theorem integral_le_riemann {f w : ℝ → ℝ} {p c : ℕ → ℝ} {n : ℕ} (hp : ∀ k < n, p k ≤ p (k + 1))
    (hf : ∀ k < n, IntervalIntegrable f volume (p k) (p (k + 1)))
    (hw : ∀ k < n, IntervalIntegrable w volume (p k) (p (k + 1)))
    (hle : ∀ k < n, ∀ s ∈ Icc (p k) (p (k + 1)), f s ≤ c k * w s) :
    ∫ s in (p 0)..(p n), f s ≤ ∑ k ∈ range n, c k * ∫ s in (p k)..(p (k + 1)), w s := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on (hp k hk') (hf k hk') ((hw k hk').const_mul _) (hle k hk')

/-! ### From `[−Y, Y]` to `[0, Y]` -/

theorem continuous_PsiG_abs (ℓ p₀ κ₁ κ₀ : ℝ) {R : ℝ} (hR : 0 < R) : Continuous fun t : ℝ => PsiG ℓ p₀ κ₁ κ₀ R |t| := by
  unfold PsiG smallT
  have hpos : ∀ t : ℝ, 0 < |t| + R := fun t => by positivity
  refine (((continuous_const.div ((continuous_const.max (continuous_const.mul continuous_abs)).pow 4)
    fun t => ?_).add (continuous_const.mul ((continuous_abs.add continuous_const).log fun t => (hpos t).ne'))).add
    continuous_const).add (continuous_const.mul ?_)
  · exact (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _).ne'
  · refine (continuous_const.div (by fun_prop) fun t => ?_).add (continuous_const.div (by fun_prop) fun t => ?_)
    · have := hpos t; positivity
    · have := hpos t; positivity

/-- The window weight `G(s) = ĝ(max(0, s − R))` as a function of `s`. -/
noncomputable def GW (δ R s : ℝ) : ℝ := gW δ 2.39 (max 0 (s - R))

theorem GW_nonneg (δ R s : ℝ) : 0 ≤ GW δ R s := gW_nonneg δ (by norm_num) _

theorem continuous_GW (δ R : ℝ) : Continuous (GW δ R) :=
  (continuous_gW δ (by norm_num)).comp (continuous_const.max (continuous_id.sub continuous_const))

/-- The integrand on `[0, Y]`: `G(s) Ψ(|s|)`. -/
noncomputable def WI (δ ℓ p₀ κ₁ κ₀ R s : ℝ) : ℝ := GW δ R s * PsiG ℓ p₀ κ₁ κ₀ R |s|

theorem continuous_WI (δ ℓ p₀ κ₁ κ₀ : ℝ) {R : ℝ} (hR : 0 < R) : Continuous (WI δ ℓ p₀ κ₁ κ₀ R) :=
  (continuous_GW δ R).mul (continuous_PsiG_abs ℓ p₀ κ₁ κ₀ hR)

/-- **Reduction to `[0, Y]`.** -/
theorem window_int_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 3 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hkB : 0 < kB ℓ R) (hKK : K0 ℓ R ≤ KRB ℓ 2 R) {p₀ κ₁ κ₀ : ℝ} (hp : p0 ℓ R ≤ p₀) (hk : kap1 ℓ R ≤ κ₁)
    (hk0 : kap0 ℓ N R ≤ κ₀) (δ Y : ℝ) (hY : 0 ≤ Y) :
    (∫ t in (-Y)..Y, gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ 2 N R t) / KRB ℓ 2 R ≤
      2 * ∫ s in (0 : ℝ)..Y, WI δ ℓ p₀ κ₁ κ₀ R s := by
  have hR0 : 0 < R := by linarith
  have hK : 0 < KRB ℓ 2 R := lt_of_lt_of_le (by unfold K0; positivity) hKK
  rw [← intervalIntegral.integral_div]
  have hc1 : Continuous fun t : ℝ => gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ 2 N R t / KRB ℓ 2 R :=
    (((continuous_gW δ (by norm_num)).comp (continuous_const.max (continuous_abs.sub continuous_const))).mul
      (continuous_PhiUp ℓ 2 N R)).div_const _
  have hc2 : Continuous fun t : ℝ => GW δ R |t| * PsiG ℓ p₀ κ₁ κ₀ R |t| :=
    ((continuous_GW δ R).comp continuous_abs).mul (continuous_PsiG_abs ℓ p₀ κ₁ κ₀ hR0)
  calc ∫ t in (-Y)..Y, gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ 2 N R t / KRB ℓ 2 R ≤
      ∫ t in (-Y)..Y, GW δ R |t| * PsiG ℓ p₀ κ₁ κ₀ R |t| := by
        refine intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
          (hc2.intervalIntegrable _ _) fun t _ => ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left ((PhiUp_div_le hℓ hN hR hkB hKK t).trans
          (PsiB_le_PsiG hR hp hk hk0 (abs_nonneg t))) (GW_nonneg δ R |t|)
    _ = 2 * ∫ s in (0 : ℝ)..Y, WI δ ℓ p₀ κ₁ κ₀ R s := by
        have := integral_symm_abs (h := fun s => GW δ R s * PsiG ℓ p₀ κ₁ κ₀ R s) hc2 Y
        rw [this]
        congr 1
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hY] at ht
        simp only [WI, abs_of_nonneg ht.1]

/-! ### Regions A and B: Riemann sums -/

/-- The value of `Ψ` on `[a, b]`, bounded by its monotone parts at the ends. -/
noncomputable def PsiBarG (ℓ p₀ κ₁ κ₀ R a b : ℝ) : ℝ :=
  p₀ / max 1 (ℓ * a) ^ 4 + κ₁ * Real.log (b + R) + κ₀ + smallT (a + R)

theorem PsiG_le_PsiBarG {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (hk₁ : 0 ≤ κ₁) {a b s : ℝ} (ha : 0 ≤ a) (hs : s ∈ Icc a b) :
    PsiG ℓ p₀ κ₁ κ₀ R s ≤ PsiBarG ℓ p₀ κ₁ κ₀ R a b := by
  unfold PsiG PsiBarG
  have h1 : p₀ / max 1 (ℓ * s) ^ 4 ≤ p₀ / max 1 (ℓ * a) ^ 4 := by
    have hp : 0 ≤ p₀ := hp₀
    have h0 : 0 < max 1 (ℓ * a) := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact div_le_div_of_nonneg_left hp (by positivity)
      (pow_le_pow_left₀ h0.le (max_le_max le_rfl (by nlinarith [hs.1])) 4)
  have h2 : κ₁ * Real.log (s + R) ≤ κ₁ * Real.log (b + R) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hs.1]) (by linarith [hs.2])) hk₁
  have h3 : smallT (s + R) ≤ smallT (a + R) := smallT_anti (by linarith) (by linarith [hs.1])
  linarith

theorem PsiBarG_nonneg {ℓ : ℝ} {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀) (hk₁ : 0 ≤ κ₁)
    (hκ : 0 ≤ κ₀ + κ₁ * Real.log R) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ PsiBarG ℓ p₀ κ₁ κ₀ R a b := by
  unfold PsiBarG
  have h1 : 0 ≤ p₀ / max 1 (ℓ * a) ^ 4 := by
    have h0 : 0 < max 1 (ℓ * a) := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact div_nonneg hp₀ (by positivity)
  have h2 : κ₁ * Real.log R ≤ κ₁ * Real.log (b + R) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hR (by linarith)) hk₁
  have h3 := smallT_nonneg (y := a + R) (by linarith)
  linarith

theorem gW_le_inv (δ : ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) (u : ℝ) : gW δ t₀ u ≤ 1 / max u t₀ := by
  unfold gW
  have h0 : 0 < max u t₀ := lt_of_lt_of_le ht₀ (le_max_right _ _)
  have : Real.exp (-(δ ^ 2 * max u t₀ ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := sq_nonneg δ; have := sq_nonneg (max u t₀); nlinarith)
  exact div_le_div_of_nonneg_right this h0.le

theorem WI_eq {δ ℓ p₀ κ₁ κ₀ : ℝ} {R s : ℝ} (hs : 0 ≤ s) : WI δ ℓ p₀ κ₁ κ₀ R s = GW δ R s * PsiG ℓ p₀ κ₁ κ₀ R s := by
  unfold WI; rw [abs_of_nonneg hs]

/-- **Region A** (`0 ≤ s ≤ R + t₀`, where `G = e^{−δ²t₀²/2}/t₀ ≤ 1/t₀`): `n` equal steps. -/
theorem regionA_le {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀) (hk₁ : 0 ≤ κ₁)
    (hκ : 0 ≤ κ₀ + κ₁ * Real.log R) (δ : ℝ) (n : ℕ) (hn : 0 < n) :
    ∫ s in (0 : ℝ)..(R + 2.39), WI δ ℓ p₀ κ₁ κ₀ R s ≤
      ∑ k ∈ range n, PsiBarG ℓ p₀ κ₁ κ₀ R (k * ((R + 2.39) / n)) ((k + 1) * ((R + 2.39) / n)) / 2.39 *
        ((R + 2.39) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set h := (R + 2.39) / n with hh
  have hh0 : 0 < h := div_pos (by linarith) hn'
  set p : ℕ → ℝ := fun k => k * h with hp
  have hpn : p n = R + 2.39 := by simp only [hp, hh]; field_simp
  have hpk : ∀ k, p (k + 1) = (k + 1) * h := fun k => by simp only [hp]; push_cast; ring
  have hc := continuous_WI δ ℓ p₀ κ₁ κ₀ hR
  have e0 : (0 : ℝ) = p 0 := by simp [hp]
  rw [e0, ← hpn]
  have hR' := integral_le_riemann (f := WI δ ℓ p₀ κ₁ κ₀ R) (w := fun _ => (1 : ℝ)) (p := p)
    (c := fun k => PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) / 2.39) (n := n)
    (fun k _ => by simp only [hp]; push_cast; nlinarith) (fun k _ => hc.intervalIntegrable _ _)
    (fun k _ => intervalIntegrable_const) (fun k hk s hs => ?_)
  · refine hR'.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, hpk]
    simp only [hp]; ring
  · have hs0 : 0 ≤ s := le_trans (by simp only [hp]; positivity) hs.1
    have hk1 : (k : ℝ) + 1 ≤ n := by have : k + 1 ≤ n := hk; exact_mod_cast this
    have hsR : s ≤ R + 2.39 := by
      have := hs.2; rw [hpk] at this
      calc s ≤ (k + 1) * h := this
        _ ≤ n * h := mul_le_mul_of_nonneg_right hk1 hh0.le
        _ = R + 2.39 := by rw [hh]; field_simp
    rw [WI_eq hs0, mul_one]
    have hG : GW δ R s ≤ 1 / 2.39 := by
      have := gW_le_inv δ (by norm_num : (0 : ℝ) < 2.39) (max 0 (s - R))
      unfold GW
      rwa [max_eq_right (max_le (by norm_num) (by linarith))] at this
    have hPs := PsiG_le_PsiBarG (κ₀ := κ₀) hℓ hR hp₀ hk₁ (by simp only [hp]; positivity) hs
    have hPb := PsiBarG_nonneg (ℓ := ℓ) hR hp₀ hk₁ hκ (a := p k) (b := p (k + 1)) (by simp only [hp]; positivity)
      (by simp only [hp]; positivity)
    calc GW δ R s * PsiG ℓ p₀ κ₁ κ₀ R s ≤ GW δ R s * PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) :=
          mul_le_mul_of_nonneg_left hPs (GW_nonneg δ R s)
      _ ≤ 1 / 2.39 * PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) := mul_le_mul_of_nonneg_right hG hPb
      _ = PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) / 2.39 := by ring

/-- **Region B** (`R + t₀ ≤ s ≤ R + t₀ r^n`, where `G ≤ 1/(s − R)`): geometric steps. -/
theorem regionB_le {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀) (hk₁ : 0 ≤ κ₁)
    (hκ : 0 ≤ κ₀ + κ₁ * Real.log R) (δ : ℝ) {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    ∫ s in (R + 2.39)..(R + 2.39 * r ^ n), WI δ ℓ p₀ κ₁ κ₀ R s ≤
      ∑ k ∈ range n, PsiBarG ℓ p₀ κ₁ κ₀ R (R + 2.39 * r ^ k) (R + 2.39 * r ^ (k + 1)) * Real.log r := by
  have hr0 : 0 < r := by linarith
  set p : ℕ → ℝ := fun k => R + 2.39 * r ^ k with hp
  have hc := continuous_WI δ ℓ p₀ κ₁ κ₀ hR
  have hpk : ∀ k, 2.39 ≤ 2.39 * r ^ k := fun k => le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hr)
  have hmono : ∀ k, p k ≤ p (k + 1) := fun k => by
    simp only [hp, pow_succ]; nlinarith [pow_pos hr0 k]
  have e0 : R + 2.39 = p 0 := by simp [hp]
  rw [e0]
  have hw : ∀ k, IntervalIntegrable (fun s : ℝ => 1 / (s - R)) volume (p k) (p (k + 1)) := by
    intro k
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [Set.uIcc_of_le (hmono k)] at hs
    have : 0 < s - R := by have := hs.1; simp only [hp] at this; linarith [hpk k]
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) this.ne').continuousWithinAt
  have hR' := integral_le_riemann (f := WI δ ℓ p₀ κ₁ κ₀ R) (w := fun s => 1 / (s - R)) (p := p)
    (c := fun k => PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1))) (n := n)
    (fun k _ => hmono k) (fun k _ => hc.intervalIntegrable _ _) (fun k _ => hw k) (fun k hk s hs => ?_)
  · refine hR'.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    congr 1
    rw [intervalIntegral.integral_comp_sub_right (fun s => 1 / s), integral_one_div_of_pos]
    · simp only [hp, add_sub_cancel_left, pow_succ]
      rw [show 2.39 * (r ^ k * r) / (2.39 * r ^ k) = r by field_simp]
    · simp only [hp, add_sub_cancel_left]; positivity
    · simp only [hp, add_sub_cancel_left]; positivity
  · have hsR : 2.39 ≤ s - R := by have := hs.1; simp only [hp] at this; linarith [hpk k]
    have hs0 : 0 ≤ s := by linarith
    rw [WI_eq hs0]
    have hG : GW δ R s ≤ 1 / (s - R) := by
      have := gW_le_inv δ (by norm_num : (0 : ℝ) < 2.39) (max 0 (s - R))
      have hm : max (max 0 (s - R)) 2.39 = s - R := by
        rw [max_eq_right (by linarith : (0 : ℝ) ≤ s - R), max_eq_left hsR]
      rw [hm] at this
      exact this
    have hpk0 : 0 ≤ p k := by simp only [hp]; positivity
    have hPs := PsiG_le_PsiBarG (κ₀ := κ₀) hℓ hR hp₀ hk₁ hpk0 hs
    have hPb := PsiBarG_nonneg (ℓ := ℓ) hR hp₀ hk₁ hκ (a := p k) (b := p (k + 1)) hpk0 (hpk0.trans (hmono k))
    calc GW δ R s * PsiG ℓ p₀ κ₁ κ₀ R s ≤ GW δ R s * PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) :=
          mul_le_mul_of_nonneg_left hPs (GW_nonneg δ R s)
      _ ≤ 1 / (s - R) * PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) := mul_le_mul_of_nonneg_right hG hPb
      _ = PsiBarG ℓ p₀ κ₁ κ₀ R (p k) (p (k + 1)) * (1 / (s - R)) := by ring

/-! ### Region C: `[R + U, R + 1/δ]` in closed form -/

theorem exp_neg_le_quad {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd : ∀ y, HasDerivAt g (-1 + y + Real.exp (-y)) y := by
    intro y
    have h1 := ((((hasDerivAt_id' y).neg.add_const 1).add ((hasDerivAt_pow 2 y).div_const 2)).sub
      ((hasDerivAt_id' y).neg.exp))
    convert h1 using 1
    · funext v; simp only [g, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
    · simp only [Pi.neg_apply]; push_cast; ring
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y _ => ?_
    rw [(hd y).deriv]
    have := Real.add_one_le_exp (-y); linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [g, neg_zero, Real.exp_zero] at this
  linarith

/-- The antiderivative for region C. -/
noncomputable def PhiC (δ c₀ κ₁ c₂ u : ℝ) : ℝ :=
  c₀ * Real.log u + κ₁ / 2 * Real.log u ^ 2 -
    δ ^ 2 / 2 * (c₀ * u ^ 2 / 2 + κ₁ * (u ^ 2 * Real.log u / 2 - u ^ 2 / 4)) +
    δ ^ 4 / 8 * (c₀ * u ^ 4 / 4 + κ₁ * (u ^ 4 * Real.log u / 4 - u ^ 4 / 16)) +
    c₂ * (-(1 / u) - δ ^ 2 * u / 2 + δ ^ 4 * u ^ 3 / 24)

/-- Its derivative. -/
noncomputable def QC (δ c₀ κ₁ c₂ u : ℝ) : ℝ :=
  (1 / u - δ ^ 2 * u / 2 + δ ^ 4 * u ^ 3 / 8) * (c₀ + κ₁ * Real.log u) +
    c₂ * (1 / u ^ 2 - δ ^ 2 / 2 + δ ^ 4 * u ^ 2 / 8)

theorem hasDerivAt_PhiC (δ c₀ κ₁ c₂ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (PhiC δ c₀ κ₁ c₂) (QC δ c₀ κ₁ c₂ u) u := by
  have hl := Real.hasDerivAt_log hu.ne'
  have hu1 := hasDerivAt_id' u
  have hinv : HasDerivAt (fun v : ℝ => 1 / v) (-(1 / u ^ 2)) u := by
    have := hasDerivAt_inv hu.ne'; simpa [one_div] using this
  have A1 := hl.const_mul c₀
  have A2 := (hl.pow 2).const_mul (κ₁ / 2)
  have B1 := ((hasDerivAt_pow 2 u).const_mul c₀).div_const 2
  have B2 := (((hasDerivAt_pow 2 u).mul hl).div_const 2).sub ((hasDerivAt_pow 2 u).div_const 4)
  have B := (B1.add (B2.const_mul κ₁)).const_mul (δ ^ 2 / 2)
  have C1 := ((hasDerivAt_pow 4 u).const_mul c₀).div_const 4
  have C2 := (((hasDerivAt_pow 4 u).mul hl).div_const 4).sub ((hasDerivAt_pow 4 u).div_const 16)
  have C := (C1.add (C2.const_mul κ₁)).const_mul (δ ^ 4 / 8)
  have D := ((hinv.neg.sub ((hu1.const_mul (δ ^ 2)).div_const 2)).add
    (((hasDerivAt_pow 3 u).const_mul (δ ^ 4)).div_const 24)).const_mul c₂
  have h := (((A1.add A2).sub B).add C).add D
  convert h using 1
  · funext v; simp only [PhiC, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Pi.pow_apply]
  · unfold QC; field_simp; push_cast; ring

theorem continuousOn_QC (δ c₀ κ₁ c₂ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (QC δ c₀ κ₁ c₂) (Set.uIcc a b) := by
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  have hlog := Real.continuousAt_log hu0.ne'
  have hinv : ContinuousAt (fun u : ℝ => 1 / u) u := continuousAt_const.div continuousAt_id hu0.ne'
  have hinv2 : ContinuousAt (fun u : ℝ => 1 / u ^ 2) u :=
    continuousAt_const.div (continuousAt_id.pow 2) (by positivity)
  unfold QC
  exact ((((hinv.sub (by fun_prop)).add (by fun_prop)).mul
    (continuousAt_const.add (continuousAt_const.mul hlog))).add
    (continuousAt_const.mul ((hinv2.sub continuousAt_const).add (by fun_prop)))).continuousWithinAt

/-- The constants of region C. -/
noncomputable def c0C (ℓ p₀ κ₀ R U : ℝ) : ℝ := κ₀ + p₀ / max 1 (ℓ * (U + R)) ^ 4
noncomputable def c2C (κ₁ R U : ℝ) : ℝ := 2 * R * κ₁ + 1 / (2 * π) + 1 / (16 * π * U)

/-- For `u ≥ U ≥ R`: `Ψ(u + R) ≤ c₀ + κ₁ log u + c₂/u`. -/
theorem PsiG_shift_le {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (hk₁ : 0 ≤ κ₁) {U u : ℝ} (hU : 0 < U) (hu : U ≤ u) :
    PsiG ℓ p₀ κ₁ κ₀ R (u + R) ≤ c0C ℓ p₀ κ₀ R U + κ₁ * Real.log u + c2C κ₁ R U / u := by
  have hu0 : 0 < u := by linarith
  have hk1 := hk₁
  have hpi := Real.pi_pos
  unfold PsiG c0C c2C
  have h1 : p₀ / max 1 (ℓ * (u + R)) ^ 4 ≤ p₀ / max 1 (ℓ * (U + R)) ^ 4 := by
    have hp : 0 ≤ p₀ := hp₀
    have h0 : 0 < max 1 (ℓ * (U + R)) := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact div_le_div_of_nonneg_left hp (by positivity)
      (pow_le_pow_left₀ h0.le (max_le_max le_rfl (by nlinarith)) 4)
  have h2 : Real.log (u + R + R) ≤ Real.log u + 2 * R / u := by
    have := log_le_log_add u (2 * R) hu0 (by linarith)
    rw [show u + R + R = u + 2 * R by ring]; exact this
  have h3 : smallT (u + R + R) ≤ (1 / (2 * π) + 1 / (16 * π * U)) / u := by
    refine (smallT_anti hu0 (by linarith)).trans ?_
    unfold smallT
    have : 1 / (16 * u ^ 2) ≤ 1 / (16 * U * u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc 1 / π * (1 / (2 * u) + 1 / (16 * u ^ 2)) ≤ 1 / π * (1 / (2 * u) + 1 / (16 * U * u)) := by gcongr
      _ = _ := by field_simp
  have e : (2 * R * κ₁ + 1 / (2 * π) + 1 / (16 * π * U)) / u =
      κ₁ * (2 * R / u) + (1 / (2 * π) + 1 / (16 * π * U)) / u := by field_simp; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h2 hk1]

/-- **Region C.** -/
theorem regionC_le {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀) (hk₁ : 0 ≤ κ₁)
    (hκ : 0 ≤ κ₀ + κ₁ * Real.log R) {δ U : ℝ} (hδ : 0 < δ) (hRU : R ≤ U) (hU0 : 2.39 ≤ U)
    (hUδ : U ≤ 1 / δ) :
    ∫ s in (R + U)..(R + 1 / δ), WI δ ℓ p₀ κ₁ κ₀ R s ≤
      PhiC δ (c0C ℓ p₀ κ₀ R U) (κ₁) (c2C κ₁ R U) (1 / δ) - PhiC δ (c0C ℓ p₀ κ₀ R U) (κ₁) (c2C κ₁ R U) U := by
  have hU : 0 < U := by linarith
  set c₀ := c0C ℓ p₀ κ₀ R U
  set c₂ := c2C κ₁ R U
  have hk1 : 0 ≤ κ₁ := hk₁
  have hc2 : 0 ≤ c₂ := by simp only [c₂, c2C]; have := Real.pi_pos; positivity
  have hc0 : κ₀ ≤ c₀ := by
    simp only [c₀, c0C]
    have h0 : 0 < max 1 (ℓ * (U + R)) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have : 0 ≤ p₀ / max 1 (ℓ * (U + R)) ^ 4 := div_nonneg hp₀ (by positivity)
    linarith
  have e : ∫ s in (R + U)..(R + 1 / δ), WI δ ℓ p₀ κ₁ κ₀ R s = ∫ u in U..(1 / δ), WI δ ℓ p₀ κ₁ κ₀ R (u + R) := by
    rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> ring
  rw [e, ← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_PhiC δ c₀ κ₁ c₂ (lt_of_lt_of_le hU (by rw [Set.uIcc_of_le hUδ] at hu; exact hu.1)))
    ((continuousOn_QC δ c₀ κ₁ c₂ hU hUδ).intervalIntegrable)]
  refine intervalIntegral.integral_mono_on hUδ
    ((continuous_WI δ ℓ p₀ κ₁ κ₀ hR).comp (continuous_id.add continuous_const) |>.intervalIntegrable _ _)
    ((continuousOn_QC δ c₀ κ₁ c₂ hU hUδ).intervalIntegrable) fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le hU hu.1
  have huR : 0 ≤ u + R := by linarith
  simp only [WI_eq huR]
  have hG : GW δ R (u + R) = Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u := by
    unfold GW gW
    rw [show u + R - R = u by ring, max_eq_right hu0.le, max_eq_left (by linarith [hu.1])]
  have hP := PsiG_shift_le (κ₀ := κ₀) hℓ hR hp₀ hk₁ hU hu.1
  have hpos : 0 ≤ c₀ + κ₁ * Real.log u + c₂ / u := by
    have : κ₁ * Real.log R ≤ κ₁ * Real.log u := mul_le_mul_of_nonneg_left
      (Real.log_le_log hR (by linarith [hu.1])) hk1
    have : 0 ≤ c₂ / u := div_nonneg hc2 hu0.le
    linarith
  have hx : 0 ≤ δ ^ 2 * u ^ 2 / 2 := by positivity
  have hE := exp_neg_le_quad hx
  rw [hG]
  calc Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * PsiG ℓ p₀ κ₁ κ₀ R (u + R) ≤
      Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (c₀ + κ₁ * Real.log u + c₂ / u) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ (1 - δ ^ 2 * u ^ 2 / 2 + (δ ^ 2 * u ^ 2 / 2) ^ 2 / 2) / u * (c₀ + κ₁ * Real.log u + c₂ / u) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE hu0.le) hpos
    _ = QC δ c₀ κ₁ c₂ u := by unfold QC; field_simp; ring

/-! ### Region D: `[R + 1/δ, R + W]`, Gaussian pieces -/

theorem integral_mul_exp_gauss {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    ∫ u in a..b, u * Real.exp (-(δ ^ 2 * u ^ 2 / 2)) =
      (Real.exp (-(δ ^ 2 * a ^ 2 / 2)) - Real.exp (-(δ ^ 2 * b ^ 2 / 2))) / δ ^ 2 := by
  have hd : ∀ u ∈ [[a, b]], HasDerivAt (fun u : ℝ => -(Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / δ ^ 2))
      (u * Real.exp (-(δ ^ 2 * u ^ 2 / 2))) u := by
    intro u _
    have h := ((((hasDerivAt_pow 2 u).const_mul (δ ^ 2)).div_const 2).neg.exp.div_const (δ ^ 2)).neg
    convert h using 1
    simp only [Pi.neg_apply]; push_cast; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- One Gaussian piece `[a/δ, b/δ]`, `1 ≤ a ≤ b`. -/
theorem gauss_piece {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {C₁ κ₁ : ℝ} (hC : 0 ≤ C₁)
    (hk : 0 ≤ κ₁) {f : ℝ → ℝ} (hf : Continuous f)
    (hle : ∀ u, a / δ ≤ u → f u ≤ Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (C₁ + κ₁ * Real.log (δ * u))) :
    ∫ u in (a / δ)..(b / δ), f u ≤
      (C₁ + κ₁ * Real.log b) * ((Real.exp (-(a ^ 2 / 2)) - Real.exp (-(b ^ 2 / 2))) / a ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hab' : a / δ ≤ b / δ := div_le_div_of_nonneg_right hab hδ.le
  have hI := integral_mul_exp_gauss hδ (a / δ) (b / δ)
  have e1 : δ ^ 2 * (a / δ) ^ 2 / 2 = a ^ 2 / 2 := by field_simp
  have e2 : δ ^ 2 * (b / δ) ^ 2 / 2 = b ^ 2 / 2 := by field_simp
  rw [e1, e2] at hI
  have hK : 0 ≤ (C₁ + κ₁ * Real.log b) * (δ ^ 2 / a ^ 2) := by
    have : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    positivity
  calc ∫ u in (a / δ)..(b / δ), f u ≤
      ∫ u in (a / δ)..(b / δ), (C₁ + κ₁ * Real.log b) * (δ ^ 2 / a ^ 2) * (u * Real.exp (-(δ ^ 2 * u ^ 2 / 2))) := by
        refine intervalIntegral.integral_mono_on hab' (hf.intervalIntegrable _ _)
          (by apply Continuous.intervalIntegrable; fun_prop) fun u hu => (hle u hu.1).trans ?_
        have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
        have hδu : a ≤ δ * u := by have := hu.1; rw [div_le_iff₀ hδ] at this; linarith
        have hδu2 : δ * u ≤ b := by have := hu.2; rw [le_div_iff₀ hδ] at this; linarith
        have hlog0 : 0 ≤ Real.log (δ * u) := Real.log_nonneg (by linarith)
        have hlog : Real.log (δ * u) ≤ Real.log b := Real.log_le_log (by linarith) hδu2
        have hinv : 1 / u ≤ δ ^ 2 / a ^ 2 * u := by
          rw [div_le_iff₀ hu0]
          have : a ^ 2 ≤ (δ * u) ^ 2 := pow_le_pow_left₀ ha0.le hδu 2
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
        have hE := Real.exp_pos (-(δ ^ 2 * u ^ 2 / 2))
        calc Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (C₁ + κ₁ * Real.log (δ * u)) =
            Real.exp (-(δ ^ 2 * u ^ 2 / 2)) * (1 / u) * (C₁ + κ₁ * Real.log (δ * u)) := by ring
          _ ≤ Real.exp (-(δ ^ 2 * u ^ 2 / 2)) * (δ ^ 2 / a ^ 2 * u) * (C₁ + κ₁ * Real.log b) := by
            gcongr
          _ = _ := by ring
    _ = _ := by
        rw [intervalIntegral.integral_const_mul, hI]
        field_simp

/-- The Gaussian tail `[3/δ, W]`. -/
theorem gauss_tail {δ : ℝ} (hδ : 0 < δ) {W : ℝ} (hW : 3 / δ ≤ W) {C₁ κ₁ : ℝ} (hC : 0 ≤ C₁)
    (hk : 0 ≤ κ₁) {f : ℝ → ℝ} (hf : Continuous f)
    (hle : ∀ u, 3 / δ ≤ u → f u ≤ Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (C₁ + κ₁ * Real.log (δ * u))) :
    ∫ u in (3 / δ)..W, f u ≤ (C₁ / 9 + κ₁ / 3) * Real.exp (-(9 / 2)) := by
  have hI := integral_mul_exp_gauss hδ (3 / δ) W
  have e1 : δ ^ 2 * (3 / δ) ^ 2 / 2 = 9 / 2 := by field_simp; norm_num
  rw [e1] at hI
  have hK : 0 ≤ (C₁ / 9 + κ₁ / 3) * δ ^ 2 := by positivity
  calc ∫ u in (3 / δ)..W, f u ≤
      ∫ u in (3 / δ)..W, (C₁ / 9 + κ₁ / 3) * δ ^ 2 * (u * Real.exp (-(δ ^ 2 * u ^ 2 / 2))) := by
        refine intervalIntegral.integral_mono_on hW (hf.intervalIntegrable _ _)
          (by apply Continuous.intervalIntegrable; fun_prop) fun u hu => (hle u hu.1).trans ?_
        have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
        have hδu : 3 ≤ δ * u := by have := hu.1; rw [div_le_iff₀ hδ] at this; linarith
        have hlog : Real.log (δ * u) ≤ δ * u := by
          have := Real.log_le_sub_one_of_pos (by linarith : 0 < δ * u); linarith
        have hE := Real.exp_pos (-(δ ^ 2 * u ^ 2 / 2))
        have h1 : C₁ / u ≤ C₁ / 9 * δ ^ 2 * u := by
          rw [div_le_iff₀ hu0]; nlinarith [mul_le_mul hδu hδu (by norm_num) (by linarith)]
        have h2 : κ₁ * Real.log (δ * u) / u ≤ κ₁ / 3 * δ ^ 2 * u := by
          rw [div_le_iff₀ hu0]
          have : κ₁ * Real.log (δ * u) ≤ κ₁ * (δ * u) := mul_le_mul_of_nonneg_left hlog hk
          nlinarith [mul_le_mul_of_nonneg_left hδu (mul_nonneg hk (mul_nonneg hδ.le hu0.le))]
        calc Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (C₁ + κ₁ * Real.log (δ * u)) =
            Real.exp (-(δ ^ 2 * u ^ 2 / 2)) * (C₁ / u + κ₁ * Real.log (δ * u) / u) := by ring
          _ ≤ Real.exp (-(δ ^ 2 * u ^ 2 / 2)) * (C₁ / 9 * δ ^ 2 * u + κ₁ / 3 * δ ^ 2 * u) := by gcongr
          _ = _ := by ring
    _ = (C₁ / 9 + κ₁ / 3) * (Real.exp (-(9 / 2)) - Real.exp (-(δ ^ 2 * W ^ 2 / 2))) := by
        rw [intervalIntegral.integral_const_mul, hI]; field_simp
    _ ≤ _ := by
        have := Real.exp_pos (-(δ ^ 2 * W ^ 2 / 2))
        have : 0 ≤ C₁ / 9 + κ₁ / 3 := by positivity
        nlinarith

/-- The Gaussian constants of region D. -/
noncomputable def EpD : ℝ :=
  (Real.exp (-(1 / 2)) - Real.exp (-((5 / 4) ^ 2 / 2))) / 1 ^ 2 +
  (Real.exp (-((5 / 4) ^ 2 / 2)) - Real.exp (-((3 / 2) ^ 2 / 2))) / (5 / 4) ^ 2 +
  (Real.exp (-((3 / 2) ^ 2 / 2)) - Real.exp (-(2 ^ 2 / 2))) / (3 / 2) ^ 2 +
  (Real.exp (-(2 ^ 2 / 2)) - Real.exp (-(3 ^ 2 / 2))) / 2 ^ 2 + Real.exp (-(9 / 2)) / 9

noncomputable def FpD : ℝ :=
  Real.log (5 / 4) * ((Real.exp (-(1 / 2)) - Real.exp (-((5 / 4) ^ 2 / 2))) / 1 ^ 2) +
  Real.log (3 / 2) * ((Real.exp (-((5 / 4) ^ 2 / 2)) - Real.exp (-((3 / 2) ^ 2 / 2))) / (5 / 4) ^ 2) +
  Real.log 2 * ((Real.exp (-((3 / 2) ^ 2 / 2)) - Real.exp (-(2 ^ 2 / 2))) / (3 / 2) ^ 2) +
  Real.log 3 * ((Real.exp (-(2 ^ 2 / 2)) - Real.exp (-(3 ^ 2 / 2))) / 2 ^ 2) + Real.exp (-(9 / 2)) / 3

/-- **Region D.** -/
theorem regionD_le {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 < R) {p₀ κ₁ κ₀ : ℝ} (hp₀ : 0 ≤ p₀) (hk₁ : 0 ≤ κ₁)
    (hκ : 0 ≤ κ₀ + κ₁ * Real.log R) {δ U W : ℝ} (hδ : 0 < δ) (hRU : R ≤ U) (hU0 : 2.39 ≤ U)
    (hUδ : U ≤ 1 / δ) (hW : 3 / δ ≤ W) :
    ∫ s in (R + 1 / δ)..(R + W), WI δ ℓ p₀ κ₁ κ₀ R s ≤
      (c0C ℓ p₀ κ₀ R U + κ₁ * Real.log (1 / δ) + c2C κ₁ R U * δ) * EpD + κ₁ * FpD := by
  have hU : 0 < U := by linarith
  set c₀ := c0C ℓ p₀ κ₀ R U
  set c₂ := c2C κ₁ R U
  set C₁ := c₀ + κ₁ * Real.log (1 / δ) + c₂ * δ with hC₁
  have hk1 : 0 ≤ κ₁ := hk₁
  have hc2 : 0 ≤ c₂ := by simp only [c₂, c2C]; have := Real.pi_pos; positivity
  have hc0 : κ₀ ≤ c₀ := by
    simp only [c₀, c0C]
    have h0 : 0 < max 1 (ℓ * (U + R)) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have : 0 ≤ p₀ / max 1 (ℓ * (U + R)) ^ 4 := div_nonneg hp₀ (by positivity)
    linarith
  have hC0 : 0 ≤ C₁ := by
    have : κ₁ * Real.log R ≤ κ₁ * Real.log (1 / δ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hR (by linarith)) hk1
    have : 0 ≤ c₂ * δ := by positivity
    linarith
  have e : ∫ s in (R + 1 / δ)..(R + W), WI δ ℓ p₀ κ₁ κ₀ R s = ∫ u in (1 / δ)..W, WI δ ℓ p₀ κ₁ κ₀ R (u + R) := by
    rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> ring
  rw [e]
  have hf : Continuous fun u => WI δ ℓ p₀ κ₁ κ₀ R (u + R) :=
    (continuous_WI δ ℓ p₀ κ₁ κ₀ hR).comp (continuous_id.add continuous_const)
  have hle : ∀ u, 1 / δ ≤ u →
      WI δ ℓ p₀ κ₁ κ₀ R (u + R) ≤ Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u * (C₁ + κ₁ * Real.log (δ * u)) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
    have huU : U ≤ u := hUδ.trans hu
    rw [WI_eq (by linarith)]
    have hG : GW δ R (u + R) = Real.exp (-(δ ^ 2 * u ^ 2 / 2)) / u := by
      unfold GW gW
      rw [show u + R - R = u by ring, max_eq_right hu0.le, max_eq_left (by linarith)]
    rw [hG]
    have hP := PsiG_shift_le (κ₀ := κ₀) hℓ hR hp₀ hk₁ hU huU
    have hlog : Real.log u = Real.log (1 / δ) + Real.log (δ * u) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have hc2u : c₂ / u ≤ c₂ * δ := by
      rw [div_le_iff₀ hu0]
      have : 1 ≤ δ * u := by rw [div_le_iff₀ hδ] at hu; linarith
      nlinarith
    refine mul_le_mul_of_nonneg_left (hP.trans ?_) (by positivity)
    rw [hlog, hC₁]; nlinarith
  have hδ1 : (1 : ℝ) / δ ≤ 5 / 4 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
  have p1 := gauss_piece hδ (a := 1) (b := 5 / 4) le_rfl (by norm_num) hC0 hk1 hf (fun u hu => hle u hu)
  have p2 := gauss_piece hδ (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num) hC0 hk1 hf
    (fun u hu => hle u (hδ1.trans hu))
  have p3 := gauss_piece hδ (a := 3 / 2) (b := 2) (by norm_num) (by norm_num) hC0 hk1 hf
    (fun u hu => hle u ((div_le_div_of_nonneg_right (by norm_num) hδ.le).trans hu))
  have p4 := gauss_piece hδ (a := 2) (b := 3) (by norm_num) (by norm_num) hC0 hk1 hf
    (fun u hu => hle u ((div_le_div_of_nonneg_right (by norm_num) hδ.le).trans hu))
  have p5 := gauss_tail hδ hW hC0 hk1 hf
    (fun u hu => hle u ((div_le_div_of_nonneg_right (by norm_num) hδ.le).trans hu))
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => WI δ ℓ p₀ κ₁ κ₀ R (u + R)) volume a b :=
    fun a b => hf.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ (5 / 4 / δ)) (hi _ W),
    ← intervalIntegral.integral_add_adjacent_intervals (hi _ (3 / 2 / δ)) (hi _ W),
    ← intervalIntegral.integral_add_adjacent_intervals (hi _ (2 / δ)) (hi _ W),
    ← intervalIntegral.integral_add_adjacent_intervals (hi _ (3 / δ)) (hi _ W)]
  rw [show (1 : ℝ) / δ = 1 / δ from rfl] at p1
  have e2 : Real.log 1 = 0 := Real.log_one
  unfold EpD FpD
  simp only [one_pow, div_one] at p1 ⊢
  norm_num at p1 p2 p3 p4 p5 ⊢
  nlinarith [p1, p2, p3, p4, p5]

/-! ### Assembly -/

/-- The four regions, `Ψ`-integrated. -/
noncomputable def RegA (ℓ p₀ κ₁ κ₀ R : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, PsiBarG ℓ p₀ κ₁ κ₀ R (k * ((R + 2.39) / n)) ((k + 1) * ((R + 2.39) / n)) / 2.39 * ((R + 2.39) / n)
noncomputable def RegB (ℓ p₀ κ₁ κ₀ R r : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, PsiBarG ℓ p₀ κ₁ κ₀ R (R + 2.39 * r ^ k) (R + 2.39 * r ^ (k + 1)) * Real.log r
noncomputable def RegC (ℓ p₀ κ₁ κ₀ R U δ : ℝ) : ℝ :=
  PhiC δ (c0C ℓ p₀ κ₀ R U) (κ₁) (c2C κ₁ R U) (1 / δ) - PhiC δ (c0C ℓ p₀ κ₀ R U) (κ₁) (c2C κ₁ R U) U
noncomputable def RegD (ℓ p₀ κ₁ κ₀ R U δ : ℝ) : ℝ :=
  (c0C ℓ p₀ κ₀ R U + κ₁ * Real.log (1 / δ) + c2C κ₁ R U * δ) * EpD + κ₁ * FpD

/-- **The window integral** over `[−(Y₁ + R), Y₁ + R]`, `(∫ G Φ⁺)/B_R ≤ 2(A + B + C + D)`, for
`3/δ ≤ Y₁`. -/
theorem window_int_regionsH {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 3 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hlR : ℓ ^ 2 * R ^ 2 ≤ 6) (hkB : 0 < kB ℓ R) {p₀ κ₁ κ₀ : ℝ} (hp : p0 ℓ R ≤ p₀) (hk : kap1 ℓ R ≤ κ₁)
    (hk0 : kap0 ℓ N R ≤ κ₀) (hκ : 0 ≤ κ₀ + κ₁ * Real.log R)
    {r : ℝ} (hr : 1 ≤ r) {nA nB : ℕ} (hnA : 0 < nA) (hRU : R ≤ 2.39 * r ^ nB) {δ : ℝ} (hδ : 0 < δ)
    (hUδ : 2.39 * r ^ nB ≤ 1 / δ) {Y₁ : ℝ} (hW : 3 / δ ≤ Y₁) :
    (∫ t in (-(Y₁ + R))..(Y₁ + R), gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ 2 N R t) / KRB ℓ 2 R ≤
      2 * (RegA ℓ p₀ κ₁ κ₀ R nA + RegB ℓ p₀ κ₁ κ₀ R r nB + RegC ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ + RegD ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ) := by
  have hR0 : 0 < R := by linarith
  have hKK := KRB_ge hℓ hR0.le hlR
  have hU0 : 2.39 ≤ 2.39 * r ^ nB := le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hr)
  have hδW : 1 / δ ≤ Y₁ := by
    have : 1 / δ ≤ 3 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
    linarith
  have hK0 : 0 < K0 ℓ R := by unfold K0; positivity
  have hp₀ : 0 ≤ p₀ := le_trans (by unfold p0; positivity) hp
  have hk₁ : 0 ≤ κ₁ := le_trans (kap1_nonneg hR0 hK0) hk
  refine (window_int_le hℓ hN hR hkB hKK hp hk hk0 δ (Y₁ + R) (by linarith)).trans ?_
  have hi : ∀ a b : ℝ, IntervalIntegrable (WI δ ℓ p₀ κ₁ κ₀ R) volume a b :=
    fun a b => (continuous_WI δ ℓ p₀ κ₁ κ₀ hR0).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (R + 2.39)) (hi _ (Y₁ + R)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi _ (R + 2.39 * r ^ nB)) (hi _ (Y₁ + R)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi _ (R + 1 / δ)) (hi _ (Y₁ + R))]
  have hA := regionA_le hℓ hR0 hp₀ hk₁ hκ δ nA hnA
  have hB := regionB_le hℓ hR0 hp₀ hk₁ hκ δ hr nB
  have hC := regionC_le hℓ hR0 hp₀ hk₁ hκ hδ hRU hU0 hUδ
  have hD := regionD_le hℓ hR0 hp₀ hk₁ hκ hδ hRU hU0 hUδ hW
  rw [show Y₁ + R = R + Y₁ by ring]
  unfold RegA RegB RegC RegD
  linarith

/-- **The window integral**, `(∫ G Φ⁺)/B_R ≤ 2(A + B + C + D)`. -/
theorem window_int_regions {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 3 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hlR : ℓ ^ 2 * R ^ 2 ≤ 6) (hkB : 0 < kB ℓ R) {p₀ κ₁ κ₀ : ℝ} (hp : p0 ℓ R ≤ p₀) (hk : kap1 ℓ R ≤ κ₁)
    (hk0 : kap0 ℓ N R ≤ κ₀) (hκ : 0 ≤ κ₀ + κ₁ * Real.log R)
    {r : ℝ} (hr : 1 ≤ r) {nA nB : ℕ} (hnA : 0 < nA) (hRU : R ≤ 2.39 * r ^ nB) {δ : ℝ} (hδ : 0 < δ)
    (hUδ : 2.39 * r ^ nB ≤ 1 / δ) (hW : 3 / δ ≤ 1e10) :
    (∫ t in (-(1e10 + R))..(1e10 + R), gW δ 2.39 (max 0 (|t| - R)) * PhiUp ℓ 2 N R t) / KRB ℓ 2 R ≤
      2 * (RegA ℓ p₀ κ₁ κ₀ R nA + RegB ℓ p₀ κ₁ κ₀ R r nB + RegC ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ + RegD ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ) :=
  window_int_regionsH hℓ hN hR hlR hkB hp hk hk0 hκ hr hnA hRU hδ hUδ hW

/-- **The line zeros `|γ| ≤ H`, in closed form**, under RH up to `H ∈ [10⁸, 3·10¹⁰]`
(`1/2 ≤ Y₁`, `Y₁ + R ≤ H/2`, `3/δ ≤ Y₁`). -/
theorem line_sum_closedH {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (h2 : Real.exp (2 * (2 : ℕ) * ℓ) < 2) {N : ℕ} (hN : 3 ≤ N) {H Y₁ : ℝ} (hRH : RHBelow H)
    (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10) {R : ℝ} (hR : 1 ≤ R) (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + R ≤ H / 2)
    (hlR : ℓ ^ 2 * R ^ 2 ≤ 6) (hkB : 0 < kB ℓ R) {p₀ κ₁ κ₀ : ℝ} (hp : p0 ℓ R ≤ p₀) (hk : kap1 ℓ R ≤ κ₁)
    (hk0 : kap0 ℓ N R ≤ κ₀) (hκ : 0 ≤ κ₀ + κ₁ * Real.log R)
    {r : ℝ} (hr : 1 ≤ r) {nA nB : ℕ} (hnA : 0 < nA) (hRU : R ≤ 2.39 * r ^ nB) {δ : ℝ} (hδ : 0 < δ)
    (hUδ : 2.39 * r ^ nB ≤ 1 / δ) (hW : 3 / δ ≤ Y₁) (a b T : ℝ) :
    ∑ u ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ H), (multRectD zetaF T u : ℝ) * ‖Mg a b δ u‖ ≤
      Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) *
        (2 * (RegA ℓ p₀ κ₁ κ₀ R nA + RegB ℓ p₀ κ₁ κ₀ R r nB + RegC ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ + RegD ℓ p₀ κ₁ κ₀ R (2.39 * r ^ nB) δ) +
          Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H) := by
  have hR0 : 0 < R := by linarith
  have hK : 0 < KRB ℓ 2 R := lt_of_lt_of_le (by positivity) (KRB_ge hℓ hR0.le hlR)
  refine (line_sum_weil_allH hℓ hℓ1 (le_refl 2) h2 hN hRH hH1 hH2 hR hY₁0 hY₁ hK a b δ T).trans ?_
  have hreg := window_int_regionsH hℓ hN hR hlR hkB hp hk hk0 hκ hr hnA hRU hδ hUδ hW
  gcongr

end TernaryGoldbach.Explicit
