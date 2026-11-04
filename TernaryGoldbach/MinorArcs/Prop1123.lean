import TernaryGoldbach.MinorArcs.GMono
import Mathlib.NumberTheory.Chebyshev

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# [H, Prop. 11.2.3]: from `η₂` to `η_* = (η₂ *_M φ)(κ·)` — corrected form

`S_{η_*}(α, x) = ∫ S_{η₂}(α, wy) φ(w) dw/w` with `y = x/κ` (`S_etaStar_eq`).  If
`2α = a/q + δ/y`, then at scale `wy` the approximation reads `2α = a/q + (wδ)/(wy)`, so
Theorem 3.1.1 at scale `wy` is in terms of `r_w = max(1, w|δ|/8) q`, **not** [H]'s
`r = max(1, |δ|/8) q` (see `NOTES.md`, "Prop 11.2.3 erratum").  Since `r_w ≥ min(1, w) r` and
`g` is non-increasing (`gx_antitoneOn`), the per-scale bound is `g_{wy}(min(1, w) r)`.

`prop_11_2_3` splits the `w`-integral into
* `(0, w₀)` and `(w₁, ∞)`: the trivial bound `|S_{η₂}(α, z)| ≤ 17 z` (`norm_S_eta2_le_trivial`,
  from Chebyshev's `ψ(z) ≤ (log 4 + 4) z`; [H] uses `1.04488 z`, Cor. C.1.3);
* `[w₀, w₁]`: Theorem 3.1.1 at scale `wy`, with any integrable majorant `G(w)` of
  `g_{wy}(min(1, w) r)` (to be supplied by numerics).

[H]'s `K` is our `1/w₀`; the condition at `w₁` is Thm 3.1.1's `|δ/y| ≤ 1/(q Q_{w₁y})`.

Proved, modulo the trusted inputs of `theorem_3_1_1` and Lemma C.2.2.
-/

open Real Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 etaStar S phi κ eta2_nonneg eta2_le eta2_eq_zero)

/-- The trivial bound `|S_{η₂}(α, z)| ≤ 3 ψ(z) ≤ 17 z`. -/
theorem norm_S_eta2_le_trivial {z : ℝ} (hz : 0 < z) (α : ℝ) : ‖S eta2 z α‖ ≤ 17 * z := by
  unfold S
  have hs : ∀ n ∉ Finset.range (⌊z⌋₊ + 1),
      ((Λ n * eta2 (n / z) : ℝ) : ℂ) * TernaryGoldbach.e (n * α) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff, Nat.floor_lt hz.le] at hn
    rw [eta2_eq_zero, mul_zero, Complex.ofReal_zero, zero_mul]
    rintro ⟨-, h1⟩
    rw [div_lt_one hz] at h1
    linarith
  rw [tsum_eq_sum hs]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n ∈ Finset.range (⌊z⌋₊ + 1),
      ‖((Λ n * eta2 (n / z) : ℝ) : ℂ) * TernaryGoldbach.e (n * α)‖ ≤ 3 * Λ n := by
    intro n _
    rw [norm_mul, TernaryGoldbach.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (eta2_nonneg _))]
    nlinarith [eta2_le (n / z), @ArithmeticFunction.vonMangoldt_nonneg n]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hpsi : ∑ n ∈ Finset.range (⌊z⌋₊ + 1), Λ n = Chebyshev.psi z := by
    have e : Finset.range (⌊z⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊z⌋₊) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [e, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
    rfl
  rw [hpsi]
  have h4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have := Chebyshev.psi_le_const_mul_self hz.le
  nlinarith

/-- `r = max(1, |δ|/8) q ≤ x^{1/3}/6` for an approximation as in Theorem 3.1.1 with
`q ≤ x^{1/3}/6` (`δ₀q = 2r ≤ x^{1/3}/3`). -/
theorem r_le_cube_root {α x δ : ℝ} {a : ℤ} {q : ℕ} (hx : 2.16e20 ≤ x)
    (h : Approx2 α x δ a q (3 / 4 * x ^ (2 / 3 : ℝ))) (hq : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) / 6) :
    max 1 (|δ| / 8) * q ≤ x ^ (1 / 3 : ℝ) / 6 := by
  obtain ⟨hT, hT3, hT23, -⟩ := cube_root_facts hx
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hq0 : (0 : ℝ) < q := by linarith
  have hd := h.2.2.2.1
  rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by rw [hT23]; positivity), one_mul] at hd
  rcases le_total 1 (|δ| / 8) with hm | hm
  · rw [max_eq_right hm]
    have : |δ| * q * (3 / 4 * (x ^ (1 / 3 : ℝ)) ^ 2) ≤ (x ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [hT3]
      calc |δ| * q * (3 / 4 * (x ^ (1 / 3 : ℝ)) ^ 2) = |δ| * (q * (3 / 4 * x ^ (2 / 3 : ℝ))) := by
            rw [hT23]; ring
        _ ≤ x := hd
    have hT0 : 0 < x ^ (1 / 3 : ℝ) := by linarith
    nlinarith
  · rw [max_eq_left hm]; linarith

/-- `min(1, w) · max(1, |δ|/8) ≤ max(1, w|δ|/8)`. -/
theorem min_mul_max_le {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    min 1 w * max 1 (d / 8) ≤ max 1 (w * d / 8) := by
  rcases le_total w 1 with h | h
  · rw [min_eq_right h, mul_max_of_nonneg _ _ hw.le, mul_one]
    exact max_le_max h (le_of_eq (by ring))
  · rw [min_eq_left h, one_mul]
    exact max_le_max le_rfl (by nlinarith)

theorem integrable_phi : Integrable phi := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [phi, Real.rpow_two]
  ring_nf

theorem phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

/-- **[H, Prop. 11.2.3], corrected** (first case, `q` small).  Let `y = x/κ` and
`2α = a/q + δ/y` with `(a, q) = 1`, `|δ/y| ≤ 1/(q Q_y)`, `Q_y = (3/4)y^{2/3}`; let
`r = max(1, |δ|/8) q`.  Let `0 < w₀ ≤ 1 ≤ w₁` with `w₀ y ≥ 2.16·10²⁰`, `q ≤ (w₀y)^{1/3}/6`,
`w₀ r ≥ 670`, and `|δ/y| ≤ 1/(q Q_{w₁y})`.  If `G(w) ≥ g_{wy}(min(1, w) r)` on `[w₀, w₁]` with
`Gφ` integrable there, then
`|S_{η_*}(α, x)| ≤ y (∫_{w₀}^{w₁} G φ + 17 (∫_0^{w₀} φ + ∫_{w₁}^∞ φ))`. -/
theorem prop_11_2_3 {α x δ w₀ w₁ : ℝ} {a : ℤ} {q : ℕ} {G : ℝ → ℝ} (hx : 0 < x)
    (h : Approx2 α (x / κ) δ a q (3 / 4 * (x / κ) ^ (2 / 3 : ℝ)))
    (hw₀ : 0 < w₀) (hw₀1 : w₀ ≤ 1) (hw₁ : 1 ≤ w₁) (hy : 2.16e20 ≤ w₀ * (x / κ))
    (hq : (q : ℝ) ≤ (w₀ * (x / κ)) ^ (1 / 3 : ℝ) / 6)
    (hr : 670 ≤ w₀ * (max 1 (|δ| / 8) * q))
    (hδ₁ : |δ / (x / κ)| ≤ 1 / (q * (3 / 4 * (w₁ * (x / κ)) ^ (2 / 3 : ℝ))))
    (hG : ∀ w ∈ Icc w₀ w₁, gx (w * (x / κ)) (min 1 w * (max 1 (|δ| / 8) * q)) ≤ G w)
    (hGi : IntegrableOn (fun w => G w * phi w) (Icc w₀ w₁)) :
    ‖S etaStar x α‖ ≤ x / κ * ((∫ w in Icc w₀ w₁, G w * phi w) +
      17 * ((∫ w in Ioo 0 w₀, phi w) + ∫ w in Ioi w₁, phi w)) := by
  have hκ : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
  set y := x / κ with hy_def
  have hy0 : 0 < y := div_pos hx hκ
  set r := max 1 (|δ| / 8) * q with hr_def
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  -- the majorant
  set B : ℝ → ℝ := fun w =>
    (Ioo 0 w₀).indicator (fun w => 17 * y * phi w) w +
      (Icc w₀ w₁).indicator (fun w => y * (G w * phi w)) w +
      (Ioi w₁).indicator (fun w => 17 * y * phi w) w with hB
  have hφi : IntegrableOn (fun w => 17 * y * phi w) univ :=
    (integrable_phi.const_mul (17 * y)).integrableOn
  have hBi : Integrable B (volume.restrict (Ioi 0)) := by
    refine Integrable.add (Integrable.add ?_ ?_) ?_
    · exact (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioo).restrict
    · exact (IntegrableOn.integrable_indicator (hGi.const_mul y) measurableSet_Icc).restrict
    · exact (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioi).restrict
  -- pointwise bound
  have hpt : ∀ w ∈ Ioi (0 : ℝ), ‖S eta2 (w * y) α‖ * (phi w / w) ≤ B w := by
    intro w (hw : 0 < w)
    have hφw : 0 ≤ phi w / w := div_nonneg (phi_nonneg w) hw.le
    have triv : ‖S eta2 (w * y) α‖ * (phi w / w) ≤ 17 * y * phi w := by
      have := norm_S_eta2_le_trivial (mul_pos hw hy0) α
      calc ‖S eta2 (w * y) α‖ * (phi w / w) ≤ 17 * (w * y) * (phi w / w) :=
            mul_le_mul_of_nonneg_right this hφw
        _ = 17 * y * phi w := by field_simp
    rcases lt_or_ge w w₀ with h1 | h1
    · have : B w = 17 * y * phi w := by
        simp only [hB, indicator, mem_Ioo, mem_Icc, mem_Ioi, hw, h1, true_and, ite_true]
        rw [ite_eq_right (by intro h'; linarith [h'.1]), ite_eq_right (by intro h'; linarith)]; ring
      rw [this]; exact triv
    rcases le_or_gt w w₁ with h2 | h2
    · have hBw : B w = y * (G w * phi w) := by
        simp only [hB, indicator, mem_Ioo, mem_Icc, mem_Ioi]
        rw [ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_left ⟨h1, h2⟩, ite_eq_right (by intro h'; linarith)]
        ring
      rw [hBw]
      -- Theorem 3.1.1 at scale `wy`
      have hz : 2.16e20 ≤ w * y := hy.trans (by gcongr)
      have hqz : (q : ℝ) ≤ (w * y) ^ (1 / 3 : ℝ) / 6 :=
        hq.trans (by gcongr)
      obtain ⟨hTz, -, hTz23, -⟩ := cube_root_facts hz
      have hQz : (q : ℝ) ≤ 3 / 4 * (w * y) ^ (2 / 3 : ℝ) := by rw [hTz23]; nlinarith
      have hδz : |δ / y| ≤ 1 / (q * (3 / 4 * (w * y) ^ (2 / 3 : ℝ))) :=
        hδ₁.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))
      have h' := h.rescale hw hδz hQz
      have hmm := min_mul_max_le hw (abs_nonneg δ)
      have hrw : min 1 w * r ≤ max 1 (|w * δ| / 8) * q := by
        rw [abs_mul, abs_of_pos hw, hr_def, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hmm (by linarith)
      have hlow : 670 ≤ min 1 w * r := by
        have : w₀ ≤ min 1 w := le_min hw₀1 h1
        nlinarith [show (0 : ℝ) ≤ r by positivity]
      have key := norm_S_eta2_le_gx hz h' hqz (by linarith)
      have hup := r_le_cube_root hz h' hqz
      have hmono := gx_antitoneOn hz ⟨hlow, hrw.trans hup⟩ ⟨hlow.trans hrw, hup⟩ hrw
      calc ‖S eta2 (w * y) α‖ * (phi w / w)
          ≤ gx (w * y) (max 1 (|w * δ| / 8) * q) * (w * y) * (phi w / w) :=
            mul_le_mul_of_nonneg_right key hφw
        _ ≤ G w * (w * y) * (phi w / w) := by
            gcongr
            exact hmono.trans (hG w ⟨h1, h2⟩)
        _ = y * (G w * phi w) := by field_simp
    · have : B w = 17 * y * phi w := by
        simp only [hB, indicator, mem_Ioo, mem_Icc, mem_Ioi]
        rw [ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_left h2]
        ring
      rw [this]; exact triv
  -- integrate
  refine (norm_S_etaStar_le hx α).trans ?_
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun w => ‖S eta2 (w * y) α‖ * (phi w / w) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w (hw : 0 < w) =>
      mul_nonneg (norm_nonneg _) (div_nonneg (phi_nonneg w) hw.le))
  refine (integral_mono_of_nonneg hf0 hBi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))).trans (le_of_eq ?_)
  have I1 : Integrable ((Ioo 0 w₀).indicator (fun w => 17 * y * phi w)) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioo).restrict
  have I2 : Integrable ((Icc w₀ w₁).indicator (fun w => y * (G w * phi w))) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hGi.const_mul y) measurableSet_Icc).restrict
  have I3 : Integrable ((Ioi w₁).indicator (fun w => 17 * y * phi w)) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioi).restrict
  have I12 : Integrable (fun w => (Ioo 0 w₀).indicator (fun w => 17 * y * phi w) w +
      (Icc w₀ w₁).indicator (fun w => y * (G w * phi w)) w) (volume.restrict (Ioi 0)) := I1.add I2
  simp only [hB]
  rw [integral_add I12 I3, integral_add I1 I2, setIntegral_indicator measurableSet_Ioo,
    setIntegral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.2 Ioo_subset_Ioi_self,
    (inter_eq_right (s := Ioi (0:ℝ)) (t := Icc w₀ w₁)).2
      (fun w (hw : w ∈ Icc w₀ w₁) => lt_of_lt_of_le hw₀ hw.1),
    (inter_eq_right (s := Ioi (0:ℝ)) (t := Ioi w₁)).2 (Ioi_subset_Ioi (by linarith)),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

end TernaryGoldbach.MinorArcs
