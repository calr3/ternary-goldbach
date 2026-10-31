import TernaryGoldbach.MinorArcs.Prop1123
import TernaryGoldbach.MinorArcs.OffArcs
import TernaryGoldbach.MinorArcs.SecondChoice

/-!
# Prop 11.2.3′: the ℓ∞ bound for `S_{η_*}` off the major arcs at scale `y`

A replacement for [B, Prop. 11.2.3] that suits Ch. 13 (NOTES, "Ch. 13: scale erratum", repair 3).
In `S_{η_*}(α, x) = ∫ S_{η₂}(α, wy) φ(w) dw/w`, `y = x/κ`, it takes **a fresh Dirichlet
approximation `2α = a_w/q_w + δ_w/(wy)` at each scale `wy`** (`exists_approx2`). If
`α ∉ 𝔐_{8,n}(y)`, then `r_w = max(1, |δ_w|/8) q_w ≥ min(1, w) n`, by `le_rAlpha_of_not_mem` at
scale `y` (with `δ = δ_w/w`) and `min_mul_max_le`. Then Theorem 3.1.1 at scale `wy` gives:
* if `q_w ≤ (wy)^{1/3}/6`: `g_{wy}(r_w) ≤ g_{wy}(min(1, w) n)`. Here `r_w ≤ (wy)^{1/3}/6`
  (`r_le_cube_root`), so `gx_antitoneOn` applies;
* if `q_w > (wy)^{1/3}/6`: the second-case bound `0.276 z^{5/6} (log z)^{3/2} + 1234 z^{2/3} log z`.

Unlike `prop_11_2_3`, there is no condition linking `w₁` to an approximation.

* `norm_S_etaStar_le_of_pointwise`: the integration step, for any pointwise majorant on `[w₀, w₁]`
  and the trivial bound `17z` elsewhere;
* **`prop_11_2_3'`**.

Proved, modulo the trusted inputs of `theorem_3_1_1` and Lemma C.2.2.
-/

open Real Set MeasureTheory

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 etaStar S phi κ majorArcs)

/-- The integration step of Prop 11.2.3: a pointwise bound `|S_{η₂}(α, wy)| ≤ G(w) wy` on
`[w₀, w₁]`, the trivial bound elsewhere. -/
theorem norm_S_etaStar_le_of_pointwise {α x w₀ w₁ : ℝ} {G : ℝ → ℝ} (hx : 0 < x)
    (hw₀ : 0 < w₀) (hw₀₁ : w₀ ≤ w₁)
    (hpw : ∀ w ∈ Icc w₀ w₁, ‖S eta2 (w * (x / κ)) α‖ ≤ G w * (w * (x / κ)))
    (hGi : IntegrableOn (fun w => G w * phi w) (Icc w₀ w₁)) :
    ‖S etaStar x α‖ ≤ x / κ * ((∫ w in Icc w₀ w₁, G w * phi w) +
      17 * ((∫ w in Ioo 0 w₀, phi w) + ∫ w in Ioi w₁, phi w)) := by
  have hκ : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
  set y := x / κ with hy_def
  have hy0 : 0 < y := div_pos hx hκ
  set B : ℝ → ℝ := fun w =>
    (Ioo 0 w₀).indicator (fun w => 17 * y * phi w) w +
      (Icc w₀ w₁).indicator (fun w => y * (G w * phi w)) w +
      (Ioi w₁).indicator (fun w => 17 * y * phi w) w with hB
  have hφi : IntegrableOn (fun w => 17 * y * phi w) univ :=
    (integrable_phi.const_mul (17 * y)).integrableOn
  have I1 : Integrable ((Ioo 0 w₀).indicator (fun w => 17 * y * phi w)) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioo).restrict
  have I2 : Integrable ((Icc w₀ w₁).indicator (fun w => y * (G w * phi w))) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hGi.const_mul y) measurableSet_Icc).restrict
  have I3 : Integrable ((Ioi w₁).indicator (fun w => 17 * y * phi w)) (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (hφi.mono_set (subset_univ _)) measurableSet_Ioi).restrict
  have I12 : Integrable (fun w => (Ioo 0 w₀).indicator (fun w => 17 * y * phi w) w +
      (Icc w₀ w₁).indicator (fun w => y * (G w * phi w)) w) (volume.restrict (Ioi 0)) := I1.add I2
  have hBi : Integrable B (volume.restrict (Ioi 0)) := I12.add I3
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
        rw [ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_left ⟨h1, h2⟩,
          ite_eq_right (by intro h'; linarith)]
        ring
      rw [hBw]
      calc ‖S eta2 (w * y) α‖ * (phi w / w) ≤ G w * (w * y) * (phi w / w) :=
            mul_le_mul_of_nonneg_right (hpw w ⟨h1, h2⟩) hφw
        _ = y * (G w * phi w) := by field_simp
    · have : B w = 17 * y * phi w := by
        simp only [hB, indicator, mem_Ioo, mem_Icc, mem_Ioi]
        rw [ite_eq_right (by intro h'; linarith [h'.2]), ite_eq_right (by intro h'; linarith [h'.2]),
          ite_eq_left h2]
        ring
      rw [this]; exact triv
  refine (norm_S_etaStar_le hx α).trans ?_
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun w => ‖S eta2 (w * y) α‖ * (phi w / w) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w (hw : 0 < w) =>
      mul_nonneg (norm_nonneg _) (div_nonneg (phi_nonneg w) hw.le))
  refine (integral_mono_of_nonneg hf0 hBi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))).trans (le_of_eq ?_)
  simp only [hB]
  rw [integral_add I12 I3, integral_add I1 I2, setIntegral_indicator measurableSet_Ioo,
    setIntegral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.2 Ioo_subset_Ioi_self,
    (inter_eq_right (s := Ioi (0:ℝ)) (t := Icc w₀ w₁)).2
      (fun w (hw : w ∈ Icc w₀ w₁) => lt_of_lt_of_le hw₀ hw.1),
    (inter_eq_right (s := Ioi (0:ℝ)) (t := Ioi w₁)).2 (Ioi_subset_Ioi (by linarith)),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- **Prop 11.2.3′.** Let `y = x/κ`, `α ∉ 𝔐_{8,n}(y)`, `0 < w₀ ≤ 1 ≤ w₁`, `w₀y ≥ 2.16·10²⁰`,
`w₀ n ≥ 670`. Let `G` be integrable against `φ` on `[w₀, w₁]` with, for `w ∈ [w₀, w₁]` and
`z = wy`, `G(w) ≥ g_z(min(1, w) n)` whenever `min(1, w) n ≤ z^{1/3}/6`, and
`G(w) z ≥ 0.276 z^{5/6} (log z)^{3/2} + 1234 z^{2/3} log z`. Then
`|S_{η_*}(α, x)| ≤ y (∫_{w₀}^{w₁} Gφ + 17 (∫_0^{w₀} φ + ∫_{w₁}^∞ φ))`. -/
theorem prop_11_2_3' {α x n w₀ w₁ : ℝ} {G : ℝ → ℝ} (hx : 0 < x)
    (hα : α ∉ majorArcs 8 n (x / κ)) (hw₀ : 0 < w₀) (hw₀1 : w₀ ≤ 1) (hw₁ : 1 ≤ w₁)
    (hy : 2.16e20 ≤ w₀ * (x / κ)) (hn : 670 ≤ w₀ * n)
    (hG1 : ∀ w ∈ Icc w₀ w₁, min 1 w * n ≤ (w * (x / κ)) ^ (1 / 3 : ℝ) / 6 →
      gx (w * (x / κ)) (min 1 w * n) ≤ G w)
    (hG2 : ∀ w ∈ Icc w₀ w₁, 0.276 * (w * (x / κ)) ^ (5 / 6 : ℝ) * Real.log (w * (x / κ)) ^ (3 / 2 : ℝ) +
      1234 * (w * (x / κ)) ^ (2 / 3 : ℝ) * Real.log (w * (x / κ)) ≤ G w * (w * (x / κ)))
    (hGi : IntegrableOn (fun w => G w * phi w) (Icc w₀ w₁)) :
    ‖S etaStar x α‖ ≤ x / κ * ((∫ w in Icc w₀ w₁, G w * phi w) +
      17 * ((∫ w in Ioo 0 w₀, phi w) + ∫ w in Ioi w₁, phi w)) := by
  have hκ : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num
  set y := x / κ with hy_def
  have hy0 : 0 < y := div_pos hx hκ
  have hn0 : 0 ≤ n := by
    by_contra h; push Not at h; nlinarith
  refine norm_S_etaStar_le_of_pointwise hx hw₀ (by linarith) (fun w hw => ?_) hGi
  have hw0 : 0 < w := lt_of_lt_of_le hw₀ hw.1
  set z := w * y with hz_def
  have hz : 2.16e20 ≤ z := hy.trans (by rw [hz_def]; exact mul_le_mul_of_nonneg_right hw.1 hy0.le)
  have hz0 : 0 < z := by linarith
  obtain ⟨hTz, -, hTz23, -⟩ := cube_root_facts hz
  have hQ1 : (1 : ℝ) ≤ 3 / 4 * z ^ (2 / 3 : ℝ) := by rw [hTz23]; nlinarith
  obtain ⟨δ, a, q, h⟩ := exists_approx2 α hz0 hQ1
  -- the same approximation, read at scale `y`
  have hy' : Approx2 α y (δ / w) a q (3 / 4 * z ^ (2 / 3 : ℝ)) := by
    obtain ⟨h1, h2, ⟨k, hk⟩, h4, h5⟩ := h
    have e : δ / w / y = δ / z := by rw [hz_def]; field_simp
    exact ⟨h1, h2, ⟨k, by rw [e]; exact hk⟩, by rw [e]; exact h4, h5⟩
  have hr := le_rAlpha_of_not_mem hy0 (by norm_num) hy' hα
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmm := min_mul_max_le hw0 (div_nonneg (abs_nonneg δ) hw0.le)
  have hrw : min 1 w * n ≤ max 1 (|δ| / 8) * q := by
    have e : w * (|δ| / w) / 8 = |δ| / 8 := by field_simp
    rw [e] at hmm
    rw [abs_div, abs_of_pos hw0] at hr
    calc min 1 w * n ≤ min 1 w * (max 1 (|δ| / w / 8) * q) :=
          mul_le_mul_of_nonneg_left hr (le_min zero_le_one hw0.le)
      _ = min 1 w * max 1 (|δ| / w / 8) * q := by ring
      _ ≤ max 1 (|δ| / 8) * q := mul_le_mul_of_nonneg_right hmm hq0
  rcases le_or_gt (q : ℝ) (z ^ (1 / 3 : ℝ) / 6) with hq | hq
  · have hlow : 670 ≤ min 1 w * n := by
      have : w₀ ≤ min 1 w := le_min hw₀1 hw.1
      nlinarith
    have key := norm_S_eta2_le_gx hz h hq (by linarith)
    have hup := r_le_cube_root hz h hq
    have hmono := gx_antitoneOn hz ⟨hlow, hrw.trans hup⟩ ⟨hlow.trans hrw, hup⟩ hrw
    calc ‖S eta2 z α‖ ≤ gx z (max 1 (|δ| / 8) * q) * z := key
      _ ≤ G w * z := by
          gcongr
          exact hmono.trans (hG1 w hw (hrw.trans hup))
  · exact ((theorem_3_1_1 hz h).2 hq).trans (hG2 w hw)

end TernaryGoldbach.MinorArcs
