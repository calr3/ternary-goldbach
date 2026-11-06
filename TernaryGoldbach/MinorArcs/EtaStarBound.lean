import TernaryGoldbach.MinorArcs.EtaStar
import TernaryGoldbach.MinorArcs.PointwiseBound

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Theorem 3.1.1 at the scales `w y` of (11.9) — towards [H, Prop. 11.2.3]

In `S_{η_*}(α, x) = ∫ S_{η₂}(α, w y) φ(w) dw/w` (`S_etaStar_eq`, `y = x/κ`), the approximation
`2α = a/q + δ/y` reads `2α = a/q + (wδ)/(wy)` at scale `wy`: **`δ` scales with `w`**, which
[H]'s proof of Prop. 11.2.3 overlooks (see `NOTES.md`).  For `w ≤ 1` the hypotheses of
Theorem 3.1.1 at scale `wy` follow from those at scale `y` (`Q_{wy} ≤ Q_y`); for `w > 1` they
need `|δ/y| ≤ 1/(q Q_{wy})` separately.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

omit [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.RamareMoebius] in
/-- An approximation at scale `y` is one at scale `wy` with `δ` replaced by `wδ`, as long as
`q ≤ Q'` and `|δ/y| ≤ 1/(q Q')` for the new `Q'`. -/
theorem Approx2.rescale {α y δ Q Q' w : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α y δ a q Q)
    (hw : 0 < w) (hQ' : |δ / y| ≤ 1 / (q * Q')) (hqQ' : (q : ℝ) ≤ Q') :
    Approx2 α (w * y) (w * δ) a q Q' := by
  obtain ⟨hq1, hcop, ⟨k, hk⟩, -, -⟩ := h
  have e : w * δ / (w * y) = δ / y := mul_div_mul_left δ y hw.ne'
  exact ⟨hq1, hcop, ⟨k, by rw [e]; exact hk⟩, by rwa [e], hqQ'⟩

omit [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.RamareMoebius] in
/-- `Q_z = (3/4) z^{2/3}` is monotone in `z`. -/
theorem Q_mono {z z' : ℝ} (hz : 0 ≤ z) (h : z ≤ z') :
    3 / 4 * z ^ (2 / 3 : ℝ) ≤ 3 / 4 * z' ^ (2 / 3 : ℝ) := by
  gcongr

/-- **Theorem 3.1.1 at scale `wy`, `w ≤ 1`** (first case).  If `2α = a/q + δ/y` is an
approximation with `Q = (3/4) y^{2/3}`, `0 < w ≤ 1`, `wy ≥ 2.16·10²⁰` and `q ≤ (wy)^{1/3}/6`, then
`|S_{η₂}(α, wy)|` is bounded by Theorem 3.1.1 at `x = wy` with `δ₀ = max(2, w|δ|/4)`. -/
theorem theorem_3_1_1_scaled_le_one {α y δ w : ℝ} {a : ℤ} {q : ℕ}
    (h : Approx2 α y δ a q (3 / 4 * y ^ (2 / 3 : ℝ))) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hz : 2.16e20 ≤ w * y) (hq : (q : ℝ) ≤ (w * y) ^ (1 / 3 : ℝ) / 6) :
    let δ₀ := max 2 (w * |δ| / 4)
    ‖S eta2 (w * y) α‖ ≤
      (R (w * y) (δ₀ * q) * Real.log (δ₀ * q) + 0.8764) / √(δ₀ * Nat.totient q) * (w * y) +
        2.526 * (w * y) / √(δ₀ * q) + 2 * (w * y) / (δ₀ * q) * L (δ₀ * q) q +
        3.8 * (w * y) ^ (5 / 6 : ℝ) := by
  intro δ₀
  have hy0 : 0 < y := by
    by_contra hy; push Not at hy
    have : w * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw0.le hy
    linarith
  have hwy : w * y ≤ y := by nlinarith
  obtain ⟨hT, -, h23, -⟩ := cube_root_facts hz
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hQle := Q_mono (by positivity) hwy
  have hQpos : 0 < 3 / 4 * (w * y) ^ (2 / 3 : ℝ) := by positivity
  have hqQ : (q : ℝ) ≤ 3 / 4 * (w * y) ^ (2 / 3 : ℝ) := by
    rw [h23]; nlinarith
  have hδ : |δ / y| ≤ 1 / (q * (3 / 4 * (w * y) ^ (2 / 3 : ℝ))) :=
    h.2.2.2.1.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))
  have h' := h.rescale hw0 hδ hqQ
  have key := (theorem_3_1_1 hz h').1 hq
  have e : |w * δ| / 4 = w * |δ| / 4 := by rw [abs_mul, abs_of_pos hw0]
  simpa only [e] using key

/-- **Theorem 3.1.1 at scale `wy`, any `w > 0`** (first case), with the scale-`wy` condition
`|δ/y| ≤ 1/(q Q_{wy})` as a hypothesis (automatic for `w ≤ 1`, see
`theorem_3_1_1_scaled_le_one`). -/
theorem theorem_3_1_1_scaled {α y δ w Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α y δ a q Q)
    (hw0 : 0 < w) (hz : 2.16e20 ≤ w * y) (hq : (q : ℝ) ≤ (w * y) ^ (1 / 3 : ℝ) / 6)
    (hδ : |δ / y| ≤ 1 / (q * (3 / 4 * (w * y) ^ (2 / 3 : ℝ)))) :
    let δ₀ := max 2 (w * |δ| / 4)
    ‖S eta2 (w * y) α‖ ≤
      (R (w * y) (δ₀ * q) * Real.log (δ₀ * q) + 0.8764) / √(δ₀ * Nat.totient q) * (w * y) +
        2.526 * (w * y) / √(δ₀ * q) + 2 * (w * y) / (δ₀ * q) * L (δ₀ * q) q +
        3.8 * (w * y) ^ (5 / 6 : ℝ) := by
  intro δ₀
  obtain ⟨hT, -, h23, -⟩ := cube_root_facts hz
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hqQ : (q : ℝ) ≤ 3 / 4 * (w * y) ^ (2 / 3 : ℝ) := by
    rw [h23]; nlinarith
  have key := (theorem_3_1_1 hz (h.rescale hw0 hδ hqQ)).1 hq
  have e : |w * δ| / 4 = w * |δ| / 4 := by rw [abs_mul, abs_of_pos hw0]
  simpa only [e] using key

end TernaryGoldbach.MinorArcs
