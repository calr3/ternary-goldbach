import TernaryGoldbach.MinorArcs.OffArcs
import TernaryGoldbach.MinorArcs.SecondChoice
import TernaryGoldbach.MinorArcs.LargeSieveProof
import TernaryGoldbach.MinorArcs.Prop1312
import TernaryGoldbach.Helfgott.Decay

/-!
# [B, Thm 13.2.1], conditional on an ℓ∞ bound at scale `x`

Combines (`thm_13_2_1_conditional`)
* the ℓ² bound over the arcs at scale `x`, Cor 12.2.5 (12.42) with `δ₀ = 8`, for coefficients
  `aₙ` supported on primes `> √x` (`S₁ = expTsum a`);
* Plancherel `∫₀¹ |S₁|² = Σ|aₙ|²` at the top level;
* the abstract combination Prop 13.1.2 (`prop_13_1_2`)

with an **ℓ∞ hypothesis** `hv`: `|S_{η_*}(α, x)| ≤ g(n)` for `α ∉ 𝔐_{8,n}` at **scale `x`**,
`r₀ ≤ n ≤ r₁`.  The conclusion is the discrete form of [B, (13.6)].

What [B]'s proof actually supplies for `hv` is the bound off the arcs at scale `y = x/κ`
(`le_rAlpha_of_not_mem` at scale `y` + Prop 11.2.3).  The difference, `𝔐_{8,n}(y) \ 𝔐_{8,n}(x)`,
is the open gap described in NOTES "Ch. 13: scale erratum".  This file proves everything else.

Proved, modulo the trusted computation Prop 12.2.4 (through Cor 12.2.5).
-/

open MeasureTheory Set

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs S etaStar summable_etaStar)
open TernaryGoldbach (expTsum)

/-- The ℓ² majorant: (12.42) for the arcs `𝔐_{8,n+1}` at scale `x` below the top level `r₁`,
and the total `T = Σ|aₙ|²` at `r₁`. -/
noncomputable def Hl2 (x T : ℝ) (r₁ n : ℕ) : ℝ :=
  if n < r₁ then (Real.log (2 * ((n : ℝ) + 1)) + 1.36) / (Real.log (2 * √(x / 16)) + cE) * T
  else T

/-- **[B, Thm 13.2.1], conditional on the ℓ∞ bound at scale `x`** (discrete (13.6)).  For
`aₙ` supported on primes `> √x`, `S₁ = Σ aₙ e(nα)`, `T = Σ|aₙ|²`, and levels
`10⁵ ≤ r₀ ≤ r₁` with `(20000 r₁)² ≤ x/16`, `2r₁ ≤ (2√(x/16))^{0.6}`: if `g` is non-increasing,
`g(r₁) ≥ 0`, and `|S_{η_*}(α, x)| ≤ g(n)` off `𝔐_{8,n}` (scale `x`) for `r₀ ≤ n ≤ r₁`, then
`∫_{(0,1] \ 𝔐_{8,r₀}} |S₁|²|S_{η_*}| ≤ g(r₀)(H(r₀) − I₀) + Σ_{r₀ < n ≤ r₁} g(n)(H(n) − H(n−1))`
with `H = Hl2 x T r₁` and `I₀ = ∫_{(0,1] ∩ 𝔐_{8,r₀}} |S₁|²`. -/
theorem thm_13_2_1_conditional {x : ℝ} (hx : 0 < x) {a : ℕ → ℂ} (ha : PrimeSupported x a)
    {g : ℕ → ℝ} {r₀ r₁ : ℕ} (h01 : r₀ ≤ r₁) (hr₀ : 1e5 ≤ (r₀ : ℝ))
    (hx₁ : (20000 * (r₁ : ℝ)) ^ 2 ≤ x / 16) (hρ : 2 * (r₁ : ℝ) ≤ (2 * √(x / 16)) ^ (0.6 : ℝ))
    (hg : ∀ n, r₀ ≤ n → n < r₁ → g (n + 1) ≤ g n) (hg0 : 0 ≤ g r₁)
    (hv : ∀ n, r₀ ≤ n → n ≤ r₁ → ∀ α ∉ majorArcs 8 n x, ‖S etaStar x α‖ ≤ g n) :
    ∫ α in Ioc 0 1 \ majorArcs 8 r₀ x, ‖expTsum a α‖ ^ 2 * ‖S etaStar x α‖ ≤
      g r₀ * (Hl2 x (∑' n, ‖a n‖ ^ 2) r₁ r₀ -
          ∫ α in Ioc 0 1 ∩ majorArcs 8 r₀ x, ‖expTsum a α‖ ^ 2) +
        ∑ n ∈ Finset.Ioc r₀ r₁, g n * (Hl2 x (∑' n, ‖a n‖ ^ 2) r₁ n -
          Hl2 x (∑' n, ‖a n‖ ^ 2) r₁ (n - 1)) := by
  set T := ∑' n, ‖a n‖ ^ 2
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  set M : ℕ → Set ℝ := fun n => majorArcs 8 n x
  have hM : ∀ n, MeasurableSet (M n) := fun n => Helfgott.measurableSet_majorArcs _ _ _
  have hmono : Monotone M := fun m n hmn =>
    majorArcs_mono (by norm_num) hx (show (m : ℝ) ≤ n by exact_mod_cast hmn)
  have hcu : Continuous fun α => ‖expTsum a α‖ ^ 2 :=
    (TernaryGoldbach.continuous_expTsum ha.2).norm.pow 2
  have hcv : Continuous fun α => ‖S etaStar x α‖ :=
    (TernaryGoldbach.continuous_expTsum (summable_etaStar hx)).norm
  have hint : ∀ {f : ℝ → ℝ}, Continuous f → Integrable f μ := fun hf =>
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hres : ∀ (s : Set ℝ) (f : ℝ → ℝ), MeasurableSet s →
      ∫ α in s, f α ∂μ = ∫ α in Ioc 0 1 ∩ s, f α := fun s f hs => by
    rw [Measure.restrict_restrict hs, inter_comm]
  have key := prop_13_1_2 (μ := μ) (u := fun α => ‖expTsum a α‖ ^ 2)
    (v := fun α => ‖S etaStar x α‖) (hint hcu) (hint (hcu.mul hcv)) (fun _ => by positivity)
    hM hmono (H := Hl2 x T r₁) h01 hg hg0 hv ?_ ?_
  · rw [hres _ _ (hM r₀), hres _ _ (hM r₀).compl] at key
    rwa [show Ioc (0 : ℝ) 1 ∩ (M r₀)ᶜ = Ioc 0 1 \ majorArcs 8 r₀ x from rfl] at key
  · intro n hn hn1
    rw [hres _ _ (hM _)]
    have hn1' : ((n : ℝ) + 1) ≤ r₁ := by exact_mod_cast hn1
    have h := cor_12_2_5 (Q₀ := (n : ℝ) + 1) (δ₀ := 8) ha (by
        have : (r₀ : ℝ) ≤ n := by exact_mod_cast hn
        linarith) (by norm_num) (by
        rw [show 2 * (8 : ℝ) = 16 by norm_num]
        refine le_trans ?_ hx₁; gcongr) (by
        rw [show 2 * (8 : ℝ) = 16 by norm_num]; linarith)
    rw [show 2 * (8 : ℝ) = 16 by norm_num] at h
    simp only [Hl2, ite_eq_left hn1, M]
    convert h using 3; push_cast; rfl
  · simp only [Hl2, lt_irrefl, ite_false]
    rw [show ∫ α, ‖expTsum a α‖ ^ 2 ∂μ = ∫ α in Ioc (0 : ℝ) 1, ‖expTsum a α‖ ^ 2 from rfl,
      TernaryGoldbach.setIntegral_norm_sq_expTsum ha.2]

/-! ## Splitting the ℓ∞ hypothesis: what [B] proves, and the gap -/

/-- **The ℓ∞ step [B] actually proves** (shape): if every approximation
`2α = a/q + δ/y (mod 1)` at scale `y` with `q ≤ Q` gives `|S_{η_*}(α, x)| ≤ B(r_α)`,
`r_α = max(1, |δ|/8) q`, and `B` is non-increasing on `[r, ∞)`, then `|S_{η_*}(α, x)| ≤ B(r)` off
`𝔐_{8,r}` **at scale `y`**.  (Prop 11.2.3 supplies such a `B` for small `q`.) -/
theorem norm_S_le_off_arcs {x y Q r : ℝ} (hy : 0 < y) (hQ : 1 ≤ Q) {B : ℝ → ℝ}
    (hB : ∀ (α δ : ℝ) (a : ℤ) (q : ℕ), Approx2 α y δ a q Q →
      ‖S etaStar x α‖ ≤ B (max 1 (|δ| / 8) * q))
    (hanti : AntitoneOn B (Ici r)) {α : ℝ} (hα : α ∉ majorArcs 8 r y) :
    ‖S etaStar x α‖ ≤ B r := by
  obtain ⟨δ, a, q, h⟩ := exists_approx2 α hy hQ
  have hr := le_rAlpha_of_not_mem hy (by norm_num) h hα
  exact (hB α δ a q h).trans (hanti self_mem_Ici (mem_Ici.2 hr) hr)

/-- **The gap.** The hypothesis `hv` of `thm_13_2_1_conditional` at level `n` follows from the
bound off the `y`-arcs (`norm_S_le_off_arcs`) together with a bound on
`𝔐_{8,n}(y) \ 𝔐_{8,n}(x)`.  [B] gives no argument for the second, and it is not available from
Thm 3.1.1 (NOTES "Ch. 13: scale erratum"). -/
theorem hv_of_split {x y n G : ℝ}
    (hoff : ∀ α ∉ majorArcs 8 n y, ‖S etaStar x α‖ ≤ G)
    (hgap : ∀ α ∈ majorArcs 8 n y \ majorArcs 8 n x, ‖S etaStar x α‖ ≤ G) :
    ∀ α ∉ majorArcs 8 n x, ‖S etaStar x α‖ ≤ G := fun α hα => by
  by_cases h : α ∈ majorArcs 8 n y
  · exact hgap α ⟨h, hα⟩
  · exact hoff α h

end TernaryGoldbach.MinorArcs
