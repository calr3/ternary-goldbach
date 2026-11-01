import TernaryGoldbach.MinorArcs.EtaU
import TernaryGoldbach.MinorArcs.Bombieri
import TernaryGoldbach.MajorArcs.Prop715

/-!
# Results from [B, Part II] used by the repaired minor-arc bound

These are major-arc results of [B]: explicit formulas plus the GRH verification for conductors
`≤ 300000` [Plab]. Their proofs do not involve the minor-arc scale question (NOTES, "Ch. 13: scale
erratum"). We state them as [B] does.

* **`cor_7_1_3`** — [B, Cor 7.1.3]: twisted sums for `η = φ *_M η₂` (our `etaU`). **Proved**
  (`MajorArcs/Cor713.lean`) from the cited [B, Prop 9.3.2] (`MajorArcs.prop_9_3_2`, conditional on GRH
  up to height `T₀`) and Platt's verification (numerical axioms `platt_odd`, `platt_even`), via
  [B, Cor 9.3.3] (`MajorArcs/Cor933.lean`).
* **`prop_7_1_5`** — [B, Prop 7.1.5]: `Σ Λ(n) log n η₊²(n/x)`. **Proved** (`MajorArcs/Prop715.lean`) from
  the cited [B, Prop 9.5.1] (`MajorArcs.prop_9_5_1`, conditional on RH up to `T₀`), Platt's verification
  at `q = 1` (`T₀ = 440`) and the numerical axiom `integral_etaPlus_sq_log` ([B, (9.94)]).
* **`l2_major_14_7`** — [B, (14.7)]: `∫_{𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα = (8.7052 + O*(0.0756)) x`
  for `x ≥ 4.9·10²⁶` (from Lemma 10.3.1 and the computations of §14.1). [B] writes `0.0754`, but its
  term `5.19 δ₀ r ET (|η₊|₁ + ET/2)` evaluates to `0.075456` with (14.1), (14.3) ([B] prints `0.075272`),
  so the error supported by [B]'s argument is `0.07553 ≤ 0.0756`.
-/

open Real Set MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum)

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs S etaPlus r₀)

/-- **[B, Cor 7.1.3]** — proved from [B, Prop 9.3.2] and [Plab] (`MajorArcs.cor_7_1_3'`). Let `η = φ *_M η₂`, `y ≥ 10⁸`, `χ` primitive mod `q`,
`1 ≤ q ≤ 300000`, `|δ| ≤ 4·300000/q`. Then
`Σ Λ(n) χ(n) e(δn/y) η(n/y) = [q = 1] η̂(-δ) y + E y` with
`|E| ≤ 2.485·10⁻¹⁹ + (381500/√q + 76)/√y`. (`η̂(t) = ∫ η(u) e(-tu) du`, our `𝓕`.) -/
theorem cor_7_1_3 {y : ℝ} (hy : 1e8 ≤ y) {q : ℕ} [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)) (δ / y) -
        (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0)‖ ≤
      (2.485e-19 + (381500 / √q + 76) / √y) * y :=
  MajorArcs.cor_7_1_3' hy hq χ hχ hδ

/-- **[B, Prop 7.1.5]** — proved (`MajorArcs.prop_7_1_5'`). For `x ≥ 10¹²`,
`Σ Λ(n) (log n) η₊²(n/x) = 0.640206 x log x - 0.021095 x + E₂ x log x`,
`|E₂| ≤ 2·10⁻⁶ + 366.91/√x`. -/
theorem prop_7_1_5 {x : ℝ} (hx : 1e12 ≤ x) :
    ∃ E₂ : ℝ, |E₂| ≤ 2e-6 + 366.91 / √x ∧
      ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 =
        0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x :=
  MajorArcs.prop_7_1_5' hx

/-- **[B, (14.7)]** — *cited*. For `x ≥ 4.9·10²⁶`,
`∫_{𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα = (8.7052 + O*(0.0756)) x` (`𝔐` read in `ℝ/ℤ`, i.e. over
`(0, 1]`). -/
theorem l2_major_14_7 {x : ℝ} (hx : 4.9e26 ≤ x) :
    |(∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, ‖S etaPlus x α‖ ^ 2) - 8.7052 * x| ≤ 0.0756 * x := by
  sorry

end TernaryGoldbach.MinorArcs
