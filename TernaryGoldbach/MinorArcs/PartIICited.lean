import TernaryGoldbach.MinorArcs.EtaU
import TernaryGoldbach.MinorArcs.Bombieri
import TernaryGoldbach.MajorArcs.Prop715
import TernaryGoldbach.MajorArcs.L2Major

/-!
# Results from [H, Part II] used by the repaired minor-arc bound

These are major-arc results of [H]: explicit formulas plus the GRH verification for conductors
`≤ 300000` [Plab]. Their proofs do not involve the minor-arc scale question (NOTES, "Ch. 13: scale
erratum"). We state them as [H] does.

* **`cor_7_1_3`** — [H, Cor 7.1.3]: twisted sums for `η = φ *_M η₂` (our `etaU`). **Proved**
  (`MajorArcs/Cor713.lean`) from [H, Prop 9.3.2] (`MajorArcs.prop_9_3_2`: proved for `q ≥ 2` with our
  constants, cited for `q = 1`; conditional on GRH up to height `T₀`) and Platt's verification
  (numerical axioms `platt_odd`, `platt_even`), via [H, Cor 9.3.3] (`MajorArcs/Cor933.lean`).
* **`prop_7_1_5`** — [H, Prop 7.1.5]: `Σ Λ(n) log n η₊²(n/x)` (for `x ≥ 4.9·10²⁶`). **Proved**
  (`MajorArcs/Prop715.lean`) from [H, Prop 9.5.1] (`MajorArcs.prop_9_5_1`, proved: `ζ` explicit formulas for
  `η₊²` and `η₊² log`, RH up to `500`), Platt's verification at `q = 1` and the numerical axiom
  `integral_etaPlus_sq_log` ([H, (9.94)]).
* **`l2_major_14_7`** — [H, (14.7)]: `∫_{𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα = (8.7052 + O*(0.0756)) x` in [H];
  we state `(8.7098 + O*(0.0802)) x` (same lower end `8.6296 x`; our Thm 7.1.4 constants are weaker)
  for `x ≥ 4.9·10²⁶`. **Proved** (`MajorArcs/L2Major.lean`, `l2_major_bounds`: in fact `8.675 x … 8.786 x`)
  from [H, Thm 7.1.4] (Prop 9.4.2, proved, + Platt), Plancherel, the bound on `‖η₊ − η◦‖₂` and the numerical
  results `integral_etaPlus_sq_log` ((9.94)) and `sum_odd_mu_sq_div_totient` (`Σ μ²/φ = 6.798779…`).
  [H] writes `0.0754`, but its term `5.19 δ₀ r ET (|η₊|₁ + ET/2)` evaluates to `0.075456` with (14.1),
  (14.3) ([H] prints `0.075272`); our proof splits the cross term differently and has a much smaller
  error, so the statement holds as given.
-/

open Real Set MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum)

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs S etaPlus r₀)

/-- **[H, Cor 7.1.3]** — proved (`MajorArcs.cor_7_1_3'`), with our constants. Let `η = φ *_M η₂`,
`y ≥ 10²⁵`, `χ` primitive mod `q`, `1 ≤ q ≤ 300000`, `|δ| ≤ 4·300000/q`. Then
`Σ Λ(n) χ(n) e(δn/y) η(n/y) = [q = 1] η̂(-δ) y + E y` with `|E| ≤ 10⁻¹⁷ + 4.7·10⁶/(√q √y)`
([H]: `2.485·10⁻¹⁹ + (381500/√q + 76)/√y`). (`η̂(t) = ∫ η(u) e(-tu) du`, our `𝓕`.) -/
theorem cor_7_1_3 {y : ℝ} (hy : 1e25 ≤ y) {q : ℕ} [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)) (δ / y) -
        (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0)‖ ≤
      (1e-17 + 4.7e6 / √q / √y) * y :=
  MajorArcs.cor_7_1_3' hy hq χ hχ hδ

/-- **[H, Prop 7.1.5]** — proved (`MajorArcs.prop_7_1_5'`). For `x ≥ 4.9·10²⁶` ([H]: `x ≥ 10¹²`),
`Σ Λ(n) (log n) η₊²(n/x) = 0.640206 x log x - 0.021095 x + E₂ x log x`,
`|E₂| ≤ 2·10⁻⁶ + 366.91/√x`. -/
theorem prop_7_1_5 {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∃ E₂ : ℝ, |E₂| ≤ 2e-6 + 366.91 / √x ∧
      ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 =
        0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x :=
  MajorArcs.prop_7_1_5' hx

/-- **[H, (14.7)]** — proved (`MajorArcs.l2_major_bounds`). For `x ≥ 4.9·10²⁶`,
`∫_{𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα = (8.7098 + O*(0.0802)) x` (`𝔐` read in `ℝ/ℤ`, i.e. over
`(0, 1]`; [H]: `8.7052 + O*(0.0756)`). -/
theorem l2_major_14_7 {x : ℝ} (hx : 4.9e26 ≤ x) :
    |(∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, ‖S etaPlus x α‖ ^ 2) - 8.7098 * x| ≤ 0.0802 * x := by
  obtain ⟨h1, h2⟩ := MajorArcs.l2_major_bounds hx
  rw [abs_le]; constructor <;> linarith

end TernaryGoldbach.MinorArcs
