import TernaryGoldbach.MinorArcs.EtaU
import TernaryGoldbach.MinorArcs.Bombieri
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Platt's GRH verification and [B, Prop 9.3.2]

[B, Part II] separates into an analytic part — explicit formulas whose error terms depend on a height
`T₀` up to which GRH is assumed — and a numerical part, D. Platt's rigorous verification of GRH up to
height `T_q` for all primitive characters of conductor `q ≤ 4·10⁵` [B, §9.6], [Plab].

* `GRHUpTo χ T`: every zero `ρ` of `L(s, χ)` with `0 < ℜρ < 1`, `|ℑρ| ≤ T`, has `ℜρ = 1/2`
  (Mathlib's `DirichletCharacter.LFunction`; for `q = 1` this is `ζ`).
* **`platt_odd`, `platt_even`** (numerical axioms): [B, §9.6] — `T_q = 10⁸/q` for odd `q ≤ 3·10⁵`,
  `T_q = max(10⁸/q, 200 + 7.5·10⁷/q)` for even `q ≤ 4·10⁵`.
* **`prop_9_3_2`** (cited, conditional on `GRHUpTo χ T₀`): [B, Prop 9.3.2], the explicit-formula bound
  for `Σ Λ(n) χ(n) e(δn/x) η(n/x)` with `η(t) = t² e^{-t²/2}`.
-/

open Real MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e)

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (phi)
open TernaryGoldbach (Schar)

/-- GRH for `L(s, χ)` up to height `T`. -/
def GRHUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Prop :=
  ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ.re = 1 / 2

theorem GRHUpTo.mono {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {T T' : ℝ} (h : GRHUpTo χ T)
    (hT : T' ≤ T) : GRHUpTo χ T' :=
  fun ρ h0 h1 h2 h3 => h ρ h0 h1 h2 (h3.trans hT)

/-- **Numerical axiom** (D. Platt [Plab], [B, §9.6]): for every primitive character `χ` of odd
conductor `q ≤ 3·10⁵`, GRH holds for `L(s, χ)` up to height `10⁸/q`. -/
axiom platt_odd {q : ℕ} [NeZero q] (hq : Odd q) (hq3 : q ≤ 300000) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : GRHUpTo χ (1e8 / q)

/-- **Numerical axiom** (D. Platt [Plab], [B, §9.6]): for every primitive character `χ` of even
conductor `q ≤ 4·10⁵`, GRH holds for `L(s, χ)` up to height `max(10⁸/q, 200 + 7.5·10⁷/q)`. -/
axiom platt_even {q : ℕ} [NeZero q] (hq : Even q) (hq4 : q ≤ 400000) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : GRHUpTo χ (max (1e8 / q) (200 + 7.5e7 / q))

/-- Platt's verification at height `10⁸/q` for every `q ≤ 3·10⁵`. -/
theorem platt_grh {q : ℕ} [NeZero q] (hq3 : q ≤ 300000) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : GRHUpTo χ (1e8 / q) := by
  rcases Nat.even_or_odd q with h | h
  · exact (platt_even h (by omega) χ hχ).mono (le_max_left _ _)
  · exact platt_odd h hq3 χ hχ

/-- `η(t) = t² e^{-t²/2}` for `t > 0`, `0` for `t ≤ 0` ([B]'s smoothing functions live on `ℝ⁺`). -/
noncomputable def phiPos (t : ℝ) : ℝ := if 0 < t then phi t else 0

/-- `e^{-0.1065 T₀²/(πδ)²}`, read as `0` at `δ = 0` (its limit). -/
noncomputable def expδ (T0 δ : ℝ) : ℝ :=
  if δ = 0 then 0 else Real.exp (-0.1065 * T0 ^ 2 / (π * δ) ^ 2)

/-- The error term (9.57) of [B, Prop 9.3.2]. -/
noncomputable def err932 (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  T0 * Real.log (q * T0 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ) +
    (1.22 * √T0 * Real.log (q * T0) + 5.056 * √T0 + 1.423 * Real.log q + 37.19) / √x +
    (3 + 11 * |δ|) / x + (Real.log q + 6) * (1 + 6 * |δ|) / (x * √x)

/-- **[B, Prop 9.3.2]** — *cited* (explicit formula, Lemmas 9.1.1, 9.1.4, 9.3.1). Let
`η(t) = t² e^{-t²/2}`, `x ≥ 1`, `δ ∈ ℝ`, `χ` primitive mod `q`. If GRH holds for `L(s, χ)` up to
height `T₀ ≥ max(10π|δ|, 50)`, then
`Σ Λ(n) χ(n) e(δn/x) η(n/x) = [q = 1] η̂(-δ) x + O*(err_{η,χ}(δ, x)) x` with `err` as in (9.57). -/
theorem prop_9_3_2 {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * phi (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (phiPos u : ℂ)) (-δ) * x else 0)‖ ≤ err932 q T0 δ x * x := by
  sorry

end TernaryGoldbach.MajorArcs
