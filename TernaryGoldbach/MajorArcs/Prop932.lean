import TernaryGoldbach.MajorArcs.GRH
import TernaryGoldbach.Explicit.ExplicitBound
import TernaryGoldbach.Explicit.ZetaBound

/-!
# [H, Prop 9.3.2]: the case `q ≥ 2` (proved), and the combined statement

For `χ` primitive of modulus `q ≥ 2` (so `χ ≠ 1`), `Explicit.norm_Ssum_le` gives, under GRH up to
`T₀ ≥ max(10π|δ|, 50)`, `|Σ Λ(n) χ(n) e(δn/x) η(n/x)| ≤ err_new · x` with
`err_new = E₂ + E₁/√x + E₀/x + V/(2π x√x)` (`Explicit/ZeroSumBound`, `Explicit/ExplicitBound`). Our
constants are weaker than [H]'s (9.57): Jensen windows replace the explicit `N(T)` of [H, Lemma 9.1.4].
For `q = 1` (`ζ`): `prop_9_3_2_one`, from `Explicit.norm_SsumG_zeta_le`.
-/

open Real MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (phi)
open TernaryGoldbach (Schar)
open TernaryGoldbach.Explicit (Ssum fδ E0b E1b E2b Vb errZ)

theorem Schar_eq_Ssum {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) :
    Schar χ (fun n => ((Λ n * phi (n / x) : ℝ) : ℂ)) (δ / x) = Ssum χ δ x := by
  unfold Schar Ssum
  congr 1; ext n
  unfold fδ TernaryGoldbach.e TernaryGoldbach.Helfgott.phi
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * ((n : ℂ) * ((δ : ℂ) / (x : ℂ)))) =
    2 * π * Complex.I * δ * ((n : ℂ) / (x : ℂ)) by ring]
  ring

/-- The error term for `q ≥ 2`: `E₂ + E₁/√x + E₀/x + V/(2π x√x)`. -/
noncomputable def errNew (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  E2b q T0 δ + E1b q T0 / √x + E0b q / x + Vb q δ / (2 * π * (x * √x))

theorem ne_one_of_primitive {q : ℕ} [NeZero q] (hq : q ≠ 1) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  apply hq
  have h1 := (DirichletCharacter.eq_one_iff_conductor_eq_one).1 h
  rw [DirichletCharacter.IsPrimitive] at hχ
  rw [← hχ, h1]

/-- **[H, Prop 9.3.2] for `q ≥ 2`** (proved, with our constants): for `χ` primitive mod `q ≠ 1`,
`x ≥ 1`, GRH up to `T₀ ≥ max(10π|δ|, 50)`: `|Σ Λ(n) χ(n) e(δn/x) η(n/x)| ≤ err_new(q, T₀, δ, x) x`. -/
theorem prop_9_3_2_ne {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * phi (n / x) : ℝ) : ℂ)) (δ / x)‖ ≤ errNew q T0 δ x * x := by
  have hx0 : 0 < x := by linarith
  rw [Schar_eq_Ssum]
  refine (Explicit.norm_Ssum_le hχ (ne_one_of_primitive hq hχ) δ hx hT0
    (fun ρ h0 h1 h2 h3 => hG ρ h0 h1 h2 h3)).trans (le_of_eq ?_)
  unfold errNew
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hrp : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrp]
  set s := √x with hs_def
  rw [← hs]
  field_simp
  ring

/-- **[H, Prop 9.3.2] for `q = 1`** (proved, with our constants, `Explicit.norm_SsumG_zeta_le`): under RH
up to `T₀ ≥ max(10π|δ|, 50)`, `x ≥ 1`: `|Σ Λ(n) e(δn/x) η(n/x) − η̂(−δ) x| ≤ errZ(T₀, δ, x) x`. -/
theorem prop_9_3_2_one {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (hq : q = 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * phi (n / x) : ℝ) : ℂ)) (δ / x) -
        𝓕 (fun u => (phiPos u : ℂ)) (-δ) * x‖ ≤ errZ T0 δ x * x := by
  subst hq
  have hχ1 : χ = 1 := Subsingleton.elim _ _
  subst hχ1
  have hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2 := by
    intro ρ h0 h1 h2 h3
    exact hG ρ (by rw [Explicit.LFunction_one_mod_one]; exact h0) h1 h2 h3
  have hm : mellin (fδ δ) 1 = 𝓕 (fun u => (phiPos u : ℂ)) (-δ) := by
    rw [Explicit.mellin_fδ_one]
    congr 1
  rw [Schar_eq_Ssum, Explicit.Ssum_eq_SsumG, ← hm]
  exact Explicit.norm_SsumG_zeta_le δ hx hT0 hRH

/-- The error term of `prop_9_3_2`: `errZ` for `q = 1`, `errNew` for `q ≥ 2`. -/
noncomputable def err932N (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  if q = 1 then errZ T0 δ x else errNew q T0 δ x

/-- **[H, Prop 9.3.2]** (proved, with our constants): `η(t) = t² e^{-t²/2}`, `x ≥ 1`, `χ`
primitive mod `q`, GRH up to `T₀ ≥ max(10π|δ|, 50)`:
`Σ Λ(n) χ(n) e(δn/x) η(n/x) = [q = 1] η̂(-δ) x + O*(err932N) x`. -/
theorem prop_9_3_2 {x : ℝ} (hx : 1 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0) (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * phi (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (phiPos u : ℂ)) (-δ) * x else 0)‖ ≤ err932N q T0 δ x * x := by
  unfold err932N
  by_cases hq : q = 1
  · rw [if_pos hq, if_pos hq]
    exact prop_9_3_2_one hx δ hq χ hχ hT0 hG
  · rw [if_neg hq, if_neg hq, sub_zero]
    exact prop_9_3_2_ne hx δ hq χ hχ hT0 hG

end TernaryGoldbach.MajorArcs
