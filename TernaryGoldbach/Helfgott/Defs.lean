import TernaryGoldbach.CircleMethod

/-!
# Helfgott's objects

Definitions of the smoothing functions, exponential sums and major arcs used in the final
chapter of H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 [H].

[H, Ch. 14] works with

* `η₊(t) = h₂₀₀(t) · t · e^{-t²/2}` [H, (7.4)] where `h_H(t) = ∫₀^∞ h(t/y) F_H(y) dy/y` [H, (7.6)],
  `h(t) = t²(2 - t)³ e^{t - 1/2}` on `[0, 2]` (zero elsewhere) [H, (7.5)],
  `F_H(y) = sin(H log y)/(π log y)`;
* `η_*(t) = (η₂ *_M φ)(κt)` with `κ = 49`, `φ(t) = t² e^{-t²/2}`, and
  `η₂(t) = 4 max(log 2 - |log 2t|, 0) = (η₁ *_M η₁)(t)`, `η₁ = 2 · 1_{[1/2, 1]}` [H, (11.10)]
  (the opening of [H, Ch. 14] misprints `η₁` as `2 · 1_{[-1/2, 1/2]}`);
* `S_η(α, x) = ∑ₙ Λ(n) e(αn) η(n/x)` [H, (10.1)];
* the major arcs `𝔐_{δ₀,r}` of [H, (10.5)] with `δ₀ = 8`, `r = 150000`;
* `x = N / (2 + 9/(196 √(2π)))` [H, (14.15)].
-/

open Complex MeasureTheory ArithmeticFunction

namespace TernaryGoldbach.Helfgott

/-- Mellin convolution `(f *_M g)(t) = ∫₀^∞ f(r) g(t/r) dr/r`. -/
noncomputable def mellinConv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0:ℝ), f r * g (t / r) / r

/-- `h(t) = t²(2 - t)³ e^{t - 1/2}` on `[0, 2]`, zero elsewhere [H, (7.5)]. -/
noncomputable def hBase (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0:ℝ) 2 then t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) else 0

/-- `F_H(y) = sin(H log y) / (π log y)` [H, (7.6)]. -/
noncomputable def F (H y : ℝ) : ℝ := Real.sin (H * Real.log y) / (Real.pi * Real.log y)

/-- `h_H(t) = ∫₀^∞ h(t/y) F_H(y) dy/y` [H, (7.6)]. -/
noncomputable def hH (H t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0:ℝ), hBase (t / y) * F H y / y

/-- `η₊(t) = h₂₀₀(t) · t · e^{-t²/2}` [H, (7.4)]. -/
noncomputable def etaPlus (t : ℝ) : ℝ := hH 200 t * t * Real.exp (-t ^ 2 / 2)

/-- `η₂(t) = 4 max(log 2 - |log 2t|, 0)` for `t > 0` (and `0` for `t ≤ 0`) [H, (11.10)]. -/
noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

/-- `φ(t) = t² e^{-t²/2}`. -/
noncomputable def phi (t : ℝ) : ℝ := t ^ 2 * Real.exp (-t ^ 2 / 2)

/-- `κ = 49`. -/
def κ : ℝ := 49

/-- `η_*(t) = (η₂ *_M φ)(κt)`. -/
noncomputable def etaStar (t : ℝ) : ℝ := mellinConv eta2 phi (κ * t)

/-- The smoothed exponential sum `S_η(α, x) = ∑ₙ Λ(n) η(n/x) e(nα)` [H, (10.1)]. -/
noncomputable def S (η : ℝ → ℝ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n * η (n / x) : ℝ) : ℂ) * e (n * α)

/-- The major arcs `𝔐_{δ₀,r}` [H, (10.5)], lifted from `ℝ/ℤ` to `ℝ`: intervals of radius
`δ₀r/(2qx)` around `a/q` for odd `q ≤ r`, and of radius `δ₀r/(qx)` for even `q ≤ 2r`,
where `gcd(a, q) = 1`. -/
def majorArcs (δ₀ r x : ℝ) : Set ℝ :=
  (⋃ (q : ℕ) (_ : 1 ≤ q ∧ (q : ℝ) ≤ r ∧ Odd q) (a : ℤ) (_ : IsCoprime a (q : ℤ)),
      Set.Ioo (a / q - δ₀ * r / (2 * q * x)) (a / q + δ₀ * r / (2 * q * x))) ∪
  (⋃ (q : ℕ) (_ : 1 ≤ q ∧ (q : ℝ) ≤ 2 * r ∧ Even q) (a : ℤ) (_ : IsCoprime a (q : ℤ)),
      Set.Ioo (a / q - δ₀ * r / (q * x)) (a / q + δ₀ * r / (q * x)))

theorem measurableSet_majorArcs (δ₀ r x : ℝ) : MeasurableSet (majorArcs δ₀ r x) := by
  unfold majorArcs
  refine MeasurableSet.union ?_ ?_ <;>
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ioo

/-- Helfgott's parameter `r₀ = 150000`. -/
def r₀ : ℝ := 150000

/-- `x = N / (2 + 9/(196 √(2π)))` [H, (14.15)]. -/
noncomputable def xOf (N : ℕ) : ℝ := N / (2 + 9 / (196 * √(2 * Real.pi)))

/-- The circle method integrand `S_{η₊}(α, x)² S_{η_*}(α, x) e(-Nα)` of [H, (14.50)]. -/
noncomputable def integrand (N : ℕ) (α : ℝ) : ℂ :=
  S etaPlus (xOf N) α ^ 2 * S etaStar (xOf N) α * e (-(N * α))

open Classical in
/-- The weighted count of representations `N = n₁ + n₂ + n₃` with every `nᵢ` satisfying `P`:
`∑ Λ(n₁)Λ(n₂)Λ(n₃) η₊(n₁/x) η₊(n₂/x) η_*(n₃/x)` (the left side of [H, (14.50)]). -/
noncomputable def repSum (P : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.range (N + 1), ∑ n₂ ∈ Finset.range (N + 1), ∑ n₃ ∈ Finset.range (N + 1),
    if n₁ + n₂ + n₃ = N ∧ P n₁ ∧ P n₂ ∧ P n₃ then
      Λ n₁ * Λ n₂ * Λ n₃ * etaPlus (n₁ / xOf N) * etaPlus (n₂ / xOf N) *
        etaStar (n₃ / xOf N)
    else 0

end TernaryGoldbach.Helfgott
