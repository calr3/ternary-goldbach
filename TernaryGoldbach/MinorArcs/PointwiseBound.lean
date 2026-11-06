import TernaryGoldbach.MinorArcs.FirstChoiceFinal
import TernaryGoldbach.MinorArcs.SecondFinal

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# The pointwise minor-arc bound [H, Theorem 3.1.1] — blueprint statement

The main result of Part I of [H]: for `η = η₂` and `2α = a/q + δ/x`, an explicit bound on
`|S_η(α, x)|` that is essentially `x (log q)/√φ(q)`.  Part I (Chs. 3–6) is its proof; it is
used in [H, Chs. 11, 13] to bound the minor-arc integral (14.49).

**Blueprint node.** The case `q ≤ x^{1/3}/6` is `theorem_3_1_1_first`, the case `q > x^{1/3}/6`
([H, §6.3.2], with [H]'s constants `0.276`, `1234`) is `theorem_3_1_1_second` (with two
corrections to [H]'s argument, see `SecondChoice.lean` and `NOTES.md`). The minor arcs use it
through `EtaStarBound.lean` and `Prop1123b.lean`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

/-- `R_{x,t} = 0.27125 log(1 + log(4t) / (2 log(9x^{1/3}/(2.004 t)))) + 0.41415` [H, (3.3)]. -/
noncomputable def R (x t : ℝ) : ℝ :=
  0.27125 * Real.log (1 + Real.log (4 * t) /
    (2 * Real.log (9 * x ^ (1 / 3 : ℝ) / (2.004 * t)))) + 0.41415

/-- `L_{x,t,q} = (q/φ(q)) (13/4 log t + 7.82) + 13.66 log t + 37.55` [H, (3.3)]. -/
noncomputable def L (t : ℝ) (q : ℕ) : ℝ :=
  q / Nat.totient q * (13 / 4 * Real.log t + 7.82) + 13.66 * Real.log t + 37.55

omit [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.RamareMoebius] in
/-- `T = x^{1/3}`: `T³ = x`, `x^{2/3} = T²`, `x^{5/6} = T²√T`, and `T ≥ 6·10⁶` for `x ≥ 2.16·10²⁰`. -/
theorem cube_root_facts {x : ℝ} (hx : 2.16e20 ≤ x) :
    6e6 ≤ x ^ (1 / 3 : ℝ) ∧ (x ^ (1 / 3 : ℝ)) ^ 3 = x ∧ x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 ∧
      x ^ (5 / 6 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 * √(x ^ (1 / 3 : ℝ)) := by
  have hx0 : 0 ≤ x := by linarith
  have h3 : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  refine ⟨?_, h3, ?_, ?_⟩
  · have : (6e6 : ℝ) = ((6e6 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_mul hx0,
      ← Real.rpow_add' hx0 (by norm_num)]
    norm_num

/-- **[H, Theorem 3.1.1], corrected** Let `x ≥ 2.16 · 10²⁰`, `η = η₂`, `2α = a/q + δ/x` with
`q ≤ Q`, `(a, q) = 1`, `|δ/x| ≤ 1/qQ`, `Q = (3/4) x^{2/3}`.  Write `δ₀ = max(2, |δ|/4)`.

**Erratum.** [H] states the first term with `R_{x,δ₀q} log δ₀q + 0.5`. Its proof (§6.4, (6.77))
bounds `√A·√B` by `A/(2√ρ) + (√ρ/2)B` with `B = 0.30214 log δ₀q + 0.67506`, `ρ = 3.397962…`,
whose constant term is `log 2/(2√ρ) + (√ρ/2)·0.67506 = 0.81020…`; [H] writes
`(1/2)(log 2/√ρ + (√ρ/2)·0.67506) = 0.49911` (the `0.67506` term is halved twice). With `0.5`
the bound does not follow from [H]'s own (6.63) (which exceeds it by up to ~2.6%, e.g. at
`x = 10²⁵`, `δ₀q ≈ 1.9·10⁵`, `q` prime).

**Second correction.** [H, (5.36)] is false. Its corrected form (`integral_H2_le`, `+0.0231`) adds
`0.0924` to the Type II factor, and our `B` is `0.30214 log δ₀q + 0.7468`. That gives the constant
`log 2/(2√ρ) + (√ρ/2)·0.7468 + 0.0000760 = 0.87639`, so we state it with `0.8764`. -/
theorem theorem_3_1_1 {α x δ : ℝ} {a : ℤ} {q : ℕ} (hx : 2.16e20 ≤ x)
    (h : Approx2 α x δ a q (3 / 4 * x ^ (2 / 3 : ℝ))) :
    let δ₀ := max 2 (|δ| / 4)
    ((q : ℝ) ≤ x ^ (1 / 3 : ℝ) / 6 →
      ‖S eta2 x α‖ ≤
        (R x (δ₀ * q) * Real.log (δ₀ * q) + 0.8764) / √(δ₀ * Nat.totient q) * x +
          2.526 * x / √(δ₀ * q) + 2 * x / (δ₀ * q) * L (δ₀ * q) q + 3.8 * x ^ (5 / 6 : ℝ)) ∧
    (x ^ (1 / 3 : ℝ) / 6 < q →
      ‖S eta2 x α‖ ≤
        0.276 * x ^ (5 / 6 : ℝ) * Real.log x ^ (3 / 2 : ℝ) + 1234 * x ^ (2 / 3 : ℝ) * Real.log x) := by
  intro δ₀
  obtain ⟨hT, h3, h23, h56⟩ := cube_root_facts hx
  set T := x ^ (1 / 3 : ℝ) with hTdef
  refine ⟨fun hqT => ?_, fun _ => ?_⟩
  · rw [h23, ← h3] at h
    have key := theorem_3_1_1_first hT h hqT
    rw [h3] at key
    refine key.trans (le_of_eq ?_)
    simp only [R, L, h56, Cxt, δ₀, delta0]
    rfl
  · rw [h23, ← h3] at h
    have key := theorem_3_1_1_second hT h (by linarith)
    rw [h3] at key
    refine key.trans (le_of_eq_of_le rfl ?_)
    have hT0 : 0 < T := by linarith
    have hL := fifteen_six_le_log hT
    have hL0 : 0 ≤ Real.log T := by linarith
    have hlx : Real.log x = 3 * Real.log T := by rw [← h3, Real.log_pow]; push_cast; ring
    have hrpow : Real.log x ^ (3 / 2 : ℝ) = 3 * Real.log T * (√3 * √(Real.log T)) := by
      rw [hlx, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
        Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
    rw [h56, h23, hrpow, hlx]
    have hs3 : 1.73205 ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hP : 0 ≤ T ^ 2 * √T * (Real.log T * √(Real.log T)) := by positivity
    nlinarith

end TernaryGoldbach.MinorArcs
