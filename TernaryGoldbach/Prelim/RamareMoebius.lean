import TernaryGoldbach.Statement
import RSBounds.Moebius003.Upstream

/-!
# Ramaré's bound `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x` ([H, (2.21)])

Stated for `x ≥ 11815` as in [Ram13, Cor. 1.4] and [H, (2.21)], and **proved** from `PlattGRH`:
Helfgott's formalization of his note `mobius003.tex` (Garald1/RSBounds, vendored unchanged under
`vendor/rsbounds/`; see its `source-provenance.json`) proves `RamareMoebius` from RH up to height
`1894438.5122` (`RSBounds.Moebius003.ramareMoebius_of_finiteRH`). The argument follows Ramaré's
recursive idea. Its inputs, all proved there:
* Schoenfeld's (5.6b*) from RH up to `1894438.5122` (Rosser–Schoenfeld's height);
* PsiCert, the kernel-checked `|ψ(x) − x| ≤ 0.8√x` on `[1500, 10¹⁰]`;
* kernel-checked bounds for `M(x) = ∑_{n≤x} μ(n)` and `∑_{n≤x} μ(n)/n` (`MoebiusCert`), and for
  sums of `Λ`.
RH up to that height follows from `PlattGRH` at `q = 1` (`Explicit.rh_upto_1e8`;
`RSBounds.Moebius003.finiteRH_of_plattGRH`).

The uses are the uniform Möbius bound of `MoebiusBound.lean` (for [H, (2.22)]), the Liouville bound
of `LiouvilleBound.lean`, and [H, Lemma 5.1.2] (`MinorArcs/G2Bound.lean`). They take
`[Fact RamareMoebius]`; the instance below provides it from `[Fact PlattGRH]`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- **Ramaré's bound, proved**: `PlattGRH` implies `RamareMoebius`
(Helfgott, `mobius003.tex`; `RSBounds.Moebius003.ramareMoebius_of_plattGRH`). -/
theorem ramareMoebius_of_plattGRH (h : TernaryGoldbach.PlattGRH) : TernaryGoldbach.RamareMoebius :=
  TernaryGoldbach.RSBounds.Moebius003.ramareMoebius_of_plattGRH h

/-- `RamareMoebius` from `PlattGRH`, as an instance. -/
instance instFactRamareMoebius [h : Fact TernaryGoldbach.PlattGRH] :
    Fact TernaryGoldbach.RamareMoebius :=
  ⟨ramareMoebius_of_plattGRH h.out⟩

/-- [H, (2.21)]: `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`.
* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Moebius function*,
  Acta Arith. 157 (2013), 365–379, Cor. 1.4: this bound for `x ≥ 11815`, as cited in [H, (2.21)];
* proved here from `PlattGRH` (`ramareMoebius_of_plattGRH`). -/
theorem ramare_moebius [h : Fact RamareMoebius] {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.03 / Real.log x :=
  h.out x hx

end TernaryGoldbach.Prelim
