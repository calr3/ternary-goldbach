import TernaryGoldbach.Helfgott.Main
import TernaryGoldbach.Prelim.RamareMoebius

/-!
# The main theorems, with explicit hypotheses

Inside the development, the two numerical hypotheses of `Statement.lean` are `Fact` instances
(section variables). Here they become ordinary hypotheses. Ramaré's bound `RamareMoebius`, also
passed as a `Fact` inside the development, is proved from `PlattGRH`
(`Prelim.ramareMoebius_of_plattGRH`). These theorems use only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). They are the theorems checked by leanprover/comparator against
`Challenge.lean` (`comparator/config.json`).
-/

namespace TernaryGoldbach

/-- **Helfgott's theorem for large `n`**: every odd `n ≥ 10²⁷` is a sum of three primes, given
Platt's GRH verification. -/
theorem ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) :
    TernaryGoldbachFrom (10 ^ 27) :=
  haveI := Fact.mk hGRH; haveI := Fact.mk (Prelim.ramareMoebius_of_plattGRH hGRH)
  Helfgott.ternaryGoldbachFrom

/-- **The ternary Goldbach conjecture** (Helfgott, 2013): every odd integer greater than `5` is a
sum of three primes, given the two published numerical results of `Statement.lean`. -/
theorem ternary_goldbach_of_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput) :
    Statement :=
  haveI := Fact.mk hGRH; haveI := Fact.mk hBG
  haveI := Fact.mk (Prelim.ramareMoebius_of_plattGRH hGRH)
  ternary_goldbach

end TernaryGoldbach
