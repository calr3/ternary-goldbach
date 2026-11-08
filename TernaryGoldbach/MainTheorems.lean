import TernaryGoldbach.Helfgott.Main

/-!
# The main theorems, with explicit hypotheses

Inside the development, the three numerical hypotheses of `Statement.lean` are `Fact` instances
(section variables). Here they become ordinary hypotheses. These theorems use only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). They are the theorems checked by
leanprover/comparator against `Challenge.lean` (`comparator/config.json`).
-/

namespace TernaryGoldbach

/-- **Helfgott's theorem for large `n`**: every odd `n ≥ 10²⁷` is a sum of three primes, given
Platt's GRH verification and the Cohen–Dress–El Marraki bound `|M(x)| ≤ x/4345`. -/
theorem ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) (hμ : CDEMertens) :
    TernaryGoldbachFrom (10 ^ 27) :=
  haveI := Fact.mk hGRH; haveI := Fact.mk hμ
  Helfgott.ternaryGoldbachFrom

/-- **The ternary Goldbach conjecture** (Helfgott, 2013): every odd integer greater than `5` is a
sum of three primes, given the three published numerical results of `Statement.lean`. -/
theorem ternary_goldbach_of_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput)
    (hμ : CDEMertens) : Statement :=
  haveI := Fact.mk hGRH; haveI := Fact.mk hBG; haveI := Fact.mk hμ
  ternary_goldbach

end TernaryGoldbach
