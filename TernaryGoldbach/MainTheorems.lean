import TernaryGoldbach.Helfgott.Main

/-!
# The main theorems, with explicit hypotheses

Inside the development, the four numerical hypotheses of `Statement.lean` are `Fact` instances
(section variables). Here they become ordinary hypotheses. These theorems use only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). They are the theorems checked by
leanprover/comparator against `Challenge.lean` (`comparator/config.json`).
-/

namespace TernaryGoldbach

/-- **Helfgott's theorem for large `n`**: every odd `n ≥ 10²⁷` is a sum of three primes, given RH
up to `3·10¹⁰`, Platt's GRH verification and Ramaré's bound for `∑ μ(n)/n`. -/
theorem ternary_goldbach_large_of_hypotheses (hRH : RHUpTo) (hGRH : PlattGRH)
    (hμ : RamareMoebius) : TernaryGoldbachFrom (10 ^ 27) :=
  haveI := Fact.mk hRH; haveI := Fact.mk hGRH; haveI := Fact.mk hμ
  Helfgott.ternaryGoldbachFrom

/-- **The ternary Goldbach conjecture** (Helfgott, 2013): every odd integer greater than `5` is a
sum of three primes, given the four published numerical results of `Statement.lean`. -/
theorem ternary_goldbach_of_hypotheses (hRH : RHUpTo) (hGRH : PlattGRH)
    (hBG : BinaryGoldbachInput) (hμ : RamareMoebius) : Statement :=
  haveI := Fact.mk hRH; haveI := Fact.mk hGRH; haveI := Fact.mk hBG; haveI := Fact.mk hμ
  ternary_goldbach

end TernaryGoldbach
