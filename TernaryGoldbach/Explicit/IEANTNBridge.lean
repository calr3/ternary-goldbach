import TernaryGoldbach.Explicit.ZetaZeroSums

/-!
# `PlattGRH` gives IEANTN's `RiemannHypothesisUpTo 1894438.5122`

IEANTN (`teorth/IEANTN`, `IEANTN/Vocabulary/Zeta.lean`) records a numerical verification of RH as
`RiemannHypothesisUpTo T`: no zero of `ζ` with real part in `(1/2, 1)` and imaginary part in
`[0, T]`. The definitions are copied here (Mathlib only). `riemannHypothesisUpTo_of_platt` derives the
form at Rosser–Yohe–Schoenfeld's height `1894438.5122` from RH up to `10⁸` (`rh_upto_1e8`).
-/

namespace TernaryGoldbach.Explicit

/-- IEANTN's `zetaZeroesIn I J`: zeros of `ζ` with real part in `I` and imaginary part in `J`. -/
def ieantnZetaZeroesIn (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ {s : ℂ | riemannZeta s = 0}}

/-- IEANTN's `RiemannHypothesisUpTo T`. -/
def IEANTNRiemannHypothesisUpTo (T : ℝ) : Prop :=
  IsEmpty (ieantnZetaZeroesIn (Set.Ioo (1 / 2) 1) (Set.Icc 0 T))

theorem riemannHypothesisUpTo_of_RHBelow {T H : ℝ} (hTH : T ≤ H) (h : RHBelow H) :
    IEANTNRiemannHypothesisUpTo T := by
  refine ⟨fun ⟨s, hre, him, hz⟩ => ?_⟩
  have h1 : s.re = 1 / 2 :=
    h s hz (by linarith [hre.1]) hre.2 (by rw [abs_of_nonneg him.1]; linarith [him.2])
  linarith [hre.1]

/-- **RH up to `1894438.5122`**, in IEANTN's form, from `PlattGRH`. -/
theorem riemannHypothesisUpTo_of_platt [Fact TernaryGoldbach.PlattGRH] :
    IEANTNRiemannHypothesisUpTo 1894438.5122 :=
  riemannHypothesisUpTo_of_RHBelow (by norm_num) rh_upto_1e8

end TernaryGoldbach.Explicit
