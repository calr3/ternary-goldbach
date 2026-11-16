import TernaryGoldbach.Prelim.McheckBig
import TernaryGoldbach.Statement
import RSBounds.Moebius003.Cells
import RSBounds.Moebius003.Tail
import RSBounds.Moebius003.Misc
import RSBounds.Moebius003.MofN

/-!
# The inputs of `McheckBig.lean` from Helfgott's RSBounds

Given RSBounds' `Inputs` (the hypotheses of `mobius003.tex`, which hold under `PlattGRH`; see
`MoebiusLogSharp.lean`) and Ramaré's bound, RSBounds proves what `McheckBigInputs` asks for: the
bound `|M(n)| ≤ 0.571 √n` on `[33, 10⁹]` and, beyond `10⁹`, the profile `|N(n)| ≤ 0.017 n`,
`|C₀| ≤ 1743` and `S(10⁹) ≤ 36113`.
-/

open Finset

namespace TernaryGoldbach.Prelim

theorem mertR_natCast_eq_M (n : ℕ) : mertR n = RSBounds.Moebius003.M n := by
  rw [mertR, Nat.floor_natCast]; rfl

theorem nfun_eq_N (n : ℕ) : nfun n = RSBounds.Moebius003.N n := rfl

theorem iint_eq_Iint (a b : ℕ) : iint a b = RSBounds.Moebius003.Iint a b := rfl

theorem sfun_eq_S (x : ℕ) : sfun x = RSBounds.Moebius003.S x := by
  rw [sfun, RSBounds.Moebius003.S]
  refine sum_congr rfl fun t _ => ?_
  rw [mertR_natCast_eq_M]

/-- `McheckBigInputs` from RSBounds' `Inputs`, Ramaré's bound and the kernel computation of
`∑_{t < 2·10⁵} |M(t)|/t`. -/
theorem mcheckBigInputs_of (hI : RSBounds.Moebius003.Inputs) (hR : RamareMoebius)
    (hk : ∑ t ∈ Ico (1 : ℕ) 200000, |mertR t| / (t : ℝ) ≤ 131) : McheckBigInputs where
  ramare x hx := hR x hx
  mertSqrt n h1 h2 := by
    rw [mertR_natCast_eq_M]
    have := RSBounds.Moebius003.abs_M_le_sqrt hI h1 (by simpa [RSBounds.Moebius003.X0] using h2)
    simpa [RSBounds.Moebius003.cM] using this
  nBound n hn := by
    rw [nfun_eq_N]
    have hc := RSBounds.Moebius003.cells hI
    rcases lt_or_ge n RSBounds.Moebius003.Dend with hD | hD
    · exact hc.nuBar n (by simpa [RSBounds.Moebius003.X0] using hn) hD
    · have := RSBounds.Moebius003.prop10 hI hc n hD
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  mOfN n hn := by
    rw [mertR_natCast_eq_M, nfun_eq_N, iint_eq_Iint]
    have h1 := RSBounds.Moebius003.abs_M_le_of_N (x := n) (by simpa [RSBounds.Moebius003.X0] using hn)
    have h2 := RSBounds.Moebius003.abs_C0_le_C0B hI
    simp only [RSBounds.Moebius003.C0B, RSBounds.Moebius003.X0] at h1 h2
    linarith
  sX0 := by
    rw [sfun_eq_S]
    have := RSBounds.Moebius003.S_X0_le hI
    simpa [RSBounds.Moebius003.X0, RSBounds.Moebius003.I0B] using this
  sX1 := hk

end TernaryGoldbach.Prelim
