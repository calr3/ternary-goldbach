import RSBounds.Schoenfeld1976Rows22
import RSBounds.Schoenfeld1976Rows6
import RSBounds.Schoenfeld1976Targets

/-!
# Schoenfeld (1976), Theorem 7*, (5.6b*): proved for every `x ≥ e^22`

Under `Goals.FiniteRH 1894438.5122`,

    |ψ(x) − x| < 0.0077629 x / log x   and   |θ(x) − x| < 0.0077629 x / log x   (x ≥ e^22).

The ranges:

| `log x` | Module | Method |
|---|---|---|
| `[22, 23]` | `Schoenfeld1976Rows22` | RS75 `b = 23` chain kept as a function of `x`; sharper `ψ − θ` |
| `[23, 38.3]` | `Schoenfeld1976Rows23` | RS75 `b = 23` bound `0.00020211` |
| `[38.3, 170]` | `Schoenfeld1976Rows38` | RS75 `b = 23` chain at `√x ≥ 2·10⁸` |
| `[100, 313]` | `Schoenfeld1976Rows4` | quartic envelope, critical-line term kept |
| `[313, 947]` | `Schoenfeld1976Rows6` | far-only sextic envelope, eleven rows |
| `[947, 1300]` | `Schoenfeld1976Rows4` | far-only quartic envelope, six rows |
| `[1300, 1737]` | `Schoenfeld1976Rows2` | far-only quadratic envelope, three rows |
| `≥ 1737` | `Schoenfeld1976Large` | Theorem 11, analytic range |
-/

namespace TernaryGoldbach.RSBounds.Schoenfeld1976PsiThetaLog

/-- **(5.6b*) for every `x ≥ e^22`**, under finite RH through `1894438.5122`. -/
theorem psiThetaLog (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 22 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt x (Real.exp 313) with h1 | h1
  · exact Schoenfeld1976Rows22.psiThetaLog_22_313 hRH hx h1
  rcases le_or_gt x (Real.exp 947) with h2 | h2
  · exact Schoenfeld1976Rows6.psiThetaLog_313_947 hRH h1.le h2
  · exact Schoenfeld1976Rows4.psiThetaLog_ge947 hRH h2.le

/-- The target proposition `Goals.Schoenfeld1976.PsiThetaLog`. -/
theorem proved : Goals.Schoenfeld1976.PsiThetaLog :=
  fun hRH _ hx => psiThetaLog hRH hx

end TernaryGoldbach.RSBounds.Schoenfeld1976PsiThetaLog
