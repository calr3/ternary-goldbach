import RSBounds.SchoenfeldPrimeWalkAll
import RSBounds.Schoenfeld1976Theorem7

/-!
# Schoenfeld (1976), Theorem 7*, given PsiCert

`Schoenfeld1976Theorem7` with the kernel walk `SchoenfeldPrimeWalk.good` plugged in. Each result
assumes PsiCert (`|ψ(x) − x| ≤ (4/5)√x` for `1500 ≤ x ≤ 10¹⁰`), which is certified outside this
project; the targets themselves keep finite RH as a premise.
-/

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Theorem7

/-- (5.5a*), given PsiCert. -/
theorem proved_psiLog (hcert : Goals.Schoenfeld1976.PsiCert) : Goals.Schoenfeld1976.PsiLog :=
  fun hRH _ hx => psiLog (fun _ h1 h2 => SchoenfeldPrimeWalk.good h1 h2) hRH hcert hx

/-- (5.5b*), given PsiCert. -/
theorem proved_psiLogLower (hcert : Goals.Schoenfeld1976.PsiCert) :
    Goals.Schoenfeld1976.PsiLogLower :=
  fun hRH _ hx => psiLogLower (fun _ h1 h2 => SchoenfeldPrimeWalk.good h1 h2) hRH hcert hx

/-- (5.6a*), given PsiCert. -/
theorem proved_thetaLogUpper (hcert : Goals.Schoenfeld1976.PsiCert) :
    Goals.Schoenfeld1976.ThetaLogUpper :=
  fun hRH _ hx => thetaLogUpper (fun _ h1 h2 => SchoenfeldPrimeWalk.good h1 h2) hRH hcert hx

/-- (5.6*), given PsiCert. -/
theorem proved_thetaLog (hcert : Goals.Schoenfeld1976.PsiCert) : Goals.Schoenfeld1976.ThetaLog :=
  fun hRH _ hx => thetaLog (fun _ h1 h2 => SchoenfeldPrimeWalk.good h1 h2) hRH hcert hx

end TernaryGoldbach.RSBounds.Schoenfeld1976Theorem7
