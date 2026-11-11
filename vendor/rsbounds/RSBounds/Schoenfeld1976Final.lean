import RSBounds.PsiFinite.Final
import RSBounds.Schoenfeld1976Theorem7Proved
import RSBounds.Schoenfeld1976Theorem11Proved

/-!
# Schoenfeld (1976), Theorems 7* and 11, with PsiCert discharged

`PsiFinite.psi_abs_sub_le_four_fifths_sqrt` (the PsiCert certification: `|ψ(x) − x| ≤ (4/5)√x`
for `1500 ≤ x ≤ 10¹⁰`) is exactly `Goals.Schoenfeld1976.PsiCert`. With it, every display of
Theorem 7* and Theorem 11 depends only on `Goals.FiniteRH 1894438.5122`, which each target keeps
as its premise.
-/

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Final

theorem psiCert : Goals.Schoenfeld1976.PsiCert :=
  fun _ h₁ h₂ => _root_.PsiFinite.psi_abs_sub_le_four_fifths_sqrt h₁ h₂

/-- (5.5a*). -/
theorem psiLog : Goals.Schoenfeld1976.PsiLog :=
  Schoenfeld1976Theorem7.proved_psiLog psiCert

/-- (5.5b*). -/
theorem psiLogLower : Goals.Schoenfeld1976.PsiLogLower :=
  Schoenfeld1976Theorem7.proved_psiLogLower psiCert

/-- (5.6a*). -/
theorem thetaLogUpper : Goals.Schoenfeld1976.ThetaLogUpper :=
  Schoenfeld1976Theorem7.proved_thetaLogUpper psiCert

/-- (5.6*). -/
theorem thetaLog : Goals.Schoenfeld1976.ThetaLog :=
  Schoenfeld1976Theorem7.proved_thetaLog psiCert

/-- (5.6b*) (needs no PsiCert). -/
theorem psiThetaLog : Goals.Schoenfeld1976.PsiThetaLog :=
  Schoenfeld1976PsiThetaLog.proved

/-- Theorem 11, (7.2). -/
theorem psiTheorem11 : Goals.Schoenfeld1976.PsiTheorem11 :=
  Schoenfeld1976Theorem11Proved.proved_psi psiCert

/-- Theorem 11, (7.3). -/
theorem thetaTheorem11 : Goals.Schoenfeld1976.ThetaTheorem11 :=
  Schoenfeld1976Theorem11Proved.proved_theta psiCert

/-- Theorem 11, (7.4). -/
theorem psiUpperTheorem11 : Goals.Schoenfeld1976.PsiUpperTheorem11 :=
  Schoenfeld1976Theorem11Proved.proved_psiUpper psiCert

end TernaryGoldbach.RSBounds.Schoenfeld1976Final
