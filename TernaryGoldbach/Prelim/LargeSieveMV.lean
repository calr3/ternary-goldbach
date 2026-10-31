import TernaryGoldbach.CircleMethod
import TernaryGoldbach.Prelim.LargeSieveMVProof

/-!
# The sharp large sieve inequalities

[B, §5.2] uses two sharp forms of the large sieve. Both are **proved** in
`Prelim/LargeSieveMVProof.lean`, from the Montgomery–Vaughan Hilbert inequalities
(`Prelim/HilbertReal.lean`, `Prelim/HilbertCsc.lean`). [MV73, Lemma 8] below is still `sorry`.

Notation: `S(α) = ∑_{M < n ≤ M+N} a(n) e(αn)`; `‖t‖ = |t - round t|` is the distance from `t`
to the nearest integer.
-/

open Finset

namespace TernaryGoldbach.Prelim

/-- **The large sieve, optimal form** (Selberg; Montgomery–Vaughan, *The large sieve*,
Mathematika 20 (1973), Thm. 1 with `δ_r ≥ δ`; see also [B, §5.2], [Sel91], [MV74]): if the points
`α_r` are pairwise `δ`-separated modulo 1, then
`∑_r |∑_{M < n ≤ M+N} a(n) e(α_r n)|² ≤ (N - 1 + δ⁻¹) ∑ |a(n)|²`. (`δ ≤ 1` is automatic for two or
more points; it is needed for a single point.) -/
theorem large_sieve_opt {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(α r - α r') - round (α r - α r')|)
    (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2 ≤
      ((N : ℝ) - 1 + δ⁻¹) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  exact LS.large_sieve_opt s α hδ hδ1 hsep M N a

/-- **The large sieve with weights** (Montgomery–Vaughan, *The large sieve*, Mathematika 20
(1973), (1.6) / Thm. 1; [B, (5.48)]): if `δ_r > 0` and `‖α_r - α_{r'}‖ ≥ δ_r` for `r' ≠ r`, then
`∑_r (N + (3/2) δ_r⁻¹)⁻¹ |∑_{M < n ≤ M+N} a(n) e(α_r n)|² ≤ ∑ |a(n)|²`. -/
theorem large_sieve_weighted {ι : Type*} (s : Finset ι) (α δ : ι → ℝ)
    (hδ : ∀ r ∈ s, 0 < δ r)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ r ≤ |(α r - α r') - round (α r - α r')|)
    (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ((N : ℝ) + 3 / 2 * (δ r)⁻¹)⁻¹ * ‖∑ n ∈ Ioc M (M + N), a n * e (α r * n)‖ ^ 2 ≤
      ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  exact LS.large_sieve_weighted s α δ hδ hsep M N a

/-- **[MV73, Lemma 8]** (for `R ≥ 100`) plus a direct numerical check for `2 ≤ R < 100`
([B, p. 97]): `∑_{r ≤ R} (1 + r/R)⁻¹ μ(r)²/φ(r) > log R + 0.25068` for `R ≥ 2`. -/
theorem sum_weighted_mu_sq_div_totient {R : ℝ} (hR : 2 ≤ R) :
    Real.log R + 0.25068 ≤ ∑ r ∈ (Icc 1 ⌊R⌋₊).filter Squarefree,
      (1 + r / R)⁻¹ * (1 / Nat.totient r : ℝ) := by
  sorry

end TernaryGoldbach.Prelim
