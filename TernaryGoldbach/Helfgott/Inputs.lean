import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.Numerics
import TernaryGoldbach.Helfgott.NonPrime
import TernaryGoldbach.Helfgott.SupNorms
import TernaryGoldbach.Helfgott.Chebyshev
import TernaryGoldbach.Reduction

/-!
# Unproved inputs

**Every `sorry` in the project is in this file.**  Each remaining one is a result from the literature,
stated as precisely as we could, with a pointer to where it is proved.  Everything else (the
way these inputs combine into the ternary Goldbach conjecture) is proved in Lean.

[H]    H. A. Helfgott, *The ternary Goldbach conjecture is true*, arXiv:1312.7748.
[Hela] H. A. Helfgott, *Major arcs for Goldbach's problem*, arXiv:1305.2897.
[Helb] H. A. Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252.
[HP]   H. A. Helfgott, D. Platt, *Numerical verification of the ternary Goldbach conjecture
       up to 8.875 · 10³⁰*, Experiment. Math. 22 (2013).
[OeSHP] T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the even
       Goldbach conjecture and computation of prime gaps up to 4 · 10¹⁸*, Math. Comp. 83 (2014).
-/

open Complex MeasureTheory ArithmeticFunction

namespace TernaryGoldbach.Helfgott

/-! ## Analytic inputs (for odd `N ≥ 10²⁷`, with `x = xOf N`) -/

/-- **Circle method identity** [H, (3.3), (7.49)].  The sums `S_{η₊}`, `S_{η_*}` converge
absolutely because `η₊` and `η_*` decay rapidly (`TernaryGoldbach.Helfgott.Decay`), and the
integral over `[0, 1]` picks out the representations of `N` (`circle_identity_tsum`).

*Proved* — this input no longer depends on `sorry`. -/
theorem circle_identity_input (N : ℕ) (hN : 0 < N) :
    IntegrableOn (integrand N) (Set.Ioc 0 1) ∧
      ∫ α in Set.Ioc (0:ℝ) 1, integrand N α = (repSum (fun _ => True) N : ℂ) := by
  have hx : 0 < xOf N := div_pos (by exact_mod_cast hN) xOf_denom_bounds.1
  have h := circle_identity_tsum N (summable_etaPlus hx) (summable_etaPlus hx)
    (summable_etaStar hx)
  have hfun : integrand N = fun α =>
      expTsum (fun n => ((Λ n * etaPlus (n / xOf N) : ℝ) : ℂ)) α *
        expTsum (fun n => ((Λ n * etaPlus (n / xOf N) : ℝ) : ℂ)) α *
        expTsum (fun n => ((Λ n * etaStar (n / xOf N) : ℝ) : ℂ)) α * e (-(N * α)) := by
    funext α; simp only [integrand, S, expTsum, sq]
  rw [hfun]
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [repSum, and_true, Complex.ofReal_sum, apply_ite (fun r : ℝ => (r : ℂ)),
    Complex.ofReal_zero, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  split_ifs <;> ring

/-- **Major arcs** [H, (7.25)]:
`∫_{𝔐_{8,r₀}} S_{η₊}(α,x)² S_{η_*}(α,x) e(-Nα) dα ≥ 1.058259 x²/κ` with `r₀ = 150000`.

*Proof in the literature:* [H, §§3, 7.1–7.2] and [Hela].  This relies on Platt's rigorous
computer verification of GRH for Dirichlet `L`-functions of modulus `q ≤ 300000` up to a
bounded height. -/
theorem major_arcs_input (N : ℕ) (hN : Odd N) (hN27 : 10 ^ 27 ≤ N) :
    1.058259 * xOf N ^ 2 / κ ≤
      (∫ α in Set.Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ (xOf N), integrand N α).re := by
  sorry

/-- **Minor arcs** [H, (7.48)]:
`∫_{(ℝ/ℤ) \ 𝔐_{8,r₀}} |S_{η_*}(α,x)| |S_{η₊}(α,x)|² dα ≤ 0.97392 x²/κ` for `x ≥ 4.9 · 10²⁶`
(true for `x = xOf N` when `N ≥ 10²⁷`, [H, (7.15)]).

*Proof in the literature:* [H, §§5–7.3] (Theorem 6.3 there), building on [Helb]: Vaughan's
identity, explicit bilinear sum bounds, and the large sieve. -/
theorem minor_arcs_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    ∫ α in Set.Ioc (0:ℝ) 1 \ majorArcs 8 r₀ (xOf N),
        ‖S etaStar (xOf N) α‖ * ‖S etaPlus (xOf N) α‖ ^ 2 ≤ 0.97392 * xOf N ^ 2 / κ := by
  sorry

/-- **Non-prime and even terms**, a weaker form of [H, (7.50)]: the terms where some `nᵢ` is
even or not prime contribute at most `10⁷ · N^{3/2} log N`.

[H] gets the constant `7.3306` from the sharp sup norms `|η₊|_∞ ≤ 1.079955`,
`|η_*|_∞ ≤ 1.414` and the Rosser–Schoenfeld bounds `ψ(x) < 1.03883 x`,
`ψ(x) - θ(x) < 1.4262 √x`.  We use the easy bounds `|η₊| ≤ 400`, `|η_*| ≤ 6.2`
(`Helfgott/SupNorms.lean`) and the elementary `ψ(N) ≤ 1.387 N`, `ψ(N) - θ(N) ≤ 1.6 √N`
(`Helfgott/Chebyshev.lean`) instead; the final inequality still has room
(`final_inequality_crude`).

*Proved.* -/
theorem nonprime_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      1e7 * (N * √N) * Real.log N := by
  have hN : 1 ≤ N := le_trans (by norm_num) hN27
  have h := repSum_sub_le_of_bounds hN (fun t ht => abs_etaPlus_le_400 ht)
    (fun t _ => abs_etaStar_le_const t)
  have hpsi := psi_le N hN27
  have hpt := psi_sub_theta_le N hN27
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN27
  have hsq : (10 : ℝ) ^ 13 ≤ √N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hlog2 : Real.log 2 ≤ 0.0001 * √N := by
    have := Real.log_two_lt_d9; nlinarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hbad0 : 0 ≤ psi N - theta N + Real.log 2 :=
    (Finset.sum_nonneg fun n _ => ΛBad_nonneg n).trans (sum_ΛBad_le N)
  have hpsi0 : 0 ≤ psi N := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  have hs0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  calc repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N
      ≤ 3 * (400 ^ 2 * 6.2) * Real.log N * (psi N - theta N + Real.log 2) * psi N := h
    _ ≤ 3 * (400 ^ 2 * 6.2) * Real.log N * (1.6001 * √N) * (1.387 * N) := by
        gcongr; linarith
    _ = (3 * (400 ^ 2 * 6.2) * 1.6001 * 1.387) * (N * √N) * Real.log N := by ring
    _ ≤ 1e7 * (N * √N) * Real.log N := by gcongr; norm_num

/-! ## Computational inputs (for the small cases) -/

/-- **Binary Goldbach up to `4 · 10¹⁸`** [OeSHP]. -/
theorem binary_goldbach_input : BinaryGoldbachUpTo (4 * 10 ^ 18) := by
  sorry

/-- **The Helfgott–Platt prime ladder** [HP]: certified primes starting at `3`, with
consecutive gaps `≤ 4 · 10¹⁸ - 4`, reaching `8.875694 · 10³⁰`.  (Building the ladder only up
to `10²⁷` would suffice here; [H, §1] says that takes about 25 hours on one processor.) -/
theorem prime_ladder_input :
    ∃ l : List ℕ, (∀ p ∈ 3 :: l, p.Prime ∧ Odd p) ∧
      List.Chain (LadderStep (4 * 10 ^ 18 - 4)) 3 l ∧
      8875694 * 10 ^ 24 ≤ (3 :: l).getLast (List.cons_ne_nil _ _) := by
  sorry

end TernaryGoldbach.Helfgott
