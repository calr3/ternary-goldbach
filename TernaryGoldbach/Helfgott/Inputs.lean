import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.Numerics
import TernaryGoldbach.Helfgott.NonPrime
import TernaryGoldbach.Helfgott.SupNorms
import TernaryGoldbach.Helfgott.Chebyshev
import TernaryGoldbach.MinorArcs.NumericsFinal
import TernaryGoldbach.MajorArcs.MajorTotal

/-!
# The top-level inputs

The four analytic inputs of [H, §14.4] (circle identity, major arcs (14.27), minor arcs (14.49),
non-prime terms (14.51)) are proved here from the rest of the development.  The computational
input for the small cases, `binary_goldbach_input` [OeSHP14], is a numerical axiom; the small
cases themselves are in `SmallCases.lean`.  All numerical axioms are listed and audited in `AXIOMS.md`.

[H]    H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015), the book
       version, which supersedes [H13], [Hela], [Helb].  **This is the reference the blueprint
       follows**; equation numbers below are the book's.
[H13]  H. A. Helfgott, *The ternary Goldbach conjecture is true*, arXiv:1312.7748.
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

/-- **Circle method identity** [H, (10.3), (14.50)].  The sums `S_{η₊}`, `S_{η_*}` converge
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

/-- `x = xOf N ≥ 4.9·10²⁶` for `N ≥ 10²⁷`. -/
theorem xOf_ge (N : ℕ) (hN27 : 10 ^ 27 ≤ N) : (4.9e26 : ℝ) ≤ xOf N := by
  obtain ⟨h0, h1⟩ := xOf_denom_bounds
  have hN : (1e27 : ℝ) ≤ N := by
    have : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN27
    norm_num at this ⊢; linarith
  unfold xOf
  rw [le_div_iff₀ h0]
  nlinarith

/-- **Major arcs** [H, (14.27)], with `1.049` in place of [H]'s `1.058259`:
`Re ∫_{𝔐_{8,r₀}} S_{η₊}(α,x)² S_{η_*}(α,x) e(-Nα) dα ≥ 1.049 x²/κ` with `r₀ = 150000`.

*Proof:* `MajorArcs.major_total` (`MajorArcs/MajorTotal.lean`), following [H, §§14.1–14.2]. On the
arcs of modulus `q` the sums are compared with `μ(q)/φ(q) η̂(−βx)x` by Cor 7.1.3 and Prop 7.1.5
(the cited Part II inputs in `MinorArcs/PartIICited.lean`); the singular series is bounded below
with the Mertens axiom; and `C_{η◦,η_*}(N/x)` is computed. -/
theorem major_arcs_input (N : ℕ) (hN : Odd N) (hN27 : 10 ^ 27 ≤ N) :
    1.049 * xOf N ^ 2 / κ ≤
      (∫ α in Set.Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ (xOf N), integrand N α).re := by
  have hx := xOf_ge N hN27
  have hNx : (N : ℝ) / xOf N = 2 + 9 / (8 * √(Real.pi / 2)) / κ := by
    have hN0 : (N : ℝ) ≠ 0 := by
      have : 0 < N := lt_of_lt_of_le (by positivity) hN27
      exact_mod_cast this.ne'
    have hs : √(2 * Real.pi) = 2 * √(Real.pi / 2) := by
      rw [show 2 * Real.pi = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have hs0 : 0 < √(Real.pi / 2) := Real.sqrt_pos.2 (by positivity)
    rw [xOf, hs, κ]
    field_simp
    ring
  exact MajorArcs.major_total hN hx hNx

/-- **Minor arcs** [H, (14.49)]:
`∫_{(ℝ/ℤ) \ 𝔐_{8,r₀}} |S_{η_*}(α,x)| |S_{η₊}(α,x)|² dα ≤ 1.0376 x²/κ` for `x ≥ 4.9 · 10²⁶`
(true for `x = xOf N` when `N ≥ 10²⁷`, [H, (14.15)]).

*Proved* (`MinorArcs/MinorTotal.lean: minor_total`) by "repair 3" of [H, Thm 13.2.1] (NOTES, "Ch. 13:
scale erratum"): [H]'s proof derives its ℓ∞ input only off the arcs at scale `x/κ`; we run
Prop 13.1.2 with the arcs at scale `x/κ` above the base level, take a fresh Dirichlet
approximation at each scale in (11.9), extend the levels to `≈ x^{0.3}`, and bound the base gap
with [H, Cor 7.1.3]. It depends on the trusted inputs of Theorem 3.1.1, the trusted computation
Prop 12.2.4, the cited Part II results `cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7`, `E_le_14_28`
(`MinorArcs/PartIICited.lean`). The numerics (`numerics_M`) are proved: generated cells for
`x ≤ 4.9·10¹⁰¹` (`scripts/gen_cells.py`) and an analytic argument beyond.

(Our constant `1.0376` is weaker than [H]'s `1.00948`. [H]'s Theorem 3.1.1 has `0.5` where its
proof gives `0.8102`; with the corrected [H, (5.36)] our Theorem 3.1.1 has `0.8764`.) -/
theorem minor_arcs_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    ∫ α in Set.Ioc (0:ℝ) 1 \ majorArcs 8 r₀ (xOf N),
        ‖S etaStar (xOf N) α‖ * ‖S etaPlus (xOf N) α‖ ^ 2 ≤ 1.0376 * xOf N ^ 2 / κ := by
  have hx := xOf_ge N hN27
  exact MinorArcs.minor_total hx (MinorArcs.numerics_M hx)

/-- **Non-prime and even terms**, a weaker form of [H, (14.51)]: the terms where some `nᵢ` is
even or not prime contribute at most `6.7 · 10⁶ · N^{3/2} log N`.

[H] gets the constant `7.3306` from the sharp sup norms `|η₊|_∞ ≤ 1.079955`,
`|η_*|_∞ ≤ 1.414` and the Rosser–Schoenfeld bounds `ψ(x) < 1.03883 x`,
`ψ(x) - θ(x) < 1.4262 √x`.  We use the easy bounds `|η₊| ≤ 400`, `|η_*| ≤ 6.2`
(`Helfgott/SupNorms.lean`) and the elementary `ψ(N) ≤ 1.387 N`, `ψ(N) - θ(N) ≤ 1.6 √N`
(`Helfgott/Chebyshev.lean`) instead; the final inequality still has room
(`final_inequality_crude`).

*Proved.* -/
theorem nonprime_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      6.7e6 * (N * √N) * Real.log N := by
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
    _ ≤ 6.7e6 * (N * √N) * Real.log N := by gcongr; norm_num

/-! ## Computational inputs (for the small cases) -/

/-- **Numerical axiom: binary Goldbach up to `1.45 · 10¹⁷`** [OeSHP]. An exhaustive computer
search (Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014)) shows that every even
`4 ≤ n ≤ 4·10¹⁸` is a sum of two primes; the range up to `3·10¹⁷` was double-checked
([OeSHP, Table 1 and §1.3]). `SmallCases.lean` needs only `1.45·10¹⁷`. -/
axiom binary_goldbach_input : BinaryGoldbachUpTo (145 * 10 ^ 15)

end TernaryGoldbach.Helfgott
