import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.Numerics
import TernaryGoldbach.Helfgott.NonPrime
import TernaryGoldbach.Helfgott.SupNorms
import TernaryGoldbach.Helfgott.HHBound
import TernaryGoldbach.Helfgott.Chebyshev
import TernaryGoldbach.MinorArcs.NumericsFinal
import TernaryGoldbach.MajorArcs.MajorTotal
import RSBounds.HelfgottAppA.NonPrime

/-!
# The top-level inputs

The four analytic inputs of [H, §14.4] (circle identity, major arcs (14.27), minor arcs (14.49),
non-prime terms (14.51)) are proved here from the rest of the development.  The computational
input for the small cases, `binary_goldbach_input` [OeSHP14], is the hypothesis `BinaryGoldbachInput`; the small
cases themselves are in `SmallCases.lean`.  All hypotheses are listed and checked against their sources in `HYPOTHESES.md`.

[H]    H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015), the book
       version, which supersedes arXiv:1205.5252, 1305.2897 and 1312.7748.  **This is the
       reference the blueprint follows**; equation numbers are the book's.
[HP13] H. A. Helfgott, D. Platt, *Numerical verification of the ternary Goldbach conjecture
       up to 8.875 · 10³⁰*, Experiment. Math. 22 (2013).
[OeSHP14] T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the even
       Goldbach conjecture and computation of prime gaps up to 4 · 10¹⁸*, Math. Comp. 83 (2014).
-/

open Complex MeasureTheory ArithmeticFunction

namespace TernaryGoldbach.Helfgott

/-! ## Analytic inputs (for odd `N ≥ 10²⁷`, with `x = xOf N`) -/

/-- **Circle method identity** [H, (10.3), (14.50)].  The sums `S_{η₊}`, `S_{η_*}` converge
absolutely because `η₊` and `η_*` decay rapidly (`TernaryGoldbach.Helfgott.Decay`), and the
integral over `[0, 1]` picks out the representations of `N` (`circle_identity_tsum`).

*Proved.* -/
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

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **Major arcs** [H, (14.27)], with `1.049` in place of [H]'s `1.058259`:
`Re ∫_{𝔐_{8,r₀}} S_{η₊}(α,x)² S_{η_*}(α,x) e(-Nα) dα ≥ 1.049 x²/κ` with `r₀ = 150000`.

*Proof:* `MajorArcs.major_total` (`MajorArcs/MajorTotal.lean`), following [H, §§14.1–14.2]. On the
arcs of modulus `q` the sums are compared with `μ(q)/φ(q) η̂(−βx)x` by Cor 7.1.3 and Prop 7.1.5
(the Part II results collected in `MinorArcs/PartIICited.lean`); the singular series is bounded below
with `∏_{3 ≤ p ≤ r₀} p/(p − 1) ≤ 15.5` (`MajorArcs.prod_p_div_le`, from the kernel computation of
`SmallMertensProd.lean`); and `C_{η◦,η_*}(N/x)` is computed. This uses `PlattGRH` and no other
hypothesis. -/
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

variable [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.RamareMoebius] in
/-- **Minor arcs** [H, (14.49)]:
`∫_{(ℝ/ℤ) \ 𝔐_{8,r₀}} |S_{η_*}(α,x)| |S_{η₊}(α,x)|² dα ≤ 1.0072 x²/κ` for `x ≥ 4.9 · 10²⁶`
(true for `x = xOf N` when `N ≥ 10²⁷`, [H, (14.15)]).

*Proved* (`MinorArcs/MinorTotal.lean: minor_total`) by "repair 3" of [H, Thm 13.2.1] (NOTES, "Ch. 13:
scale erratum"): [H]'s proof derives its ℓ∞ input only off the arcs at scale `x/κ`; we run
Prop 13.1.2 with the arcs at scale `x/κ` above the base level, take a fresh Dirichlet
approximation at each scale in (11.9), extend the levels to `≈ x^{0.3}`, and bound the base gap
with [H, Cor 7.1.3]. It uses Theorem 3.1.1, Prop 12.2.4 (with `c₊ = 2`), the Part II results
`cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7` (`MinorArcs/PartIICited.lean`) and `E_le_14_28`
(`MinorArcs/EBound.lean`), all proved. The numerics (`numerics_M`) are proved: generated cells for
`x ≤ 4.9·10¹⁰¹` (`scripts/gen_cells.py`) and an analytic argument beyond.

(Our constant `1.0072` is below [H]'s `1.00948`, although our Theorem 3.1.1 has `0.8764` where
[H]'s has `0.5`: [H]'s proof gives `0.8102`, and the corrected [H, (5.36)] gives `0.8764`.) -/
theorem minor_arcs_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    ∫ α in Set.Ioc (0:ℝ) 1 \ majorArcs 8 r₀ (xOf N),
        ‖S etaStar (xOf N) α‖ * ‖S etaPlus (xOf N) α‖ ^ 2 ≤ 1.0072 * xOf N ^ 2 / κ := by
  have hx := xOf_ge N hN27
  exact MinorArcs.minor_total hx (MinorArcs.numerics_M hx)

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **Non-prime and even terms**, [H, (14.51)]: the terms where some `nᵢ` is even or not prime
contribute at most `7.3306 · N^{3/2} log N`, with [H]'s
`7.3306 = 3 · 1.079955² · 1.414 · 1.4262 · 1.03883`. The proof is Helfgott's (Garald1/RSBounds,
`RSBounds/HelfgottAppA/`), through our `repSum_sub_le_of_bounds`: the sup norm
`|η₊|_∞ ≤ 1.079955` of Appendix A ([H, (14.3)], proved there), [H]'s `|η_*|_∞ ≤ 1.414`
(`Helfgott/SupNorms.lean`), and `ψ(n) ≤ 1.03883 n`, `ψ(y) − θ(y) < 1.4262 √y` ([H, (2.15), (5.5)];
`Prelim/LambdaMu.lean`, from `PlattGRH`).

*Proved.* -/
theorem nonprime_input (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      7.3306 * (N * √N) * Real.log N :=
  _root_.RSBounds.HelfgottAppA.nonprime_input_book (fun t _ => abs_etaStar_le_1414 t)
    (fun n => (Prelim.psi_bounds n).1) (fun _ hy => Prelim.sum_vonMangoldt_nonprime_lt hy) N hN27

/-! ## Computational inputs (for the small cases) -/

/-- **Numerical hypothesis: binary Goldbach up to `4 · 10¹⁸`** [OeSHP14]. An exhaustive computer
search (Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014)) shows that every even
`4 ≤ n ≤ 4·10¹⁸` is a sum of two primes; the range up to `3·10¹⁷` was double-checked
([OeSHP14, Table 1 and §1.3]). `SmallCases.lean` uses the whole range. -/
theorem binary_goldbach_input [h : Fact BinaryGoldbachInput] :
    BinaryGoldbachUpTo (4 * 10 ^ 18) :=
  h.out

variable [Fact TernaryGoldbach.BinaryGoldbachInput]

end TernaryGoldbach.Helfgott
