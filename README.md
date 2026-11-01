# Ternary Goldbach in Lean 4

A formalization of Helfgott's proof of the ternary Goldbach conjecture in Lean 4 and Mathlib. The
conjecture says that every odd integer greater than 5 is a sum of three primes:
`TernaryGoldbach.ternary_goldbach : Statement` (see `TernaryGoldbach/Statement.lean`). The proof
follows H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 [B].

## Status

The proof is complete: there is no `sorry`, and `ternary_goldbach` depends on 36 explicitly stated
axioms besides Lean's standard three. They are:
* 22 finite computations of our own;
* 6 published computations: RH up to `3·10¹²`, Platt's GRH verification (2 axioms), binary
  Goldbach up to `4·10¹⁸`, the Helfgott–Platt prime ladder, and Büthe's bound on `θ` up to `10¹⁹`;
* 8 numerical results of [B]:
  * three of them (`fsq_le`, `H2_le` and our corrected (5.36)) are re-checked rigorously by our
    scripts;
  * four ((B.6), (B.11), (9.94), and (5.31) on its computed range) are re-checked by float
    computations;
  * the rest rests on [B]: Prop 12.2.4, which uses Ramaré's explicit estimate, and the analytic
    ranges of (5.31) and (B.6).

So this is a Lean proof of the ternary Goldbach conjecture, following Helfgott, relative to these
axioms.

Every axiom has been checked against its source or script ([`AXIOMS.md`](AXIOMS.md)).

## Checking it

```
lake exe cache get
lake build
echo 'import TernaryGoldbach
#print axioms TernaryGoldbach.ternary_goldbach' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

```
'TernaryGoldbach.ternary_goldbach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 TernaryGoldbach.Explicit.rh_upto,
 TernaryGoldbach.Helfgott.binary_goldbach_input,
 TernaryGoldbach.Helfgott.prime_ladder_input,
 TernaryGoldbach.MajorArcs.integral_etaPlus_sq_log,
 TernaryGoldbach.MajorArcs.platt_even,
 TernaryGoldbach.MajorArcs.platt_odd,
 TernaryGoldbach.MajorArcs.sum_odd_mu_sq_div_totient,
 TernaryGoldbach.MinorArcs.H2_le,
 TernaryGoldbach.MinorArcs.T2_le,
 TernaryGoldbach.MinorArcs.eta2_fourier_bound',
 TernaryGoldbach.MinorArcs.eta2log_fourier_bound,
 TernaryGoldbach.MinorArcs.integral_H2_le,
 TernaryGoldbach.MinorArcs.prop_12_2_4,
 TernaryGoldbach.Prelim.C_grid,
 TernaryGoldbach.Prelim.K_blocks,
 TernaryGoldbach.Prelim.K_pieces,
 TernaryGoldbach.Prelim.buthe_theta,
 TernaryGoldbach.Prelim.fsq_le,
 TernaryGoldbach.Prelim.liouville_small,
 TernaryGoldbach.Prelim.logsq_small,
 TernaryGoldbach.Prelim.mertens_lower_small,
 TernaryGoldbach.Prelim.mertens_point,
 TernaryGoldbach.Prelim.mertens_product_small,
 TernaryGoldbach.Prelim.mertens_small,
 TernaryGoldbach.Prelim.moebius_sqrt_small,
 TernaryGoldbach.Prelim.nonprime_small,
 TernaryGoldbach.Prelim.psi_mid,
 TernaryGoldbach.Prelim.psi_mul_mid,
 TernaryGoldbach.Prelim.psi_small,
 TernaryGoldbach.Prelim.psi_sqrt,
 TernaryGoldbach.Prelim.theta_cube_small,
 TernaryGoldbach.Prelim.theta_sqrt,
 TernaryGoldbach.Prelim.MV.GS_N0,
 TernaryGoldbach.Prelim.MV.lemma7_numeric,
 TernaryGoldbach.Prelim.MV.lemma8_numeric,
 TernaryGoldbach.Prelim.MV.prod_ap_le]
```

Beyond these axioms, the trust base is the Lean kernel and Mathlib. The development uses no
`native_decide`. The primality certificates in `PrattPrime.lean` are evaluated by the kernel.

## How the proof is organized

The top level is [B, §14.4] (`Helfgott/Main.lean`).

* **Small cases.** Odd `5 < n ≤ 8.875694·10³⁰` (`Reduction.lean`, `PrattPrime.lean`):
  * binary Goldbach up to `4·10¹⁸` [OeSHP14];
  * the Helfgott–Platt ladder of primes with gaps `≤ 4·10¹⁸` [HP13];
  * the decomposition `4·10¹⁸ + 2 = 2000000000000001301 + 1999999999999998701` [B, §1.6], with
    both primes proved prime in Lean.
* **Large cases.** Odd `n ≥ 10²⁷`, by the circle method with Helfgott's smoothings `η₊` and `η_*`
  (`CircleMethod.lean`, `Helfgott/`):
  * **major arcs**, [B, (14.27)] with constant `1.049` (`MajorArcs/MajorTotal.lean`). This needs:
    * the explicit formulas for Dirichlet `L`-functions, [B, Props 9.3.2, 9.4.2, 9.5.1], proved in
      `Explicit/` with weaker constants (zeros are counted by Jensen's formula in windows);
    * Platt's GRH verification;
    * [B, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5];
    * the `ℓ²` norm over the major arcs, [B, (14.7)] (`8.6296x … 8.79x`);
    * the singular series and the Chapter 10–11 main term;
  * **minor arcs**, [B, (14.49)] with constant `1.0376` (`MinorArcs/MinorTotal.lean`). This needs:
    * Vaughan's identity and the Type I and Type II sums of [B, Chs. 3–6], which give Theorem 3.1.1
      with constants `0.8764` and `3.8x^{5/6}`;
    * the large sieve for primes (Prop 12.1.2 proved; Prop 12.2.4 an axiom);
    * Ch. 11 and a repaired Theorem 13.2.1;
    * [B, (14.28)] in a weaker form;
  * **non-prime terms**, [B, (14.51)], with cruder constants;
  * **final inequality**: `(1.049 − 1.0376) x²/κ = 0.0114 x²/κ > 0` beats the error terms
    (`Helfgott/Numerics.lean`).
* **Inputs from [B, §2]** (`Prelim/`):
  * bounds on `ψ`, `θ`, and sums of `Λ` and `μ`;
  * Mertens products ([B, Lemma C.2.2]);
  * the large sieves of [MV73];
  * (2.22) with constant `2.8`, by Ramaré's Liouville route;
  * (2.23) in the form `q/φ(q) + 2.67`.
* **Explicit prime number theorem** (`Explicit/`, `Prelim/ThetaExplicit.lean`):
  `|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 89 967 803`. Here `ε_pl(n) = 2.2·10⁻¹¹` for
  `3400 < log n < 20000` and `0` otherwise. It replaces Dusart's bound, which [B] uses. It comes from:
  * a finite check up to `10¹⁰`;
  * Büthe's bound up to `10¹⁹`;
  * above `10¹⁹`, a Gaussian-smoothed explicit formula for `ψ`, with RH up to `3·10¹²` and the
    zero-free region `β ≤ 1 − 1/(11 log|γ|)` for `|γ| ≥ 10⁹`. The zero-free region is proved with
    partial fractions for `ξ'/ξ` and Stechkin's lemma.

[`BLUEPRINT.md`](BLUEPRINT.md) maps [B] chapter by chapter to the Lean files.

## Differences from [B]

**Constants.** Ours are weaker where our proofs or corrections require it:

| [B] | Statement | [B]'s constant | ours |
|---|---|---|---|
| Thm 3.1.1 | minor-arc pointwise bound (first case) | `0.5`, `3.36 x^{5/6}` | `0.8764`, `3.8 x^{5/6}` |
| (14.49) | minor-arc total | `1.00948 x²/κ` | `1.0376 x²/κ` |
| (14.27) | major-arc total | `1.058259 x²/κ` | `1.049 x²/κ` |
| (14.28) | `E` in the minor-arc total | `8.4029·10⁻¹²` | `8·10⁻¹¹` |
| (14.51) | non-prime terms | `7.3306` | `6.7·10⁶` |
| (2.22) | `∑_{n≤x,(n,q)=1} μ(n)/n` | `4/5` | `2.8` |
| (2.23) | `∑ μ(n)/n log(x/n)` | `1.00303 q/φ(q)` | `q/φ(q) + 2.67` |
| Props 9.3.2, 9.4.2, 9.5.1 | explicit formulas | — | weaker (Jensen windows) |
| Prop 12.1.2 | large sieve for primes | `δ₀ ≥ 1` | `δ₀ ≥ 2` (the proof uses `δ₀ = 8`) |

The final margin is `0.0114 x²/κ`, against [B]'s `0.04877 x²/κ`.

**Errors in [B] and how the proof handles them** (details in `NOTES.md`):

* (6.77) has an arithmetic slip. [B]'s own argument gives the first-case constant `0.8102` in Thm
  3.1.1, not `0.5`. With the corrected (5.36) below, ours is `0.8764`.
* The proof of Thm 13.2.1 mixes two scales of major arcs. Its `ℓ∞` input is derived off the arcs at
  scale `x/κ`, but its `ℓ²` input and (14.27) use scale `x`.
  * Repaired as follows: the scale-`x/κ` arcs are used above the base level, the Dirichlet
    approximation is redone at each scale, the levels are extended to `≈ x^{0.3}`, and the base gap
    is bounded with Cor 7.1.3.
  * Numerically this gives `≤ 0.965 x²/κ` (with `0.8764`); we state `1.0376`.
* The proof of Prop 11.2.3 does not rescale `δ` to `wδ`. The statement still holds, with about 11% to
  spare (`scripts/prop_11_2_3_check.py`).
* (4.40) states the main term of the all-`n` version. The corrected statement has `x/2q`,
  `η̂(−δ/2)` and `(m, 2q) = 1`. (4.50)–(4.52) (Lemma 4.2.4) are also corrected; see NOTES.
* The proof of Lemma 4.1.3 has a gap. The lemma is proved by a sharper argument.
* In Lemma 9.1.3, `N⁺ = N/2` holds only for real `χ`. The proof sums over `χ` and `χ̄`.
* (14.7) has an arithmetic slip (`0.0754`); our error analysis avoids it.
* (5.32) is false for `v = 2`, and so is (5.36), which depends on it: `∫₁⁴ T₂(S)/S dS = 0.53344 >
  0.37273 log 4` (`AXIOMS.md`, Finding 1).
  * We use (5.36) with `+0.0231`, checked by `scripts/h2_integral_check.py`.
  * This adds `0.0924` to the Type II factor and raises the first-case constant of Thm 3.1.1 to
    `0.8764`.
  * (14.49) stays `1.0376`, because repair 3 below has room.
* The prime ladder's gaps are at most `4·10¹⁸`, as [HP13] and [B, §1.6] state. The case
  `n − p = 4·10¹⁸ + 2` uses [B]'s explicit decomposition.

**Other differences:**
* Dusart's bound is replaced by `theta_explicit`, above.
* Helfgott works on `ℝ/ℤ`; here it is `(0, 1]`, with the major arcs lifted periodically to `ℝ`.

## Layout

| Path | Content |
|---|---|
| `Statement.lean`, `Reduction.lean`, `PrattPrime.lean` | the statement; small cases from binary Goldbach and a prime ladder; primality certificates |
| `CircleMethod.lean` | the finite circle method and the circle identity for absolutely summable series |
| `Helfgott/` | Helfgott's smoothings and major arcs (`Defs`), sup norms and decay, the non-prime terms, the top-level inputs (`Inputs`) and the assembly (`Main`) |
| `MinorArcs/` | [B, Chs. 3–6, 11–13] and §14.3: Vaughan's identity, Type I and II sums, Thm 3.1.1, the large sieve for primes, the minor-arc total; generated numerics (`scripts/gen_*.py`) |
| `MajorArcs/` | [B, Chs. 7, 9–11] and §14.1–14.2: GRH input, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5, (14.7), the singular series, the major-arc total |
| `Explicit/` | explicit formulas for `L(s, χ)` and `ζ`; growth, Jensen and Landau bounds; the zero-free region; the explicit prime number theorem for `ψ` |
| `Prelim/` | [B, §2]: `ψ`, `θ`, Mertens products, sums of `μ` and Liouville's function; the large sieves of [MV73]; Hilbert inequalities; Plancherel; Gauss sums |
| `scripts/` | the computations behind the numerical axioms; generators of numeric Lean files; exploratory checks |
| `AXIOMS.md` | the axiom audit |
| `BLUEPRINT.md`, `NOTES.md` | map from [B] to Lean; working notes |

## References

* [B] H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015). This is the book
  version, superseding arXiv:1205.5252, 1305.2897 and 1312.7748 [H].
* [HP13] H. A. Helfgott, D. J. Platt, *Numerical verification of the ternary Goldbach conjecture up
  to 8.875·10³⁰*, arXiv:1305.3062.
* [OeSHP14] T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the even Goldbach
  conjecture and computation of prime gaps up to 4·10¹⁸*, Math. Comp. 83 (2014).
* [Pla] D. J. Platt, *Numerical computations concerning the GRH*, arXiv:1305.3087.
* [PT21] D. Platt, T. Trudgian, *The Riemann hypothesis is true up to 3·10¹²*, Bull. LMS 53 (2021),
  arXiv:2004.09765.
* [Bü18] J. Büthe, *An analytic method for bounding ψ(x)*, Math. Comp. 87 (2018), arXiv:1511.02032.
* [Dus18] P. Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. 45 (2018).
* [RS62] J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962).
* [MV73] H. L. Montgomery, R. C. Vaughan, *The large sieve*, Mathematika 20 (1973).
* O. Ramaré, Acta Arith. 165 (2014) (Liouville route to (2.22)); hal-02572851 (the `q = 1` Möbius
  bound).
* `Prelim/PNTMertens.lean` is ported from the PrimeNumberTheoremAnd project (Apache 2.0; see
  `licenses/`).

Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.
