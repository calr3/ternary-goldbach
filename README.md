# Ternary Goldbach in Lean 4

A formalization of Helfgott's proof of the ternary Goldbach conjecture in Lean 4 and Mathlib. The
conjecture says that every odd integer greater than 5 is a sum of three primes:
`TernaryGoldbach.ternary_goldbach : Statement` (see `TernaryGoldbach/Statement.lean`). The proof
follows H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 [H].

## Status

The proof is complete: there is no `sorry`, and the main theorems use only Lean's standard three
axioms. They take 2 published numerical results as explicit hypotheses, stated in
`TernaryGoldbach/Statement.lean`:

* `PlattGRH`: Platt's GRH verification (at `q = 1`, RH up to `10⁸`);
* `BinaryGoldbachInput`: binary Goldbach up to `4·10¹⁸`.

```lean
theorem TernaryGoldbach.ternary_goldbach_of_hypotheses (hGRH : PlattGRH)
    (hBG : BinaryGoldbachInput) : Statement
theorem TernaryGoldbach.ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) :
    TernaryGoldbachFrom (10 ^ 27)
```

(`TernaryGoldbach/MainTheorems.lean`). The large case `n ≥ 10²⁷` does not need binary Goldbach.
Inside the development, the hypotheses are `Fact` instances, restated as the theorems
`MajorArcs.platt_verification` and `Helfgott.binary_goldbach_input`; `RamareMoebius` is also passed
as a `Fact` instance, which `Prelim/RamareMoebius.lean` provides from `Fact PlattGRH`. Each theorem takes only the instances its proof uses (the
`unusedSectionVars` linter checks this), so its statement shows what it depends on:

| Stage of [H, §14.4] | Lean | Hypotheses |
|---|---|---|
| major arcs, (14.27) | `Helfgott.major_arcs_input` | `PlattGRH` |
| minor arcs, (14.49) | `Helfgott.minor_arcs_input` | `PlattGRH` (and `RamareMoebius`, proved from it) |
| non-prime terms, (14.51) | `Helfgott.nonprime_input` | none |
| circle identity (14.50); final inequality | `Helfgott.circle_identity_input`; `Helfgott.final_inequality_crude` | none |
| odd `n < 10²⁷` | `Helfgott.ternaryGoldbachUpTo_1e27` | `BinaryGoldbachInput` |

Ramaré's bound `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815` ([H, (2.21)], `RamareMoebius`) is
**proved**, from `PlattGRH`: `Prelim.ramareMoebius_of_plattGRH`. The proof is Helfgott's
formalization of his note `mobius003.tex`, which follows Ramaré's recursive idea (Garald1/RSBounds,
vendored unchanged under `vendor/rsbounds/`; see "Helfgott's RSBounds" below). So are [H, (2.14)] and
(2.17) with [H]'s constants `1.0004` and `1.0008` (`Prelim/PsiHelfgott.lean`).

The bounds for `ψ`, `θ` and Mertens' product (Lemma C.2.2) that replace [H]'s citations of
[RS62], [RS75] and [RR96] (`Prelim.theta_explicit`, `Prelim.psi_two_sided`) use RH up to `10⁸`,
which `PlattGRH` gives at `q = 1` (`Explicit.rh_upto_1e8`).

Ramaré's asymptotic for `∑_{r≤R, (r,d)=1} μ²(r)/φ(r)` ([H, (12.12)], [Ram95, Lemma 3.4]) is proved,
including the value of `c_E` (`Prelim/Ramare.lean`). One step of [Ram95]'s proof, (3.9), is false;
our proof avoids it (`HYPOTHESES.md`, Finding 5).

### Helfgott's RSBounds

`vendor/rsbounds/` holds the part of H. A. Helfgott's RSBounds development (Garald1/RSBounds, with
Claude; MIT, with Apache 2.0 file headers) that this proof uses: 2429 modules, copied unchanged from commit `0393b52`.
`vendor/rsbounds/source-provenance.json` records the source path, Git blob and SHA-256 of every
file; `python3 vendor/rsbounds/check_source_provenance.py` checks them. RSBounds was itself built
against this repository at `192ca57`, whose modules it imports. It provides:
* `RSBounds.Moebius003.ramareMoebius_of_finiteRH`: [H, (2.21)], Ramaré's `0.03/log x` for
  `x ≥ 11815`, from RH up to `1894438.5122` (the formalization of `mobius003.tex`). Its inputs are
  Schoenfeld's (5.6b*) (1976), PsiCert, and kernel-checked bounds for sums of `μ` (`MoebiusCert`)
  and of `Λ`;
* PsiCert (`PsiFinite.psi_abs_sub_le_four_fifths_sqrt`): `|ψ(x) − x| ≤ 0.8√x` on `[1500, 10¹⁰]`,
  a kernel-checked sieve campaign;
* Rosser–Schoenfeld (1975), `|ψ(x) − x| < 0.00020211 x` for `x ≥ e²³` from RH up to
  `1894438.5122`, with the first 29 zeros located by kernel-checked certificates (`vendor/rsbounds/rh100/`,
  from `teal-sea/zeta-lab`);
* `RSBounds.HelfgottPsiBoundsFinal`: [H, (2.14)] and (2.17) with `1.0004` and `1.0008`.

RH up to `1894438.5122` follows from `PlattGRH` at `q = 1`
(`RSBounds.Moebius003.finiteRH_of_plattGRH`), so nothing is added to the hypotheses.

So this is a Lean proof of the ternary Goldbach conjecture, following Helfgott, relative to these
hypotheses.

No full `lake build` of the current version has been recorded.

Every hypothesis has been checked against its source ([`HYPOTHESES.md`](HYPOTHESES.md)). The project's
metadata are in [`formalization.yaml`](formalization.yaml).

## Checking it

```
lake exe cache get
lake build
echo 'import TernaryGoldbach
#print axioms TernaryGoldbach.ternary_goldbach_of_hypotheses' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

```
'TernaryGoldbach.ternary_goldbach_of_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The theorems can also be checked with [Comparator](https://github.com/leanprover/comparator)
against `Challenge.lean`, which states them with Mathlib-only definitions (see
[`comparator/README.md`](comparator/README.md)). **The current version has not been through
Comparator yet.** The only recorded run is from 2026-11-06, at commit `83ac1e1`, when the main
theorems took four hypotheses (`RHUpTo`, `PlattGRH`, `BinaryGoldbachInput`, `RamareMoebius`).
Comparator accepted both theorems then. The two-hypothesis statements have not been checked with
it.

Beyond these hypotheses, the trust base is the Lean kernel and Mathlib. The development uses no
`native_decide`. The kernel itself evaluates the finite computations of the proof:
* the tables `|ψ(t) − t| ≤ √t`, `t − 2.3662√t ≤ θ(t) ≤ t` on `[12, 10⁶)` (trial division,
  `Prelim/SmallPsiTable*.lean`) and `t − 5√t ≤ θ(t) ≤ t + 3√t` on `[10⁶, 5·10⁷)` (a bit sieve,
  `Prelim/PsiSieve*.lean`);
* the small-range checks in `Prelim/SmallPsi.lean`, `SmallPsi700.lean`, `SmallMertens.lean`,
  `SmallProdAp.lean`, `SmallFsq.lean`, `SmallG.lean`, `SmallNonprime.lean`, `SmallLiouville.lean`,
  `SmallW.lean`, `SmallMuPhi.lean`, `SmallMertensLower.lean`, `SmallCGrid.lean`, `SmallMoebius.lean`
  and `SmallMertensProd.lean`;
* the products and sums behind Ramaré's (12.12) and `c_E` in `Prelim/RamareBound.lean` and
  `RamareWalk.lean`;
* the piecewise form of `T₂` and the bounds on `H₂` in `MinorArcs/H2Bound.lean`;
* `g₂(n)` for `n ≤ 10⁴` and `T₂ ≤ 0.37273` on `[16, 10⁴)` in `MinorArcs/SmallG2.lean`, and the sums
  behind the tail of `∫ |g₂|/y` in `MinorArcs/G2TailNum.lean`;
* the bisection grids behind `|η̂₂''|_∞ ≤ 32` ([H, Lemma B.1.2]) in `MinorArcs/Eta2DDBound.lean`;
* the Riemann sums of the Weil-window bound (`Explicit/WeilNumC.lean`) and the constants of the
  `ψ` ranges (`Explicit/PsiRanges1e8.lean`);
* the reduction of [H, Prop 12.2.4] to the divisors of `30030` (`MinorArcs/LSQuot8g.lean`);
* the prime ladder up to `10²⁷`: `2.5·10⁸` Proth primes (`Ladder/`, below);
* in `vendor/rsbounds/`, Helfgott's checks: PsiCert (`RSBounds/PsiFinite/`, about 1000 modules),
  the Möbius certificates (`MoebiusCert/`), and the zero certificates up to height 100 (`rh100/`).
  None uses `native_decide`.

**The prime ladder.** Rung `i` (`1 ≤ i ≤ 254638308`) is `c = (111616 i − t)·2⁴⁵ + 1` with
`0 ≤ t < 2048`, and its certificate is `3^((c−1)/2) ≡ −1 (mod c)`: every prime factor of `c` is then
`≡ 1 (mod 2⁴⁵)` (Mathlib's `Nat.pow_pow_add_primeFactors_one_lt`), and `c < (2⁴⁵ + 1)²`
(`Ladder/Spec.lean`). The offsets `t` are not in the repository. `ladder_hints%`
(`LadderHints.lean`, compiled to native code with `precompileModules`) finds them during
elaboration, about `1.5·10⁻⁵` s per rung, and packs each chunk of 4096 into one literal. The kernel
then checks the chunk by evaluation (`decide +kernel`). It checks 32 rungs at a time modulo the
product `M` of their candidates: one exponentiation `3^(2⁴⁴·111616·i₀) mod M` per block, then a few
operations on 3000-bit numbers per rung (`Ladder/Check.lean`). This is about `5.5·10⁻⁵` s per rung.
The 128 files `Ladder/Data/L*.lean` (`scripts/gen_ladder.py`) take about 5 hours of one core (about
140 s per file of 486 chunks, 1.7 GB each), of which about 4 hours are kernel checking.

[H, Prop 12.2.4] is proved with `c₊ = 2` in place of [H]'s `1.36`. [H]'s argument covers
`q ≥ 2.2·10¹⁰`; for smaller `q`, [H] needs a computation over all `q < 2.2·10¹⁰`. With `c₊ = 2` there
is room for a structural argument instead: removing a prime `p ≥ 17` from `q` never makes the
required inequality fail (`MinorArcs/LSQuotRed.lean`), so everything reduces to the 64 divisors of
`30030`, checked by the kernel for `4 ≤ n < 2600` (`LSQuot8g.lean`, about 90 s), plus a short
exchange argument for `n ≤ 3` (`LSQuot9.lean`).

(B.6) is proved with the constant `c₀ = 32` in place of [H]'s `31.521` (the true maximum is
`31.52065`, at `t ≈ 17.4`), as Helfgott suggested; (B.11) follows. For `t ≥ 2`, three integrations
by parts give `(2πt)² η̂₂(t) = F(e(−t/4), 1/2πt) + O*(6120/(2πt)³)` with `F` a polynomial, and the
kernel bisects `‖F(z, w)‖ + 6120w³ ≤ 32` over `|z| = 1`, `0 ≤ w ≤ 2/25`. For `t ≤ 2`, it checks
Taylor polynomials of degree `< 50` on a grid (`MinorArcs/Eta2DDExpand.lean`, `Eta2DDTaylor.lean`,
`Eta2DDBound.lean`; about 4 minutes in all).

With `c₀ = 32`, `c₊ = 2` and (2.14), (2.17) with `1.0064`, `1.022` (the constants the Type I
statements carry; their proofs use [H]'s; see below), Theorem 3.1.1 has `2.526 x/√t` for [H]'s
`2.5 x/√t`, and the worst cell of the final minor-arc inequality is `1.00717` (against `1.037`).

(9.94) is proved by Parseval from four elementary integrals (`MajorArcs/EtaPlusSqLog.lean`; the
integrals by exact polynomial integration, `MajorArcs/EtaONum.lean`); [H]'s own derivation of it
drops a factor 2 (`HYPOTHESES.md`, Finding 3). (5.31) `T2_le` is proved from
`g₂(n)`, `n ≤ 10⁴`, computed by the kernel (`T₂` itself for `S < 700`, `T₂(S) ≈ ¼ ∫₁^S g₂(y)/y dy`
above; `MinorArcs/T2Small.lean`), and a mean-square bound `∫_{10⁴}^S |g₂(y)|/y dy ≤ 0.0045`: by
Cauchy–Schwarz it reduces to integrals of `m(⌊t⌋)²/t`, `m(x) = ∑_{n≤x} μ(n)/n`, which come from
`m(n)` for `n < 11815` and Ramaré's bound beyond (`MinorArcs/G2Tail.lean`). [H, Lemma 5.1.2] is
not needed.

## How the proof is organized

The top level is [H, §14.4] (`Helfgott/Main.lean`).

* **Small cases.** Odd `5 < n ≤ 10²⁷` (`Helfgott/SmallCases.lean`):
  * binary Goldbach up to `4·10¹⁸` ([OeSHP14]; they double-checked `3·10¹⁷`);
  * for `n > 4·10¹⁸ + 3`, a prime `p` with `n − 4·10¹⁸ ≤ p ≤ n − 4` from a prime ladder
    (`Ladder/`): for each `1 ≤ i ≤ 254638308`, a Proth prime `(111616 i − t)·2⁴⁵ + 1`, `0 ≤ t < 2048`,
    certified by `3^((c−1)/2) ≡ −1 (mod c)`. Consecutive rungs are less than `4·10¹⁸ − 4` apart. The
    Lean kernel checks all `2.5·10⁸` rungs (see "The prime ladder" below). Then `n − p` is even and
    at most `4·10¹⁸`.
* **Large cases.** Odd `n ≥ 10²⁷`, by the circle method with Helfgott's smoothings `η₊` and `η_*`
  (`CircleMethod.lean`, `Helfgott/`):
  * **major arcs**, [H, (14.27)] with constant `1.049` (`MajorArcs/MajorTotal.lean`). This needs:
    * the explicit formulas for Dirichlet `L`-functions, [H, Props 9.3.2, 9.4.2, 9.5.1], proved in
      `Explicit/` with weaker constants (zeros are counted by Jensen's formula in windows);
    * Platt's GRH verification;
    * [H, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5];
    * the `ℓ²` norm over the major arcs, [H, (14.7)] (`8.6296x … 8.79x`);
    * the singular series and the Chapter 10–11 main term;
  * **minor arcs**, [H, (14.49)] with constant `1.0376` (`MinorArcs/MinorTotal.lean`). This needs:
    * Vaughan's identity and the Type I and Type II sums of [H, Chs. 3–6], which give Theorem 3.1.1
      with constants `0.8764` and `3.8x^{5/6}`;
    * the large sieve for primes (Props 12.1.2 and 12.2.4 proved; 12.2.4 with `c₊ = 2`);
    * Ch. 11 and a repaired Theorem 13.2.1;
    * [H, (14.28)] in a weaker form;
  * **non-prime terms**, [H, (14.51)], with cruder constants;
  * **final inequality**: `(1.049 − 1.0376) x²/κ = 0.0114 x²/κ > 0` beats the error terms
    (`Helfgott/Numerics.lean`).
* **Inputs from [H, §2]** (`Prelim/`):
  * bounds on `ψ`, `θ`, and sums of `Λ` and `μ`;
  * Mertens products ([H, Lemma C.2.2]);
  * the large sieves of [MV73];
  * (2.22) with constant `2.8`, by Ramaré's Liouville route;
  * (2.23) in the form `q/φ(q) + 2.67`.
* **Explicit prime number theorem** (`Explicit/`, `Prelim/ThetaExplicit.lean`):
  `|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 10¹²`. Here `ε_pl(n) = 4.92·10⁻⁷` for
  `120 < log n < 20000` and `0` otherwise. [H] quotes its bounds for `ψ` and `θ` ([H, §2.5]) from
  [RS62], [RS75] and [RR96]. We prove them instead, from this and from bounds `|ψ(x) − x| ≤ c√x` for
  moderate `x`:
  * `c = 1` on `[12, 10⁶)` (kernel, trial division) and `t − 5√t ≤ θ(t) ≤ t + 3√t` on
    `[10⁶, 5·10⁷)` (kernel bit sieve, `Prelim/PsiSieve*.lean`);
  * `c = 31`–`200` on `[10⁶, 10¹⁷]` (`c ≤ 72` up to `10¹⁵`; `Prelim/PsiTwoSided.lean`), from the Weil
    explicit formula with RH up to `10⁸` and a compactly supported test function, with a zero-free
    region `|γ| ≥ 2.39` near the real axis;
  * above `10¹⁷`, a Gaussian-smoothed explicit formula for `ψ`, with RH up to `10⁸` and the
    zero-free region `β ≤ 1 − 1/(11 log|γ|)` for `|γ| ≥ 10⁸`. The zero-free region is proved with
    partial fractions for `ξ'/ξ` and Stechkin's lemma.

  With these alone, (2.14) and (2.17) hold with `1.0064` and `1.022` (for `y ≥ 2.5·10⁷`;
  `Prelim/LambdaMu.lean`), and (2.19) for `y ≥ 2·10⁶`; these are the ranges the minor arcs use.
  [H]'s `1.0004` and `1.0008` are proved by Helfgott (`Prelim/PsiHelfgott.lean`, from RSBounds:
  the kernel-checked PsiCert `|ψ(x) − x| ≤ 0.8√x` on `[1500, 10¹⁰]` and Rosser–Schoenfeld's (1975)
  `|ψ(x) − x| < 0.00020211 x` for `x ≥ e²³` from RH up to `1894438.5122`), and the minor arcs use
  them.

[`BLUEPRINT.md`](BLUEPRINT.md) maps [H] chapter by chapter to the Lean files.

## Differences from [H]

**Constants.** Ours are weaker where our proofs or corrections require it:

| [H] | Statement | [H]'s constant | ours |
|---|---|---|---|
| Lemma B.1.2, (B.6) | `\|η̂₂''\|_∞` | `31.521` | `32` (proved; true value `31.52065`) |
| Prop 12.2.4 | `c₊` in `(log Q₀ + c₊)/(log Q + c_E)` | `1.36` | `2` (proved, no computational hypothesis) |
| Thm 3.1.1 | minor-arc pointwise bound (first case) | `0.5`, `2.5 x/√t`, `3.36 x^{5/6}` | `0.8764`, `2.526 x/√t`, `3.8 x^{5/6}` |
| (2.14), (2.17) | `ψ(y) ≤ c y`, `∑_{n≤y} Λ(n) n < c y²/2` | `1.0004`, `1.0008` | [H]'s, `y ≥ 2.5·10⁷` (Helfgott's proof, RSBounds); the Type I statements carry `1.0064`, `1.022` |
| (14.49) | minor-arc total | `1.00948 x²/κ` | `1.0376 x²/κ` |
| (14.27) | major-arc total | `1.058259 x²/κ` | `1.049 x²/κ` |
| (14.28) | `E` in the minor-arc total | `8.4029·10⁻¹²` | `8·10⁻¹¹` |
| (14.51) | non-prime terms | `7.3306` | `6.7·10⁶` |
| (2.22) | `∑_{n≤x,(n,q)=1} μ(n)/n` | `4/5` | `2.8` |
| (2.23) | `∑ μ(n)/n log(x/n)` | `1.00303 q/φ(q)` | `q/φ(q) + 2.67` |
| Props 9.3.2, 9.4.2, 9.5.1 | explicit formulas | — | weaker (Jensen windows) |
| Prop 12.1.2 | large sieve for primes | `δ₀ ≥ 1` | `δ₀ ≥ 2` (the proof uses `δ₀ = 8`) |

The final margin is `0.0114 x²/κ`, against [H]'s `0.04877 x²/κ`.

**Errors in [H] and how the proof handles them** (details in `NOTES.md`):

* (6.77) has an arithmetic slip. [H]'s own argument gives the first-case constant `0.8102` in Thm
  3.1.1, not `0.5`. With the corrected (5.36) below, ours is `0.8764`.
* The proof of Thm 13.2.1 mixes two scales of major arcs. Its `ℓ∞` input is derived off the arcs at
  scale `x/κ`, but its `ℓ²` input and (14.27) use scale `x`.
  * Repaired as follows: the scale-`x/κ` arcs are used above the base level, the Dirichlet
    approximation is redone at each scale, the levels are extended to `≈ x^{0.3}`, and the base gap
    is bounded with Cor 7.1.3.
  * Numerically the repaired bound is at most `1.00717 · x²/κ` before the split `S_{η₊} = S₁ + S₂`
    (worst generated cell, against `1.037`); we state (14.49) with `1.0376`.
* The proof of Prop 11.2.3 does not rescale `δ` to `wδ`. This erratum is Helfgott's own: he found
  it around 2016 and reported it to the publisher. A float check suggests the statement still holds,
  with about 11% to spare (`scripts/prop_11_2_3_check.py`), but we do not use it. We use a variant,
  Prop 11.2.3′ (`MinorArcs/Prop1123b.lean`). It is stated off the major arcs at scale `y = x/κ`, and it
  takes a fresh Dirichlet approximation at each scale `wy` in (11.9). The majorant is crude:
  `g_{wy}(min(1, w) n) ≤ max(1, 1/w) g_y(n)`. That costs a factor `∫ max(1, 1/w) φ ≤ 1.398` in `ℓ∞`,
  which repair 3 of Thm 13.2.1 (levels up to `x^{0.3}`) absorbs. So it is a quick repair rather than a
  clean one.
* (4.40) states the main term of the all-`n` version. The corrected statement has `x/2q`,
  `η̂(−δ/2)` and `(m, 2q) = 1`. (4.50)–(4.52) (Lemma 4.2.4) are also corrected; see NOTES.
* The proof of Lemma 4.1.3 has a gap. The lemma is proved by a sharper argument.
* In Lemma 9.1.3, `N⁺ = N/2` holds only for real `χ`. The proof sums over `χ` and `χ̄`.
* (14.7) has an arithmetic slip (`0.0754`); our error analysis avoids it.
* (5.32) is false for `v = 2`, and so is (5.36), which depends on it: `∫₁⁴ T₂(S)/S dS = 0.53344 >
  0.37273 log 4` (`HYPOTHESES.md`, Finding 1).
  * We use (5.36) with `+0.0231`. This form, and (5.37), are proved in Lean
    (`MinorArcs/H2Bound.lean`).
  * This adds `0.0924` to the Type II factor and raises the first-case constant of Thm 3.1.1 to
    `0.8764`.
  * (14.49) holds with `1.0376` all the same, because repair 3 (above) has room.
* The proof of Prop 12.2.4 applies Lemma 12.2.3, whose bound has `log Q + 1.312` in the denominator,
  where (12.23) needs `log Q + c_E`. Our proof bounds the quotient against `log Q + c_E` directly
  (`HYPOTHESES.md`, Finding 4).
* [H, (12.12)] is [Ram95, Lemma 3.4]. Its proof there uses (3.9),
  `∏_p (1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≤ 8`, but the product is about `8.0845`. We prove (12.12)
  as stated by a different decomposition, which gives the constant `7.04 ≤ 7.284` (`HYPOTHESES.md`,
  Finding 5).

**Other differences:**
* [H, §2.5] quotes its bounds for `ψ`, `θ` and `Λ` from [RS62], [RS75] and [RR96]; we prove them
  (`Prelim/LambdaMu.lean`, `ThetaExplicit.lean`) from the `c√x` bounds and `theta_explicit`, above.
* The small cases follow [H, §1.6] with a ladder of our own up to `10²⁷`, checked in Lean, in place
  of the Helfgott–Platt ladder [HP13] (up to `8.875·10³⁰`, a cited computation in [H]).
* Platt's verification reaches the minor-arc total through (14.7) and Prop 7.1.5, as in [H], and also
  through Cor 7.1.3, which bounds the base gap in the repaired Thm 13.2.1
  (`MinorArcs.norm_S_etaStar_le_gap`).
* Helfgott works on `ℝ/ℤ`; here it is `(0, 1]`, with the major arcs lifted periodically to `ℝ`.

## Layout

| Path | Content |
|---|---|
| `Statement.lean` | the statement and the hypotheses |
| `MainTheorems.lean` | the main theorems, with explicit hypotheses |
| `CircleMethod.lean` | the finite circle method and the circle identity for absolutely summable series |
| `Helfgott/` | Helfgott's smoothings and major arcs (`Defs`), sup norms and decay, the non-prime terms, the top-level inputs (`Inputs`), the small cases (`SmallCases`) and the assembly (`Main`) |
| `Ladder/` | the prime ladder up to `10²⁷`: the kernel check (`Check`), its correctness and Proth's criterion (`Spec`), the generated chunk files (`Data/`), `ladder_prime` (`Main`) |
| `LadderHints.lean` | the search for the ladder hints, run during elaboration (compiled to native code) |
| `MinorArcs/` | [H, Chs. 3–6, 11–13] and §14.3: Vaughan's identity, Type I and II sums, Thm 3.1.1, the large sieve for primes, the minor-arc total; generated numerics (`scripts/gen_*.py`) |
| `MajorArcs/` | [H, Chs. 7, 9–11] and §14.1–14.2: GRH input, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5, (14.7), the singular series, the major-arc total |
| `Explicit/` | explicit formulas for `L(s, χ)` and `ζ`; growth, Jensen and Landau bounds; the zero-free region; the explicit prime number theorem for `ψ` |
| `Prelim/` | [H, §2]: `ψ`, `θ`, Mertens products, sums of `μ` and Liouville's function; the large sieves of [MV73]; Hilbert inequalities; Plancherel; Gauss sums |
| `vendor/rsbounds/` | Helfgott's RSBounds (Garald1/RSBounds), vendored unchanged: (2.21), (2.14), (2.17), PsiCert, Rosser–Schoenfeld (1975) |
| `scripts/` | generators of the numeric Lean files (`gen_*.py`); independent float and interval-arithmetic checks of numerical claims of [H] and of quantities in the proof (`scripts/rigorous/`); models behind the errata |
| `Challenge.lean`, `Solution.lean`, `comparator/` | the Comparator check of the main theorems |
| `HYPOTHESES.md` | the hypotheses, checked against their sources; errors found in the sources |
| `BLUEPRINT.md`, `NOTES.md` | map from [H] to Lean; working notes |

## References

* [H] H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015). This is the book
  version, superseding arXiv:1205.5252, 1305.2897 and 1312.7748.
* [HP13] H. A. Helfgott, D. J. Platt, *Numerical verification of the ternary Goldbach conjecture up
  to 8.875·10³⁰*, arXiv:1305.3062.
* [OeSHP14] T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the even Goldbach
  conjecture and computation of prime gaps up to 4·10¹⁸*, Math. Comp. 83 (2014).
* [Pla] D. J. Platt, *Numerical computations concerning the GRH*, arXiv:1305.3087.
* [RS62] J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962).
* [RS75] J. B. Rosser, L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x)*,
  Math. Comp. 29 (1975), 243–269.
* [RR96] O. Ramaré, R. Rumely, *Primes in arithmetic progressions*, Math. Comp. 65 (1996), 397–425.
* [MV73] H. L. Montgomery, R. C. Vaughan, *The large sieve*, Mathematika 20 (1973).
* [Ram95] O. Ramaré, *On Šnirel'man's constant*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 22
  (1995), 645–706.
* O. Ramaré, Acta Arith. 157 (2013), Cor. 1.4 (the `q = 1` Möbius bound, [H, (2.21)]); Acta Arith.
  165 (2014) and hal-02572851 (Liouville route to (2.22)).
* [Hm] H. A. Helfgott (with Claude), `mobius003.tex`, a proof of `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x`
  for `x ≥ 11815` along Ramaré's recursive idea, shared on the Lean Zulip; formalized in
  Garald1/RSBounds (`RSBounds/Moebius003/`).
* H. A. Helfgott, RSBounds, https://github.com/Garald1/RSBounds (commit `0393b52`), vendored in
  `vendor/rsbounds/` (MIT, with Apache 2.0 file headers; it contains code from PrimeNumberTheoremAnd, IEANTN and
  teal-sea/zeta-lab, whose licenses are in `vendor/rsbounds/licenses/` and `vendor/rsbounds/rh100/`).
* `Prelim/PNTMertens.lean` is ported from the PrimeNumberTheoremAnd project (Apache 2.0).

Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.

License: Apache 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
