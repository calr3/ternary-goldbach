# Axiom audit

`ternary_goldbach` depends on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on the 22 axioms below (`#print axioms`). A false axiom makes the axiom set
inconsistent, and then the formal proof says nothing. So each axiom has been checked against its
source:

* For our own computations, against the script: its range, edge cases, the precise Lean
  definitions involved, rounding, and the margin.
* For published results, against the paper.

All scripts were re-run. The audit was done on 2026-11-01. Sources: [B] = Helfgott, *The ternary
Goldbach problem*, arXiv:1501.05438v2. The papers below are cited by arXiv number. [RS62] and [MV73] are
as in the README.

## Findings

1. **[B, (5.36)] is false as stated. Fixed: we use, and now prove, a corrected form (`integral_H2_le`).**
   * The book's (5.36) inherits an error in [B, (5.32)] for `v = 2`.
   * Our `T2` is exactly the sum in [B, (5.19)]. Its values agree with [B]'s stated
     `G₂(S) = 1 − 1/S` on `[1, 2)`, and `T₂(S) = 1/2` exactly on `[2, 3)`.
   * Exactly, `∫₁⁴ T₂(S) dS/S = (log 2 − 1/2) + ½ log(3/2) + ⅓ log(4/3) + 1/24 = 0.53344`. This is
     more than `0.37273 log 4 = 0.51671`, and (5.32) claims the bound for `G₂ ≥ T₂`.
   * Hence `∫₁⁴ H₂(S)/S dS = 0.21619 > 0.15107 log 4 = 0.20943`.
   * `integral_H2_le` states `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T + 0.0231` for all `T ≥ 1`. The
     supremum of the excess is `0.023059`. Because `H₂ = 0.15107` for `S ≥ 16`, the excess is
     constant from `T = 16` on. It is now a theorem (`MinorArcs/H2Bound.lean`; see "Removed
     axioms"); `scripts/h2_integral_check.py` is an independent check in interval arithmetic.
   * Propagation:
     * The Type II totals (`typeII_637`, `typeII_640`, `typeII_gen`, `typeII_split_gen`) have
       `0.60428 Λ₀ + 0.0924 + 8ζ³√(x/V)/U` in place of `0.60428 Λ₀ + 8ζ³√(x/V)/U`.
     * In the first case of Thm 3.1.1 the factor is `≤ 0.30214 log t + 0.7468`; our bound
       `≤ 0.2355` on the `ζ³` term leaves room for most of the `0.0924`. The constant
       `log 2/(2√ρ) + (√ρ/2)·0.7468 + 0.000076 = 0.87639` replaces `0.8103`; Thm 3.1.1 is now stated
       with `0.8764`.
     * In the second case, `B₀ᵃ` and `B₀ᵇ` gain `+0.0231`. The generated piece inequalities still
       hold: the worst pieces are `1.3991` and `1.2789`, against `1.413`.
     * The minor-arc cells were regenerated (`scripts/gen_cells.py`); the worst cell is `0.965`.
     * So (14.49) is still `1.0376` and the final margin is still `0.0114 x²/κ`.
2. **`prime_ladder_input` was stronger than its sources. Fixed.**
   * It stated gaps `≤ 4·10¹⁸ − 4`. [HP13, §4] says "no gap between primes exceeded `4·10¹⁸`", and
     [B, §1.6] says "at most `4·10¹⁸`".
   * It is now stated with gaps `≤ 4·10¹⁸`. That leaves `n − p ≤ 4·10¹⁸ + 2`, and the extra case is
     [B]'s decomposition `4·10¹⁸ + 2 = 2000000000000001301 + 1999999999999998701`.
   * Both primes are proved prime in Lean (`PrattPrime.lean`), by Lucas's test with Pratt
     certificates. The kernel evaluates the certificates; there is no `native_decide`, and the proof
     uses only the standard axioms.
3. **Citations (fixed).**
   * `eta2_fourier_bound'` is [B, Lemma B.1.2, (B.6)] in arXiv v2. Its docstring used to say
     "Lemma B.2.3", which is the source of `eta2log_fourier_bound`.
   * `rh_upto` also covers `γ ≤ 0`, which is not part of the cited computation; the docstring now
     says so:
     * `γ < 0` follows by `ζ(s̄) = conj ζ(s)`;
     * `γ = 0` holds because `ζ(σ) < 0` on `(0, 1)`, a classical fact.
4. **[B] is inconsistent about Platt's range.** [B, §1.6] says odd conductors up to `2·10⁵`; [B, §9.6]
   says `3·10⁵`. Platt's paper covers all `q ≤ 4·10⁵`, so `platt_odd` is covered either way.
5. **[B]'s derivation of (9.94) drops a factor 2. Fixed: (9.94) is now a theorem, with [B]'s constants.**
   * `integral_etaPlus_sq_log` rests on [B]'s rigorous integration of `η◦` and also on the bounds
     (A.23), (A.24) on `η₊ − η◦`.
   * [B, p. 197] writes `∫η₊² log xt = ∫η◦² log xt + 2∫(η₊ − η◦)η◦ log xt + ∫(η₊ − η◦)² log xt`,
     and bounds `|∫(η₊ − η◦)η◦ log xt| ≤ 1.944·10⁻⁶ log x + 5.2·10⁻⁷`. It then concludes (9.94)
     with `O*(1.95·10⁻⁶) log x` and `O*(5.3·10⁻⁷)`, without the factor 2 of the cross term. With
     it, the same argument gives about `3.9·10⁻⁶ log x + 1.27·10⁻⁶`.
   * The stated constants are still probably true: a direct float computation of `η₊`
     (`scripts/eta_plus_check.py`) puts both integrals within `2.6·10⁻⁹` and `2.2·10⁻⁷` of the
     centres, because the actual `‖η₊ − η◦‖₂ ≈ 6.2·10⁻⁷` is well below (A.23)'s `2.43·10⁻⁶`. But
     [B]'s argument does not prove them.
   * `integral_etaPlus_sq_log` is now proved (`MajorArcs/EtaPlusSqLog.lean`) with the stated
     constants. The proof bounds the cross terms by Parseval in `u = log t` instead of Cauchy–Schwarz
     on all of `L²`. It needs only our Lean bound `‖g''‖₂² ≤ 368` and four elementary integrals
     (`etaO_numerics`, see "Removed axioms").
6. **Two slips in [B]'s proof of Prop 12.2.4 (neither affects the result; it is now proved).**
   * Lemma 12.2.3 bounds the quotient by `(log Q₀ + σ)/(log Q + 1.312)`, and the proof of Prop 12.2.4
     uses it with `σ = c₊ = 1.36` for the range (12.29) of small `R`. But (12.23) has
     `log Q + c_E` in the denominator, with `c_E = 1.33258 > 1.312`. So with `σ = c₊` the lemma does not give
     (12.23). Taking `σ ≈ 1.347` would, at a cost of about `0.5 %` in `ϖ(q)`. Our proof (`regionS`) bounds
     the quotient against `log Q + c_E` directly.
   * (12.15) claims `G(R) ≥ log R + 1.312` from (12.12) for `R ≥ 4·10⁷`. But (12.12) gives
     `c_E − 7.284 R^{−1/3} ≥ 1.312` only from `R ≈ 4.42·10⁷` on. We do not use (12.15).
7. **Binary Goldbach was double-checked only to `4·10¹⁷`.** [OeSHP14] verified binary Goldbach up to
   `4·10¹⁸`; according to the project page, the independent double-check reaches `4·10¹⁷`.

## The axioms

### Our own computations (13)

Each of these was first checked by a float script in `scripts/`, then re-checked by an independent
rigorous program in `scripts/rigorous/` (see its README):
* `rig_checks.c` encloses every real quantity in an interval of MPFR numbers, rounding the lower
  end down and the upper end up. MPFR is correctly rounded, including `log`, `exp`, `sqrt` and `γ`.
  Sieves, `φ`, `μ` and `λ` are exact integers.
* `moebius_sqrt_rig.c` uses IEEE double arithmetic in round-down mode only (upper bounds via
  negation).

A check passes only if it holds for the whole interval. All passed on 2026-11-01; the reference
output is `scripts/rigorous/output.txt`. "Also published" lists results in the literature that
contain the axiom.

| Axiom | Statement | Float script | Rigorous re-check: worst case | Also published |
|---|---|---|---|---|
| `Prelim.mertens_lower_small` | `∑_{m≤n} Λ(m)/m ≥ log(n+1) − log(3/√2)`, `3 ≤ n ≤ 10⁶` | `psi_checks.py` | min margin `0.0140806` at `n = 6` | |
| `Prelim.mertens_point` | value at `X = 10⁶` `≥ −1.5776` | `psi_checks.py` | `−1.5772056` | |
| `Prelim.mertens_product_small` | `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`, primes `5 ≤ x ≤ 2·10⁸` | `mertens_product_check.py` | min margin `2.4367·10⁻⁷` at `x = 23`; `≥ 0.13088` above `10⁴` | [RS62, Thm 15, (3.42)] at `n = ∏_{p≤x} p` (`log n = θ(x)`), as cited in [B, (C.19)] |
| `Prelim.K_pieces` | piecewise sum `≤ 0.4035` | `moebius_K_check.py` | `0.4034195` | |
| `Prelim.K_blocks` | block bounds `hblk j`, `1000 ≤ k < 10⁹` | `moebius_K_check.py` | all 20 blocks hold; e.g. block 19: `2.55663·10⁻⁵ ≤ 2.567·10⁻⁵` | |
| `Prelim.moebius_sqrt_small` | `\|∑_{n≤k} μ(n)/n\| ≤ √(2/(k+1))`, `1 ≤ k < 10¹⁰` | `moebius_sqrt_check.py` | equality at `k = 1`; otherwise max ratio `0.612372` at `k = 2` | [B, (2.24)] (Helfgott, interval arithmetic, `x ≤ 10¹²`; Ramaré earlier `x ≤ 10¹⁰`) |
| `Prelim.C_grid` | `(2.8 + (i+1)/100) G(2.8 + i/100) ≤ 2.8`, `i < 7720` | `moebius_C_grid.py` | max `2.742169` at `i = 0` | |
| `MinorArcs.eta2DD_small` | [B, (B.6)] on `0 ≤ t ≤ 655` in explicit form: `‖eta2DD t‖ ≤ 31.521`, `eta2DD t = (2πt)² η̂₂(t)` | — | max `31.52065207` at `t ≈ 17.4148` (`scripts/rigorous/eta2_fourier_rig.py`, Arb ball arithmetic, Si/Ci closed form, Lipschitz stepping: 137334 steps) | [B, Lemma B.1.2] (interval arithmetic, `\|t\| < 655`) |
| `MajorArcs.etaO_numerics` | `∫₀² η◦² ∈ [0.640205997, 0.640205998]`, `∫₀² η◦² log t ∈ [−0.0210947787, −0.0210947786]`, `‖W₀''‖₂² ≤ 36`, `‖W₁''‖₂² ≤ 8.4` (elementary integrals) | — | `0.64020599736635…`, `−0.02109477869887…`, `35.790`, `8.389` (`scripts/rigorous/eta_circ_rig.py`, Arb integration) | first two: [B, p. 197] (VNODE-LP) |
| `MinorArcs.T2_small` | `T₂(S) ≤ 0.37273` for `16 ≤ S < 10⁵` | `t2_check.py` (float, grid) | max `0.3712486` at `S = 16` (`scripts/rigorous/t2_rig.c`, MPFR; exact pieces `α_n + β_n/S`) | [B, (5.31)] (computation) |
| `MinorArcs.T2_mid` | `¼ ∫₁^S g₂(y)/y dy ≤ 0.3607` for `10⁵ ≤ S ≤ 10⁸`; `∫₁^{10⁸} \|g₂\| ≤ 10.5` | — | `0.360582066`; `10.4187` (`t2_rig.c`, `g₂(n)` exactly for every `n ≤ 10⁸`) | `0.360576` is [B]'s main term (5.31) |
| `MinorArcs.prop1224_check` | for `1 ≤ q < 2.2·10¹⁰` and `1 ≤ n < λ(q)`: `n` is in the range of `regionS`, or `checkC q n` ([B, (12.31)] at `R ∈ [n, n+1)`) | `p1224_check.c` (long double) | no failures; `87 972 745` explicit checks for `2 102 258` values of `q`; min margin of `checkC` `0.0236` at `q = 1` (`scripts/rigorous/p1224_rig.c`, interval arithmetic: directed rounding, MPFR tables, rigorous series for `log` and `exp`) | replaces [B]'s computation for Prop 12.2.4 (`q < 3.3·10⁹`, two weeks single-core) |
| `MajorArcs.sum_odd_mu_sq_div_totient` | `6.798779 ≤ ∑_{q≤150000 odd} μ²(q)/φ(q) ≤ 6.79878` | `check_sum_mu2_phi.py` (directed rounding, 40 digits; rigorous) | `6.7987791731…` | |

Cross-checks:
* The rigorous values agree with the float scripts to the digits printed.
* `moebius_sqrt_rig` also checks [B, p. 38]: the stronger bound `|m(x)| ≤ 1/(2√x)` first fails on
  `[7727068587, 7727068588)`. It fails already at `x = 7727068587`: `μ(7727068587) = 1`, so `m` jumps
  there, and `4 m(x)² x ∈ [1.0000156, 1.0000165]`. [B] states that the bound holds for
  `x ≤ 7727068587`. This remark is not used anywhere.
* `rig_checks` gives `Ψ(10⁹) = ∑_{n≤10⁹} Λ(n)/n ∈ [20.146051364519, 20.146051364606]`. So
  `E(10⁹) = Ψ(10⁹) − log 10⁹ ≈ −0.5772144724`, close to `−γ = −0.5772156649` (Mertens).

Unused (in `Prelim/LambdaMuExtra.lean`, not on the path of `ternary_goldbach`):
* `lambda_mul_small` (`k ≤ 2.5·10⁷`): max ratio `1.03583`.
* `lambda_sqrt_small` (`k ≤ 6·10⁶`): max ratio `1.99906`.
* `lambda_sqrt_point` (at `6·10⁶`): value `−3.6619`.

All three come from `psi_extra_check.py`.

### Published results (9)

| Axiom | Statement | Source | Check |
|---|---|---|---|
| `Explicit.rh_upto` | zeros of `ζ` with `0 < ℜρ < 1`, `\|ℑρ\| ≤ 3·10¹²` have `ℜρ = 1/2` | Platt–Trudgian, arXiv:2004.09765 | abstract: "all zeroes `β + iγ` … with `0 < γ ≤ 3·10¹²` have `β = 1/2`"; for `γ ≤ 0` see Finding 3 |
| `MajorArcs.platt_odd` | primitive `χ`, odd conductor `q ≤ 3·10⁵`: GRH up to `10⁸/q` | Platt, arXiv:1305.3087 | abstract: all primitive `χ`, `q ≤ 4·10⁵`; odd `q` to `max(10⁸/q, 3.75·10⁷/q + 200)`; Thm 3.2 counts zeros with `\|ℑs\| ≤ t₀`, `ℜs ∈ (0,1)`; [B, §9.6] |
| `MajorArcs.platt_even` | even `q ≤ 4·10⁵`: GRH up to `max(10⁸/q, 200 + 7.5·10⁷/q)` | same | same |
| `Helfgott.binary_goldbach_input` | every even `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes | [OeSHP14], Math. Comp. 83 (2014) | [B, §1.6]; the project page says "all consecutive even numbers up to `4·10¹⁸`" (the journal page returned 403) |
| `Helfgott.prime_ladder_input` | odd primes from `3` to `≥ 8.875694·10³⁰`, gaps `≤ 4·10¹⁸` | Helfgott–Platt, arXiv:1305.3062 | §4 and Thm 4.1 (top `8 875 694 145 621 773 516 800 000 000 000`); see Finding 2 |
| `Prelim.buthe_theta` | `\|θ(n) − n\| ≤ 1.95 √n`, `1423 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.6) `x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`; (1.7) `x − θ(x) > 0.05√x`; this combines an analytic method with a computation |
| `Prelim.ramare_Gq` | `G_d(R) = (φ(d)/d)(log R + c + ∑_{p∣d} log p/p) + O*(7.284 R^{−1/3} f₁(d))` for all `d, R ≥ 1`, some `c ∈ [1.3325822, 1.3325823]` | Ramaré, *On Šnirel'man's constant*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 22 (1995) 645–706, Lemma 3.4 (open access: numdam ASNSP_1995_4_22_4_645_0) | checked against the paper: Lemma 3.4 states this for all `X > 0`, `d ≥ 1`, with this `f₁`; (3.6) gives `c = γ + ∑_p log p/(p(p−1)) = 1.332582275332…`. `scripts/rigorous/ramare_check.c`: `c ∈ [1.332582274733, 1.332582276813]` (MPFR, primes `≤ 10⁹`, tail via our `ψ(t) ≤ 1.03883 t`); the estimate holds for all `d ≤ 2000`, three primorials and all `X ≤ 2·10⁶` (interval arithmetic), using at most `0.18` of the error bound |
| `Prelim.ramare_moebius` | `\|∑_{n≤x} μ(n)/n\| ≤ 0.03/log x` for real `x ≥ 10¹⁰` (the range used) | Ramaré, Acta Arith. 157 (2013) 365–379, for `x ≥ 11815` ([B, (2.21)]) | implied by Ramaré, Math. Comp. 84 (2015), Thm 1.2 (`≤ (0.0144 log X − 0.1)/(log X)²` for `X ≥ 463 421`), which Ramaré and Zuniga-Alterman re-derive in arXiv:2408.05969. That paper also proves `≤ 0.010032/log X` for `X ≥ 617 990` (Cor. 1.2). |
| `Prelim.buthe_psi` | `\|ψ(n) − n\| ≤ 0.94 √n`, `12 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.5) `\|x − ψ(x)\| ≤ 0.94√x` for `11 < x ≤ 10¹⁹` (same theorem as `buthe_theta`) |

### Results of Helfgott's book [B] (0)

None: the last ones, (5.31), Lemma 5.1.2 and Prop 12.2.4, are now proved (see "Removed axioms").
The Lean definitions that the axioms above refer to were compared with the book's:
* `T2` and `g2` with (5.19) and Lemma 5.1.2;
* `Gq`, `Sq`, `f1q` and `cE` with (12.2), (12.12)–(12.14).

## Summary by kind

* **Our own computations (13):** all are checked rigorously in `scripts/rigorous/` (interval
  arithmetic with directed rounding); most also have a float script in `scripts/`. Two are also contained in
  published results: `mertens_product_small` [RS62, Thm 15] and `moebius_sqrt_small` [B, (2.24)].
* **Published results (9):** RH to `3·10¹²`, Platt's GRH check (2 axioms), binary Goldbach to
  `4·10¹⁸`, the Helfgott–Platt ladder, Büthe's bounds for `θ` and `ψ` (2 axioms), and Ramaré's
  `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x` and his estimate for `G_d(R)`. They are stated as in the papers
  (or weaker). The two Ramaré axioms are also checked independently: (12.12) against the original
  paper and numerically on a finite range, with `c_E` recomputed; the Möbius bound is implied by a
  later published bound that is re-derived on arXiv.
* **Results of [B]:** none.

## Removed axioms

* `theta_sqrt` (`|θ(n) − n| ≤ 1.95 √n`, `5·10⁵ ≤ n ≤ 10¹⁰`, our computation) was a special case of
  `buthe_theta` (same bound, `1423 ≤ n ≤ 10¹⁹`); it is now derived from it.
* `psi_sqrt`, `psi_small`, `psi_mid`, `psi_mul_mid` and `theta_cube_small` (our computations) are
  now proofs. They use Büthe's bounds (`buthe_theta`, and the new `buthe_psi` from the same Theorem 2),
  together with a kernel-checked computation for small `n`:
  * `psi_sqrt`: Büthe for `n ≥ 12` (`0.94 ≤ 0.95`); the uses at `n = 11` are covered by `ψ ≥ 0` and
    `ψ(11) ≤ 1.03883·11`.
  * `psi_small` (`ψ(n) < 1.03883 n`): Büthe for `n ≥ 587`; for `n ≤ 586`,
    `Prelim/SmallPsi.lean` checks `lcm(1, …, n) < e_lo^a T(f)` for every `n` with `decide +kernel`
    (`ψ(n) = log lcm(1, …, n)`).
  * `psi_mid` (`ψ ≤ 1.0004 n`): Büthe for `n ≥ 6·10⁶`. [B, (2.14)] is now stated for `y ≥ 6·10⁶`
    (the proof uses it only at `y ≥ 2.7·10⁷`).
  * `psi_mul_mid`: [B, (2.17)] for `2.5·10⁷ ≤ N ≤ 10¹⁹` by partial summation from Büthe's bounds; it
    is now stated for `y ≥ 2.5·10⁷` (used only at `y ≥ 2.7·10⁷`).
  * `theta_cube_small`: `theta_explicit` now starts at `2·10⁸`, where Büthe's `1.95 √n` is below
    `n/log³n`. Its only use below `10⁹`, the Mertens product bound, now switches from the finite
    check to the analytic bound at `2·10⁸` (`mertens_product_small` was re-run to `2·10⁸`).

* `mertens_small`, `prod_ap_le` (our computations) and `fsq_le` ([B, p. 83]) are now proofs. The
  numerics are checked by the kernel (`decide +kernel`, no `native_decide`):
  * `Prelim/SmallMertens.lean`: `∑_{m ≤ n} Λ(m)/m ≤ log n` for `n ≤ 100`, from the prime-power
    decomposition, upper bounds `log p < U(p)` (checked as `p < e_lo^{U(p)}`) and lower bounds
    `V(n) ≤ log n` (checked as `e_hi^{V(n)} ≤ n`).
  * `Prelim/SmallProdAp.lean`: the 1229 primes below `10⁴` from a table. Its entries are checked
    prime, a chunked scan shows no prime is missing, `p k_p³ ≥ 10¹⁸` gives `p^{−1/3} ≤ k_p/10⁶`, and
    the product of the upper bounds is `≤ 7.99` in exact rational arithmetic
    (`scripts/gen_prod_ap.py`).
  * `Prelim/SmallFsq.lean`: `f(X) = Q(⌊X⌋) + (X²/2) S(⌊X⌋)`.
    * For `⌊X⌋ ≥ 200`: no multiple of `4` is squarefree, and the tail is at most `1/n`.
    * For `⌊X⌋ < 200`: the bound is concave on each `[n, n+1]`, so both endpoints are checked by the
      kernel; for `n = 2` the tail sum to `3000` is checked in blocks of 250.

* `H2_le` ([B, (5.37)]) and the corrected (5.36) `integral_H2_le` are now proofs
  (`MinorArcs/H2Bound.lean`):
  * By [B, (5.19)] (`integral_g2`), `T₂(S) = α_n + β_n/S` on `[n, n+1)`. `α_n` and `β_n` are
    rationals; the kernel evaluates them for `n ≤ 15` from tables of `μ` and `σ`, which it also checks.
  * `H2_le`: `T₂ ≤ 1/2` on `[1, 16)` follows from the endpoints of each piece.
  * `integral_H2_le`: each piece integrates to `(4/π²)(α_n log(b/a) + β_n(1/a − 1/b))`. The bound at
    the integers uses `log j` to `10⁻⁹` (checked as in `SmallMertens`) and `π` to `10⁻²⁰`
    (Mathlib). On `[2, 15]`, `H₂ ≥ 0.15107`, so the excess is largest at the right end of each
    piece. On `[1, 2]` and `[15, 16]`, `log x ≤ x − 1` and `log x ≥ 1 − 1/x` are used.
  * The tightest bound is `0.0230978 ≤ 0.0231`, on `[15, 16]` (the true supremum is `0.023059`).

* (B.6) `eta2_fourier_bound'` and (B.11) `eta2log_fourier_bound` are now proofs
  (`MinorArcs/Eta2Fourier.lean`), except for the finite range `0 ≤ t ≤ 655` of (B.6), which is the
  new computation axiom `eta2DD_small`:
  * Two integrations by parts on `[1/4, 1/2]` and `[1/2, 1]` give `(2πt)² η̂₂(t) = eta2DD t`, with
    `eta2DD t = 16 e(−t/2) − 16 e(−t/4) − 4 e(−t) + 4 ∫_{1/4}^{1/2} e(−ut)/u² − 4 ∫_{1/2}^1 e(−ut)/u²`.
  * With `z = e(−t/4)`, the first three terms are `−z(4z³ − 16z + 16)`. Here
    `|4z³ − 16z + 16|² = 512c³ − 256c² − 896c + 656` (`c = ℜz`), so `|4z³ − 16z + 16| ≤ 31.4821`.
  * One more integration by parts gives `|∫_a^b e(−ut)/u²| ≤ 1/(π|t|a²)`. So
    `‖eta2DD t‖ ≤ 31.4821 + 80/(π|t|) ≤ 31.521` for `|t| ≥ 655`; this is [B]'s argument.
  * The range `0 ≤ t ≤ 655` is `eta2DD_small` (computation in ball arithmetic); negative `t` follow by
    conjugation.
  * (B.11): `η̂_(ρ) = (log·η₂)^ + log ρ · η̂₂`. For `ρ = 4`, the same integration by parts gives
    `‖(2πt)² η̂_(4)(t)‖ ≤ 48 log 2 = 24 log 4`, with no numerics: the derivative jumps are
    `16 log 2` and `8 log 2`, and `∫|h''|` is `16 log 2` and `8 log 2`. For `ρ > 4`, the extra
    `(log ρ − log 4) η̂₂` is bounded by (B.6). Since `24 ≤ 31.521`, (B.11) follows.

* (9.94) `integral_etaPlus_sq_log` is now a proof (`MajorArcs/EtaPlusSqLog.lean`), with [B]'s
  constants `1.95·10⁻⁶ log x + 5.3·10⁻⁷`. The computation is the new axiom `etaO_numerics`:
  * `∫₀^∞ η₊² log(xt) dt = A log x + B` with, in `u = log t`, `A = ∫ (g + D)² E`, `B = ∫ (g + D)² E u`.
    Here `g(u) = h(eᵘ)`, `D = g_H − g`, and `E(u) = e^{3u − e^{2u}}`.
  * The main terms `∫ g² E = ∫₀² η◦²` and `∫ g² E u = ∫₀² η◦² log t` are elementary integrals
    (`etaO_numerics`; [B] gets the same values with VNODE-LP).
  * `∫ D² E ≤ ½ ‖D‖₂²` and `|∫ D² E u| ≤ 0.37 ‖D‖₂²`, with
    `‖D‖₂² = ∫_{|ξ| > H/2π} |ĝ|² ≤ 368/H⁴` (`HHFourier2.lean`).
  * The cross terms `∫ D W` (`W = gE`, `ugE`): `D` has its Fourier transform on `|ξ| > H/2π`, so
    by Parseval `|∫ D W| ≤ ∫_{|ξ|>H/2π} |ĝ||Ŵ| ≤ (λ T_g + T_W/λ)/2`. Each tail is at most
    `‖·''‖₂²/H⁴`, which gives `≤ 7.2·10⁻⁸` and `≤ 3.5·10⁻⁸`.
  * In total the errors are at most `2.6·10⁻⁷ log x + 3.8·10⁻⁷`.

* `T2_le` ([B, (5.31)]) is now a proof (`MinorArcs/T2Bound.lean`), with a simpler argument than
  [B]'s (5.29)–(5.30):
  * `∫_{1/2}^1 g₂(uz) du = z⁻¹ ∫_{z/2}^z g₂` gives `T₂(S) = S⁻¹ ∫₀^S g₂(y) N(y) dy`, where `N(y)` is
    the number of odd `s ∈ (S/2y, S/y]`.
  * So `|N(y) − S/(4y)| ≤ 1`, and `|T₂(S) − ¼ ∫₁^S g₂/y| ≤ S⁻¹ ∫₁^S |g₂|` (`abs_T2_sub_le`).
  * For `16 ≤ S < 10⁵` this is replaced by the exact computation `T2_small`.
  * For `10⁵ ≤ S ≤ 10⁸`: `T₂ ≤ 0.3607 + 10.5/10⁵` (`T2_mid`).
  * For `S > 10⁸`: the extra terms are at most `1.25 ∫_{10⁸}^S |g₂|/y ≤ 1.25 · 0.0036`, by
    Lemma 5.1.2 in the form below (explicit antiderivative of the bound).
  * So `T₂ ≤ 0.3652` there, against `0.37273`.
  * This replaces the bundle "(5.31) = Lemma 5.1.2 + (5.29)–(5.30) + a computation on `[16, 10⁵]`"
    by our computations `T2_small`, `T2_mid` and Lemma 5.1.2.

* [B, Lemma 5.1.2] (`v = 2`) is now a proof (`MinorArcs/G2Moebius.lean`, `G2Euler.lean`,
  `G2Numerics.lean`, `G2Bound.lean`), with cruder constants than [B]:
  `|g₂(x)| ≤ 0.0215/(log x)² + 528 (1 + log x)²/x` for `x > 1` (`abs_g2_le_large`). The only input
  beyond our earlier axioms is Ramaré's `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x` ([B, (2.21)], the published
  axiom `ramare_moebius`). The proof:
  * `g₂(x) = ∑_{d ≤ x} μ(d) f(d)² S_d(x/d)²` with `f(r) = μ(r)/σ(r)` for odd `r` and
    `S_d(M) = ∑_{r ≤ M, (r,d)=1} f(r)` ([B, (5.20)]).
  * `f·1_{(·,d)=1} = H_d ∗ (μ/id)` with `H_d = f·1_{(·,d)=1} ∗ (1/id)`, which is multiplicative and
    `≥ 0` (`H_d(p^k) = p^{−k}/(p+1)` for odd `p ∤ d`, `p^{−k}` otherwise). So
    `S_d(M) = ∑_{a ≤ M} H_d(a) m(M/a)` with `m(y) = ∑_{n≤y} μ(n)/n`. This one convolution replaces
    [B]'s two steps (5.21).
  * `|m(x/u)| ≤ 0.03 u^{1/22}/log x + √(2u/x)`. If `x/u ≥ 10¹⁰`, use Ramaré and
    `log x/log(x/u) ≤ 1 + log u/22 ≤ u^{1/22}`. Otherwise use `moebius_sqrt_small`.
  * Euler products (Mathlib's `EulerProduct`): `∑_{a ≤ A} H_d(a) a^s ≤ c_s(2) ∏_{2<p≤A} ℓ_s(p)
    ∏_{p∣d} ρ_s(p)`, `∑_d f(d)² d^{2s} ∏_{p∣d} ρ_s(p)² ≤ ∏_{p>2} (1 + (p^s/(p+1−p^s))²)` and
    `∑_{d≤N} f(d)² d ∏_{p∣d} ρ_{1/2}(p)² ≤ ∑_{d≤N} τ(d)/d ≤ (1 + log N)²`.
  * The products are evaluated at `s = 1/22` and `s = 1/2` with rational bounds for `p^s` at the
    primes below `12` (resp. `30`) and the integral bound for the tails. There is no new numerical
    axiom.
  * [B]'s constants (`0.038128/(log x)² + 0.2046/√x`) are better; ours give
    `∫_{10⁸}^∞ |g₂|/y ≤ 0.0036`, which (5.31) can afford (it allows `0.0096`).

* `prop_12_2_4` ([B, Prop 12.2.4]) is now a proof (`MinorArcs/LSQuot1.lean`–`LSQuot6.lean`). Its
  inputs are Ramaré's (12.12) (published axiom `ramare_Gq`) and our computation `prop1224_check`.
  With `R = Q₀/sq`, `t = Q/Q₀`:
  * The reduction [B, (12.25)–(12.26)] (`star_suffices`) uses
    `θ = (log Q₀ + 1.36)/(log Q + c_E) ≤ 0.6274`.
  * `R ≥ λ(q)`: (12.12) suffices (`regionL`).
  * Small `R` (`regionS`, in place of [B, Lemmas 12.2.1–12.2.3]): `G_q(R) G_P(t) ≤ G_q(tR)` with
    `P = ∏_{p ≤ R or p ∣ q} p`, `G(t) ≤ (P/φ(P)) G_P(t)`, `G(t) ≥ log t + 1.064` from (12.12), and
    Lemma C.2.2 (`div_totient_lt`) for `P/φ(P)`. This applies when
    `log q + 1.039 R ≤ c′ (qR)^{2/9}`.
  * `q ≥ 2.2·10¹⁰` (in place of [B, (12.34)–(12.40)]): `λ(q)⁷ ≤ (103/120)⁹ q²`. The proof replaces
    the primes of `q` by the first `k` primes (an antitone majorant of `(p/(p−1)) f₁(p)`), checks
    `k ≤ 10` at `q = 2.2·10¹⁰`, and inducts over primorials for `k ≥ 11`. Then `regionS` covers
    every `R < λ(q)`.
  * `q < 2.2·10¹⁰`: the computation decides, for each integer `n < λ(q)`, between `regionS` and
    the explicit check (12.31).
  * See Finding 6 for two slips in [B]'s argument.

* `lemma7_numeric` and `GS_N0` ([MV73, Lemma 7], `Prelim/MVLemma7.lean`) are gone.
  * Ramaré's (12.12) at `d = 1` (`Prelim.ramare_Gq`, moved to `Prelim/RamareGq.lean`) gives
    `G(r) ≥ log r + c_E − 7.284 r^{−1/3} ≥ log r + 1.07` for `r ≥ 21400`. This also makes the constant
    `κ = c_E` known, which `GS_N0` used to provide.
  * For `6 ≤ r < 21400` the kernel checks `G(r) ≥ log r + 1.07` (`Prelim/SmallG.lean`, 23 s).
    `G(a) ≥ ∑_{T ⊆ P, ∏T ≤ a} ∏_{p∈T} 1/(p−1)` for any set `P` of primes, and a depth-first search over the
    primes `≤ 21400` computes this sum in fixed point, rounding down. 32 blocks `[a, b)` with
    `G(a) > log b + 1.07` cover the range. Only the primality of the listed primes is used.

* `nonprime_small` (`ψ(n) − θ(n) < 1.4262 √n` for `1 ≤ n ≤ 10¹²`, [RS62, Thm 13] in this range) is
  now a theorem (`Prelim/LambdaMu.lean`).
  * For `10⁶ ≤ n ≤ 10¹²`: `ψ − θ ≤ θ(√n) + θ(n^{1/3}) + θ(n^{1/4}) + n^{1/5} log n`, with `θ(√n) ≤ ψ(√n) ≤
    √n + 0.94 n^{1/4}` ([Büthe], `buthe_psi`), `θ(y) ≤ 1.03883 y` and `log n ≤ 20 n^{1/20}/e`.
  * For `n ≤ 10⁶` the kernel checks it (`Prelim/SmallNonprime.lean`, 9 s): `ψ(n) − θ(n) ≤ ∑_{p < 1001}
    #{2 ≤ k ≤ 20 : p^k ≤ n} u_p/10⁹` with `log p < u_p/10⁹`, on 31 blocks. The minimum margin is
    `1.3·10⁻⁴` (the constant `1.4262` is attained to within `7·10⁻⁶` at `n = 361`).

* `logsq_small` (`∑_{n/2<p≤n} (log p)² ≤ ½ n log n` for `117 ≤ n ≤ 10⁶`, [B, (2.19)]) is now a theorem
  (`Prelim/LambdaMu.lean`).
  * For `40000 ≤ n ≤ 10⁶`: Abel summation against `θ`, with `θ(n) ≤ ψ(n) ≤ n + 0.94√n` and
    `θ(n) ≥ n − 2.3662√n` (`buthe_psi` and `nonprime_small`); the margin is `½ n (1 − log 2)`.
  * For `117 ≤ n < 40000` the kernel checks it (`Prelim/SmallLogSq.lean`, 78 s). The primes below
    `40000` are listed in 40 chunks (complete by `scan`) with `log p < u_p/10⁶`, and 225 blocks
    `[A, B)` satisfy `∑_{A/2<p<B} u_p²/10¹² ≤ ½ A log A`.

* `liouville_small` (`|∑_{n≤k} λ(n)/n| log(k+1) ≤ 0.99` for `1 ≤ k ≤ 10⁵`) is now checked by the kernel
  (`Prelim/SmallLiouville.lean`, 4.7 min). `λ(n) = (−1)^{Ω(n)}`, with `Ω(n)` by trial division
  (`omTD`, proved correct); the kernel walks `n ≤ 10⁵` keeping `P(k), Q(k) = ∑_{n≤k, λ(n)=±1} ⌊10¹²/n⌋`
  (so `|10¹² ∑ λ(n)/n − (P − Q)| ≤ k`) and checks `100 (|P − Q| + k) u ≤ 99·10¹⁸` at every `k`, with
  `log(k+1) < u/10⁶` on each of 104 chunks.

* `lemma8_numeric` ([MV73, Lemma 8] for `2 ≤ R ≤ 10⁴`, two finite sums) is gone (`Prelim/MVLemma8.lean`).
  * The Abel-summation proof from Lemma 7 now covers `R ≥ 1000` (it needs `R ≥ 742`).
  * For `6 ≤ R < 1000`: `W(R) ≥ W(A) > log B + 0.25068` on 18 blocks `[A, B)`, with `W(A)` bounded
    below by a weighted depth-first search over subsets of primes (`Prelim/SmallW.lean`, kernel).
  * For `2 ≤ R < 6`: the two sums at `n = ⌊R⌋ ≤ 5` are exact rationals (margin `1.1·10⁻⁶` at `n = 4`,
    with `log 5 < 1.609437913` by `chkStep`).

## Candidates for proofs in Lean

No finite axiom small enough for the kernel remains.

The checks over large ranges (`10⁸`–`10¹⁰`) are beyond what the kernel can evaluate. A kernel
check handles about `10⁵` simple steps per declaration, and `Nat.primesBelow 10⁴` already runs out
of memory. They would need `native_decide`, which means trusting Lean's compiler.
