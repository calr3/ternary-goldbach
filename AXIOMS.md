# Axiom audit

`ternary_goldbach` depends on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on the 26 axioms below (`#print axioms`). A false axiom makes the axiom set
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
5. **(9.94) contains analysis.** `integral_etaPlus_sq_log` rests on [B]'s rigorous integration of `η◦`
   and also on the bounds (A.23), (A.24) on `η₊ − η◦`. Our own Lean bound on `‖η₊ − η◦‖₂` is far
   too weak to replace them. A direct float computation of `η₊` (`scripts/eta_plus_check.py`)
   confirms the values.
6. **Binary Goldbach was double-checked only to `4·10¹⁷`.** [OeSHP14] verified binary Goldbach up to
   `4·10¹⁸`; according to the project page, the independent double-check reaches `4·10¹⁷`.

## The axioms

### Our own computations (14)

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
| `Prelim.nonprime_small` | `ψ(n) − θ(n) < 1.4262 √n`, `1 ≤ n ≤ 10¹²` | `psi_checks.py` | max ratio `1.4261933` at `n = 361` (all `80070` prime powers `p^k`, `k ≥ 2`) | [RS62, Thm 13] (all `x > 0`), as cited in [B, (5.5), (14.51)] |
| `Prelim.mertens_lower_small` | `∑_{m≤n} Λ(m)/m ≥ log(n+1) − log(3/√2)`, `3 ≤ n ≤ 10⁶` | `psi_checks.py` | min margin `0.0140806` at `n = 6` | |
| `Prelim.mertens_point` | value at `X = 10⁶` `≥ −1.5776` | `psi_checks.py` | `−1.5772056` | |
| `Prelim.logsq_small` | `∑_{n/2<p≤n} (log p)² ≤ ½ n log n`, `117 ≤ n ≤ 10⁶` | `psi_checks.py` | min margin `2.1373` at `n = 117` | |
| `Prelim.mertens_product_small` | `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`, primes `5 ≤ x ≤ 2·10⁸` | `mertens_product_check.py` | min margin `2.4367·10⁻⁷` at `x = 23`; `≥ 0.13088` above `10⁴` | [RS62, Thm 15, (3.42)] at `n = ∏_{p≤x} p` (`log n = θ(x)`), as cited in [B, (C.19)] |
| `Prelim.K_pieces` | piecewise sum `≤ 0.4035` | `moebius_K_check.py` | `0.4034195` | |
| `Prelim.K_blocks` | block bounds `hblk j`, `1000 ≤ k < 10⁹` | `moebius_K_check.py` | all 20 blocks hold; e.g. block 19: `2.55663·10⁻⁵ ≤ 2.567·10⁻⁵` | |
| `Prelim.moebius_sqrt_small` | `\|∑_{n≤k} μ(n)/n\| ≤ √(2/(k+1))`, `1 ≤ k < 10¹⁰` | `moebius_sqrt_check.py` | equality at `k = 1`; otherwise max ratio `0.612372` at `k = 2` | [B, (2.24)] (Helfgott, interval arithmetic, `x ≤ 10¹²`; Ramaré earlier `x ≤ 10¹⁰`) |
| `Prelim.liouville_small` | `\|∑_{n≤k} λ(n)/n\| log(k+1) ≤ 0.99`, `1 ≤ k ≤ 10⁵` | `liouville_small_check.py` | max `0.783122` at `k = 10` | |
| `Prelim.C_grid` | `(2.8 + (i+1)/100) G(2.8 + i/100) ≤ 2.8`, `i < 7720` | `moebius_C_grid.py` | max `2.742169` at `i = 0` | |
| `Prelim.MV.lemma7_numeric` | `G(r) ≥ log(r+1) + 1.07`, `6 ≤ r < 3·10⁷` | `mv_lemma8_check.py` | min margin `0.044082` at `r = 9` | |
| `Prelim.MV.GS_N0` | `G(3·10⁷) ≥ log(3·10⁷) + 1.3325` | `mv_lemma8_check.py` | `1.3325830` | |
| `Prelim.MV.lemma8_numeric` | two finite sums, `2 ≤ n ≤ 10⁴` | `mv_lemma8_check.py` | min margin `1.1352·10⁻⁶` at `n = 4`; second sum max `0.638395` | first sum: [MV73, Lemma 8] for `R ≥ 100`, as cited in [B, p. 97] |
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

### Published computations (7)

| Axiom | Statement | Source | Check |
|---|---|---|---|
| `Explicit.rh_upto` | zeros of `ζ` with `0 < ℜρ < 1`, `\|ℑρ\| ≤ 3·10¹²` have `ℜρ = 1/2` | Platt–Trudgian, arXiv:2004.09765 | abstract: "all zeroes `β + iγ` … with `0 < γ ≤ 3·10¹²` have `β = 1/2`"; for `γ ≤ 0` see Finding 3 |
| `MajorArcs.platt_odd` | primitive `χ`, odd conductor `q ≤ 3·10⁵`: GRH up to `10⁸/q` | Platt, arXiv:1305.3087 | abstract: all primitive `χ`, `q ≤ 4·10⁵`; odd `q` to `max(10⁸/q, 3.75·10⁷/q + 200)`; Thm 3.2 counts zeros with `\|ℑs\| ≤ t₀`, `ℜs ∈ (0,1)`; [B, §9.6] |
| `MajorArcs.platt_even` | even `q ≤ 4·10⁵`: GRH up to `max(10⁸/q, 200 + 7.5·10⁷/q)` | same | same |
| `Helfgott.binary_goldbach_input` | every even `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes | [OeSHP14], Math. Comp. 83 (2014) | [B, §1.6]; the project page says "all consecutive even numbers up to `4·10¹⁸`" (the journal page returned 403) |
| `Helfgott.prime_ladder_input` | odd primes from `3` to `≥ 8.875694·10³⁰`, gaps `≤ 4·10¹⁸` | Helfgott–Platt, arXiv:1305.3062 | §4 and Thm 4.1 (top `8 875 694 145 621 773 516 800 000 000 000`); see Finding 2 |
| `Prelim.buthe_theta` | `\|θ(n) − n\| ≤ 1.95 √n`, `1423 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.6) `x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`; (1.7) `x − θ(x) > 0.05√x`; this combines an analytic method with a computation |
| `Prelim.buthe_psi` | `\|ψ(n) − n\| ≤ 0.94 √n`, `12 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.5) `\|x − ψ(x)\| ≤ 0.94√x` for `11 < x ≤ 10¹⁹` (same theorem as `buthe_theta`) |

### Results of Helfgott's book [B] (5)

The book obtains these by interval arithmetic or rigorous integration. Some of them also contain
analytic arguments. The Lean definitions involved were compared with the book's:
* `T2` and `g2` with (5.19) and Lemma 5.1.2;
* `H2` with (5.35);
* `fsq` with the definition on p. 83;
* `Gq` and `cE` with (12.2) and (12.14);
* `etaPlus`, `hBase` and `F` with (7.3)–(7.6);
* `eta2log` with Lemma B.2.3.

| Axiom | [B] | Content | Independent check |
|---|---|---|---|
| `MinorArcs.T2_le` | (5.31), p. 92 | `T₂(S) ≤ 0.37273`, `S ≥ 16`: analytic for `S ≥ 10⁵` (Lemma 5.1.2, (5.30)), numerical below | `scripts/t2_check.py` (float, grid, all of `[16, 10⁵]`): max `0.371249` at `S = 16` |
| `MinorArcs.eta2_fourier_bound'` | Lemma B.1.2, (B.6) | `\|(η₂'')^\|_∞ ≤ 31.521` | float, `t < 700`, step `5·10⁻⁴`: max `31.52065` at `t ≈ 17.415`; [B] covers `\|t\| ≥ 655` analytically |
| `MinorArcs.eta2log_fourier_bound` | Lemma B.2.3, (B.11) | `\|(η_(ρ)'')^\|_∞ < 31.521 log ρ`, `ρ ≥ 4` | float, at `ρ = 4`: max `16.34 log 4`. For `ρ > 4` it follows from this and (B.6), because the bound is convex in `1/log ρ` |
| `MajorArcs.integral_etaPlus_sq_log` | (9.94) | `∫ η₊² log(xt) dt` | `scripts/eta_plus_check.py` computes `η₊` itself (FFT band limit in `log t`, float): `∫ η₊² = 0.640205997…` and `∫ η₊² log t = −0.021094779…`, within `2.6·10⁻⁹` and `2.2·10⁻⁷` of (9.94)'s values (allowed: `1.95·10⁻⁶`, `5.3·10⁻⁷`); `‖η₊ − η◦‖₂² = 3.9·10⁻¹³` |
| `MinorArcs.prop_12_2_4` | Prop 12.2.4 | `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)` | hypotheses and conclusion match; our `c_E = 1.33258` is [B]'s `1.3325822…` rounded down, which makes the axiom weaker; the content is Ramaré's explicit (12.12) plus a computation for `q < 3.3·10⁹` |

## Summary by kind

* **Our own computations (14):** all are checked rigorously (interval arithmetic with directed
  rounding, `scripts/rigorous/`), besides the float scripts in `scripts/`. Four are also contained in
  published results: `nonprime_small` [RS62, Thm 13], `mertens_product_small` [RS62, Thm 15],
  `moebius_sqrt_small` [B, (2.24)] and the first half of `lemma8_numeric` for `R ≥ 100`
  [MV73, Lemma 8].
* **Published computations (7):** RH to `3·10¹²`, Platt's GRH check (2 axioms), binary Goldbach to
  `4·10¹⁸`, the Helfgott–Platt ladder, and Büthe's bounds for `θ` and `ψ` (2 axioms). They are stated as
  in the papers.
* **Results of [B] (5):**
  * (B.6), (B.11), (9.94) and (5.31) on its computed range `[16, 10⁵]` are re-checked by float
    computations.
  * The rest rests on [B]: Prop 12.2.4 (Ramaré's explicit estimate and a computation), (5.31) for
    `S ≥ 10⁵` (Lemma 5.1.2), and the `|t| ≥ 655` part of (B.6).

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

## Candidates for proofs in Lean

No finite axiom small enough for the kernel remains.

The checks over large ranges (`10⁸`–`10¹⁰`) are beyond what the kernel can evaluate. A kernel
check handles about `10⁵` simple steps per declaration, and `Nat.primesBelow 10⁴` already runs out
of memory. They would need `native_decide`, which means trusting Lean's compiler.
