# Axiom audit

`ternary_goldbach` depends on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on the 36 axioms below (`#print axioms`). A false axiom makes the axiom set
inconsistent, and then the formal proof says nothing. So each axiom has been checked against its
source:

* For our own computations, against the script: its range, edge cases, the precise Lean
  definitions involved, rounding, and the margin.
* For published results, against the paper.

All scripts were re-run. The audit was done on 2026-11-01. Sources: [B] = Helfgott, *The ternary
Goldbach problem*, arXiv:1501.05438v2. The papers below are cited by arXiv number.

## Findings

1. **[B, (5.36)] is false as stated. Fixed: `integral_H2_le` is now its corrected form.**
   * The book's (5.36) inherits an error in [B, (5.32)] for `v = 2`.
   * Our `T2` is exactly the sum in [B, (5.19)]. Its values agree with [B]'s stated
     `G₂(S) = 1 − 1/S` on `[1, 2)`, and `T₂(S) = 1/2` exactly on `[2, 3)`.
   * Exactly, `∫₁⁴ T₂(S) dS/S = (log 2 − 1/2) + ½ log(3/2) + ⅓ log(4/3) + 1/24 = 0.53344`. This is
     more than `0.37273 log 4 = 0.51671`, and (5.32) claims the bound for `G₂ ≥ T₂`.
   * Hence `∫₁⁴ H₂(S)/S dS = 0.21619 > 0.15107 log 4 = 0.20943`.
   * The axiom now states `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T + 0.0231` for all `T ≥ 1`. This is checked
     rigorously by `scripts/h2_integral_check.py` (exact rationals and interval logs; the supremum
     of the excess is `0.023059`). Because `H₂ = 0.15107` for `S ≥ 16`, the excess is constant from
     `T = 16` on.
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

### Our own computations (22)

Scripts are in `scripts/`; all were re-run on 2026-11-01 and reproduce the stated values.
"float64" means double precision. In those cases the rounding error is bounded in the script's
docstring and is orders of magnitude below the margin.

| Axiom | Statement | Script | Arithmetic | Result (margin) |
|---|---|---|---|---|
| `Prelim.psi_small` | `ψ(n) < 1.03883 n`, `1 ≤ n < 2·10⁶` | `psi_checks.py` | float64 | max `1.0388206` at `n = 113` |
| `Prelim.nonprime_small` | `ψ(n) − θ(n) < 1.4262 √n`, `1 ≤ n ≤ 10¹²` | `psi_checks.py` | float64 (checked at every prime power `p^k`, `k ≥ 2`) | max `1.4261933` at `n = 361` |
| `Prelim.mertens_small` | `∑_{m≤n} Λ(m)/m ≤ log n`, `1 ≤ n ≤ 100` | `psi_checks.py` | mpmath, 30 digits | max of difference `0` (equality at `n = 1`) |
| `Prelim.mertens_lower_small` | `∑_{m≤n} Λ(m)/m ≥ log(n+1) − log(3/√2)`, `3 ≤ n ≤ 10⁶` | `psi_checks.py` | float64 | min margin `0.0141` at `n = 6` |
| `Prelim.mertens_point` | value at `X = 10⁶` `≥ −1.5776` | `psi_checks.py` | float64 | `−1.57721` |
| `Prelim.logsq_small` | `∑_{n/2<p≤n} (log p)² ≤ ½ n log n`, `117 ≤ n ≤ 10⁶` | `psi_checks.py` | float64 | min margin `2.137` at `n = 117` |
| `Prelim.psi_mid` | `ψ(n) ≤ 1.0004 n`, `2·10⁶ ≤ n ≤ 10⁹` | `psi_mid_check.py` | float64 | max `1.0003639` at `n = 3 445 943` |
| `Prelim.psi_sqrt` | `\|ψ(n) − n\| ≤ 0.95 √n`, `11 ≤ n ≤ 10¹⁰` | `psi_mid_check.py` | float64 | max `0.7906` |
| `Prelim.theta_sqrt` | `\|θ(n) − n\| ≤ 1.95 √n`, `5·10⁵ ≤ n ≤ 10¹⁰` | `psi_mid_check.py` | float64 | `θ(n) < n`; max `1.8071` |
| `Prelim.psi_mul_mid` | `∑_{m≤n} Λ(m) m < 1.0008 n²/2`, `1.6·10⁶ ≤ n ≤ 10⁸` | `psi_mid_check.py` | long double | min margin `4.3·10⁻⁵ n²` |
| `Prelim.theta_cube_small` | `\|θ(n) − n\| < n/log³n`, `89 967 803 ≤ n ≤ 10¹⁰` | `theta_cube_check.py` | float64 | max ratio `0.999336` at `n = 89 967 810` (absolute margin `≈ 9.7`) |
| `Prelim.mertens_product_small` | `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`, primes `5 ≤ x ≤ 10⁸` | `mertens_product_check.py` | mpmath, 40 digits, below `10⁴`; float64 above | min margin `2.44·10⁻⁷` at `x = 23`; `≥ 0.1357` above `10⁴` |
| `Prelim.K_pieces` | piecewise sum `≤ 0.4035` | `moebius_K_check.py` | float64 | `0.403420` |
| `Prelim.K_blocks` | block bounds `hblk j`, `1000 ≤ k < 10⁹` | `moebius_K_check.py` | float64 (block maxima `+10⁻⁷`, rounded up) | the 20 Lean constants equal the script's list |
| `Prelim.moebius_sqrt_small` | `\|∑_{n≤k} μ(n)/n\| ≤ √(2/(k+1))`, `1 ≤ k < 10¹⁰` | `moebius_sqrt_check.py` | float64 | equality at `k = 1`; otherwise max ratio `0.6124` at `k = 2` |
| `Prelim.liouville_small` | `\|∑_{n≤k} λ(n)/n\| log(k+1) ≤ 0.99`, `1 ≤ k ≤ 10⁵` | `liouville_small_check.py` | float64 | max `0.7831` at `k = 10` |
| `Prelim.C_grid` | `(2.8 + (i+1)/100) G(2.8 + i/100) ≤ 2.8`, `i < 7720` | `moebius_C_grid.py` | float64 | max `2.7422` |
| `Prelim.MV.prod_ap_le` | `∏_{p<10⁴} (1 + (p^{−2/3} + p^{−1/3})/(p−1)) ≤ 7.99` | `mv_lemma8_check.py` | mpmath, 30 digits | `7.98552` |
| `Prelim.MV.lemma7_numeric` | `G(r) ≥ log(r+1) + 1.07`, `6 ≤ r < 3·10⁷` | `mv_lemma8_check.py` | float64 | min margin `0.0441` at `r = 9` |
| `Prelim.MV.GS_N0` | `G(3·10⁷) ≥ log(3·10⁷) + 1.3325` | `mv_lemma8_check.py` | float64 | `1.332583` |
| `Prelim.MV.lemma8_numeric` | two finite sums, `2 ≤ n ≤ 10⁴` | `mv_lemma8_check.py` | float64; exact rationals at `n = 4` | min margin `1.14·10⁻⁶` at `n = 4`; second sum max `0.638` |
| `MajorArcs.sum_odd_mu_sq_div_totient` | `6.798779 ≤ ∑_{q≤150000 odd} μ²(q)/φ(q) ≤ 6.79878` | `check_sum_mu2_phi.py` | directed rounding, 40 digits (rigorous) | `6.7987791731…` |

Unused (in `Prelim/LambdaMuExtra.lean`, not on the path of `ternary_goldbach`):
* `lambda_mul_small`: max ratio `1.03583`.
* `lambda_sqrt_small`: max ratio `1.99838`.
* `lambda_sqrt_point`: value `−3.2553`.

All three come from `psi_extra_check.py`.

### Published computations (6)

| Axiom | Statement | Source | Check |
|---|---|---|---|
| `Explicit.rh_upto` | zeros of `ζ` with `0 < ℜρ < 1`, `\|ℑρ\| ≤ 3·10¹²` have `ℜρ = 1/2` | Platt–Trudgian, arXiv:2004.09765 | abstract: "all zeroes `β + iγ` … with `0 < γ ≤ 3·10¹²` have `β = 1/2`"; for `γ ≤ 0` see Finding 3 |
| `MajorArcs.platt_odd` | primitive `χ`, odd conductor `q ≤ 3·10⁵`: GRH up to `10⁸/q` | Platt, arXiv:1305.3087 | abstract: all primitive `χ`, `q ≤ 4·10⁵`; odd `q` to `max(10⁸/q, 3.75·10⁷/q + 200)`; Thm 3.2 counts zeros with `\|ℑs\| ≤ t₀`, `ℜs ∈ (0,1)`; [B, §9.6] |
| `MajorArcs.platt_even` | even `q ≤ 4·10⁵`: GRH up to `max(10⁸/q, 200 + 7.5·10⁷/q)` | same | same |
| `Helfgott.binary_goldbach_input` | every even `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes | [OeSHP14], Math. Comp. 83 (2014) | [B, §1.6]; the project page says "all consecutive even numbers up to `4·10¹⁸`" (the journal page returned 403) |
| `Helfgott.prime_ladder_input` | odd primes from `3` to `≥ 8.875694·10³⁰`, gaps `≤ 4·10¹⁸` | Helfgott–Platt, arXiv:1305.3062 | §4 and Thm 4.1 (top `8 875 694 145 621 773 516 800 000 000 000`); see Finding 2 |
| `Prelim.buthe_theta` | `\|θ(n) − n\| ≤ 1.95 √n`, `1423 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.6) `x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`; (1.7) `x − θ(x) > 0.05√x`; this combines an analytic method with a computation |

### Results of Helfgott's book [B] (8)

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
| `MinorArcs.integral_H2_le` | (5.36), **corrected** | `∫₁ᵀ H₂/S ≤ 0.15107 log T + 0.0231` | **rigorous** (`scripts/h2_integral_check.py`); [B]'s version without `+0.0231` is false (Finding 1) |
| `MinorArcs.H2_le` | (5.37) | `H₂ ≤ 2/π²`, i.e. `T₂ ≤ 1/2` on `S < 16` | **rigorous** (`scripts/h2_integral_check.py`, exact): holds, with equality on `[2, 3)` |
| `Prelim.fsq_le` | p. 83 | `f(X) ≤ 1.27 X` | **rigorous** (`scripts/fsq_check.py`, interval arithmetic and [B]'s reduction to `X ≤ 50`): max `f(2)/2 = 15/π² − 1/4 = 1.2698177…` |
| `MinorArcs.eta2_fourier_bound'` | Lemma B.1.2, (B.6) | `\|(η₂'')^\|_∞ ≤ 31.521` | float, `t < 700`, step `5·10⁻⁴`: max `31.52065` at `t ≈ 17.415`; [B] covers `\|t\| ≥ 655` analytically |
| `MinorArcs.eta2log_fourier_bound` | Lemma B.2.3, (B.11) | `\|(η_(ρ)'')^\|_∞ < 31.521 log ρ`, `ρ ≥ 4` | float, at `ρ = 4`: max `16.34 log 4`. For `ρ > 4` it follows from this and (B.6), because the bound is convex in `1/log ρ` |
| `MajorArcs.integral_etaPlus_sq_log` | (9.94) | `∫ η₊² log(xt) dt` | `scripts/eta_plus_check.py` computes `η₊` itself (FFT band limit in `log t`, float): `∫ η₊² = 0.640205997…` and `∫ η₊² log t = −0.021094779…`, within `2.6·10⁻⁹` and `2.2·10⁻⁷` of (9.94)'s values (allowed: `1.95·10⁻⁶`, `5.3·10⁻⁷`); `‖η₊ − η◦‖₂² = 3.9·10⁻¹³` |
| `MinorArcs.prop_12_2_4` | Prop 12.2.4 | `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)` | hypotheses and conclusion match; our `c_E = 1.33258` is [B]'s `1.3325822…` rounded down, which makes the axiom weaker; the content is Ramaré's explicit (12.12) plus a computation for `q < 3.3·10⁹` |

## Summary by kind

* **Our own computations (22):** reproducible with the scripts in `scripts/`.
* **Published computations (6):** RH to `3·10¹²`, Platt's GRH check, binary Goldbach to `4·10¹⁸`,
  the Helfgott–Platt ladder, and Büthe's bound. They are stated as in the papers.
* **Results of [B] (8):**
  * `fsq_le`, `H2_le` and the corrected `integral_H2_le` are re-checked rigorously by our scripts.
  * (B.6), (B.11), (9.94) and (5.31) on its computed range `[16, 10⁵]` are re-checked by float
    computations.
  * The rest rests on [B]: Prop 12.2.4 (Ramaré's explicit estimate and a computation), (5.31) for
    `S ≥ 10⁵` (Lemma 5.1.2), and the `|t| ≥ 655` part of (B.6).

## Candidates for proofs in Lean

These axioms are finite, explicit and small:
* `fsq_le` (squarefree `X ≤ 50` and a crude bound);
* `H2_le` and the corrected `integral_H2_le` (piecewise `α + β/S` on `[1, 16)`);
* `mertens_small` (`n ≤ 100`);
* `prod_ap_le` (1229 primes).
