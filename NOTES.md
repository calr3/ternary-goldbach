# Working notes

Notes for working on the formalization: conventions, the errors found in [H] and how the proof
handles them, design notes for the main parts, and practical lessons about Lean and the kernel.
`README.md` has the overview, `BLUEPRINT.md` maps [H] to the Lean files, and `HYPOTHESES.md` lists
the hypotheses and checks them against their sources.

## Conventions

* The proof follows the book [H] = arXiv:1501.05438v2, not the 2013 papers. Equation numbers are the
  book's. Its minor-arc bound is `1.00948` (the 2013 paper has `0.97392`), so [H]'s final margin is
  `0.048779·x²/κ`. Ours is `0.0114·x²/κ` (`1.049 − 1.0376`).
* Where the final inequality has room, we prove cruder constants than the book's sharp ones (e.g.
  the non-prime terms: `6.7·10⁶` instead of `7.3306`). Each change is recorded in the docstrings and
  in the README.
* Published results enter only as the two hypotheses of `Statement.lean`, as `Fact` instances
  (`RamareMoebius` is also a `Fact`, provided from `Fact PlattGRH` by `Prelim/RamareMoebius.lean`).
  Everything else is proved. Each theorem takes only the instances its proof uses, so its statement
  shows what it depends on; the `unusedSectionVars` linter reports any other. A file's
  `variable [Fact …]` line lists an instance only if most of its theorems use it; otherwise theorems add
  it with `variable [Fact …] in` (or drop it with `omit [Fact …] in`). Finite computations are evaluated by the kernel (`decide +kernel`);
  there is no `native_decide`.
* Blueprint statements use the book's exact constants and are transcribed from the typeset PDF.
  Watch division by zero: write `min(1, c/δ²)` with an explicit `δ = 0` case (`minInv`).
  `C / sin² = C/0 = 0` is fine where it only makes the left side smaller.

## Reading the book

* The arXiv PDF has 327 pages. **PDF page = printed page + 10.**
* Extracted text (`pypdf`) loses fraction structure. For formulas, render pages with PyMuPDF
  (`pip install pymupdf` in a venv, `page.get_pixmap(dpi=110).save(...)`) and read the images.
* Before formalizing any inequality, check it numerically (`mpmath`, high precision; float
  cancellation near 0 gives false negatives). This caught the Lemma 4.1.3 gap and picked the
  Taylor degrees.

## Errors in [H] and how the proof handles them

`HYPOTHESES.md` ("Errors found in the sources") has the numbered findings; the README has a summary.

### Part I (Chs. 2–6)

* Small slips. (3.6) prints `+ μ_{≤U} ∗ Λ_{≤V} ∗ 1`; the derivation after it and (3.8) have `−`.
  (4.32) cites "(4.8)" where it means (4.29). (4.34) ends with a stray factor `x`. In the proof of
  4.2.1/4.2.2, `Q = ⌊x/|δq|⌋` is too small by rounding for `c₂x/q ≤ Q/2`; we use the unrounded `Q`
  (`Mof`). Lean's `C/0 = 0` makes `min(A, C/sin²)` vanish where `sin = 0`, so Lemma 4.1.1 is proved
  with the honest summand (`lemma_4_1_1'`, `minA`).
* **Lemma 4.1.3**: the proof does not give its `max(2, …)` form. The lemma is proved by a sharper
  argument (`TrigSums.lean`).
* **(4.40) is inconsistent with its proof.** The statement has `x/q`, `η̂(−δ)` (so
  `min(1, c₀/(2πδ)²)`) and `(m, q) = 1`, the values for the all-`n` version. The proof (p. 67) gives
  `x/2q`, `η̂(−δ/2)` (so `min(1, c₀/(πδ)²)`) and `(m, 2q) = 1`, as in (4.30). `bound_4_40` is the
  corrected form; §6.2.1 copies the uncorrected (4.40), and `typeI1_le` uses the corrected one.
* **Lemma 4.2.3**: the last term of (4.41) uses `log(2ex/c₂)` (the book's step needs `q ≥ 2`).
* **Lemma 4.2.4** (`TypeI2Rest.lean`; all in the `bound_4_5x` docstrings):
  * `c₁ = 1 + |η'|₁/(x/D)` (odd `n`; [H] prints the all-`n` value `2x/D`);
  * the main term (4.50) needs a factor `3/2` (erratum in (4.55));
  * (4.59)–(4.60) as printed is garbled ("`≤ x`" for "`≤ log x`") and its constant could not be
    reproduced. Our (R2) gives `(2√c₀/π)√(2c₂x)(2 + 12 log 5D) + 5c₀/6π²` instead of
    `(25c₀/4π²)(2c₂)^{3/2}√x log x` (similar size);
  * `log⁺(q/2)` for `log(q/2)` (negative at `q = 1`).
* **Lemma 5.2.1** needs `R ≤ W'` (primes `p > W'` coprime to `r ≤ R`); we cap `R`. Statement (ii)
  takes any `1 ≤ R ≤ W'` with `qR²(ν+υ) ≤ 1`, gaining `(φ(q)/q) log R`.
* **(5.52)** must be over odd `m` (the display omits it).
* **(5.51)/(5.54)**: `#(W', W] ≤ W/2 + 1`, not `W/2`. We assume `W ≥ 50000`; the slack
  `1 − 3σ/(1 − σ/3.5) = 0.0054` absorbs the `+1`. We use `σ₀ = 0.30286` (rational) instead of
  `σ = e^{−0.50136}/2`. (5.56) is stated as (i) without and (ii) with the log gain (`R` capped at `W'`),
  which avoids `min(1, ·/log)` with `log ≤ 0`.
* **(5.32) is false for `v = 2`, and so is (5.36)** (Finding 1). Exactly,
  `∫₁⁴ T₂(S) dS/S = 0.53344 > 0.37273 log 4`. We prove `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T + 0.0231`
  (`integral_H2_le`). Consequences: the Type II factor is `0.60428 Λ₀ + 0.0924 + 8ζ³√(x/V)/U`; in the
  first case `B ≤ 0.30214 log t + 0.7468`, and by AM–GM with `√ρ = 1.84332` the constant of Thm 3.1.1
  is `0.8764`; in the second case `B₀ᵃ`, `B₀ᵇ` gain `+0.0231` (the regenerated pieces stay below
  `1.413`).
* **(6.12) understates the μ-sum for odd `q`.** The sum is over `(m, 2q) = 1`, so (2.22) applies with
  modulus `2q` and gives a factor `2q/φ(2q)`; [H] writes `q/φ(q)`. For odd `q`, `2q/φ(2q) = 2q/φ(q)`,
  so the term `(3/2 log q + 2.74) x/φ(q)` of (6.58) should be doubled. This does not break Thm 3.1.1,
  but [H]'s slot-by-slot derivation of `L_{x,t,q}` does not go through as written; we use
  `min(1, a/ℓ)(ℓ + b) ≤ a + b` to move the `b` part into the `x/(δ₀q)` slot.
* **(6.77): Theorem 3.1.1's constant `0.5` is not proved.** The AM–GM step gives
  `log 2/(2√ρ) + (√ρ/2)·0.67506 = 0.81020` (`ρ = 3.397962`), but [H] computes
  `(1/2)(log 2/√ρ + (√ρ/2)·0.67506) = 0.49911`. [H]'s own (6.63) exceeds the stated bound by up to
  about 2.6% (numerically, `q` prime, `δ₀q ~ 10⁵–10⁷`). With the corrected (5.36), ours is `0.8764`.
* **§6.3.2 uses (5.54) outside its range.** Prop 5.2.4 assumes `Q ≥ 3.5W`, but with [H]'s second
  choice `Q = x/U`, (6.38) applies (5.54) for `W` up to `x/U = Q`. Fix: re-approximate with
  `Q₀ ≥ 3.5x/U` (the `Q`-terms of `S_I` are lower order).
* **§6.3.2's case split has a gap.** [H] says that for the new approximation `a'/q'`, either `q' > y`
  or `|δ'| > 8y/q'`, "since otherwise `a'/q'` would already be a valid approximation under the first
  choice". But Thm 3.1.1's hypothesis is an *arbitrary* approximation `a/q` with `q > y`, and two
  approximations can coexist (e.g. `2α = 1/Q`: `1/1` with `δ = x/Q`, and `1/⌊Q⌋`). Fix
  (`SecondChoice.lean`, `SecondBridge.lean`): in that case (`q' ≤ y`, `|δ'| ≤ 8y/q'`), `a'/q'` is an
  approximation for `Q = (3/4)x^{2/3}`, and `1/qq' ≤ |a/q − a'/q'| ≤ 1/qQ + |δ'|/x` forces
  `δ₀'q' ∈ [2y(1 − y/Q), 2y]`, where the first case gives `≈ 59 x^{5/6} ≤ 0.276 x^{5/6}(log x)^{3/2}`.

### Part II (Chs. 7–11)

* **Lemma 9.1.3**: `N⁺ = N/2` holds only for real `χ`. The correct version sums over `χ` and `χ̄`
  (zeros of `L(χ)` with `γ < 0` are conjugates of zeros of `L(χ̄)` with `γ > 0`), which needs bounds
  for `|G_δ|` and `|G_{−δ}|`. Cor 8.0.2 (and our rotation bound) is symmetric in the sign of `δ`.
* **(9.70)**: the second line has `x^{1/2}` for `x^{−1/2}`.
* **(9.94)**: [H]'s derivation drops the factor 2 of the cross term (Finding 3). (9.94) with [H]'s
  constants is proved anyway, by Parseval.
* **Platt's range**: [H, §1.6] says odd conductors up to `2·10⁵`, [H, §9.6] says `3·10⁵` (Finding 2).
* The rest of §9.6 checks out: `(1000/3)·log(10⁸/2π)·6.11·e^{−0.1598·1000/3} = 2.48404·10⁻¹⁹ ≤
  2.485·10⁻¹⁹`; Thm 7.1.4's `q = 1` constants hold with `4.7712·10⁻¹¹`, `251385`.

### Part III (Chs. 12–14)

* **Prop 12.2.4**: two slips (Finding 4). Lemma 12.2.3 has `log Q + 1.312` in the denominator where
  (12.23) needs `log Q + c_E`; (12.15)'s analytic range starts at `4.42·10⁷`, not `4·10⁷`. Our proof
  bounds the quotient against `log Q + c_E` directly and does not use (12.15).
* **Thm 13.2.1 mixes two scales of major arcs**: see "Ch. 13: scale erratum (repair 3)".
* **Prop 11.2.3 ignores that `δ` scales with `w`**: see "Ch. 11: Prop 11.2.3 erratum and Prop 11.2.3′".
* **(14.7)**: the term `5.19 δ₀ r ET_{η₊,δ₀r/2} (|η₊|₁ + ET/2)` is printed as `≤ 0.075272`, but with
  [H]'s own (14.1) (`ET ≤ 1.1405·10⁻⁸`) and (14.3) (`|η₊|₁ ≤ 1.062319`) it is `0.075456`. So (14.7)
  holds with `O*(0.0756)`, not `O*(0.0754)`; the lower end is `8.7052 − 0.0756 = 8.6296`. Our proof of
  (14.7) has a different error analysis (see "Major arcs") and states `8.6296x ≤ ∫ ≤ 8.79x`.
* The opening of Ch. 14 defines `η₁ = 2·1_{[−1/2,1/2]}`, which disagrees with (11.7)/(11.10); we
  use `η₁ = 2·1_{[1/2,1]}`.
* **(14.17)** prints `1.33805·10⁻⁸/κ`; the expression evaluates to `1.338·10⁻⁷/κ` (exponent slip;
  harmless).

### Sources that [H] cites

* **[Ram95, (3.9)] is false** (Finding 5): `∏_p (1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≈ 8.0845 > 8` (the
  product over the primes `< 10⁷` is already `8.07754`). Ramaré's route would give about `7.36` for
  `7.284` in (12.12). Our proof of (12.12) gives `7.04`.
* **Ram14 (hal-02572851), Lemma 2.4**: the first claim `|ℓ(x)| ≤ 0.55/log x` for all `x > 1` fails on
  `x ∈ (≈ 10.6, 11)`: `ℓ(10) = 0.3266` and `0.3266 · log 11 = 0.783`. We use `0.99`.
* **[H, p. 38]** says `|m(x)| ≤ 1/(2√x)` holds for `x ≤ 7727068587`; it fails at `x = 7727068587`
  (Finding 6; not used).

## The explicit formulas: Props 9.3.2, 9.4.2, 9.5.1 (`Explicit/`, `MajorArcs/`)

[H]'s proofs: Prop 9.x = Lemma 9.1.1 (explicit formula: shift `∫_{(3/2)} −L'/L G_δ x^s` to `ℜs = −1/2`)
+ Lemma 9.1.4 (zeros with `|γ| ≤ T₀`, on the line, Cauchy–Schwarz + Mellin–Plancherel) + Lemma 9.1.3
with Cor 8.0.2 (zeros with `|γ| > T₀`). [H] cites `N(T, χ)` with explicit error terms ([Ros41],
[McC84a], [Tru]), the functional equation and digamma bounds. We avoid `N(T)`:

* **Cor 8.0.2** (`MellinRotate.lean`): rotate `t = re^{iθ}`; same exponents `0.1598`, `0.1065`,
  constants `0.892|τ|`, `0.588 y²` per term ([H]: `5.13`, `1.99` for pairs).
* **Growth**: `LGrowth` (`L = s∫S(t)t^{−s−1}`, `|L| ≤ (q+1)|s|/σ` for `σ > 0`); `LGrowthPoly`
  (`|L(z, χ)| ≤ 1400 q⁹(q+1)(|ℑz|+9)(1.25(|ℑz|+1))^{10}` on `−8 ≤ ℜz ≤ 1/4`) via the exact ratio
  `Γ((s+κ)/2)/Γ((1−s+κ)/2) = 2^{1−s}π^{−1/2}Γ(s) sin(π(1−s+κ)/2)` and the rotation bound
  `|Γ(x+iy)| ≤ e^{−φ|y|}Γ(x)/cos^xφ` (`GammaBounds`). Polynomial growth matters: with the
  `e^{π|t|/2}` growth of `LGrowthLeft` alone, Jensen gives `O(T)` zeros per window, useless for
  Lemma 9.1.4.
* **Zeros**: Jensen's formula on discs (`ZeroCount`, `ZeroSums`: windows of height about 10, at most
  `log(B'/0.355)/log(10/6)` zeros each, about 10 times the true density); Landau's partial fractions
  (`Landau`, `LogDerivL`); residues on rectangles (`RectResidue`).
* **Explicit formula** (`ExplicitFormula.explicit_formula`): rectangles `[−1/2, 3/2] × [−T_k, T_k]` at
  good heights, `T_k → ∞` by the decay of `G`. Generic layers: `Datum` (contour identity for any
  entire `f`), `GoodSmoothing`, `ZeroSumGen`. `ζ`: `ZetaGrowth` (`zetaF = (s−1)ζ(s)` entire),
  `ZetaDatum`, `ZetaExplicit` (main term from the datum `s − 1`), `ZetaPoly`, `ZetaBound`.
* **The zero sum must stay `O(√T₀ log qT₀)`** (Lemma 9.1.4's Cauchy–Schwarz + Mellin–Plancherel
  `∫|G(1/2+it)|²dt = 2π|η|₂²`). The trivial `|G(1/2+it)| ≤ |η/√t|₁` gives `O(T₀ log)`, i.e. relative
  errors `~10⁻³` in Thm 7.1.4, which breaks (14.7). We use windows, `sup_window |G| ≤ (1/h)∫|G| +
  ∫|G'|`, Cauchy–Schwarz, and Plancherel in `v = log u`.
* **`η₊`** (Props 9.4.2, 9.5.1): `h_H` is band-limited, so `M₊(s) = ∫_{|ξ|≤100/π} ĝ(ξ)
  G₁(s−1+2πiξ) dξ` (`EtaPlusMellin`); `GoodSmoothing` with `θ = min(θ_δ, 1/200)` avoids an `e^{56}`
  factor. Prop 9.5.1 splits `log n = log x + log(n/x)` into the `ζ` explicit formulas for `η₊²` and
  `η₊² log` (`EtaPlusSq`, `EtaPlusSqBound`; `M(φ₂) = M(φ₁)'` by Cauchy's estimate).
* **Restated results** (weaker constants than [H], all for the ranges the proof uses):
  Cor 7.1.3 `|E| ≤ 10⁻¹⁷ + 4.7·10⁶/(√q √y)` for `y ≥ 10²⁵` ([H]: `2.485·10⁻¹⁹ + (381500/√q + 76)/√y`);
  Thm 7.1.4 for `x ≥ 4.9·10²⁶`: `q = 1`: `10⁻¹⁸ + 6.24·10⁶/√x`, `q ≥ 2`:
  `(7.5·10⁻⁸ + 7.7·10⁶/√x)/√q` (`T₀ = 10⁸/q`; for even `q > 1.25·10⁵`, `T₀ = 200 + 7.5·10⁷/q`);
  Prop 7.1.5 `|E₂| ≤ 2·10⁻⁶ + 366.91/√x` for `x ≥ 4.9·10²⁶` ([H]: `x ≥ 10¹²`).

## Bounds for `ψ` and `θ`

[H, §2.5] quotes them: (2.12), (2.13) from [RS62, (3.23), (3.21)]; (2.14) `ψ(y) ≤ 1.0004y` for
`y ≥ 2·10⁶` from the second table of [RR96, p. 423] plus a computation; (2.15) [RS62, Thm 12];
(2.17) from [RR96] and computations below `10⁷`; (2.19) [RS75, Cor. 2] plus a computation; (5.5)
[RS62, Thm 13]; (C.19) [RS62, Thm 15]. We prove all of them from RH up to `10⁸` (`rh_upto_1e8`, from
`PlattGRH`) and kernel tables. The pieces, by range:

| range | bound | file |
|---|---|---|
| `[12, 10⁶)` | `\|ψ(t) − t\| ≤ √t`, `t − 2.3662√t ≤ θ(t) ≤ t` | `Prelim/SmallPsiTable*.lean` (kernel, trial division) |
| `[10⁶, 5·10⁷)` | `t − 5√t ≤ θ(t) ≤ t + 3√t` | `Prelim/PsiSieve*.lean` (kernel, bit sieve) |
| `[10⁶, 10¹⁷]` | `\|ψ(x) − x\| ≤ cW8(x)√x`, `cW8` from `32.84` to `199` (`≤ 33` up to `10⁸`, `≤ 72` up to `10¹⁵`) | `Explicit/PsiRanges1e8.lean` (Weil windows) |
| `x ≥ 10¹⁷` | `\|ψ(x) − x\| ≤ 4.91·10⁻⁷x + 1145√x + 4.2·10¹⁰` | `Explicit/PsiPlateau1e8.lean` |
| `x ≥ e^{20000}` | `2.1·10⁻¹⁴ x` | `Explicit/PsiRange1.lean` (`psi_range1_8`) |
| `x ≥ e^{35000}` | `0.2 x/log³x` | `Explicit/PsiAsymp.lean` (`psi_asymp8`) |

`psi_two_sided` combines the first and third rows (`cB(n) = 1` below `10⁶`, `cW8(n)` above), and
`theta_explicit` (`|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 10¹²`, `ε_pl = 4.92·10⁻⁷` for
`120 < log n < 20000`) the rest, with `ψ(n) − θ(n) ≤ √n (1.036 + 0.049 log n)`.

### The Weil explicit formula on `[10⁶, 10¹⁷]` (`Explicit/Weil*.lean`, `PsiWeil`, `PsiRange*`)

* **Identity** (`weil_formula`): `Σ_γ h(γ) = h(i/2) + h(−i/2) − g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 +
  ir/2) dr` with `ĝ = h` and `g` supported in `(−log 2, log 2)`, so the prime side vanishes.
  `scripts/weil_check.py` checks it against the first 149 zeros. In Lean: along good heights `T_k`,
  `2π Σ_{ρ ∈ [−½,3/2]×[−T_k,T_k]} m_ρ H_{T₀}(ρ) → 2π H̃(1) + ∫ A(½ + iy) H̃(½ + iy) dy`, with
  `H̃ = H + H(1 − ·)` and `A(s) = −½ log π + ½ψ(s/2)`, for `0 < ℓ ≤ 1`, `m ≥ 2`, `e^{2mℓ} < 2`.
  Files: `WeilTest` (test function), `WeilPrime` (prime side and line shifts), `WeilRect`,
  `WeilSplit`, `WeilLines`, `WeilFormula`; `WeilBridge` matches `ξ`-multiplicities with `zetaF`'s.
* **Test function**: `B(z) = (2 sin(ℓz)/z)^m = (2ℓ sinc(ℓz))^m`, `ℓ = 0.173`, `m = 2`
  (`2mℓ = 0.692 < log 2`), and `H(s) = B(−i(s − ½) − T)²`. Then `H(½ + ir) = B(r − T)² ≥ 0` and
  `|H(σ + it)| ≤ (2e^{ℓ|σ−½|}/|t − T|)^{2m}`. The prime side `∫_{(3/2)} H(s) n^{−s} ds = 0` for `n ≥ 2`,
  by moving the line to `ℜs → ∞`.
* **Why not `N(T)`**: with Jensen-only bounds `|S(T)| ≤ A log T + B`, the bound at `T = 14` allows
  about 25 "phantom" zeros below height 14, each of weight up to 4 in the ψ zero sums, which swamps
  the ideal `Z ≈ 10`. The Weil identity is exact near `T = 0` (`Σ_γ B(γ)² = 0.029`), so phantoms never
  arise.
* **Windows** (`WeilWindow`, `WeilWeights`): per window, `Σ_S m B(γ − T₀)² ≤ Φ(T₀) + Off` (zeros above
  the RH height `H` counted crudely, `|H| ≤ 4^m e^{mℓ} 64/γ⁴`); for a weight `w ≥ 0` with
  `w̄(T) = sup_{|γ−T|≤R} w(γ)`, `w(γ) ≤ (K − tail_R)⁻¹ ∫ w̄(T) B(γ − T)² dT` (`K = ∫ B²`), so
  `Σ_S m w ≤ (K − tail_R)⁻¹ ∫ w̄(T)(Φ(T) + Off) dT`. No Poisson summation is needed.
* **Archimedean part** (`WeilArch`, `WeilPhiBound`): `Re ψ(¼ + iy) ≤ ψ_N(y)` (`re_digamma_le` and
  the recurrence `N` times), `Φ(t) + Off ≤ Φ⁺(t)`.
* **Low zeros** (`ZetaLowZeroFree`): one more integration by parts in `Izeta` gives
  `zetaF(½ + it) ≠ 0` for `|t| < 2.39`, so with RH every zero has `|γ| ≥ 2.39`. The weight is then
  `ĝ(u) = e^{−δ² max(u,t₀)²/2}/max(u, t₀)`, `t₀ = 2.39`: the same on the actual zeros, and
  nonincreasing. Without this, a crude `Φ⁺` puts phantom mass near `γ = 0` and the bound is several
  times the ideal one.
* **Numbers** (`WeilLineSum`, `WeilNumA/B/C`): `‖Mg(½+iγ)‖ ≤ C e^{−δ²γ²/2}/|γ|`,
  `C = e^{δ²/8}(e^{a/2} + e^{b/2})`; zeros `|γ| ≤ Y₁` by the windows, `Y₁ < |γ| ≤ H` by Jensen times
  `e^{−δ²Y₁²/2}`. `ψ_N(y) ≤ log((N+¼)/(N−¾)) + log y + 1/(2y) + 1/(32y²)`; `B_R ≥ (2ℓ)⁴k₀`
  from `sin x ≥ x − x³/6`; four regions of integration (Riemann sums on `[0, R+t₀]` and
  `[R+t₀, R+t₀r^n]`, a closed form up to `1/δ`, Gaussian pieces beyond). Parameters `N = 20`,
  `R = 13`, `n_A = 8`, `r = 5/4`, `n_B = 20`; the Riemann sums are kernel-checked rationals with
  certified logs. Result `line_sum_numH`, for `RHBelow H`, `10⁸ ≤ H ≤ 3·10¹⁰`, `Y₁ + 13 ≤ H/2` and
  `3/Y₁ ≤ δ ≤ 1/208`:
  `Σ_{|γ|≤H} m_ρ‖Mg(ρ)‖ ≤ e^{δ²/8}(e^{a/2}+e^{b/2})(JW(δ) + e^{−δ²Y₁²/2}LWH(H))`,
  `JW(δ) = 0.16385 L² − 0.4271 L + 7.2032 + 57.73δ`, `L = log(1/δ)`; 2–8% above the exact window bound
  (`scripts/weil_chain.py`).
* **Ranges** (`PsiRange`, `PsiRanges1e8`, generated by `scripts/gen_psi_ranges_1e8.py`): one
  `(δ, K, y₀)` per half-decade of `[10⁶, 10¹⁷]` (22 ranges), each error term of
  `psi_upper_WH`/`psi_lower_WH` maximised separately over the range, atoms certified by
  `decide +kernel`. With RH up to `H = 10⁸`: Weil windows for `|γ| ≤ Y₁ = 4.9·10⁷`, Jensen windows on
  `(Y₁, H]` with `e^{−δ²Y₁²/2} LWH(H) ≤ 1142 e^{−δ²Y₁²/2}`, and `TailBH ≤ 10.7 e^{−δ²H²/2}`
  (`TailBH_1e8_le`), so `δ ≥ 7·10⁻⁸`. Then `cW8 ≤ 72` up to `10¹⁴`, and the
  smoothing term makes it grow to `199` at `10¹⁷`. The model's `ε(x) = |ψ(x) − x|/x` with RH to
  `3·10¹⁰` (`scripts/weil_psi_model.py`), the same as at `10⁸` up to `10¹⁴`:

  | `x` | `10⁶` | `10⁷` | `2.7·10⁷` | `10⁸` | `10⁹` | `10¹⁰` | `10¹²` | `10¹⁴` | `10¹⁷` |
  |---|---|---|---|---|---|---|---|---|---|
  | `ε(x)` | `2.8·10⁻²` | `8.6·10⁻³` | `5.3·10⁻³` | `2.8·10⁻³` | `9.3·10⁻⁴` | `3.2·10⁻⁴` | `4.0·10⁻⁵` | `5.0·10⁻⁶` | `2.2·10⁻⁷` |
  | `ε√x` | 27.7 | 27.1 | 27.3 | 27.8 | 29.5 | 32.1 | 39.7 | 49.7 | 68.7 |

  So `|θ(x) − x| < x/log³x` from about `10¹²` (`ε log³x = 0.84` there).

### Above `10¹⁷`: the Gaussian-smoothed explicit formula

* `GaussSmooth`: `φ(u) = Φ((a − log u)/δ) − Φ((b − log u)/δ)` (`Φ` the normal cdf), with the entire
  Mellin transform `M(s) = e^{δ²s²/2}(e^{as} − e^{bs})/s`. `PsiSandwich`: `ψ` between the sums with
  `a = ±K₀δ`.
* Zeros with `|γ| ≤ H` lie on the line (`RHBelow H`) and are counted in Jensen windows
  (`ZetaZeroSums`); zeros above are damped by `e^{−δ²γ²/2}` and, up to a height `Γ`, by the zero-free
  region (`PsiLarge`).
* `rh_upto_1e8` (`ZetaZeroSums`): `RHBelow 10⁸` from `PlattGRH` at `q = 1` (the trivial character
  mod `1` is primitive and its `L`-function is `ζ`). This is the only RH height the proof uses.
* The explicit-formula error bounds take the RH height as a parameter, `RHBelow H` with
  `H ∈ [10⁸, 3·10¹⁰]`: `SsumG_gsm_errH` (Jensen windows), `SsumG_gsm_errWH` (Weil windows for
  `|γ| ≤ Y₁`, centres `|T₀| ≤ H/2`, `Y₁ + 13 ≤ H/2`, `3/Y₁ ≤ δ`; Jensen windows on `(Y₁, H]` with the
  factor `e^{−δ²Y₁²/2}`; the zeros above `H` cost at most `OffC`), `SsumG_gsm_err_zfH` (zero-free
  region on `(H, Γ]`). The proof instantiates them at `H = 10⁸`.
* With RH only up to `10⁸` (`PlattGRH`): `psi_mid8` (`PsiRanges1e8`, `scripts/gen_psi_ranges_1e8.py`;
  `|ψ(x) − x| ≤ cW8(x)√x` on `[10⁶, 10¹⁷]`, `cW8 ≤ 72` up to `10¹⁴`, then up to `199` near `10¹⁷`),
  `psi_plateau8` (`4.91·10⁻⁷ x + 1145√x + 4.2·10¹⁰` from `10¹⁷`), `psi_range1_8` (`2.1·10⁻¹⁴ x` from
  `e^{20000}`) and `psi_asymp8` (`0.2x/log³x` from `e^{35000}`); the last two count the zeros in
  `(10⁸, 3·10¹⁰]` with the zero-free region (`SsumG_gsm_err_zf3H`, `MidB0_8_le`, `MidB0_8_asymp_le`).
  `psi_two_sided` and `theta_explicit` are built from these.
* **Zero-free region** (`ZeroFreeRegion.zero_free`): `β ≤ 1 − 1/(11 log|γ|)` for `|γ| ≥ 10⁸`, without
  the Hadamard product. `XiPartial`: `ξ(s) = s(s−1)Λ₀(s) + 1`, squares at good heights,
  `|ξ'/ξ| = O(log² k)` on their boundary; the symmetry `w ↦ 1 − w` gives a kernel `O(|w|⁻²)`, so
  `ξ'/ξ(s) ≈ Σ_{ρ in square} m_ρ/(s − ρ)` uniformly on discs. `ZeroFree`: Stechkin's lemma
  (`Φ_s(ρ) ≥ κ Φ_{s₁}(ρ)` for `(σ−½)² + (σ₁−½)² ≥ 3/2`), proved algebraically. `ZeroFreeRegion`:
  `18 + 30cos θ + 17cos 2θ + 6cos 3θ + cos 4θ = 8(½ + (3/2)cos θ + cos²θ)² ≥ 0`, `σ = 1 + 0.31/log t`,
  `σ₁ = 1.6181`.
* `psi_plateau8` (`δ = 7/H`, `K₀ = 7`, `y₀ = 10¹⁰`, `H = 10⁸`); `psi_range1_8` (`δ = 1.4·10⁻¹⁵`,
  `K₀ = 9`, `Γ = 6.43·10¹⁵`); `psi_asymp8` (`K₀ = log L + 4`, `Γ = L⁴/5`, `δ = 5(log L + 5)/L⁴`,
  `L = log x`). The `x`-term of `psi_plateau8` is forced by the smoothing width needed to kill the
  zeros above `H`; the `√x`-term is Jensen's zero count, about 8 times the true density.

### The kernel tables

* **`[12, 10⁶)`** (`SmallPsiTable.lean`, data `SmallPsiData1–6.lean`, assembly
  `SmallPsiTableMain.small_table`, generated by `scripts/gen_small_psi_table.py`). The true extremes
  on `[12, 10⁶]` are `(ψ(t) − t)/√t ≤ 0.710`, `(t − ψ(t))/√t ≤ 0.878` and `(t − θ(t))/√t ≤ 2.054`.
  `spf` is trial division by the primes `≤ 1000` (`spf_eq_zero_iff`: it decides primality for
  `2 ≤ n ≤ 10⁶`); `vonMangoldt_of_spf` gives `Λ`; `LQ` holds certified `log q`, `q ≤ 1000`. Checkpoints
  `N_j` (every integer below 1000, then gaps about `0.2√N`); per window, `θ_lo += LL(N_j)`,
  `θ_hi += LH(N_{j+1})` for primes (scaled by `10⁹`), with the log chain
  `LH(b) = LH(a) + ⌈10⁹(b−a)/a⌉`, `LL(b) = LL(a) + ⌊10⁹(b−a)/b⌋` (an exp certificate only at chunk
  starts and below `2·10⁴`). `winOK` holds the four checks, `outer_spec` is the soundness proof.
  14123 windows in chunks of `10⁴` numbers (capped at 250 windows); 81–246 s per data file.
* **`[10⁶, 5·10⁷)`** (`PsiSieve.lean`, data `PsiSieveData1–13.lean`, `PsiSieveMain.lean`, generated by
  `scripts/gen_psi_sieve.py`). Each window `(n, n + W]`, `W ≤ 2¹⁵`, is sieved by the primes `≤ 7100`.
  Each prime's pattern (its multiples below `40000`) is built once per chunk (`pats`); per window it is
  shifted by `(n + 1) mod p` and or-ed in (`orP`, three GMP operations per prime). The primes of the
  window are the set bits of the complement, counted by halving down to 256-bit leaves and clearing
  the lowest set bit there (`pcL`, `popc`); `cnt_spec` proves this is the prime count. The window
  chain `outerT` starts from `SmallTab.stage117`: 3343 windows, 128 chunks, about `2·10⁻⁶` s per
  integer. The data files import each other in a chain (lake builds them one at a time): about
  2.5 min in all, 7.5 GB resident, of which 6.9 GB is the Mathlib import.

### The bounds of [H, §2.5] (`Prelim/LambdaMu.lean`)

* (2.15) `ψ(y) < 1.03883y`: kernel `lcm` check to 700 (`SmallPsi700.lean`), the table (from 663),
  `psi_two_sided` from `10⁶` (`cW8 ≤ 33` up to `10⁸`, `≤ 200` above, beats `0.0388√n`),
  `theta_explicit` above `10¹⁷`. (2.12) via
  `∑ Λ(n)⌊N/n⌋ = log N! ≤ N log N − N + 1 + log N` and Abel summation of `∑ Λ(n){N/n}` over `(N/2, N]`.
* (5.5) `ψ − θ < 1.4262√N`: kernel to `10⁶` (`SmallNonprime.lean`); on `[10⁶, 10¹²)` via
  `ψ − θ ≤ θ(√n) + θ(n^{1/3}) + θ(n^{1/4}) + n^{1/5} log n` (`nonprime_mid`); above via
  `ψ − θ ≤ ψ(√y) + y^{1/3} log y`.
* (2.14), (2.17): the minor arcs use them at `V = ⌊9T/2⌋` for every level `wy ≥ 2.16·10²⁰`, so `V`
  goes down to `2.7·10⁷`. There `|ψ(y) − y| ≤ 31.5√y` gives only `ψ(y) ≤ 1.0064y` and
  `∑ Λ(n)n < 1.022y²/2` (`psi_mul_of`, partial summation with five ranges of `c`), stated for
  `y ≥ 2.5·10⁷` (`sum_vonMangoldt_le_10064`, `sum_vonMangoldt_mul_lt_1022`). [H]'s `1.0004`, `1.0008`
  are not reachable this way below about `10⁹`. Helfgott proves them (`Prelim/PsiHelfgott.lean`, from
  RSBounds: PsiCert `|ψ(x) − x| ≤ 0.8√x` on `[1500, 10¹⁰]`, kernel-checked, and RS75's
  `0.00020211 x` above `e²³`), and `TypeI2Large`, `TypeI2Sum` use his bounds. Their statements, and
  `FirstChoiceTypeI2*`, still carry `1.0064` and `1.022`: propagating `1.0004`, `1.0008` through the
  Type I numerics is open (it needs a build to regenerate the constants).
* (2.13): summation by parts from `X = 10⁴` with `|ψ(n) − n| ≤ cPsi(n)√n` (the tables below `5·10⁷`,
  `psi_two_sided` above) and `theta_explicit` above `10¹⁷`; kernel for `N ≤ 10⁴`
  (`SmallMertensLower.lean`); `log(3/√2) ≥ 0.74`.
* (2.19) `∑_{y/2<p≤y} (log p)² ≤ ½ y log y` for `y ≥ 2·10⁶`: one Abel-summation lemma `logsq_abel`,
  applied with the sieve table below `5·10⁷`, `cB` on `[4.6·10⁷, 2·10¹²]` and `theta_explicit` above.
  The minor arcs use it at `W ≥ V ≥ 2·10⁶` (`V₂ = ⌊T/3⌋`, second choice), so the Type II theorems
  assume `2·10⁶ ≤ V`. Below `2·10⁶` the `c√y` bounds are too weak for the constant `½` (with
  `c ≈ 33`, it closes analytically only from about `4·10⁷`; hence the sieve).
* (2.16) is only claimed for `y > 663` (it fails at `y = 3`); it is not used.

### Mertens' product, Lemma C.2.2 (`Prelim/MertensProduct.lean`)

* PNT+'s Mertens file (ported to `Prelim/PNTMertens.lean`) gives
  `∑_{d≤x} Λ(d)/(d log d) = log log x + γ + E₂Λ(x)`. With
  `log ∏ p/(p−1) ≤ ∑ Λ(d)/(d log d) + 7/(6⌊√x⌋)` this gives [RS62, Thm 15]
  `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`.
* `|E₂Λ(x)| ≤ 2D/log x` for `x ≥ 10¹²` (`F_large`) needs `|E₁Λ(t) − E₁Λ(x)| ≤ D` for all `t ≥ x`.
  Summation by parts against the pointwise `θ` bound would integrate its plateau `ε_pl` over
  `log(t/x)` up to `20000`. `E1_var` instead integrates the explicit formula for
  `Ψ(y) = Σ Λ(n) gsm(n/y)` (window `[1, e²]`, `δ = 8·10⁻⁸`, RH up to `10⁸`) against `dy/y²`
  (`Prelim/MertensWindow.lean`):
  `∫₀^∞ (E₁Λ(Y₂v) − E₁Λ(Y₁v)) gsm(v) dv = ∫_{Y₁}^{Y₂} (Ψ(y) − M y)/y² dy`, `M = ∫₀^∞ gsm`. The two edge
  terms `∫ |E₁Λ(Yv) − E₁Λ(Y)| gsm(v) dv` use `E1_local` (`A + B log v`, from `theta_explicit`) for
  `v > 1` and the Chernoff bound `gsm(v) ≤ e^{1/2} v^{1/δ}` below `v = 1`. The zeros enter through
  `ErrGH ≤ 4247√y + 3·10⁻¹³ y` (those above `10⁸` are damped by `e^{−δ²γ²/2} ≤ e^{−32}`), and the
  pointwise errors only at `x` and `t`: `D(x) = 1443/√x + 13/x + 16/log³x + 8.5·10⁻⁶` while
  `log x < 20000` (`8.4·10⁻⁶` of it from `ε_pl` in `E1_local`); beyond `e^{20000}` (`ε_pl = 0`)
  summation by parts (`E1_diff`). `F_large` uses `η L² ≤ 0.58` of its budget `0.6174`;
  `|E₂Λ(10¹⁸)| ≤ 1.2·10⁻⁵`.
* `|E₂Λ(M)|` on `[10⁵, 10¹²)`: the variation of `∑ Λ(n)/(n log n) − log log n` up to `10¹⁸`
  (`E2_var`: summation by parts against `ψ(n) − n` with weight `1/(n log n)`; `E2_le_bin`), plus
  `|E₂Λ(10¹⁸)|`. The `ψ`-errors above `10¹⁵` (`c ≤ 200` up to `10¹⁷`, then `ε_pl`) contribute
  `≤ 2.93·10⁻⁴` (`tail_sum_le`). This gives `|E₂Λ(M)| ≤ 0.003` already at `M = 10⁵`. `F_mid` covers
  `[10⁵, 10¹²)` in 7 bins (worst `2.470 < 2.5`); `F_large` starts at `10¹²`; `e^η ≤ 1 + 1.02η`. With `c ≈ 33` from
  `10⁶`, `F_mid` would fail on `[10⁶, 5·10⁶]` (the `log θ(x)` term alone uses most of the budget),
  which is why it needs the sieve table.
* Kernel for primes `≤ 10⁵` (`SmallMertensProd.lean`, 5.5 min; tight only at `x = 23`, margin
  `2.4·10⁻⁷`): `log θ = log m + log(θ/m)` with an integer `m` advanced with `θ` and an artanh series;
  `e^γ` from a 22-term Taylor sum.
* Lemma C.2.2 (`div_totient_lt`): the exchange argument (`Finset.induction_on_max`,
  `Nat.nth_lt_of_lt_count`) and monotonicity of `t ↦ e^γ t + c/t` for `t ≥ log 4`.

## Sums of `μ`: (2.21)–(2.24)

* **(2.21)** `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x`, `x ≥ 11815` (`RamareMoebius`, `ramare_moebius`) is
  proved from `PlattGRH` (`ramareMoebius_of_plattGRH`) by Helfgott's formalization of
  `mobius003.tex` (RSBounds, `vendor/rsbounds/RSBounds/Moebius003/`), which follows Ramaré's
  recursive idea with inputs Schoenfeld's (5.6b*), PsiCert and kernel-checked `M` bounds
  (`MoebiusCert`). `MoebiusBound.lean` derives the weaker `0.55/(log x − 0.7521)` for `x ≥ 10¹⁰`
  from it. Our earlier route (Schoenfeld's induction with only `PlattGRH`'s `ψ` bounds, which gave
  `|m(x)| log x ≤ 0.092` at worst) is at commit `23b2d68` in `main`'s history.
* **(2.22) with `2.8`** (for [H]'s `4/5`, [Ramb]): Ramaré's Liouville route (Ram14 = hal-02572851;
  `Liouville.lean`, `LiouvilleBound.lean`).
  1. `λ = sq ∗ μ`, `μ = μ_sq ∗ λ`, `λχ_q = d_q ∗ λ`, and the `1/n`-weighted partial sums: Lemmas 2.3,
     3.2, 2.5 of Ram14 for every `q`.
  2. `|ℓ(z)| log z ≤ 0.99` for all `z > 1`: the kernel for `z ≤ 10⁵` (`SmallLiouville.lean`, max
     `0.7831` at `z → 11⁻`), and for `z ≥ 10⁵`, `ℓ(z) = ∑_{u²≤z} m(z/u²)/u²` with Ramaré for
     `z/u² ≥ 11815` (`log z/log(z/u²) ≤ 1 + (2/9) log u`) and the kernel's `|m(y)| ≤ √(2/y)` below.
     Then `|ℓ_q(x)| log(x/q) ≤ 0.99 q/φ(q)` and `|ℓ_q| ≤ 5/3`.
  3. `|m_q(x)| ≤ (q/φ(q)) ∑_{u² ≤ x} |μ(u)|/u² β(log(x/q), u)`, `β(y, u) = min(5/3, 0.99/(y − 2 log u))`;
     `y·∑ ≤ 2.8` on `[2.8, 80)` on 17 kernel-checked intervals (`SmallCGrid.lean`), analytically for
     `y ≥ 80`, and `|m_q| ≤ 1` for `y ≤ 2.8`.

  Downstream, `muBound` uses `2.8`; the `x/(δ₀φ(q))` slot of Thm 3.1.1 gets `3.8 + 2.8 + 1.22 = 7.82`,
  [H]'s statement.
* **(2.23)**, elementary (`MoebiusLog.lean`): `|∑_{(n,q)=1} μ(n)/n log(x/n)| ≤ q/φ(q) + 2.67`, from
  `∑_{(n,q)=1} μ(n)/n H(x/n) = ∑_{k≤x, rad k | q} 1/k ∈ [1, q/φ(q)]` and Mathlib's
  `eulerMascheroniSeq` bounds ([H]: `1.00303 q/φ(q)` from [Ramb]). Downstream: `(log t + 2.96)·2x/t`
  in `typeI1_first`.
* **(2.24)** for `x < 11815`: kernel (`SmallMoebius.lean`, `(k+1) m(k)² ≤ 2`).
* (2.20) is proved elementarily (`MoebiusCoprime.lean`).

## Ramaré's (12.12) and `c_E` (`Prelim/Ramare*.lean`)

* `g_d = h_d ∗ v` with `v = [odd]/n`, `h_d = g_d ∗ (μ v)`, and `h_d(p^e) = 0` for `e ≥ 3`.
  `GqP d R = (log R/2 + C)∑' h_d − ½∑' h_d log a + ∑' h_d(a) Fo(R/a)` (`GqP_decomp`), with
  `|Fo(x)| x^{1/3} ≤ 0.64` (`Fo_bound`).
* `∑ |h_d(a)| a^{1/3} ≤ 11 f₁(d)` (`sum_wD_le`): a generated table `⌈10⁴ p^{1/3}⌉` for odd `p ≤ 1000`, a
  kernel product `≤ 7.2863`, and the tail `∏_{p>1000} ≤ 1.494`. Error `0.64·11 = 7.04` (for [H]'s
  `7.284`).
* `c_E ∈ [1.3325822734, 1.3325822894]` (`cR_bounds`): `∑ Λ(n)/n² = (∑ log n/n²)/ζ(2)` from
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`; `∑ log n/n² = 2X + log 2·ζ(2)`, the tail of `X`
  bracketed by convexity; a kernel walk (`RamareWalk.lean`: 10 fields at `D = 10³⁰`, 24 chunks to
  `n = 20001`, 125 s). Generators: `scripts/ramare/gen_bound.py`, `gen_walk_num.py`.

## [MV73, Lemmas 7, 8] and the large sieves (`Prelim/`)

* **Lemma 7** `G(r) ≥ log r + 1.07` (`r ≥ 6`): (12.12) for `r ≥ 21400`; below, a DFS over subsets of
  primes gives a lower bound (`SmallG.lean`, 23 s). `MVLemma7.lean` also proves the asymptotic
  `|G(N) − log N − κ| ≤ (2 + 3/e + γ) P N^{−1/3}` (`GS_asymp`, Rankin with `σ = 2/3`,
  `P = ∑|h(d)|d^{−2/3} ≤ 9.32`); the main theorems do not use it.
* **Lemma 8**: Abel summation against Lemma 7 for `R ≥ 1000`, comparing `∑ f(r) log(r/(r−1))` with
  `Φ(t) = log(t/(R+t))`; a weighted DFS lower bound for `6 ≤ R < 1000` (`SmallW.lean`); exact
  rationals for `R < 6`.
* **Large sieves** (`LargeSieveMV.lean`; files `Shan`, `HilbertIdentity`, `HilbertReal`, `HilbertCsc`,
  `LargeSieveMVProof`): constants `4.66` (weighted, real line) and `4.66/π ≤ 1.4834 ≤ 3/2` (csc).
  Sources: Yangjit, arXiv:2203.14950 (Shan's spacing lemma, Preissmann's Cauchy–Schwarz argument);
  Preissmann–Lévêque, arXiv:1303.1085, Lemma 5(b) (the eigenvector identity).
  1. Shan's lemma: `∑_{k≠l} δ_k/|λ_k−λ_l|^σ ≤ 2ζ(σ)/δ_l^{σ−1}`.
  2. Eigenvector identity: for `H = [c_m c_n/(λ_m−λ_n)]` and `Hu = iμu`, `μ² ≤ S + 2T`.
  3. In place of Preissmann's Lemme 6 (not available to us):
     `∑_{k≠l,m} δ_k/(a_k² b_k²) ≤ (1/D²)[(π²/3)(1/δ_l+1/δ_m) − (δ_l+δ_m)/D² + (2/D)(F_l+F_m)]`, with
     `F_l = ∑_{between} δ_k/|a_k| ≤ (1 − ½log 2) + log(D/δ_l)` (each step from `artanh t ≥ t`). Hence
     `κ = 1.3356`, `C(½) ≤ K + √(K² + π⁴/45) = 9.028` (`K = κπ²/3`), `C₁ = √(π²/3 + 2C(½)) = 4.620 < 3π/2`.
  4. Periodization to the circle (Cesàro kernel → `π csc πx`).
  5. Duality: `N + δ⁻¹`, resp. weights `(N + (3/2)δ_r⁻¹)⁻¹`. For `N − 1 + δ⁻¹`, apply the bound to
     `n ↦ kn` at the points `(α_r + j)/k` and let `k → ∞`.

## Type I sums (Ch. 4, §6.2)

How the Lemma 4.2.2 proof is organised (reused for 4.2.3, 4.2.4):
* `typeI = mainPart + restPart` (`typeI_eq_main_add_rest`): `mainPart` is `q ∣ m ≤ M`, done by Poisson
  (`Todd_main`); `restPart` by `|T_{m,∘}|` bounds (`norm_Todd_le_minA`, `norm_Todd_le_min_sin`) and
  Lemmas 4.1.1'/4.1.2/4.1.3 applied to `2α ≈ a/q + δ/x` (`approx_of` with a *real* `Q = x/|δq|`).
* Case (a) uses `second_approx` (Dirichlet via `Real.exists_rat_abs_sub_le_and_den_le`,
  `q' ≥ εQ/(1+ε)`), `sum_A1` and `sum_R3'` with `(a', q')`. The proof gives (4.32) with the unrounded
  `x/|δq|` where [H] has `min(⌊x/|δq|⌋ + 1, 2D)` (never larger).
* Index sums are over `ℤ` (`Ioc ⌊y₁⌋ ⌊y₂⌋`, `Tn α x n = ‖Todd α x n.toNat‖`), to match §4.1.

Lemma 4.2.4 (`TypeI2Rest.lean`): `typeI2 = ∑_{a odd} c(a) T_{a,∘}`, `|c(a)| ≤ log a`. The rest has
weights `log m`; on each block of length `q` it uses `log` of the block's upper end
(`sum_log_mul_le_blocks`), with the per-block bounds `block_R2`/`block_R3` from Lemma 4.2.2. The
leading terms are [H]'s; the `q`- and `x/Q₀`-terms have the same shape with cruder constants.
Hypotheses `x ≥ 10`, `UV ≥ 2` (for [H]'s `x ≥ e²c₂/2`); [H]'s `UV + (19/18)Q₀ ≤ x/5.6` is not needed.

§6.2 (`TypeITotal`, `TypeI2Total`, `GcdSums`, `TypeI2Sum`, `TypeI2Large`): (6.5)–(6.9), with
`∑ Λ(v)(q,v)/v ≤ log N + log q` and `∑ Λ(v) v (q,v) ≤ ∑ Λ(v) v + N q log q` via
`(q,v) = ∑_{d|(q,v)} φ(d)`. Differences from [H]: `U²V log V` → `U²V log q`; the `Q log(U/(q/2))` term
→ `Q (log⁺(2U/q) + 1/e)`; in (6.14) the `UV/e` term carries a factor `1 + V/Q`, and the coefficients
are kept as exact expressions in `c₊`.

## Type II sums (Ch. 5, §6.2)

* §5.2 (`TypeII.lean`, `v = 2`, i.e. `m` odd): Montgomery's inequality (`ω(p) = 1`: Ramanujan sum
  `c_r(n) = μ(r)` + Cauchy–Schwarz), (5.41) via `rad`/σ-multiplicativity, Lemmas 5.2.1, 5.2.3,
  Prop 5.2.4, with the sharp large sieves above (the `S₂` side has little slack, so a weaker
  large sieve, e.g. Gallagher's, would not do).
* §5.1 (`SqfreeCount.lean`, `S1Lemma.lean`, `TypeIIS1.lean`): the reduction (5.7)–(5.8)
  (`S1_eq`); Lemma 5.1.1 for `v = 2` (main-term constant `(6/π²)P/σ(P)` from
  `L(χ₀μ, 2) = 1/L(χ₀, 2)`); (5.19) (`integral_g2`); (5.34) `S1_bound` (assumes `U ≥ 1`). `H₂` is
  defined with the exact triple sum `T₂` in place of [H]'s computable bound `G₂ ≥ T₂`, and with
  `max(T₂, 0)`. `f(X) ≤ 1.27X` ([H, p. 83]) by the kernel for `⌊X⌋ < 200` (`SmallFsq.lean`).
* **(5.31) `T₂(S) ≤ 0.37273` for `S ≥ 16`** (`T2Bound.lean`):
  * `SmallG2.lean` (kernel, 54 s) walks `n ≤ 10⁴` with `F(r) = μ(r)⌊10³⁰/σ(r)⌋` for odd `r`, a binary
    trie of `Ã_d(n) = ∑_{r≤n, d∣r} F(r)`, and `G̃(n) = ∑_d μ(d) Ã_d(n)²`, updated at odd squarefree `n`
    through its divisors. For `16 ≤ S < 700`, `T₂(S) = a(n) − a(n/2)/2 + (c(n) − c(n/2))/S` on
    `[n, n+1)` (`T2_eq_ac`); both `a` and `c` change only at odd `k`, so the kernel needs `Δg₂` at
    squarefree divisors only (max `0.3712486` at `S = 16`). For `700 ≤ S < 10⁴`, `¼ I(S) + J(S)/S`.
  * `G2Tail.lean`: `∫_{10⁴}^S |g₂|/y ≤ 0.0045`. Pointwise `|g₂(y)| ≤ ∑_d f(d)² S_d(N/d)²` with
    `S_d = ∑_a H_d(a) m(·/a)`; Cauchy–Schwarz with weights `H_d(a) λ(da)` gives
    `∫_X^S |g₂|/y ≤ ∑_d f(d)² (∑_a H_d(a) λ(da)) (∑_a H_d(a) V(X/(da))/λ(da))`,
    `V(Y) = ∫_Y^∞ m(⌊t⌋)²/t`; with `λ ≈ √V` this is Minkowski's inequality. `V(k)` for `k ≤ 10⁴`
    (`G2TailNum.lean`, kernel 82 s) from `m(j)`, `j < 11815`, and Ramaré beyond. The sum over
    `d > 10⁴` and `a > 10⁴/d` uses `∏_{p>2} p²/(p²−1) ≤ π²/8`; the slack there matters (with `1.27` the
    double sum would be `0.0158`).
  * `T₂(S) ≤ 0.3605763 + 0.000922 + (5/4)·0.0045 ≤ 0.3672` for `S ≥ 10⁴`.
  * The pointwise route (Lemma 5.1.2, `G2Bound.lean`, proved but unused) cannot reach `10⁴`: even with
    exact `m(k)` it gives about `36/x`; the mean-square route gains `m(k)²` on average.
* (5.36) corrected and (5.37) (`H2Bound.lean`): `T₂ = α_n + β_n/S` on `[n, n+1)`, kernel tables for
  `n ≤ 15`, the integral by FTC.
* §6.2: `typeII_637` ((6.37), `q ≤ V/2e`) and `typeII_640` ((6.40), `|δ| ≥ 8`). Main terms exactly
  [H]'s `x/√(2φ) √((Λ₀+Φ)(0.60428Λ₀ + 0.0924 + 8κ₀ζ³√(x/V)/U))`; secondary terms cruder
  (`4√(κ₁qx/2φ)(…)` for [H]'s `√2κ₂√(q/φ)(1+1.15√…)x/√U`, and `8·1.4262 x√(κ₁(1/2+1/U))/√V` for
  `κ₉x/√V`), with `κ₁ = 2/π² + κ₀ζ³√(x/V)/U` kept exact.

## Theorem 3.1.1 (§6.3; `PointwiseBound.lean`)

* **First case** `q ≤ x^{1/3}/6` (`FirstChoice*.lean`, `T = x^{1/3}`, `t = δ₀q`): `U = ⌊T²/(9√t)⌋`,
  `V = ⌊9T/2⌋`, `Q = 3T²/4`.
  * Type II (`typeII_first`): `x/√(δ₀φ) √(C_{x,t}(log t + 0.002) + log(4t)/2) √(0.30214 log t + 0.7468)
    + 3.2 x^{5/6}`, with `C_{x,t} ≤ 0.1 log t + 0.14`; AM–GM (6.77) with `√ρ = 1.84332` gives
    `R_{x,t} log t + 0.8764`.
  * Type I: `typeI1_first`: `3.8·2x/(δ₀φ) + (log t + 2.96)·2x/t + 0.014 x^{5/6}`; `typeI2_first`:
    `2.5257 x/√t + 2.8·2x/(δ₀φ) + (15.267 log t + 21.46)·2x/t + 0.556 x^{5/6}` (`ε = 0.07` in (6.14)).
  * Result (`theorem_3_1_1_first`): `((R log t + 0.8764)/√(δ₀φ) + 2.526/√t + L_{x,t,q}·2/t) x +
    3.8 x^{5/6}` with [H]'s `L = (q/φ)(13/4 log t + 7.82) + 13.66 log t + 37.55`; the `x/(δ₀q)` terms fit
    into the `13.66 log t + 37.55` slot plus the unused part of the `x/(δ₀φ)` slot.
* **Second case** `q > x^{1/3}/6` (`Second*.lean`): `U = ⌊1225T⌋`, `V = ⌊T/3⌋`, `Q₀ = T²/349 ≥ 3.5x/U`,
  `θ = 8` in (6.38) and (6.41). All Type II cases are `≤ 1.413 L^{3/2} T^{5/2}` (`L = log T`; target
  `0.276·3√3 = 1.4341`), and Type I is `≤ (0.0717 L² + 3199.9 L + 8471.0) T²`. Result: [H]'s
  `0.276 x^{5/6}(log x)^{3/2} + 1234 x^{2/3} log x`. Piece generators: `scripts/gen_a1_pieces.py`,
  `scripts/gen_b_pieces.py` (exact rational checks first); Taylor exp/log bounds `log_le_num`,
  `le_log_num` (`SecondNumerics.lean`).
* With `c₀ = 32` (below): `√c₀ ∈ [5.6568, 5.6569]`, `c₂ ∈ [0.6664, 0.6665]`, `2√c₀/π ≤ 3.6015`.

## Ch. 11: Prop 11.2.3 erratum and Prop 11.2.3′

[H]'s proof writes `S_{η_*}(α,x) = ∫ S_{η₂}(α, wx) φ(w) dw/w` (11.9) and applies Thm 3.1.1 to each
`S_{η₂}(α, wx)` with the same `r = max(1, |δ|/8) q`. At scale `wx`, though, `2α = a/q + δ_w/(wx)` with
**`δ_w = wδ`**:
* for `w < 1` the parameter is `r_w = max(1, w|δ|/8) q ≤ r`, and `g_{wx}(r_w)` is *weaker* than the
  `g_{wx}(r)` [H] uses (`g` is decreasing);
* for `w > 1`, Thm 3.1.1's hypothesis `|δ_w/(wx)| ≤ 1/(q Q_{wx})` does not follow from
  `|δ/x| ≤ 1/(q Q_x)`, because `Q_{wx} > Q_x`. It holds for `w ≤ ((4/3)x^{1/3}/(8r))^{3/2}`, which is
  `≥ 94` when `r ≤ r₁ = (3/8)x^{4/15}`, `x ≥ 10²⁵`.

Helfgott found this erratum himself around 2016 and reported it. The statement seems to survive: for
`|δ| ≤ 8`, `r_w = q = r`; for `|δ| > 8`, `r_w ≥ w r`, and the gain for `w > 1` outweighs the loss for
`w < 1` (`∫ g_{wy,1}(wr) φ(w) dw ≤ 0.89 ∫ g_{wy,1}(r) φ(w) dw` in `scripts/prop_11_2_3_check.py`,
`r₀ ≤ r ≤ r₁`, `y ∈ [10²⁵, 10¹⁰⁰]`). We do not use that. We use Prop 11.2.3′ (`Prop1123b.lean`):
off `𝔐_{8,n}(y)`, take a **fresh Dirichlet approximation at each scale `wy`**. Since
`𝔐_{8,r}(wy) ⊆ 𝔐_{8,r}(y)` for `w ≥ 1` and `⊆ 𝔐_{8,r/w}(y)` for `w < 1`, this gives `r_w ≥ min(1,w) n`,
and Thm 3.1.1 at scale `wy` gives `max(g_{wy}(min(1,w)n), h(wy))`. The first case always has
`r_w ≤ (wy)^{1/3}/6`, so `gx_antitoneOn` (`GMono.lean`) applies. The majorant is crude:
`g_{wy}(min(1,w)n) ≤ max(1, 1/w) g_y(n)`, `h(wy) ≤ max(1, 1/w) h(y)`, costing
`∫_{w₀}^∞ max(1, 1/w) φ ≤ 1.398` (`PhiIntegrals.lean`); with `w₀ = 670/n`,
`ghatY(y, n) = 1.398·max(g_y(n), h(y)) + 17(670/n)³/3` (`LinftyLevels.norm_S_etaStar_le_ghat`). A
cleaner repair would follow the `r_w ≥ wr` analysis above.

`Prop1123.lean` has Prop 11.2.3 in corrected form with any integrable majorant `G(w) ≥
g_{wy}(min(1,w) r)`, and the trivial bound `17z` from Chebyshev's `ψ ≤ (log 4 + 4)x`.

## Ch. 12: the large sieve for primes

* **Prop 12.1.2** (`LargeSieveProof.lean`): Bombieri's identity in the form
  `φ(q) Σ_b^* |S(b/q+β)|² = Σ_{Ψ mod L, cond Ψ ∣ q} w(q, cond Ψ) |S_{Ψ⁻¹}(β)|²` (Parseval over
  characters, `gaussSum_mulShift_eq`, `τ(χ↑) = μ(r)χ(r)τ(χ)`, `|τ(χ)|² = N` for primitive `χ`, and the
  lift to one modulus `L = ∏_{q ≤ 2Q} q`, which avoids dependent types); `weight_sum`; periodization,
  covering and Farey disjointness at level `Q`. **`δ₀ ≥ 2` instead of [H]'s `δ₀ ≥ 1`**: primes
  `n > √x` must be coprime to every modulus `q ≤ 2Q = √(2x/δ₀)`, which needs `2Q ≤ √x` ([H] uses `δ₀ = 8`).
* **Prop 12.2.4 with `c₊ = 2`** ([H]: `1.36`). [H]'s argument covers `q ≥ 2.2·10¹⁰` (`star_suffices`,
  `regionL`, `regionS`, `large_q_hS`: `λ⁷ ≤ (103/120)⁹ q²` by exchange and primorial induction); for
  smaller `q` [H] needs a computation over 88 million `(q, n)`. Weakening the constant alone leaves
  about 24 million checks; what works is a structural reduction, which `c₊ = 2` makes possible:
  * `Φ(q, n, L) = (q/φ) G_q(n) − log n − c − S_q + 0.1768 (q/φ) f₁ n^{−1/3} − (0.3414 (L − S_q) + 0.6674177)`;
    `Φ(q, ⌊R⌋, L) ≤ 0` with `L ≤ log sq` gives Prop 12.2.4 at `R` (`checkC2_suffices`, `LSQuot7`;
    `θ ≤ 0.6586`).
  * **Removing a prime** (`LSQuotRed`): for squarefree `q < 2.2·10¹⁰` with largest prime `p ≥ 17`,
    `G_{q/p}(n) = G_q(n) + G_q(n/p)/(p − 1)` and `(q/φ(q)) G_q(x) ≥ G(x) ≥ log x` give
    `(1 − 1/p) Φ(q) ≤ Φ(q/p) + Δ(p)` with `Δ(p) ≤ −0.12`. `G(x) ≥ log x`: Ramaré for `x ≥ 200`, a kernel
    walk `H_n ≤ G(n)` below. So `Φ(q) ≤ 0` follows from `Φ(A) ≤ 0` for `A ∣ 30030` (radicals handle
    non-squarefree `q`).
  * **The divisors of `30030`, `n ≥ 4`** (`LSQuot8`, `LSQuot8g`, generated by `scripts/gen_lsq_base.py`):
    Ramaré for `n ≥ 2600`; below, a kernel walk per `A` (trial-division `φ`, `⌈10¹²/φ(r)⌉`
    accumulators, 82 blocks). Margin `≥ 0.33`; 90 s.
  * **`n ≤ 3`** (`LSQuot9`): `G_q(n)` depends only on `2 ∣ q`, `3 ∣ q`; the primes `≥ 5` (at most 8) are
    bounded by exchange; 72 rational checks, worst `−0.051`.
  * Downstream: `cL n = log 2(n+1) + 2` in Cor 12.2.5 and Thm 13.2.1; `NumericsAsymp` has
    `cL 150000 ≤ 14.61155`.

## Ch. 13: scale erratum (repair 3)

Prop 13.1.2 combines, **for one family of arcs** `𝔐_{δ₀,r}` ((10.5), defined with a parameter `x`), an
ℓ² bound `∫_{𝔐_{δ₀,r+1}} |S₁|² ≤ H(r) Σ|aₙ|²` (13.4) and an ℓ∞ bound `|S₂(α)| ≤ g(r)` off
`𝔐_{δ₀,r}` (13.5). In the proof of Thm 13.2.1 (pp. 249–252):
* the ℓ² input `H(r) = (log(r+1) + c⁺)/(log √x + c⁻)` comes from Cor 12.2.5 (12.42) with arcs at
  **scale `x`** (`c⁻ = 0.6394` is `log 2Q + c_E` with `Q = √(x/16)`); `J` (14.7), the major arcs (14.27)
  and (14.17) are also at scale `x`;
* the ℓ∞ input (13.14)–(13.17) is derived only for `α` outside the arcs at **scale `y = x/κ`**: "Let
  α ∉ 𝔐_{8,r} … where y is used instead of x to define 𝔐_{8,r}" (p. 249; arXiv:1312.7748, p. 48, has
  the same sentence).

The `y`-arcs are `κ = 49` times wider. For `α` outside the `x`-arcs but inside the `y`-arcs, Thm 3.1.1
at scale `y` gives only `r_α ≥ max(q, r/κ)`; e.g. for `q = 1` just outside the `x`-arc at level `r₀`,
`r_α ≈ 3061` and the bound is about `7 g(r₀)`. Two obvious repairs fail
(`scripts/minor_arc_scale_check.py`): everything at scale `y` costs `log 7` in `c⁻` and lands above
[H]'s major-arc constant `1.058259` (and needs major arcs beyond Thm 7.1.4's range); everything at
scale `x`, with Part II on the gap, fails because the gap at levels `r > 300000` contains moduli
beyond Platt's range, where only `g(q) ≥ g(300000)` is available.

**Repair 3** (`Thm1321.thm_13_2_1_repaired`, `MinorTotal.lean`; model
`scripts/minor_arc_y_scale_repair.py`):
* Prop 13.1.2 with the family `M_{r₀} = 𝔐_{8,r₀}(x)`, `M_n = 𝔐_{8,n}(y) = 𝔐_{392,n}(x)` for `n > r₀`
  (nested). The base term keeps `I₀ ≥ (√J − √E)²` over `𝔐_{8,r₀}(x)`.
* ℓ² from (12.42) with `δ₀ = 392`.
* ℓ∞ off `𝔐_{8,n}(y)` from Prop 11.2.3′ (above).
* **Levels up to `r₂ ≈ x^{0.3}`** (the range of (12.42)), not [H]'s `r₁ = (3/8)y^{4/15} ≈ 10⁶`; this
  shrinks the tail (14.43) from about `0.30` to `0.12`.
* The base gap `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)` is covered by [H, Cor 7.1.3], whose range `q ≤ 300000`,
  `|δ| ≤ 1.2·10⁶/q` is exactly `𝔐_{8,r₀}(y)`; in the gap `|δ| ≥ 12245/q`, so `|S_{η_*}| ≤ 0.0121 y`
  (`BaseGap2.lean`).

**Numerics** (`numerics_M`): `Mexpr x r₂ ≤ 1.037`, where `Mexpr` bounds `Z₁/(x · x/κ)` with
`r₂ = min((2√(x/784))^{0.6}/2 − 1, √(x/784)/20000)`. Cells `y ∈ [Y_k, Y_{k+1}]` for
`x ∈ [4.9·10²⁶, 4.9·10¹⁰¹]` with blocks of ratio `1.25` in the level (`NumericsCells.lean`, generated by
`scripts/gen_cells.py`; worst cell `1.00717`, at the bottom), and `NumericsAsymp.lean` beyond. Then
`S_{η₊} = S₁ + S₂` (`S₁`: primes `> √x`) with `|a + b|² ≤ (1+t)|a|² + (1+1/t)|b|²`, `I₀ ≥ 8.6294x`, and
(14.28) with `8·10⁻¹¹` give `(1.0005·1.037 + 2001·22.75·8·10⁻¹¹) ≤ 1.0376` (`t = 5·10⁻⁴`).

## Major arcs: (14.7) and (14.27) (`MajorArcs/`)

* **(14.7)** (`L2Major.lean`): [H, Lemma 10.3.1] for `η₊` with a Cauchy–Schwarz-free error analysis:
  each pointwise square is split as `|u + v|² = (1 ± t)|u|² + O((1 + 1/t)|v|²)`, `t = 10⁻⁴`. Steps:
  arcs (`ArcsEq`); the `η◦` tail (`EtaCirc`: `∫_{|δ|>T} |η̂◦|² ≤ 98/(2πT)⁴`, two integrations by parts);
  `‖η₊ − η◦‖₂` (`HHFourier`, `HHFourier2`: `h_H(eᵘ) = ∫_{|ξ|≤H/2π} ĝ(ξ)e(ξu)dξ`,
  `‖g − g_H‖₂ ≤ ‖g''‖₂/H²`, `‖η₊ − η◦‖₂² ≤ 368/(2·200⁴)`); the main term (`EtaPlusL2`, from (9.94));
  the coprime split and the characters per modulus with Thm 7.1.4 (`ArcChars`); `Σ_{q odd ≤ r} μ²/φ =
  6.798779…` (`SumMuPhi`, kernel). The numbers give about `8.675x ≤ ∫ ≤ 8.786x`; `l2_major_bounds`
  states `8.6296x` and `8.79x`.
* **(14.27)** (`MajorTotal.lean`, Prop 10.4.1 + §14.2): at `α = b/q + β`, `S_η = M_η + R_η` with
  `M_η = μ(q)/φ(q) η̂(−βx)x`; the error `R_* S₊² + M_* R₊(S₊ + M₊)`, with `|R_*|` pointwise (Cor 7.1.3
  per character, `ArcCharsStar`) and `Σ_b |R₊|²` by Bombieri without the principal character; AM–GM
  instead of Cauchy–Schwarz for the `β`-integrals. Main term: the singular series
  `Σ_q c_q(N) ≥ 1.314` (`Singular.lean`: Ramanujan sums, Euler product, the Mertens product bound),
  `C_{η◦,η_*}(N/x) ≥ 0.800689/κ` (`CMain.lean`: polarization,
  `(η◦∗η◦)(ρ) ≥ ‖η◦‖₂² − ½(2−ρ)²‖η◦'‖₂²`; moments of `η_*`; `FourierMain.lean`: (10.22) by Fourier
  inversion). Total `1.314 · 0.800689 = 1.05211`, minus `0.00283` for `η₊ → η◦` and the `β`-tail, minus
  the residuals: `1.049` holds with a margin of about `6.6·10⁻⁵`.
* **(14.28)** (`MinorArcs/EBound.lean`, `Helfgott/HHBound.lean`) with `8·10⁻¹¹` for [H]'s
  `8.4029·10⁻¹²`, which is exactly tight at `x = 4.9·10²⁶` and needs Appendix A's sharp sup norms. Ours
  uses `|h_H| ≤ (3/π)·TV(h) + O(Hε²) ≤ 3.15` (integrate by parts against `G_H(z) = ∫_0^z sin(Hv)/(πv)dv`,
  `|G_H| ≤ 3/π`).
* `final_inequality_crude` with margin `0.0114` needs `v = N^{1/64}` (the `N^{1/16}` + `log u ≤ u/e`
  argument loses a factor of about 4.6).

## Lemma B.1.2 with `c₀ = 32` (`MinorArcs/Eta2DD*.lean`, `InnerSums.lean`)

Helfgott suggested a slightly weaker constant than his `31.521` (the true maximum is `31.52065`, at
`t ≈ 17.4`).
* `t ≥ 2`: `eta2DD t = F(z, w) + O*(6120 w³)`, `z = e(−t/4)`, `w = 1/2πt`, by three integrations by
  parts of `Jq`. `F` is a polynomial in `z, w` (`Fz`); `z` is treated as free on the circle,
  parametrised by `zm m = ((1−m²) + 2mi)/(1+m²)` for `m ∈ [−1, 1]` and sign `±`. `chk` bisects
  `(m, w) ∈ [−1,1] × [0, 2/25]` with Lipschitz constants `LzQ`, `LwQ` (`chk_sound`).
* `t ≤ 2`: `x = 2πt ≤ 12.6`, Taylor polynomials of degree `< 50` (`Complex.exp_bound'`), error
  `120 |x|^50/50!`; the coefficients are rational (`βR_eq`), `PQ` evaluates the polynomial exactly
  over `ℚ`, and `chkC` bisects with the 24-Lipschitz bound `norm_eta2DD_sub_le`.
* The three `decide +kernel` checks take about 4 minutes in all. (B.11) follows (`Eta2Fourier.lean`:
  `ibp2`, `eta2DD_eq`, the cubic `512c³ − 256c² − 896c + 656 ≤ 991.1226` by `nlinarith` with the hint
  `(c + 0.61507)²(1.7302 − c) ≥ 0`). (B.17), (B.18) are in `Eta2LogFourier.lean`.

## (9.94) (`MajorArcs/EtaPlusSqLog.lean`, `EtaONum.lean`)

`∫ η₊² log(xt) = A log x + B`; write `η₊² = η◦² + 2(η₊ − η◦)η◦ + (η₊ − η◦)²`. The `η◦` integrals are
exact polynomial and `tᵐ log t` integrals after a Taylor sandwich of `e^{−(t−1)²}` (`EtaONum`). The
cross terms: in `u = log t`, `(η₊ − η◦)η◦ dt = (g_H − g)(u) W(u) du`; `g − g_H` has its Fourier
transform supported on `|ξ| > H/2π`, so Parseval (`integral_conj_mul_fourier`) gives
`|∫ (g_H − g) W| ≤ ∫_{|ξ|>H/2π} |ĝ| |Ŵ|`, with both tails `O(H⁻⁴)` (`tail_fourier_le_deriv2`, crude
polynomial bounds for `‖W₀''‖₂² ≤ 1000`, `‖W₁''‖₂² ≤ 60`). Weights in the form
`W(u) = eᵘ 1_{[0,2]}(eᵘ) k(eᵘ)` (`IF`) for integrability.

## Small cases (`Helfgott/SmallCases.lean`, `Ladder/`)

For odd `n ≤ 4·10¹⁸ + 3`, `n = 3 + (n − 3)` and binary Goldbach. For `4·10¹⁸ + 3 < n ≤ 10²⁷`, rung
`i = ⌊(n − 5)/(S·2⁴⁵)⌋` of the ladder (`S = 111616`) gives a prime in
`[(S·i − 2047)·2⁴⁵ + 1, S·i·2⁴⁵ + 1] ⊂ [n − 4·10¹⁸, n − 4]` (`Ladder.ladder_prime`).

The ladder (`Ladder/`):
* Rung `i`, `1 ≤ i ≤ 254638308 = ⌊(10²⁷ − 5)/(S·2⁴⁵)⌋`, is `c = (S·i − t)·2⁴⁵ + 1`, `0 ≤ t < 2048`, with
  `c ≡ 2 (mod 3)` and `3^((c−1)/2) ≡ −1 (mod c)`. `S` is the largest grid step with
  `(S + 2047)·2⁴⁵ + 4 ≤ 4·10¹⁸` (up to a few units), so the rungs are as sparse as binary Goldbach
  allows. `S·i < 2⁴⁵` keeps `c < (2⁴⁵ + 1)²`, which Proth's criterion needs. The largest offset is
  about `1100` (expected gap `62` between rungs that pass base `3`).
* Proth's criterion is Mathlib's `Nat.pow_pow_add_primeFactors_one_lt` (prime factors `≠ 2` of
  `a^(2ⁿ) + 1` are `≡ 1 (mod 2ⁿ⁺¹)`) plus `minFac² ≤ c` (`prime_of_dvd_pow_add_one`).
* The check (`Check.lean`) works on blocks of 32 rungs, modulo the product `M ≈ 2²⁹⁰⁰` of their
  candidates: `B = 3^(2⁴⁴)`, `A = B^S`, `U = A^{i₀}` mod `M` (about 90 squarings per block), then per
  rung `U ← U·A mod M` and the test `c ∣ U + (B mod c)^t`. `3 ∤ M` replaces a test `3 ∤ c` per rung.
  Blocks of 32 balance the kernel's overhead per operation (about `1 µs`) against GMP's cost on `M`.
* Costs: hints `1.5·10⁻⁵` s per rung (native, `LadderHints.lean`); kernel `5.5·10⁻⁵` s per rung, of
  which about `0.8·10⁻⁵` the products, `2.2·10⁻⁵` the block exponentiations and `2.5·10⁻⁵` the
  tests.
* The hints exist only during elaboration (in the `.olean`s, `11` bits per rung). A file of hints
  would be about `350 MB`.

Lower limits of the method: `r₀ = 150000` is fixed by Platt's GRH range (`q ≤ 3·10⁵`), and Thm 3.1.1
as formalized needs scale `≥ 2.16·10²⁰` and `r ≤ y^{1/3}/6`, so `y ≥ (6r₀)³ ≈ 7·10¹⁷` at least. Moving
the circle method below `10²⁷` would also mean redoing the major arcs, (14.7) and the non-prime terms.

## Kernel computations: lessons

* Costs: about `10⁵` simple steps per declaration is fine, `10⁶` runs out of memory. Trial division
  runs at about 30K steps/s. GMP-backed `Nat` operations (`Nat.lor`, shifts, division) are fast:
  the bit sieve does about `2·10⁻⁶` s per integer.
* `Nat.log2` is not accelerated by the kernel (it unfolds: 0.3 s on a 30000-bit number); `Nat.land`,
  `Nat.sub` and shifts are. The kernel's `whnf` recursion depth grows with the number of iterations
  of a loop, so a loop of more than about 3000 steps fails with "deep recursion" however it is
  written: split long loops (halving, `pcL`). An accumulator `acc + 1` that is only read at the end
  is a chain of unevaluated additions, which fails the same way; return a value that is a literal at
  each step instead (the remaining fuel, `popc`).
* Lazy accumulators exhaust kernel memory beyond a few thousand numbers per `decide`; force evaluation
  through the control flow (as `SmallMoeb.walk` does). At about 570 certified windows a single
  `decide +kernel` "fails to reduce", while both halves pass: keep data in chunks.
* `Nat.primesBelow 10⁴` is too heavy; use chunked checks and verified loops. A single `decide` over a
  4203-element `IsChain` recurses too deeply: keep tables in chunks and use only upper bounds. A DFS
  over the 13847 primes `≤ 150000` also recurses too deeply (`SmallMuPhi` walks instead).
* With `O(n)` lookups per step the heartbeat limit is hit at 23 GB; restructure (e.g. divisors only).
* If a proof term needs `(⟨…, (adv 30 …).1, …⟩).m = (adv 30 …).1`, the kernel evaluates `adv` with
  symbolic arguments and runs out of memory, even after `generalize`. State the step lemma for an
  arbitrary `r` (`Inv_stepR`) and instantiate it.
* `congr 1` on `aL (2 (j + 1000) + 1) = aL (2j + 2001)` hits max recursion (unary unfolding); use
  `add_right_inj` + `tsum_congr` + `ring`.
* Build what every step reuses once per declaration (the sieve patterns `pats`): the kernel caches it
  within a declaration, not across declarations.
* The Mathlib import alone is about 7 GB resident. Files with large kernel checks import each other in
  a chain so that lake builds them one at a time.
* Assembly over many data files: a chain of small lemmas (`stage_k`); one big theorem timed out
  because `linarith` scanned hundreds of large hypotheses.
* `Nat.powMod` is not accelerated by the kernel (about 12 ms for a 90-bit modulus, by unfolding).
  `Nat.pow` is, for exponents below `2²⁴`. Straight-line GMP operations cost about `1 µs` each in the
  kernel; a `cond` costs about `9 µs` more than `Bool.rec`, and `match`-compiled loops cost about
  `30 µs` per iteration: write kernel loops as `Nat.rec` with `Bool.rec` branches.
* Kernel definitional checks unfold `Nat.add iS 111616` (raw) against `iS + 111616` (notation) by
  structural recursion on the literal, which recurses `111616` levels deep. State loop equations in
  the definitions' own raw syntax, or as equations of functions, and use them with `rw`, not `simp`.
  Similarly a `Bool.rec` whose condition is a loop with literal fuel on symbolic data makes the kernel
  unroll the loop during `whnf`: write such definitions for abstract loop functions (`blkWith`,
  `runWith`) and prove the specification there.
* With Mathlib, `x ^ n : ℕ` elaborates to `Monoid.npow`, not core's `Nat.pow`: a power written in a
  core-only file and the same power written in a Mathlib file are different terms. Name such
  constants (`mask352`). Keep `3 ^ 2 ^ 44` from being normalized: `ring` on it makes the kernel
  evaluate it (state such identities for a variable exponent `D`).
* Many theorems in one file elaborate in parallel (`Elab.async`), up to about 7 GB for a ladder
  file; the generated files set `Elab.async false`, so lake's parallelism across files is the only one.

## Lean 4 / Mathlib pitfalls

* `linarith` can fail on decimal literals (`0.93`) and on `set`-introduced variables. Use fractions,
  and `obtain ⟨t, ht⟩ : ∃ t, t = … := ⟨_, rfl⟩` instead of `set`. It cannot use hypotheses with division
  by a decimal literal (`L / 2.9`): rewrite as multiplication or with `div_le_iff₀` first. `set` does not
  abbreviate hypotheses created later, so `linarith` may see `Real.log …` and the `set` variable as
  different atoms.
* Unascribed numeral `have`s (`have : 4 * … ≤ 0.13`) may elaborate in the wrong type; write `(4 : ℝ)`.
  `norm_num` can turn a real hypothesis about a cast into one about `ℕ`; restate it over `ℝ` first.
* `interval_cases q` does not update variables introduced by `set … := f q`, so handle small cases
  before any `set`.
* `rw [← integral_add_adjacent_intervals]` may rewrite the wrong side. State
  `have e := integral_add_adjacent_intervals (a := …) (b := …) (c := …) (μ := volume) …` and use
  `linarith`. Likewise `rw [← h]` may rewrite inside `√`; `linear_combination` is safer.
* `split_ifs` splits the `if`s on both sides; use `by_cases` with `if_pos`/`if_neg` to control which.
* `∫ u in x / 2..y` misparses (`2..`): parenthesise the bounds. The body of `∫ y in a..b, …` absorbs a
  following `+ …`, so parenthesize.
* `ConvexOn.2 … (a := l)` clashes with local variables named `a`/`b`: give the expected type.
  Lemmas declared inside our namespace as `ConvexOn.foo` need `_root_.ConvexOn.foo` for dot notation.
* Opening `Set` and `Finset` together makes `mem_Icc` etc. ambiguous. Opening `ArithmeticFunction`
  makes `μ` mean Möbius; use `open scoped ArithmeticFunction.vonMangoldt` (and
  `ArithmeticFunction.Moebius`, `ArithmeticFunction.zeta`) instead.
* An instance-implicit section variable with no dependencies (`variable [Fact …]`) is included in
  every theorem of the section, used or not; the `unusedSectionVars` linter reports the unused ones.
  `omit h in` on an `include`d explicit hypothesis removes an explicit argument, so callers change.
* In a `variable [Fact …]` section, a bare identifier in a statement can be auto-bound as a new
  variable; qualify names from other namespaces (e.g. `(SmallTab.S : ℝ)`).
* Big `nlinarith`/`linarith` calls time out (or exhaust memory) in large contexts. Use
  `linarith only [...]`, split into explicit `have`s, or raise `maxHeartbeats` locally.
* Tight polynomial inequalities: reduce to one variable (replace a variable by its bound using the
  sign of its coefficient, then prove monotonicity via an explicit factorisation), then `nlinarith`;
  or split into one-function inequalities (`x cot x ≤ …`, `t²/sin²t ≤ …`).
* `field_simp` is strong: a trailing `ring` often errors with "no goals" (`field_simp; try ring`).
* `convert … using 1` with `hasDerivAt_id`, `.sub`, `.add` leaves function-equality goals: close them
  with `funext y; simp only [Pi.sub_apply, id_eq]`.
* `setIntegral_const` gives `volume.real s • c`: use `Real.volume_real_Ioc_of_le` etc.
  `integrableOn_const` takes the finiteness proofs as (auto)arguments. `Complex.abs` is gone: use
  `‖·‖` (`Complex.norm_exp`, `Complex.abs_re_le_norm`, `Complex.norm_real`).
* Useful Mathlib lemmas: `ConvexOn.comp_concaveOn`, `strictConcaveOn_sin_Icc`, `convexOn_zpow`,
  `monotone_arcsin`, `Real.cos_arcsin`, `primorial_le_four_pow`, `Real.lt_tan`, `Real.sin_gt_sub_cube`
  (`0 < x → x − x³/6 < sin x`). Reusable lemmas of ours: `le_of_hasDerivAt_le`, the sin/cos Taylor
  chain, `sum_range_pair`, `sum_Icc_low_high`, `sum_Icc_parity`, and `residue_form_gen` in
  `TrigSums.lean`.
* Names that already exist in `MinorArcs`: `kap`, `Gq_nonneg`, `ghat`, `sum_moebius_divisors`.

## Environment

* Lean/Mathlib v4.35.0. Fetch the prebuilt Mathlib with `lake exe cache get`.
* Compile single files with `timeout 1500 lake env lean -M 9000 File.lean` (`-M 20000` for the kernel
  data files). Build heavy modules sequentially; a full `lake build` takes well over an hour, most of
  it in `SmallPsiData*.lean` (about 3 min per file). The 128 ladder files take about 5 hours
  of one core (1.7 GB each, about 40 minutes in waves of 16 on 24 threads).
* Clone/push via SSH (`git@github.com:calr3/ternary-goldbach.git`).

## Open directions

* The bounds for `ψ`, `θ` and Mertens' product ([H, (2.13)–(2.15), (2.17), (2.19), (5.5)] and Lemma
  C.2.2) use RH up to `10⁸` from `PlattGRH` at `q = 1`. Helfgott has proposed proofs from smaller
  inputs (RH to a lower height, as in [RS75]).

* (2.22) with `2.8` uses (2.21) through Ramaré's Liouville route. With Ramaré's `0.03/log x` that
  route gives about `1.78` at best (`scripts/liouville_222_model.py`): the small-`z` peak of
  `|ℓ(z)| log z` (`0.7831` as `z → 11⁻`) caps it. [H]'s `4/5` comes from a different argument of
  Ramaré's [Ramb], not formalized. Downstream only `2.8` is needed (the `7.82` slot of Thm 3.1.1).
* Proved but not used by the main theorems: [H, Lemma 5.1.2] (`G2Bound.lean`), `GS_asymp`
  (`MVLemma7.lean`), `Prelim/SmallLogSq.lean`, and [H]'s form of Prop 11.2.3 (`Prop1123.lean`).
* A cleaner Prop 11.2.3 (with `r_w ≥ wr`) would remove the factor `1.398` in the ℓ∞ bound.
