# Blueprint: from Helfgott's book to Lean

Source: H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015), 327 pp.
This is the book version, and it supersedes the three papers. References `[H, …]` are to it.

This is a chapter-level map from [H] to the Lean files. There is no `sorry`. `ternary_goldbach`
uses only Lean's three standard axioms and takes three published results as hypotheses (`Fact`
instances), listed and checked against their sources in `HYPOTHESES.md`. [H, (5.36)] is used in
corrected form (`+0.0231`), because [H, (5.32)] is false for `v = 2`. The README lists the other
differences from [H]; `NOTES.md` has the details.

## Top level ([H, §14.4])

`ternary_goldbach` follows [H, §14.4] and is proved in Lean from:

| [H] | Lean | Notes |
|---|---|---|
| (14.50) circle identity | `circle_identity_input` | ✅ |
| (14.27) major arcs `≥ 1.058259 x²/κ` | `major_arcs_input` (`MajorArcs/MajorTotal.lean`) | ✅ with `1.049` |
| (14.49) minor arcs `≤ 1.00948 x²/κ` | `minor_arcs_input` (`MinorArcs/MinorTotal.lean`) | ✅ with `1.0376`, via repair 3 of Thm 13.2.1 |
| (14.51) non-prime terms | `nonprime_input` | ✅ with `6.7·10⁶` for `7.3306` |
| final inequality | `final_inequality_crude` (`Helfgott/Numerics.lean`) | ✅ margin `0.0114 x²/κ` |
| `N < 10²⁷`: [HP13] | `ternaryGoldbachUpTo_1e27` (`Helfgott/SmallCases.lean`) | ✅ binary Goldbach up to `4·10¹⁸` (`binary_goldbach_input`) and a prime in `[n − 4·10¹⁸, n − 4]` from a prime ladder up to `10²⁷` (`Ladder.ladder_prime`, `Ladder/`), checked by the kernel, in place of [HP13]'s |

## Minor arcs: (14.49) ⟸ Thm 13.2.1

```
(14.49)  [§14.3: numerics]  ✅ MinorArcs/MinorTotal.lean `minor_total` (≤ 1.0376 x²/κ)
 │   [S_{η₊} = S₁ + S₂ (S₁: primes > √x); numerics `numerics_M`: generated cells
 │    (NumericsCells, scripts/gen_cells.py, worst Mexpr 1.00717 ≤ 1.037) and NumericsAsymp;
 │    (14.7) from MajorArcs/L2Major.lean; (14.28) with 8·10⁻¹¹ (MinorArcs/EBound.lean)]
 └─ Thm 13.2.1  (minor-arc total: ℓ² over arcs × ℓ∞ bounds)
     │   ⚠ [H]'s proof uses arcs at scale x/κ for the ℓ∞ input but at scale x for the ℓ² input and
     │     (14.27); see NOTES "Ch. 13: scale erratum"
     │   [repair 3: `thm_13_2_1_repaired` ✅ MinorArcs/Thm1321.lean (base level 𝔐_{8,r₀}(x),
     │    higher levels 𝔐_{8,n}(y), (12.42) with δ₀ = 392, levels up to ≈ x^{0.3});
     │    ℓ∞ off 𝔐_{8,n}(y) ✅ MinorArcs/OffArcs.lean, LinftyLevels.lean;
     │    base gap via Cor 7.1.3 ✅ MinorArcs/BaseGap2.lean]
     ├─ Prop 13.1.2  (combining ℓ² and ℓ∞ bounds) ✅ MinorArcs/Prop1312.lean (discrete form)
     ├─ Thm 3.1.1  (pointwise: |S_{η₂}(α,x)| for 2α = a/q + δ/x, x ≥ 2.16·10²⁰)   ← Part I
     │   ✅ MinorArcs/PointwiseBound.lean `theorem_3_1_1`: first case 0.8764, 2.526 x/√t, 3.8 x^{5/6};
     │      second case [H]'s 0.276, 1234
     │   ├─ Ch 3.3  Vaughan's identity ✅ MinorArcs/Vaughan.lean
     │   ├─ Ch 4  Type I sums: trigonometric sums (§4.1), Type I estimates (§4.2)
     │   │   [§2.3 (Lemma 2.3.1, (2.2), π²/sin² series) ✅ MinorArcs/FourierSums.lean;
     │   │    §4.1: Lemmas 4.1.1–4.1.3 ✅ MinorArcs/TrigSums.lean (4.1.3: [H]'s proof has a gap; fixed);
     │   │    §4.2: Lemma 4.2.2 ✅ MinorArcs/TypeIProof.lean; Lemma 4.2.3 ✅ MinorArcs/TypeILogProof.lean
     │   │          ((4.40) corrected; the unused (4.42) is omitted); Lemma 4.2.4 ✅ MinorArcs/TypeI2Rest.lean
     │   │          ((4.50)–(4.52) corrected, see NOTES);
     │   │    App. B: |η̂₂''|_∞ ≤ 32 ✅ MinorArcs/Eta2DDBound.lean (kernel grids; [H] has 31.521),
     │   │          (B.17), (B.18) ✅ MinorArcs/Eta2LogFourier.lean]
     │   ├─ Ch 5  Type II sums: S₁ via a sum with μ (§5.1), S₂ via the large sieve (§5.2, Prop 5.2.4)
     │   │   [§5.2: Lemmas 5.2.1, 5.2.3, Prop 5.2.4 ✅ MinorArcs/TypeII.lean (v = 2); sharp large
     │   │    sieves ✅ Prelim/LargeSieveMV.lean; Montgomery's inequality, (5.41) ✅;
     │   │    §5.1: Lemma 5.1.1, (5.7)–(5.8), (5.34) ✅ MinorArcs/TypeIIS1.lean; f(X) ≤ 1.27X ✅
     │   │    Prelim/SqfreeCount.lean, SmallFsq.lean; (5.31) T₂(S) ≤ 0.37273 (S ≥ 16) ✅
     │   │    MinorArcs/T2Bound.lean (kernel g₂(n), n ≤ 10⁴: SmallG2, T2Small; mean-square tail
     │   │    ∫_{10⁴}^S |g₂|/y ≤ 0.0045: G2Tail, from (2.21)); (5.36) corrected and (5.37) ✅
     │   │    MinorArcs/H2Bound.lean]
     │   └─ Ch 6  totals and parameter choices (§6.3)
     │       [(3.11) decomposition ✅ MinorArcs/Decomposition.lean; (5.2)–(5.5) Type II reduction ✅
     │        MinorArcs/TypeIIReduction.lean; §6.2: S_I1 ✅ TypeITotal, S_I2 (qV ≤ Q) ✅ TypeI2Sum/Large,
     │        S_II (6.37), (6.40) ✅ TypeIITotal(Gen); (6.38), (6.39), (6.41) ✅ TypeIILarge;
     │        §6.3.1 + §6.4 ✅ FirstChoice*: q ≤ x^{1/3}/6 (corrected constants);
     │        §6.3.2 ✅ Second*: q > x^{1/3}/6 ([H]'s constants; corrected case split)]
     ├─ Prop 11.2.3  (adapting Thm 3.1.1 from η₂ to η_*; [H]'s proof ignores δ_w = wδ, see NOTES)
     │   [(11.9) ✅ MinorArcs/EtaStar.lean; Thm 3.1.1 at scale wy ✅ MinorArcs/EtaStarBound.lean;
     │    (11.11) ✅ GBound.lean; Lemma 11.2.4 (one scale) ✅ GMono.lean;
     │    Prop 11.2.3 with a majorant G ✅ Prop1123.lean; the variant used, Prop 11.2.3′ (fresh
     │    Dirichlet approximation per scale) ✅ Prop1123b.lean]
     ├─ Ch 12  large sieve for primes: Props 12.1.1, 12.1.2, 12.2.4; Cors 12.2.5, 12.2.6
     │   [Prop 12.1.2 ✅ MinorArcs/LargeSieveProof.lean (δ₀ ≥ 2; Bombieri's identity, arcs, Plancherel);
     │    Prop 12.2.4 ✅ with c₊ = 2: MinorArcs/LSQuot1–9.lean, LSQuotRed.lean, LSQuot8g.lean
     │    (Ramaré's (12.12), proved in Prelim/Ramare*.lean; prime-removal reduction to the divisors
     │    of 30030, kernel walks); Cor 12.2.5 ✅; Gauss sums ✅ Prelim/GaussInduced.lean]
     └─ Appendices B (Fourier transforms of η₂''), C (sums with Λ and φ: Lemma C.2.2 ✅
        Prelim/MertensProduct.lean)
 Preliminaries: §2.5 explicit bounds on sums of μ and Λ ✅ Prelim/LambdaMu.lean and the files it
 imports: (2.12)–(2.15), (2.17), (2.19), (5.5) from Prelim/PsiTwoSided.lean, the kernel tables and
 Prelim/ThetaExplicit.lean; (2.20) MoebiusCoprime; (2.21) the hypothesis `ramare_moebius`;
 (2.22) with 2.8 LiouvilleBound; (2.23) with q/φ(q) + 2.67 MoebiusLog; (2.24) for x < 11815
 SmallMoebius
```

## Major arcs: (14.27) ⟸ Prop 10.4.1

```
(14.27)  [§§14.1–14.2: numerics]   ✅ MajorArcs/MajorTotal.lean `major_total` (≥ 1.049 x²/κ)
 │   [per modulus: S_η = μ(q)/φ(q) η̂(−βx)x + residual (τ(1) = μ(q), Cor 7.1.3 / Thm 7.1.4 per
 │    character, ArcChars + ArcCharsStar); the residuals by AM–GM against (14.7); main term
 │    Σ_q c_q(N) ≥ 1.314 (Singular), C_{η◦,η_*}(N/x) ≥ 0.800689/κ (CMain, FourierMain), with
 │    η₊ → η◦ and the β-tail costing ≤ 2.03·10⁻⁵ x² per modulus]
 └─ Prop 10.4.1  (+ §10.1 character decomposition, §10.2 main term, §10.3 ℓ² over major arcs)
     │   [§10.3 + §14.1, i.e. (14.7) ✅ MajorArcs/L2Major.lean `l2_major_bounds` (8.6296x … 8.79x):
     │    arcs (ArcsEq), η◦ tail (EtaCirc), ‖η₊ − η◦‖₂ via h_H in log coordinates (HHFourier,
     │    HHFourier2), ‖η₊‖₂ from (9.94) (EtaPlusL2), per-modulus characters + Thm 7.1.4 (ArcChars),
     │    Σ_{q≤r odd} μ²/φ (kernel check, SumMuPhi + Prelim/SmallMuPhi); Plancherel for L¹ ∩ L²
     │    (Prelim/PlancherelReal)]
     ├─ Thm 7.1.1, Thm 7.1.2, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5   ← Part II
     │   [Cor 7.1.3 ✅ MajorArcs/Cor713.lean ⇐ Cor 9.3.3 ✅ (Cor933.lean) ⇐ Prop 9.3.2 ✅
     │    (MajorArcs/Prop932.lean: q ≥ 2 from Explicit/ExplicitBound, q = 1 from Explicit/ZetaBound;
     │    weaker constants) + Platt (the hypothesis `PlattGRH`, through `platt_verification`,
     │    MajorArcs/GRH.lean);
     │    Prop 7.1.5 ✅ MajorArcs/Prop715.lean ⇐ Prop 9.5.1 ✅ (same file, from Explicit/EtaPlusSqBound)
     │    + Platt (q = 1) + (9.94) ✅ (EtaPlusSqLog + EtaONum); Thm 7.1.4 ✅ MajorArcs/Thm714.lean
     │    ⇐ Prop 9.4.2 ✅ (MajorArcs/Prop942.lean from Explicit/EtaPlusBound; weaker constants) + Platt]
     │   (explicit bounds on S_η(δ/x, x) twisted by primitive χ, for η = Gaussian, t²e^{−t²/2},
     │    η_*, η₊)
     │   ├─ Ch 8  Mellin transform of the twisted Gaussian: Thm 8.0.1, Cor 8.0.2 (saddle point)
     │   │        [Cor 8.0.2 by rotating the contour ✅ Explicit/MellinRotate.lean]
     │   └─ Ch 9  explicit formulas: §9.1 general explicit formula; Props 9.2.2, 9.3.2,
     │            Cor 9.3.3, Props 9.4.2, 9.5.1   ✅ Explicit/ (zeros counted by Jensen's formula
     │            in windows; Landau's partial fractions; residues on rectangles)
     │       └─ §9.6  verification of zeros (Platt: GRH for q ≤ 300000, height ~10⁸/q)  ← hypothesis
     ├─ Ch 11  the smoothing functions η◦, η_* (§11.1 η◦(t)η◦(ρ−t))  ✅ (CMain: polarization bound
     │         for η◦∗η◦ and the moments of η_*; constant 8.82)
     └─ Appendix A  norms of η₊ (A.3–A.5: |η₊|_∞ ≤ 1.079955, …)
         (✅ cruder bounds suffice: Helfgott/Decay.lean, Helfgott/SupNorms.lean, Helfgott/HHBound.lean)
```

## Bounds for `ψ` and `θ` (quoted in [H], proved here)

[H, §2.5] quotes its bounds for `ψ` and `θ` from [RS62], [RS75] and [RR96]; here they are proved:

```
(2.12)–(2.15), (2.17), (2.19), (5.5)  (Prelim/LambdaMu.lean); Lemma C.2.2 (Prelim/MertensProduct.lean, Prelim/MertensWindow.lean)
 ├─ psi_two_sided  (Prelim/PsiTwoSided.lean: |ψ(n) − n| ≤ c(n)√n, 12 ≤ n ≤ 10¹⁷)
 │   ├─ the trial-division table on [12, 10⁶) (Prelim/SmallPsiTable*.lean, kernel)
 │   └─ psi_mid8 on [10⁶, 10¹⁷] (Explicit/PsiRanges1e8.lean ⇐ PsiRange ⇐ PsiWeil ⇐ the Weil explicit
 │      formula with a compactly supported test function: Weil*.lean; low zeros |γ| ≥ 2.39:
 │      ZetaLowZeroFree.lean; RH up to 10⁸: rh_upto_1e8 from PlattGRH at q = 1)
 ├─ the bit-sieve table on [10⁶, 5·10⁷) (Prelim/PsiSieve*.lean, kernel)
 ├─ theta_explicit (Prelim/ThetaExplicit.lean: |θ(n) − n| < n/log³n + ε_pl(n) n, n ≥ 10¹²)
 │   ├─ psi_two_sided below 10¹⁷
 │   └─ above 10¹⁷: the Gaussian-smoothed explicit formula with RH up to 10⁸ (Explicit/PsiExplicit,
 │      PsiPlateau1e8, PsiLarge, PsiRange1, PsiAsymp) with the zero-free region
 │      β ≤ 1 − 1/(11 log|γ|), |γ| ≥ 10⁸
 │      (Explicit/XiPartial, ZeroFree, ZeroFreeRegion)
 └─ for Lemma C.2.2 above 10¹², the variation of E₁Λ: the same smoothed explicit formula
    integrated against dy/y² (Prelim/MertensWindow.lean, E1_var), theta_explicit at the two ends
```
