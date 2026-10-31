# Blueprint: from Helfgott's book to Lean

Source: H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2 (2015), 327 pp.
This is the book version, and it supersedes the three papers. References `[B, …]` are to it.

This is a chapter-level map of what feeds each remaining `sorry` in
`TernaryGoldbach/Helfgott/Inputs.lean`. The next step is to turn each node into Lean
statements, each with its own `sorry`.

## Top level ([B, §14.4]) — done

`ternary_goldbach` follows [B, §14.4] and is proved in Lean from:

| [B] | Lean | Status |
|---|---|---|
| (14.50) circle identity | `circle_identity_input` | ✅ proved |
| (14.27) major arcs `≥ 1.058259 x²/κ` | `major_arcs_input` | ❌ `sorry` |
| (14.49) minor arcs `≤ 1.00948 x²/κ` | `minor_arcs_input`, stated with `1.0376` (re-run with the corrected Thm 3.1.1, `scripts/minor_arc_total_numerics.py`) | ❌ `sorry` |
| (14.51) non-prime terms | `nonprime_input` (constant `6.7·10⁶` instead of `7.3306`) | ✅ proved |
| final inequality | `final_inequality_crude` | ✅ proved |
| `N < 10²⁷`: [HP13] | `binary_goldbach_input`, `prime_ladder_input` | ❌ trusted computation |

## Minor arcs: (14.49) ⟸ Thm 13.2.1

```
(14.49)  [§14.3: numerics, M ≤ 0.80508x (14.48)]
 └─ Thm 13.2.1  (minor-arc total: ℓ² over arcs × ℓ∞ bounds)
     │   [conditional on an ℓ∞ bound off the scale-x arcs ✅ MinorArcs/Thm1321.lean
     │    `thm_13_2_1_conditional` (uses only Prop 12.2.4); off the scale-y arcs r_α ≥ r ✅
     │    MinorArcs/OffArcs.lean; missing: the gap 𝔐_{8,n}(y) \ 𝔐_{8,n}(x) (`hv_of_split`)]
     ├─ Prop 13.1.2  (combining ℓ² and ℓ∞ bounds) ✅ MinorArcs/Prop1312.lean (discrete form)
     │   ⚠ Thm 13.2.1's proof uses arcs at scale x/κ for the ℓ∞ input but at scale x for the ℓ²
     │     input and (14.27); see NOTES "Ch. 13: scale erratum"
     ├─ Thm 3.1.1  (pointwise: |S_{η₂}(α,x)| for α = a/q + δ/x, x ≥ 2.16·10²⁰)   ← Part I
     │   [stated: MinorArcs/PointwiseBound.lean `theorem_3_1_1`]
     │   ├─ Ch 3.3  Vaughan's identity (✅ MinorArcs/Vaughan.lean), alternative route
     │   ├─ Ch 4  Type I sums: trigonometric sums (§4.1), Type I estimates (§4.2)
     │   │   [§2.3 (Lemma 2.3.1, (2.2), π²/sin² series) ✅ MinorArcs/FourierSums.lean;
     │   │    §4.1: Lemmas 4.1.1–4.1.3 ✅ MinorArcs/TrigSums.lean (4.1.3: book's proof has a gap; fixed);
     │   │    §4.2: Lemma 4.2.2 ✅ MinorArcs/TypeIProof.lean; Lemma 4.2.3 ✅ MinorArcs/TypeILogProof.lean
     │   │          ((4.40) corrected; unused (4.42) omitted); Lemma 4.2.4 ✅ MinorArcs/TypeI2Rest.lean
     │   │          ((4.50)–(4.52) corrected, see NOTES); trusted literature (2.12), (2.15), (2.20);
     │   │    trusted (App. B): |η̂₂''|_∞ ≤ 31.521, |η̂_(ρ)''|_∞ ≤ 31.521 log ρ]
     │   ├─ Ch 5  Type II sums: S₁ via a sum with μ (§5.1), S₂ via the large sieve (§5.2, Prop 5.2.4)
     │   │   [§5.2: Lemmas 5.2.1, 5.2.3, Prop 5.2.4 ✅ MinorArcs/TypeII.lean (v = 2), trusted sharp large
     │   │    sieves (Prelim/LargeSieveMV.lean); Montgomery's inequality, (5.41) proved;
     │   │    §5.1: Lemma 5.1.1, (5.7)–(5.8), (5.34) ✅ MinorArcs/TypeIIS1.lean; trusted f(X) ≤ 1.27X,
     │   │    T₂(S) ≤ 0.37273 (S ≥ 16; Lemma 5.1.2 + computations), (5.36), (5.37)]
     │   └─ Ch 6  minor-arc totals; parameter choices (§6.3)
     │       [(3.11) decomposition ✅ MinorArcs/Decomposition.lean; (5.2)–(5.5) Type II reduction ✅
     │        MinorArcs/TypeIIReduction.lean; §6.2: S_I1 ✅ TypeITotal, S_I2 (qV ≤ Q) ✅ TypeI2Sum/Large,
     │        S_II (6.37), (6.40) ✅ TypeIITotal(Gen); (6.38), (6.39), (6.41) ✅ TypeIILarge;
     │        §6.3.1 + §6.4 ✅ FirstChoice*: Thm 3.1.1 for q ≤ x^{1/3}/6 (corrected constants);
     │        §6.3.2 ✅ Second*: Thm 3.1.1 for q > x^{1/3}/6 ([B]'s constants; corrected case split)]
     │   ⇒ Thm 3.1.1 ✅ PointwiseBound `theorem_3_1_1` (modulo the trusted inputs)
     ├─ Prop 11.2.3  (adapting Thm 3.1.1 from η₂ to η_*; [B]'s proof ignores δ_w = wδ, statement
     │   survives for r ≤ r₁, see NOTES and scripts/prop_11_2_3_check.py)
     │   [(11.9) ✅ MinorArcs/EtaStar.lean; Thm 3.1.1 at scale wy ✅ MinorArcs/EtaStarBound.lean;
     │    (11.11) ✅ GBound.lean; Lemma 11.2.4 (one scale) ✅ GMono.lean;
     │    Prop 11.2.3 (corrected, with a majorant G) ✅ Prop1123.lean]
     ├─ Ch 12  large sieve for primes: Props 12.1.1, 12.1.2, 12.2.4; Cors 12.2.5, 12.2.6
     │   [Prop 12.1.2 ✅ MinorArcs/LargeSieveProof.lean (δ₀ ≥ 2; Bombieri's identity, arcs, Plancherel);
     │    Prop 12.2.4 trusted computation (LargeSievePrimes.lean); Cor 12.2.5 ✅ from the two;
     │    Gauss sums ✅ Prelim/GaussInduced.lean]
     │   (✅ a basic large sieve is in MinorArcs/LargeSieve.lean; Ch 12 needs sharper weighted versions)
     └─ Appendices B (Fourier transforms of η₂''), C (sums with Λ and φ)
 Preliminaries: §2.5 explicit bounds on sums of μ and Λ (Ramaré et al.)
```

## Major arcs: (14.27) ⟸ Prop 10.4.1

```
(14.27)  [§§14.1–14.2: numerics]
 └─ Prop 10.4.1  (+ §10.1 character decomposition, §10.2 main term, §10.3 ℓ² over major arcs)
     ├─ Thm 7.1.1, Thm 7.1.2, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5   ← Part II
     │   (explicit bounds on Sη(δ/x, x) twisted by primitive χ, for η = Gaussian, t²e^{-t²/2},
     │    η_*, η₊)
     │   ├─ Ch 8  Mellin transform of the twisted Gaussian: Thm 8.0.1, Cor 8.0.2 (saddle point)
     │   └─ Ch 9  explicit formulas: §9.1 general explicit formula; Props 9.2.2, 9.3.2,
     │            Cor 9.3.3, Props 9.4.2, 9.5.1
     │       └─ §9.6  verification of zeros (Platt: GRH for q ≤ 300000, height ~10⁸/q)  ← trusted
     ├─ Ch 11  the smoothing functions η◦, η_* (§11.1 η◦(t)η◦(ρ−t))
     └─ Appendix A  norms of η₊ (A.3–A.5: |η₊|_∞ ≤ 1.079955, …)
         (✅ crude bounds in Helfgott/Decay.lean, Helfgott/SupNorms.lean)
```

## Trusted computations (planned `axiom`s)

1. [OeSHP14] binary Goldbach up to `4·10¹⁸`.
2. [HP13] the prime ladder up to `8.875694·10³⁰`.
3. Platt's GRH verification [B, §9.6].
4. The "rigorous computations" (interval arithmetic, [B, §2.6]) used inside proofs. These
   still need to be catalogued while we formalize the chapters. Each will be either
   formalized or stated as a small trusted fact.

## Suggested order

1. Part I bottom-up: §2.5 (sums of μ, Λ), Ch 4 (Type I; mostly elementary), Ch 5, Ch 6 → Thm 3.1.1.
2. Ch 12 (large sieve for primes) and Ch 13 → Thm 13.2.1 → (14.49).
3. Part II: Ch 8 and Ch 9 (the heavy analysis), with §9.6 as an axiom → Ch 10 → (14.27).
