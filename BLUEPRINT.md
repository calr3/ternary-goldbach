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
| (14.49) minor arcs `≤ 1.00948 x²/κ` | `minor_arcs_input` | ❌ `sorry` |
| (14.51) non-prime terms | `nonprime_input` (constant `6.7·10⁶` instead of `7.3306`) | ✅ proved |
| final inequality | `final_inequality_crude` | ✅ proved |
| `N < 10²⁷`: [HP13] | `binary_goldbach_input`, `prime_ladder_input` | ❌ trusted computation |

## Minor arcs: (14.49) ⟸ Thm 13.2.1

```
(14.49)  [§14.3: numerics, M ≤ 0.80508x (14.48)]
 └─ Thm 13.2.1  (minor-arc total: ℓ² over arcs × ℓ∞ bounds)
     ├─ Prop 13.1.2  (combining ℓ² and ℓ∞ bounds)
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
     │   │    sieves (Prelim/LargeSieveMV.lean); Montgomery's inequality, (5.41) proved; §5.1 (S₁) to do]
     │   └─ Ch 6  minor-arc totals; parameter choices (§6.3)
     ├─ Prop 11.2.3  (adapting Thm 3.1.1 from η₂ to η_*)
     ├─ Ch 12  large sieve for primes: Props 12.1.1, 12.1.2, 12.2.4; Cors 12.2.5, 12.2.6
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
