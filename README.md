# Ternary Goldbach in Lean 4 (a blueprint of Helfgott's proof)

**Status: not a complete formal proof.** `TernaryGoldbach.ternary_goldbach` states that every
odd integer greater than 5 is a sum of three primes, and it is derived in Lean from **four
explicitly stated inputs from the literature**, which are still `sorry`. Everything that
connects those inputs to the theorem is proved.

```
$ lake build
$ echo 'import TernaryGoldbach
#print axioms TernaryGoldbach.ternary_goldbach' > /tmp/ax.lean && lake env lean /tmp/ax.lean
'TernaryGoldbach.ternary_goldbach' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

See [`BLUEPRINT.md`](BLUEPRINT.md) for the chapter-by-chapter map from the book to Lean.

The four `sorry`s that `ternary_goldbach` depends on are all in
[`TernaryGoldbach/Helfgott/Inputs.lean`](TernaryGoldbach/Helfgott/Inputs.lean).

Files under `TernaryGoldbach/MinorArcs/` named in `BLUEPRINT.md` as *blueprint nodes*
(`TypeI.lean`, `PointwiseBound.lean`) also contain `sorry`s. They are
statements of intermediate results from the book, waiting to be proved, and `ternary_goldbach`
does not depend on them (check with `#print axioms`).

Two `sorry`s there are **trusted computations** rather than gaps: the bounds
`|η̂₂''|_∞ ≤ 31.521` (`MinorArcs/InnerSums.lean: eta2_fourier_bound'`, [B, (B.6)]) and
`|η̂_(ρ)''|_∞ ≤ 31.521 log ρ` (`MinorArcs/Eta2Log.lean: eta2log_fourier_bound`, [B, Lemma B.2.3]),
which [B, App. B] obtains by rigorous numerics.

## Layout

| File | Content | `sorry`-free? |
|---|---|---|
| `Statement.lean` | `Statement`, the finite-range versions, and how to combine them | ✅ |
| `Reduction.lean` | binary Goldbach up to `N` + a prime ladder with gaps `≤ N − 4` ⇒ ternary Goldbach up to the top of the ladder | ✅ |
| `CircleMethod.lean` | finite circle method: orthogonality, `∫₀¹ S_a S_b S_c e(−Nα) = #weighted reps`, Parseval, an L² Cauchy–Schwarz bound, the minor-arc bound `≤ sup_𝔪|S_a| ‖b‖₂‖c‖₂`, a general "major > minor ⇒ three primes" criterion, and the circle identity for absolutely summable series | ✅ |
| `Helfgott/Defs.lean` | Helfgott's η₊, η_*, h_H, F_H, η₂, φ, Mellin convolution, `S_η(α,x)`, the major arcs `𝔐_{δ₀,r}`, `x = N/(2+9/(196√(2π)))`, the weighted count | ✅ (definitions) |
| `Helfgott/Decay.lean` | Gaussian decay of η₊ and η_*, so `S_η(α,x)` converges absolutely | ✅ |
| `Helfgott/NonPrime.lean` | [H, (7.50)] from sup bounds on η₊, η_* and bounds on ψ, ψ − θ (constants as parameters) | ✅ |
| `Helfgott/SupNorms.lean` | easy sup bounds `|η₊| ≤ 400`, `|η_*| ≤ 6.2` | ✅ |
| `Helfgott/Chebyshev.lean` | elementary `θ(N) ≤ N log 4`, `ψ(N) − θ(N) ≤ 1.6√N`, `ψ(N) ≤ 1.387 N` (for `N ≥ 10²⁷`) | ✅ |
| `Helfgott/Numerics.lean` | the final inequality of [B, §14.4], `C·N^{3/2} log N < 0.048779 x²/κ` for `N ≥ 10²⁷`, both with Helfgott's `C = 7.3306` and with the cruder `C = 6.7·10⁶` we actually use | ✅ |
| `MinorArcs/Vaughan.lean` | Vaughan's identity `Λ = Λ_{≤V} + μ_{≤U}∗log − μ_{≤U}∗Λ_{≤V}∗1 + μ_{>U}∗Λ_{>V}∗1` | ✅ |
| `MinorArcs/LargeSieve.lean` | Gallagher's lemma; the large sieve `∑_r |S(α_r)|² ≤ (δ⁻¹ + 4πX)‖a‖²` for `δ`-spaced points; the Farey version with `Q² + 4πX` | ✅ |
| `Helfgott/Eta2.lean` | explicit formulas for `η₂`, `|η₂|₁ = 1`, continuity, compact support, total variation `8 log 2` | ✅ |
| `MinorArcs/TrigSums.lean` | [B, §4.1, Lemmas 4.1.1–4.1.3]: trigonometric sums (4.1.3 by a sharper argument than the book's; 4.1.1 also with the summand read as `A` where `sin = 0`) | ✅ |
| `MinorArcs/FourierSums.lean` | [B, §2.3]: `∑ 1/(n−s)² = π²/sin²(πs)` (via Parseval), `∑_{n≠0} 1/(n−r)² ≤ π² − 4`, Lemma 2.3.1 (via Poisson summation), both bounds of (2.2) (with total variation for `|f'|₁`) | ✅ |
| `MinorArcs/InnerSums.lean` | `T_{m,∘}` and its bounds [B, (4.36)]; the Poisson main term [B, (4.33)–(4.34)]; the trusted `|η̂₂''|_∞ ≤ c₀` | 🟡 one trusted computation |
| `MinorArcs/BlockSums.lean` | splitting sums into blocks of length `q`; `∑ 1/(R+jq)` and `∑ √(1+q/(R+jq))` bounds | ✅ |
| `MinorArcs/TypeI.lean` | definitions and bounds of [B, Lemmas 4.2.2–4.2.4] (the bounds of 4.2.4 in our corrected form) | ✅ definitions |
| `MinorArcs/TypeIProof.lean` | **[B, Lemma 4.2.2] proved** (both cases), modulo the trusted `|η̂₂''|_∞ ≤ 31.521` | ✅ (uses the trusted bound) |
| `MinorArcs/InnerSumsGen.lean` | (4.36) and the Poisson main term for a general smoothing function | ✅ |
| `MinorArcs/Eta2Log.lean` | `η_(ρ)(t) = log(ρt) η₂(t)`: [B, (4.38)], Lemma B.2.1; trusted Lemma B.2.3 | 🟡 one trusted computation |
| `MinorArcs/SumTools.lean` | sums vs antiderivatives (MVT); the log-weighted sums of [B, Lemma 4.2.3] | ✅ |
| `MinorArcs/TypeILogProof.lean` | **[B, Lemma 4.2.3] proved** in the form [B, §6.2.1] uses ((4.40) corrected, (4.41) slightly weakened; the unused (4.42) omitted) | ✅ (uses the trusted bounds) |
| `Prelim/LambdaMu.lean` | trusted literature bounds on sums of `Λ` and `μ` [B, (2.12), (2.15), (2.16), (2.20)] | 🟡 trusted |
| `MinorArcs/TypeI2Proof.lean` | [B, Lemma 4.2.4]: regrouping by `a = uv`, the main term (4.50) (factor `3/2` added) | ✅ |
| `MinorArcs/TypeI2Rest.lean` | **[B, Lemma 4.2.4] proved** (both cases): log-weighted range sums, (4.51)/(4.52) in our form (corrected `c₁`, cruder lower-order terms) | ✅ (uses trusted bounds) |
| `Prelim/LargeSieveMV.lean` | trusted literature: the optimal large sieve `N − 1 + δ⁻¹` (Selberg, Montgomery–Vaughan), the weighted large sieve [MV73, (1.6)], [MV73, Lemma 8] (+ numerical check) | 🟡 trusted |
| `Prelim/SumMuSqPhi.lean` | `∑_{n≤N} 1/n ≤ ∑_{r≤N sq-free} 1/φ(r)`; the coprime reduction; [B, (5.41)] `(φ(q)/q) log R ≤ ∑_{r≤R,(r,q)=1} μ²/φ` | ✅ |
| `MinorArcs/Montgomery.lean` | Ramanujan sums at coprime `n`; Montgomery's inequality (case `ω(p) = 1`) | ✅ |
| `MinorArcs/TypeII.lean` | [B, §5.2]: **Lemma 5.2.1, Lemma 5.2.3 ((5.50)–(5.52)), Prop 5.2.4 ((5.53)–(5.57)) proved** (odd `m`, `v = 2`), modulo the trusted sharp large sieves | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIINumerics.lean` | numerical inequalities for (5.51) | ✅ |
| `Prelim/SqfreeCount.lean` | `∑_{m²∣l} μ(m) = [l sq-free]`; `∑_{(m,P)=1} μ(m)/m² = (6/π²)/∏_{p∣P}(1-p⁻²)` (via `L(μ·χ₀, 2)`); squarefree `l ∈ (a, b]` coprime to `P`: `(b-a)(6/π²)P/σ(P) + O*(∑_{e∣P} f(√(b/e)))`; trusted `f(X) ≤ 1.27X` [B, p. 83] | ✅ (one trusted computation) |
| `MinorArcs/S1Lemma.lean` | [B, Lemma 5.1.1] (`v = 2`), with `∑_{t≤Y odd} t^{-1/2} ≤ √Y` and `∑_{d odd} d^{-3/2} ≤ (1-2^{-3/2})ζ(3/2)` | ✅ |
| `MinorArcs/Decomposition.lean` | [B, (3.11)]: `S_{η₂} = S_{I,1} − S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}` (`v = 2`) from Vaughan's identity | ✅ |
| `MinorArcs/TypeIIReduction.lean` | [B, (5.2)–(5.5)]: `S_{II} = 4∫ IIsum(W) dW/W`, Cauchy–Schwarz `|IIsum| ≤ √S₁(√S₂+√S₃)`; trusted [RS62, Thm. 13] | ✅ |
| `MinorArcs/TypeIITools.lean`, `MinorArcs/TypeIITotal.lean` | [B, §6.2.3]: integrals, our version of (6.37) `typeII_637` (Type II total for `q ≤ V/2e`) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIITotalGen.lean` | [B, §6.2.3]: general Type II total `typeII_gen`; our (6.40) `typeII_640` (`|δ| ≥ 8`) | ✅ (uses trusted bounds) |
| `MinorArcs/Eta2LogFourier.lean` | [B, (B.17), (B.18)]: `|(log·η₂)^| ≤ 2 − log 4`, `(2πt)²|(log·η₂)^(t)| ≤ 96 log 2` | ✅ |
| `MinorArcs/TypeITotal.lean` | [B, §6.2.1]: `|S_{I,1}|` total `typeI1_le` | ✅ (uses trusted bounds) |
| `MinorArcs/GcdSums.lean` | [B, (6.9)]: `∑ Λ(v)(q,v)/v ≤ log N + log q`, `∑ Λ(v) v (q,v) ≤ ∑ Λ(v) v + N q log q` | ✅ (uses (2.12)) |
| `MinorArcs/TypeI2Total.lean`, `TypeI2Sum.lean`, `TypeI2Large.lean` | [B, §6.2.2] (`qV ≤ Q`): (6.5)–(6.8), totals `typeI2_le_small` ((6.12)+(6.13)) and `typeI2_le_large` ((6.12)+(6.14)) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIIS1.lean` | [B, §5.1]: the reduction (5.7)–(5.8), (5.19), **(5.34) `S1_bound` proved**; trusted: `T2_le` [B, (5.31)], (5.36), (5.37) | ✅ (uses trusted numerics) |
| `MinorArcs/Assembly.lean` | [B, §6.1]: `S_{0,∞} = 0`, `|S_{0,2}| ≤ 3 log x`, `|S| ≤ |S_{I,1}| + |S_{I,2}| + |S_{II}| + 3 log x` | ✅ |
| `MinorArcs/FirstChoice*.lean` | [B, §6.3.1, §6.4]: the parameters (6.49); `S_{II}`, `S_{I,1}`, `S_{I,2}` at them; AM–GM (6.77) (corrected); **Thm 3.1.1 for `q ≤ x^{1/3}/6`** | ✅ (uses trusted bounds) |
| `MinorArcs/PointwiseBound.lean` | [B, Theorem 3.1.1] (corrected: `0.8103` for `0.5`, `3.8x^{5/6}` for `3.36x^{5/6}`): case `q ≤ x^{1/3}/6` proved, case `q > x^{1/3}/6` `sorry` | 🟡 half |
| `Helfgott/Inputs.lean` | proved inputs 1 and 4, and **the four unproved facts** (see below) | ❌ |
| `Helfgott/Main.lean` | assembly: inputs ⇒ odd `N ≥ 10²⁷` is a sum of three primes; ladder ⇒ small cases; ⇒ `ternary_goldbach` | ✅ |

## The inputs

The blueprint follows Helfgott's book *The ternary Goldbach problem*, arXiv:1501.05438v2 [B],
which supersedes the papers (arXiv:1205.5252, 1305.2897, 1312.7748 [H]). Its definitions and
constants match [H], with one exception: the corrected minor-arc bound is `1.00948 x²/κ` [B,
(14.49)] rather than `0.97392 x²/κ` [H, (7.48)], so the final margin is `0.04877 x²/κ`.

1. ~~`circle_identity_input`~~ **proved**: [H, (3.3)/(7.49)] for the infinite smoothed sums,
   from `circle_identity_tsum` and the decay bounds in `Helfgott/Decay.lean`.
2. `major_arcs_input`: [B, (14.27)], `∫_{𝔐_{8,150000}} S_{η₊}² S_{η_*} e(−Nα) ≥ 1.058259 x²/κ`.
   This uses explicit formulas for Dirichlet L-functions and Platt's rigorous GRH verification
   for moduli up to 300000.
3. `minor_arcs_input`: [B, (14.49)], `∫_𝔪 |S_{η_*}||S_{η₊}|² ≤ 1.00948 x²/κ`. This uses Vaughan's
   identity, explicit bilinear bounds, and the large sieve. Vaughan's identity and a (non-sharp)
   large sieve are now proved in `MinorArcs/`, but they aren't yet connected to this input.
4. ~~`nonprime_input`~~ **proved**, a weaker form of [B, (14.51)] with constant `6.7·10⁶` in place of
   `7.3306`. Helfgott's sharp inputs (`|η₊| ≤ 1.079955`, `|η_*| ≤ 1.414`, and Rosser–Schoenfeld)
   are replaced by easy ones: `|η₊| ≤ 400`, `|η_*| ≤ 6.2`, `ψ(N) ≤ 1.387 N`,
   `ψ(N) − θ(N) ≤ 1.6√N`. The final inequality still has room.
5. `binary_goldbach_input`: even Goldbach up to `4·10¹⁸` (Oliveira e Silva–Herzog–Pardi).
6. `prime_ladder_input`: the Helfgott–Platt prime ladder up to `8.875694·10³⁰`.

## Caveats

* The definitions in `Helfgott/Defs.lean` were transcribed from extracted PDF text and
  cross-checked against [B] (η₁ = 2·1_{[1/2,1]}, η₂ as in [B, (11.10)], η₊ as in [B, (7.4)–(7.6)]
  with `H = 200`, major arcs [B, (10.5)]). A numerical check gives `max |η₊| ≈ 1.0000` and
  `max |η_*| ≈ 1.2267`, consistent with [B, (14.3), (14.21)].
* [B, (4.40)] (Lemma 4.2.3) states the main term of the all-`n` version; its own proof gives
  `x/2q`, `η̂(−δ/2)` and `(m, 2q) = 1`. `bound_4_40` is the corrected statement. The last term
  of (4.41) is proved with `log(2ex/c₂)` in place of `log(2√e x/c₂)`.
* [B]'s proof of Lemma 4.1.3 has a small gap: its intermediate bound can exceed the stated
  `(2Bq/π) max(2, log(Ce³q/(Bπ)))` for small `C`. The lemma is nonetheless true, and
  `MinorArcs/TrigSums.lean` proves it with a sharper argument (see the docstring there).
* Helfgott works on `ℝ/ℤ`; here it's `(0, 1]` with the major arcs lifted periodically to `ℝ`.
* Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0` (`lake exe cache get` fetches the Mathlib build).
