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
(`TypeI.lean`, `PointwiseBound.lean`) also contain `sorry`s. They are statements of intermediate
results from the book, waiting to be proved, and `ternary_goldbach` does not depend on them
(check with `#print axioms`).

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
| `Helfgott/Eta2.lean` | explicit formulas for `η₂`, and `|η₂|₁ = 1` | ✅ |
| `MinorArcs/TrigSums.lean` | [B, Lemma 4.1.1]: trigonometric sums `∑ min(A, C/sin²(παn)) ≤ min(2A + 6q²C/π², 3A + (4q/π)√(AC))` | ✅ |
| `MinorArcs/TypeI.lean` | blueprint: [B, Lemmas 4.1.2–4.1.3, 4.2.2–4.2.4] (Type I sums), facts about `η₂` | 🟡 statements (4.1.1 and `eta2_L1` proved) |
| `MinorArcs/PointwiseBound.lean` | blueprint: [B, Theorem 3.1.1], the pointwise minor-arc bound | 🟡 statement |
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
* Helfgott works on `ℝ/ℤ`; here it's `(0, 1]` with the major arcs lifted periodically to `ℝ`.
* Toolchain: Lean `v4.15.0`, Mathlib `v4.15.0`.
