# Ternary Goldbach in Lean 4 (a blueprint of Helfgott's proof)

**Status: not a complete formal proof.** `TernaryGoldbach.ternary_goldbach` states that every
odd integer greater than 5 is a sum of three primes, and it is derived in Lean from **six
explicitly stated inputs from the literature**, which are still `sorry`. Everything that
connects those inputs to the theorem is proved.

```
$ lake build
$ lake env lean -c '#print axioms TernaryGoldbach.ternary_goldbach'   # sorryAx appears
```

All six `sorry`s are in [`TernaryGoldbach/Helfgott/Inputs.lean`](TernaryGoldbach/Helfgott/Inputs.lean).
No other file contains one.

## Layout

| File | Content | `sorry`-free? |
|---|---|---|
| `Statement.lean` | `Statement`, the finite-range versions, and how to combine them | ✅ |
| `Reduction.lean` | binary Goldbach up to `N` + a prime ladder with gaps `≤ N − 4` ⇒ ternary Goldbach up to the top of the ladder | ✅ |
| `CircleMethod.lean` | finite circle method: orthogonality, `∫₀¹ S_a S_b S_c e(−Nα) = #weighted reps`, Parseval, an L² Cauchy–Schwarz bound, the minor-arc bound `≤ sup_𝔪|S_a| ‖b‖₂‖c‖₂`, and a general "major > minor ⇒ three primes" criterion | ✅ |
| `Helfgott/Defs.lean` | Helfgott's η₊, η_*, h_H, F_H, η₂, φ, Mellin convolution, `S_η(α,x)`, the major arcs `𝔐_{δ₀,r}`, `x = N/(2+9/(196√(2π)))`, the weighted count | ✅ (definitions) |
| `Helfgott/Numerics.lean` | the final inequality of [H, §7.4]: `7.3306 N^{3/2} log N < 0.084339 x²/κ` for `N ≥ 10²⁷` | ✅ |
| `Helfgott/Inputs.lean` | **the six unproved inputs** (see below) | ❌ |
| `Helfgott/Main.lean` | assembly: inputs ⇒ odd `N ≥ 10²⁷` is a sum of three primes; ladder ⇒ small cases; ⇒ `ternary_goldbach` | ✅ |

## The six inputs

References are to H. A. Helfgott, *The ternary Goldbach conjecture is true*, arXiv:1312.7748 [H].

1. `circle_identity_input`: [H, (3.3)/(7.49)] for the infinite smoothed sums. Its finite
   analogue is already proved (`circle_identity`), so what's missing is convergence/decay of η₊
   and η_* and swapping the sum with the integral. **The easiest of the six.**
2. `major_arcs_input`: [H, (7.25)], `∫_{𝔐_{8,150000}} S_{η₊}² S_{η_*} e(−Nα) ≥ 1.058259 x²/κ`.
   This uses explicit formulas for Dirichlet L-functions and Platt's rigorous GRH verification
   for moduli up to 300000.
3. `minor_arcs_input`: [H, (7.48)], `∫_𝔪 |S_{η_*}||S_{η₊}|² ≤ 0.97392 x²/κ`. This uses Vaughan's
   identity, explicit bilinear bounds, and the large sieve.
4. `nonprime_input`: [H, (7.50)], terms with an even or non-prime `nᵢ` contribute at most
   `7.3306 N^{3/2} log N`. This uses sup-norm bounds on η₊, η_* and Rosser–Schoenfeld bounds
   for ψ − θ and ψ. **Elementary apart from those constants; a good next target.**
5. `binary_goldbach_input`: even Goldbach up to `4·10¹⁸` (Oliveira e Silva–Herzog–Pardi).
6. `prime_ladder_input`: the Helfgott–Platt prime ladder up to `8.875694·10³⁰`.

## Caveats

* The definitions in `Helfgott/Defs.lean` were transcribed from the text of arXiv:1312.7748
  and should be checked against the paper before anyone invests effort in proving inputs 2–4.
  In particular, §7 of the extracted text writes `η₁ = 2·I[−1/2,1/2]`, while (4.10) gives
  `η₂(t) = 4 max(log 2 − |log 2t|, 0)` (= `(2·I[1/2,1]) *_M (2·I[1/2,1])`). We used (4.10).
* Helfgott works on `ℝ/ℤ`; here it's `(0, 1]` with the major arcs lifted periodically to `ℝ`.
* Toolchain: Lean `v4.15.0`, Mathlib `v4.15.0`.
