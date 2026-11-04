# Working notes

Notes for continuing the formalization. For the overall map, see `BLUEPRINT.md`. For the
`sorry` policy, see `README.md`.

## Roadmap: the explicit-formula sorries (Props 9.3.2, 9.4.2, 9.5.1) and Dusart

[H]'s proofs: Prop 9.x = Lemma 9.1.1 (explicit formula: shift `∫_{(3/2)} −L'/L G_δ x^s` to `ℜs = −1/2`) +
Lemma 9.1.4 (zeros with `|γ| ≤ T₀`, on the line, Cauchy–Schwarz + Mellin–Plancherel) + Lemma 9.1.3 with
Cor 8.0.2 (zeros with `|γ| > T₀`). Inputs [H] cites: `N(T,χ) = (T/π)log(qT/2πe) + O*(0.5 log qT + 17.7)`
([Ros41], [McC84a], [Tru]), the functional equation (9.8), digamma bounds (9.10), `|ζ'/ζ(3/2)| ≤ 1.50524`.
Erratum-ish: Lemma 9.1.3's `N⁺ = N/2` holds only for real `χ`; correct version sums over `χ` and `χ̄` (zeros
of `L(χ)` with `γ < 0` are conjugates of zeros of `L(χ̄)` with `γ > 0`), which needs `f` to bound
`|G_δ|` and `|G_{−δ}|` — Cor 8.0.2 (and our rotation bound) is symmetric in the sign of `δ`, so fine.
1. **Cor 8.0.2 — DONE** (`Explicit/MellinRotate.lean`, no `sorry`): rotate `t = re^{iθ}`; same exponents
   `0.1598`, `0.1065`, constants `0.892|τ|`, `0.588 y²` (per term; [H]: `5.13`, `1.99` for pairs).
**Progress (2026-11-01):** `Explicit/MellinRotate` (Cor 8.0.2), `Explicit/LGrowth` (`L = s∫S(t)t^{-s-1}` and
`|L| ≤ (q+1)|s|/σ` for `σ > 0`), `Explicit/ZeroCount` (Jensen: zeros in `|s−(2+iT)| ≤ 1.6`),
`Explicit/Landau` (`|f'/f − Σ_{|ρ−c|<R/2} m/(z−ρ)| ≤ 48 log(B/|f(c)|)/R` on `|z−c| ≤ R/4`) — all sorry-free.
Also done (sorry-free): `Explicit/LGrowthLeft` (`|L(z,χ)| ≤ 512 q⁹(q+1)(|ℑz|+9)e^{π|ℑz|/2}` for
`−8 ≤ ℜz ≤ 1/4`, any `ℑz`), `Explicit/LogDerivL` (Landau for `L` at `c = 2+iT`, `R = 10`, every `T`:
`|L'/L(z) − Σ_{|ρ−c|<5} m/(z−ρ)| ≤ 4.8 log(B_T/0.355)` on `|z−c| ≤ 5/2`; `≤ log(B_T/0.355)/log 2` zeros in
`|ρ−c| ≤ 5`), `Explicit/RectResidue` (`rectInt`; `∮ ds/(s−ρ) = 2πi`; Cauchy's formula; residue theorem
`∮ (f'/f) h = 2πi Σ_{ρ inside} m_ρ h(ρ)` for entire `f`, rectangle in `ball c (R/2)`, no zeros on sides).
**Explicit formula DONE (2026-11-01)**: `Explicit/ExplicitFormula.explicit_formula` (no sorry; axioms only
propext/choice/Quot.sound): for `χ` primitive `≠ 1`, `η = t²e^{−t²/2}`, along `T_k ∈ [k+1, k+2]`,
`Σ_{ρ ∈ (−1/2,3/2)×(−T_k,T_k)} m_ρ G_δ(ρ)x^ρ → −S − (1/2π)∫ (L'/L)(−1/2+iy)G_δ(−1/2+iy)x^{−1/2+iy}dy`.
Also `Explicit/GMellin` (`G_δ` holomorphic on `ℜs > −2`, `|G_δ| ≤ K_δ e^{−0.28|t|}` on `−1/2 ≤ σ ≤ 3/2`).
*Next:* (a) zero sums: `‖S‖ ≤ sup_k Σ_{zerosRect} m|G(ρ)|x^{ℜρ} + (1/2π)x^{−1/2}∫|L'/L||G|`; bound the zero sum
by windows (Jensen counts `log(B_T/0.355)/log(10/r)` per window) × rotation bounds; under GRH up to `T₀`
(`GRHUpTo`) zeros with `|γ| ≤ T₀` have `ℜρ = 1/2` (plus `ρ = 0` for even `χ`). (b) restate Prop 9.3.2 with
the resulting (weaker) constants and redo Cor 9.3.3 → Cor 7.1.3 → uses. (c) `q = 1` (ζ, pole at `s = 1`),
`η₊` (Props 9.4.2, 9.5.1), Dusart.
**Done since:** `Explicit/GammaBounds` (`|Γ(x+iy)| ≤ e^{−φ|y|}Γ(x)/cos^xφ`), `Explicit/LGrowthPoly`
(`|L(z,χ)| ≤ 1400 q⁹(q+1)(|ℑz|+9)(1.25(|ℑz|+1))^{10}` on `−8 ≤ ℜz ≤ 1/4`). **Remaining for Prop 9.3.2**
(in order): (a) `ZeroSums`: `B'_T = 1400q⁹(q+1)(|T|+22)(1.25(|T|+11))^{10}` on `|z−(2+iT)| ≤ 10`; Jensen windows
(radius 6 in 10: height ≈ 10.9, `≤ log(B'/0.355)/log(10/6)` zeros, ≈ 2 log T per unit height vs true 0.16);
uniform bound for `Σ_{zerosRect} m|G(ρ)|x^{ℜρ}`: zeros with `|γ| ≤ T₀` on the line (GRH), the rest via the
rotation bounds; `ρ = 0` contributes `|G(0)| ≤ 1`. (b) explicit bound for the `ℜs = −1/2` integral (Landau +
`|z−ρ| ≥ 1/2`, now polynomial). (c) `‖S‖ ≤ E_new x`. (d) `q = 1` (ζ: pole at 1 gives `G(1)x = η̂(−δ)x`; needs
ζ versions of LGrowth/Landau/explicit formula). (e) restate `prop_9_3_2` with `E_new`; redo `Cor933.err932_le_Er`,
`Cor713` numerics, check `ArcCharsStar`, `BaseGap*`, (14.27). Then Props 9.4.2/9.5.1 (`η₊`) and Dusart.
**Prop 9.3.2 DONE for all q (2026-11-01, late)**: generic layers `Explicit/Datum` (`LDatum`: contour
identity for any entire `f`), `GoodSmoothing` (any smoothing with exponentially decaying Mellin transform),
`ZeroSumGen` (`PolyDatum` + Plancherel + geometric tail); ζ: `ZetaGrowth` (`zetaF = (s−1)ζ(s)` entire,
Abel bound, functional equation), `ZetaDatum`, `ZetaExplicit` (main term `M(1)x` from the datum `s − 1`),
`ZetaPoly` (`B''_ζ`, zeros in `0<ℜ<1`), `ZetaBound` (`errZ`). Cor 7.1.3 for `q = 1` at `T₀ = 10⁸`: E₁ ≤
3.42e6 (actual ≈3.07e6). **Remaining sorries**: Props 9.4.2, 9.5.1 (η₊: need `GoodSmoothing` for
`η₊(t)e(δt)` via `h_H` band-limited: `M(s) = (1/2π)∫_{−H}^{H} ĥ(r) G₁(s − ir) dr`, `G₁(s) = G₂(s−1)`; then
`zero_sum_boundG` for χ (`ldatum_L` + a `PolyDatum` for `L`) and ζ; 9.5.1 needs `η₊²·log`) and Dusart.
**Prop 9.4.2 DONE (2026-11-01, later)**: `Explicit/EtaPlusMellin` (`M₊(s) = ∫_{|ξ|≤100/π} ĝ(ξ)
G₁(s−1+2πiξ) dξ`; the `G` bounds shifted by `≤ 200` in height; `GoodSmoothing` with `θ = min(θ_δ, 1/200)`, which
avoids an `e^{56}` factor), `Explicit/EtaPlusCg` (`C_g = ∫|g| = 92e^{−1/2} − 12e^{3/2} ≤ 2.03`, by FTC),
`Explicit/MellinPlancherelGen` (Mellin–Plancherel on `ℜs = 1/2` for any smoothing with `|e^{−u/2}φ(e^{−u})| ≤
Ce^{−c|u|}`), `Explicit/ExplicitBoundGen` (explicit-formula bounds for any admissible smoothing, `χ` and `ζ`),
`Explicit/EtaPlusBound` (`∫₀^∞ (log v)²η₊² ≤ 3.15²(1 − √π/2) ≤ 1.129`), `MajorArcs/Prop942` (`prop_9_4_2`,
error `err942N`, with `∫η₊² ≤ 0.6403` from `EtaPlusL2`). **Thm 7.1.4 restated** (`MajorArcs/Thm714.lean`) for
`x ≥ 4.9·10²⁶`: `q = 1` (`T₀ = 10⁸`): `|E| ≤ 10⁻¹⁸ + 6.24·10⁶/√x`; `q ≥ 2`: `|E| ≤ (7.5·10⁻⁸ + 7.7·10⁶/√x)/√q`
(`T₀ = 10⁸/q`; for even `q > 1.25·10⁵`, `T₀ = 200 + 7.5·10⁷/q`, where the regime-A tail at `u₀ = 19.89` gives
`√q E₂ ≤ 6.86·10⁻⁸`; the vertical-line term `V ~ 10¹⁹` forces the larger `x`). Consumers: ArcChars
`2.41e-8 → 4.25e-7` and `1.141e-8 → 2.83e-7`; L2Major per modulus `1.57e-6 → 9.62e-4`, `4.3e-9 → 2.17e-7`, total
`8.675x … 8.786x` (stated `8.6296x … 8.79x`); `l2_major_14_7` restated `8.7098 ± 0.0802` (same lower end, so
MinorTotal is unchanged); `resid_plus` `2.14e-15 → 7.83e-13`; (14.27) still `1.049` (margin ≈ `6.6·10⁻⁵`).
**Prop 9.5.1 DONE (2026-11-01, latest)**: `log n = log x + log(n/x)` splits the sum into the `ζ` explicit
formulas for `φ₁ = η₊²` and `φ₂ = η₊² log`. `Explicit/EtaPlusSq`: `mellin_hHc_mul` (`M(h_H g)(s) =
∫_{|ξ|≤a} ĝ(ξ) M g(s + 2πiξ) dξ` for any `|g| ≤ C t^b e^{−t²/2}`), applied twice to `η₊² = h_H·h_H·t²e^{−t²}`;
`M(t²e^{−t²}) = Γ(s/2+1)/2`, bounded by the rotation bound for `Γ` (angle `1.2`): `|M(φ₁)(s)| ≤ (2aC_g)² 8 e^{400c}
e^{−c|ℑs|}` on `−1 ≤ ℜs ≤ 2` for `0 ≤ c ≤ 0.6` (`c = 1/400` for `GoodSmoothing` and the line `ℜs = −1/2`,
`c = 0.6` for the tail above `T₀ = 500`); `M(φ₂) = M(φ₁)'` by Cauchy's estimate (radius `1/2`).
`Explicit/EtaPlusSqBound`: Plancherel data (`|Φ| ≤ 9.93e^{−|u|}`), crude `L²` moments (`η₊⁴ ≤ 98.46 v⁴e^{−v²}`,
`log²v ≤ v + 1/v`). `MajorArcs/Prop715`: `prop_9_5_1` for `x ≥ 4.9·10²⁶` with error `10⁻⁸ x log x` (actual
`≈ 2.65·10⁻⁹ + 4·10⁻⁹/log x`); Prop 7.1.5 keeps `|E₂| ≤ 2·10⁻⁶ + 366.91/√x` but now for `x ≥ 4.9·10²⁶` (the
only use, `MinorTotal.T_le`, has that). **Remaining sorry**: Dusart.
**Prop 9.3.2 for `q ≥ 2` DONE** (`Explicit/LineZeros`, `ZeroSumBound`, `ExplicitBound`, `MajorArcs/Prop932`):
`|S| ≤ E₀ + E₁√x + E₂x + V/(2π√x)`; `prop_9_3_2` now = cited `prop_9_3_2_one` (ζ, [H]'s constants) for
`q = 1`, proved for `q ≥ 2`. Cor 9.3.3 averages either error (`err933N`); Cor 7.1.3 restated as
`|E| ≤ 10⁻¹⁷ + 4.7·10⁶/√(qy)`, `y ≥ 10²⁵` (E₁ ≤ 3.42·10⁶/√q, E₂ ≤ 2·10⁻¹⁸, E₀ ≤ 15300, V ≤ 2.1·10¹⁶);
ArcCharsStar `1.35e-7, 1.21e-7 → 1.49e-6`, resid_star `9.9e-14 → 1.34e-11`, MajorTotal `3.15e-7 → 3.67e-6`
(14.27 still 1.049), BaseGap2 still `≤ 0.012 y` (0.01190). **Next**: `q = 1` (ζ): `f(s) = (s−1)ζ(s)` entire;
growth (right: `ζ(s) = s/(s−1) − s∫{t}t^{−s−1}`; left: `riemannZeta_one_sub`), Landau/Jensen for `f`,
rectangle identity with `∮ ζ'/ζ·h = ∮ f'/f·h − 2πi h(1)`, Mellin inversion (`LSeries_vonMangoldt_eq_deriv_
riemannZeta_div`), the residue `G_δ(1)x = η̂(−δ)x`; zeros in the rectangle lie in `0 < ℜ < 1`. Then 9.4.2/9.5.1.
*Constraint found:* the `|γ| ≤ T₀` zero sum must stay `O(√T₀ log qT₀)` (Lemma 9.1.4's Cauchy–Schwarz +
Mellin–Plancherel `∫|G(1/2+it)|²dt = 2π|η|₂²`); the trivial `|G(1/2+it)| ≤ |η/√t|₁` gives `O(T₀ log)`, i.e.
relative errors `~10⁻³` in Thm 7.1.4, which breaks (14.7) (needs `E ≲ 6·10⁻⁵`). Plan: windows of height 10
(radius 6 in 10), `sup_window |G| ≤ (1/h)∫|G| + ∫|G'|`, Cauchy–Schwarz, Plancherel via `v = log u`
(`F(v) = e^{v/2} η(e^v) e(δe^v)`, `PlancherelReal`), and `G'` = Mellin of `log t · η e(δt)`.
*Zero density problem:* `LGrowthLeft`'s bound grows like `e^{π|t|/2}` (Gamma decay dropped), so Jensen gives
`O(T)` zeros per window — fine for convergence, useless for Lemma 9.1.4. Fix (in progress): polynomial growth
of `L` on `σ ≤ 1/4` via the exact ratio `Γ((s+κ)/2)/Γ((1−s+κ)/2) = 2^{1−s} π^{−1/2} Γ(s) sin(π(1−s+κ)/2)`
(reflection + duplication `Complex.Gamma_mul_Gamma_add_half`) and the rotation bound
`|Γ(x+iy)| ≤ e^{−φ|y|} Γ(x)/cos^x φ` (from `norm_Gr_le` via `Gr(2a−2,0,0) = 2^{a−1}Γ(a)`, i.e. `t = u²/2`;
Mathlib: `mellin_comp_rpow`, `mellin_comp_mul_left`, `mellin_cpow_smul`). Then `log B_T = O(log qT)` and
`O(log qT)` zeros per window (≈ 10× the true density; downstream tolerates ~30×).
*Old plan:* explicit formula = Mellin inversion on `ℜs = 3/2` (Mathlib `mellin_inversion`) + `Σ Λχ n^{-s} = −L'/L`
(+ interchange) + residue theorem on `[−1/2, 3/2] × [−T_k, T_k]` (heights `T_k ∈ [k, k+1]` at distance
`≥ 1/(2N+2)` from all ordinates) + `T_k → ∞` (horizontal sides: `|L'/L| ≤ N/δ + 4.8 log B` vs `|G| ≲ e^{−0.16T}`).
The trivial zero `s = 0` (even `χ`) is just one of the zeros inside the rectangle.
*Refined plan:* (i) growth for `σ ≤ 1/4` from `completedLFunction_one_sub` (`Λ = Γℝ(s+κ) L`, no `q^{s/2}`):
`|L(1−s,χ)| = q^{σ−1/2} π^{1/2−σ} |Γ((s+κ)/2)/Γ((1−s+κ)/2)| |L(s,χ⁻¹)|`, numerator `≤ Γ(ℜ)` (integral),
denominator `≥ π e^{−π|t|/2}/(|Γ(1−w)|)` (reflection) ⇒ `|L| ≲ q^{O(1)} e^{π|t|/2}` — exponential growth is
fine: Landau then gives `|L'/L| ≲ |t|` and Jensen `≲ |t|` zeros per window, and `G_δ` decays like
`e^{−0.16|t|}`. (ii) Landau at `c = 2+iT`, `R = 10` covers `σ ∈ [−1/2, 3/2]` (horizontal sides at heights
chosen `≥ 1/(2N+2)` from all ordinates, by a measure argument) and the line `σ = −1/2` (there
`|s−ρ| ≥ 1/2`). No digamma bounds needed. (iii) The only constant that matters downstream is the
`√T₀ log qT₀ x^{−1/2}` term of Lemma 9.1.4; a Jensen density (`≈ 30–40×` worse) makes Cor 7.1.3's
`381500/√q` about `1.5·10⁷/√q`; estimated effect: (14.27) `1.0493 → ≈ 1.0488` (state `1.048`), minor arcs and
(14.7) unaffected in substance. Props 9.x, Cor 9.3.3, Cor 7.1.3, Thm 7.1.4, Prop 7.1.5 constants get restated.
2. *A priori growth of `L(s,χ)`* (σ > 0 done): second-order partial summation (`S(u) = Σ_{n≤u} χ(n)` periodic,
   subtract its mean, integrate twice) ⇒ `|L(σ+it, χ)| ≤ C q² (|t|+2)²` for `σ ≥ −1/2`, `χ ≠ 1`; identity
   theorem from `LFunction_eq_LSeries` + `LSeries_eq_mul_integral` (SumCoeff). On `ℜs = −1/2` exactly:
   `|L(s,χ)| = (q/π)|(κ − 1/2 + it)/2| |L(3/2 − it, χ̄)|` (functional equation, `Γ(w̄+1) = w̄Γ(w̄)`).
3. *Zeros*: multiplicities (`analyticOrderAt`), local finiteness; crude local count by Jensen
   (`MeromorphicOn.circleAverage_log_norm`): `#{ρ : |γ − T| ≤ 1} ≤ C log(q(|T|+2))`.
4. *Landau's lemma* (partial fractions for `L'/L` near `s₀`): `MeromorphicOn.extract_zeros_poles` +
   `Complex.borelCaratheodory` on `log g`.
5. *Explicit formula* (Lemma 9.1.1): rectangles `[−1/2, 3/2] × [−T_k, T_k]` at good heights, residues of
   `L'/L G x^s` (`∮ ds/(s−ρ) = 2πi` by hand), `T_k → ∞` using the decay of `G`.
6. *Zero sums*: with a Jensen density the `√T₀ log qT₀ x^{−1/2}` terms get worse constants (≈5–25×); the
   downstream uses (Cor 7.1.3 at `y ≥ 10²⁵`, Thm 7.1.4, Prop 7.1.5, (14.7), (14.27)) have room, but the
   constants in Props 9.x / Cor 9.3.3 / Cor 7.1.3 / Thm 7.1.4 must then be restated and re-verified.
   (Sharp alternative: Weil's explicit formula with a test function supported in `|log n| < log 2`.)
7. *Dusart*: explicit formula for `ζ` + zero-free region (3-4-1 with step 4) + RH verification (numerical
   axiom) + numerics; or weaken `dusart_theta` to what the uses need.

## Plan: replacing `dusart_theta` (2026-11-01)

Dusart's `|θ(x) − x| < x/log³x` for all `x ≥ 89 967 803` needs zero-density estimates (Faber–Kadiri /
Ramaré) beyond `x ≈ e^{4000}`; we do not formalize those. Instead:
1. **Numerical axioms** (computer-verified, finite range): [Büthe 2018, Thm 2] (arXiv:1511.02032, zeros to
   `10¹¹`): `0.05√x < x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`; [Platt–Trudgian 2021] (arXiv:2004.09765):
   RH up to `3·10¹²`.
2. **Digamma**: `ψ(s) = ∫₀^∞ (e^{−u} − (1+u)^{−s}) du/u` (Fubini + Frullani), so
   `Re ψ(σ+it) − ψ(σ) = ∫₀^∞ e^{−(σ−1)v}(1 − cos tv)/(e^v − 1) dv ≤ log|t| + O(1)`.
3. **Hadamard-type identity** without the product theorem: for `ξ = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)` and squares
   `R_k` symmetric about `ℜs = 1/2` at good heights, `ξ'/ξ(s) − ξ'/ξ(s₀) = lim Σ_{ρ∈R_k} (1/(s−ρ) − 1/(s₀−ρ))`
   (kernel `O(|w|^{−2})`, `|ξ'/ξ| ≪ log² T` on the squares: polynomial `B''_ζ` + FE). With `s₀` on the critical
   line, `Re ξ'/ξ(s₀) = 0` and the `R_k` sums of `Re 1/(s₀−ρ)` vanish (pairing `ρ ↔ 1 − ρ̄`), so
   `Re ξ'/ξ(s) = lim Σ_{R_k} Re 1/(s−ρ) ≥ Σ_{ρ∈S} Re 1/(s−ρ)` for `ℜs > 1`.
4. **Zero-free region** (3-4-1 + Stechkin's trick, target `R ≈ 10`) for `|t| ≥ 3·10¹²`.
5. **ψ via a Gaussian-smoothed sandwich** (`φ± = Φ((±Aδ − log t)/δ)` minus the part near 0) in
   `explicit_formula_zeta`; zeros on the line by windows (sup per window, not Sobolev), tails by Gaussian
   decay, off-line zeros above `3·10¹²` by the zero-free region.
6. **The new interface** (Python model `zf.py` in the session scratchpad): relative error `1/log³x` for
   `10^{10} ≤ x ≤ e^{3900}`, a plateau `≈ 1.5·10⁻¹¹` up to `e^{L₁}` (`L₁ ≈ 10⁴` for `R ≈ 10`), then fast decay.
7. **Consumers**: `LambdaMu` (`psi_upper_of`, `psi_lower2`, `psi_lower_all`, `thetaN_close`, …),
   `MertensProduct` (`psi_err`, `F_large`), `MoebiusBound.K_partC` (the plateau costs
   `≈ ε·L₁²`; budget: `K ≤ 0.54` has slack `8·10⁻⁴`, `abs_ls_big` allows `K ≤ 0.543`).

## Zero-free region DONE (2026-11-01)

`Explicit/ZeroFreeRegion.lean` `zero_free`: every zero `ρ = β + iγ` of `ξ` with `|γ| ≥ 10⁹` has
`β ≤ 1 − 1/(11 log|γ|)` (Stechkin-type; only the standard axioms). Route, without the Hadamard product:
* `Explicit/XiPartial.lean`: `ξ(s) = s(s−1)Λ₀(s) + 1` (`xiF`), squares `[½−T, ½+T] × [−T, T]` at good heights
  (polynomial datum `ldatum_zeta2`, `HkD` polylog), `|ξ'/ξ| ≤ MX(k) = O(log² k)` on their boundary
  (digamma + `|ζ'/ζ| ≤ C₃` for `ℜ ≥ 3/2` + FE). Symmetry `w ↦ 1 − w` turns `∮ ξ'/ξ(w)(w−s)⁻¹` into
  `½∮ ξ'/ξ(w)[(w−s)⁻¹ − (w−(1−s))⁻¹]` (kernel `O(|w|⁻²)`), so `xi_partial_approx`:
  `ξ'/ξ(s) ≈ Σ_{ρ in square} m_ρ/(s − ρ)` uniformly on discs.
* `Explicit/ZeroFree.lean`: Stechkin's lemma (an elementary inequality, proved algebraically):
  `Φ_s(ρ) ≥ κ Φ_{s₁}(ρ)` for `Φ_s(ρ) = Re 1/(s−ρ) + Re 1/(s−(1−ρ̄))`, `κ = (σ−½)/(σ₁−½)` whenever
  `(σ−½)² + (σ₁−½)² ≥ 3/2`; pairing `ρ ↔ 1 − ρ̄` via the identity at `1 − s̄` and `ξ(s̄) = conj ξ(s)`.
* `Explicit/ZeroFreeRegion.lean`: `18 + 30cos θ + 17cos 2θ + 6cos 3θ + cos 4θ = 8(½ + (3/2)cos θ + cos²θ)² ≥ 0`,
  `σ = 1 + 0.31/log t`, `σ₁ = 1.6181`; digamma via `ψ(z) = ψ(z+2) − 1/z − 1/(z+1)` and the Dirichlet integral.
  The model (`zf/stech2.py` in the session scratchpad) gives `R ≈ 10.3` at `t = 3·10¹²`; `R = 11` is proved
  for `t ≥ 10⁹` with margin.

## ψ-sandwich design (2026-11-01, after the zero-free region)

Model `zf/eps2.py` (session scratchpad): smoothing `φ(u) = Φ((a − log u)/δ) − Φ((b − log u)/δ)` (`Φ` normal cdf,
`e^b = 10¹⁰/x`, `a = ±K₀δ`), `M(s) = e^{δ²s²/2}(e^{as} − e^{bs})/s` (entire), zeros: Jensen windows
(`count_tail_windowG` at `T₀ = H = 3·10¹²`, `count_line_windowG` below), RH to `H` (Platt–Trudgian axiom),
`zero_free` above `H`. Sandwich: `ψ(x) ≤ S(K₀δ)/Φ(K₀)`, `ψ(x) ≥ S(−K₀δ) − tail`. Achievable relative error:
`6·10⁻⁷` at `x = 10¹⁹`, `≈ 2·10⁻¹¹` for `100 ≤ log x ≤ 7000` (`δH ≈ 7.5`, `K₀ = 7`), `< 1/log³x` again from
`log x ≈ 12000` (needs the zero-free region; crude window bounds need `≈ 15000`). Interface plan:
`|θ(x) − x| ≤ x/log³x` for `x ≤ e^{3500}` and `x ≥ e^{15000}`, `≤ 2.1·10⁻¹¹ x` in between.
K-budget (MoebiusBound): the plateau costs `≈ ε_p·ΔL·L ≈ 2–4·10⁻³` in `K_partC`; current slack is `8·10⁻⁴`, so
relax `K ≤ 0.54` to `0.55` — `abs_ls_big` still gives `≤ 0.99` if `Σ 1/u² ≤ 5/3` is replaced by `π²/6`
(`0.55·(1.034·π²/6 + 0.09·1.0117) + 0.0042 = 0.990`, check exactly) or a tighter partial sum.
Vertical line `ℜs = −1/2`: `|M| ≲ √(x/10¹⁰)/|s| e^{−δ²y²/2}` — absolute size `≈ 10¹⁰`, negligible.

## Fewer axioms (2026-11-01, after the audit)

* Step 1: `theta_sqrt` removed; it is a special case of `buthe_theta`.
* Step 2: `psi_sqrt`, `psi_small`, `psi_mid`, `psi_mul_mid`, `theta_cube_small` removed, and
  `buthe_psi` added (Büthe 2018, Thm 2, (1.5), same paper as `buthe_theta`):
  * `ψ < 1.03883 n` for `n ≤ 586` by `Prelim/SmallPsi.lean`: `ψ(n) = log lcm(1..n)`, and a verified
    loop that carries the lcm is checked with `decide +kernel` in about 15 s.
  * Thresholds moved up to where Büthe applies:
    * (2.14) for `y ≥ 6·10⁶`;
    * (2.17) for `y ≥ 2.5·10⁷`, with a new Büthe-based proof `psi_mul_buthe`;
    * `theta_explicit` from `2·10⁸`, using `1.95√n < n/log³n` there;
    * the Type I hypotheses `V ≥ 2.5·10⁷` (the actual `V ≥ 2.7·10⁷`);
    * `F_large` from `2·10⁸`, with `mertens_product_small` re-run to `2·10⁸`.
  * The unused `LambdaMuExtra` axioms were re-checked on their extended ranges (that file has
    since been deleted).
* Step 3: `mertens_small`, `prod_ap_le` and `fsq_le` proved, with the kernel doing the numerics:
  * `SmallMertens`: per-prime upper bounds on log p, per-`n` lower bounds on log n, and a rational
    check for each `n ≤ 100`.
  * `SmallProdAp`: a 1229-entry prime table checked in chunks of 100 entries; the completeness scan is
    split into ten ranges of 1000.
  * `SmallFsq`: endpoint checks in blocks of 4 values of `n`; for `n = 2` the 3000-term tail is checked
    in 12 blocks.
  ternary_goldbach now depends on 28 axioms (14 our own, 7 published, 7 from [H]).
* `H2_le` ((5.37)) and the corrected (5.36) `integral_H2_le` proved (`MinorArcs/H2Bound.lean`):
  * `T₂ = α_n + β_n/S` on `[n, n+1)` from `integral_g2`; the case split is `2 s max(r₁, r₂) ≤ n`;
  * kernel tables of `μ`, `σ` (`r ≤ 15`), `α_n`, `β_n` (`n ≤ 15`) and `log j` (`j ≤ 16`, `10⁻⁹`);
  * the integral by FTC with antiderivative `k(α log S − β/S)`; the excess at integers from these
    tables; `[2, 15]` by monotonicity (`H₂ ≥ 0.15107`), `[1, 2]` and `[15, 16]` by hand;
  * `g2`, `T2`, `H2` moved to `MinorArcs/T2Defs.lean` so that `TypeIIS1` can import the proofs.
  ternary_goldbach now depends on 26 axioms (14 our own, 7 published, 5 from [H]).
* Rigorous re-checks of all our computation axioms (`scripts/rigorous/`):
  * `rig_checks.c`: MPFR intervals with directed rounding;
  * `moebius_sqrt_rig.c`: IEEE round-down mode, `10¹⁰` terms in 6 min.
  All pass; the values agree with the float scripts. Published equivalents:
  * `mertens_product_small`: [RS62, Thm 15] at primorials;
  * `moebius_sqrt_small`: [H, (2.24)];
  Building needs only `gcc`, `gmpy2` (for the MPFR headers) and the system MPFR.
* (B.6) and (B.11) proved (`MinorArcs/Eta2Fourier.lean`); new axiom `eta2DD_small` for
  `0 ≤ t ≤ 655`:
  * `ibp2`: two integrations by parts against `e(−ut)` for a `C²` piece;
  * `eta2DD_eq`: `(2πt)² η̂₂ = eta2DD`;
  * `norm_trig_le`: the cubic `512c³ − 256c² − 896c + 656 ≤ 991.1226`, by `nlinarith` with the hint
    `(c + 0.61507)²(1.7302 − c) ≥ 0`;
  * `norm_Jq_le`: one more integration by parts;
  * `norm_eta2log4_le`: `48 log 2` with no numerics, from FTC for `∫|h''|` (constant sign).
  The finite range is checked by `scripts/rigorous/eta2_fourier_rig.py` (python-flint/Arb, 3 s).
  Found: [H]'s derivation of (9.94) drops the factor 2 of the cross term (`AXIOMS.md`, Finding 3).
  ternary_goldbach now depends on 25 axioms (15 our own, 7 published, 3 from [H]).
* (9.94) proved (`MajorArcs/EtaPlusSqLog.lean`), with [H]'s constants; inputs `etaO_numerics` (now proved):
  * expand `(g + D)²` in `u = log t`;
  * cross terms by Parseval (`integral_conj_mul_fourier` via `Lp.inner_fourier_eq`, and Fubini for
    `g_H`), with the general tail bound `tail_fourier_le_deriv2`;
  * weights in the form `W(u) = eᵘ 1_{[0,2]}(eᵘ) k(eᵘ)` (`IF`) for integrability, with `t log t`
    continuous for the `log` weight;
  * computation: `scripts/rigorous/eta_circ_rig.py` (Arb, under a second).
  ternary_goldbach now depends on 25 axioms (16 our own, 7 published, 2 from [H]).
* (5.31) `T2_le` proved (`MinorArcs/T2Bound.lean`):
  * `T₂(S) = S⁻¹ ∫₀^S g₂ N` with `N` the count of odd `s ∈ (S/2y, S/y]`; the counting lemma via
    `#{odd ≤ n} = (n+1)/2`;
  * notation pitfall: the body of `∫ y in a..b, …` absorbs a following `+ …`, so parenthesize;
  * computations: `scripts/rigorous/t2_rig.c` (MPFR, `g₂(n)` for all `n ≤ 10⁸` in 8 min), giving
    `T2_small`, `T2_mid`;
  * [H, Lemma 5.1.2] is the remaining axiom, used only for `x ≥ 10⁸`. Removing it needs Ramaré's
    `|m(x)| ≤ 0.03/log x` ([H, (2.21)]): our Lean `0.55/(log x − 0.75)` is about 18 times too weak.
  ternary_goldbach now depends on 27 axioms (18 our own, 7 published, 2 from [H]).
* [H, Lemma 5.1.2] proved (`MinorArcs/G2Moebius.lean` → `G2Euler.lean` → `G2Numerics.lean` →
  `G2Bound.lean`): `|g₂(x)| ≤ 0.0215/(log x)² + 528(1 + log x)²/x`, from the new published axiom
  `ramare_moebius` ([H, (2.21)], Ram13) and `moebius_sqrt_small`:
  * one convolution `f·1_{(·,d)=1} = H_d ∗ (μ/id)`, `H_d = f·1_{(·,d)=1} ∗ (1/id) ≥ 0`, via
    `ArithmeticFunction` ring identities and `sum_Ioc_mul_eq_sum_sum`;
  * Rankin weight `u^{1/22}` (valid since `log(x/u) ≥ 22` when Ramaré is used);
  * Euler products via `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
    (`sum_le_euler`);
  * numerics use rational `p^s` bounds at small primes (`rpow_le_of_pow_le`) and
    `MV.sum_rpow_neg_le` tails;
  * the `d`-sum at `s = 1/2` is compared with `τ(d)/d` (multiplicative comparison on prime powers,
    `(t−1)⁴ + 1 ≥ 0`);
  * the tail integral in `T2Bound` is now `≤ 0.0036`.
  ternary_goldbach now depends on 27 axioms (18 our own, 8 published, 1 from [H]).
* [H, Prop 12.2.4] proved (`MinorArcs/LSQuot1.lean` … `LSQuot6.lean`); no [H] axiom remains:
  * inputs: Ramaré's (12.12) (published axiom `ramare_Gq`, stated with an existential
    `c ∈ [1.3325822, 1.3325823]` since `c_E` is not computed in Lean) and the computation
    `prop1224_check` (`scripts/rigorous/p1224_check.c`, 22 min on 22 threads for `q < 2.2·10¹⁰`;
    [H] needed two weeks single-core, mostly because it recomputed more);
  * structure: `star_suffices` (θ ≤ 0.6274), `regionL` (`R ≥ λ(q)`), `checkC_suffices`, `regionS`
    (`G_q(R) G_P(t) ≤ G_q(tR)`, `G(t) ≤ (P/φ(P)) G_P(t)`, `div_totient_lt`, `G(t) ≥ log t + 1.064`),
    `large_q_hS` (`λ⁷ ≤ (103/120)⁹ q²` by exchange + primorial induction, `ĝ(p)^{21} ≤ p²` for
    `p ≥ 37`);
  * the computation's (S)-branch uses the monotone form `log q + 1.039(n+1) ≤ 0.826 (qn)^{2/9}`, so
    Lean needs no concavity; τ = 2/9 makes the large-`q` condition polynomial;
  * [H] slips found (AXIOMS.md Finding 4): Lemma 12.2.3 has `log Q + 1.312`, not `+ c_E`; (12.15)'s
    analytic range starts at `4.42·10⁷`, not `4·10⁷`;
  * name clashes to watch: `kap`, `Gq_nonneg`, `ghat`, `sum_moebius_divisors` already exist in
    `MinorArcs`.
  ternary_goldbach now depends on 28 axioms (19 our own, 9 published, 0 from [H]).
* Independent checks of the inputs:
  * `prop1224_check` was re-run in interval arithmetic (`scripts/rigorous/p1224_rig.c`).
  * `ramare_Gq` was checked against Ramaré's 1995 paper (numdam, open access: Lemma 3.4 and (3.6)).
    `ramare_check.c` recomputes `c_E` and tests (12.12) on `d ≤ 2000`, `X ≤ 2·10⁶`. (It is now
    proved in Lean; see below.)
  * `ramare_moebius` is now stated only for `x ≥ 10¹⁰`. It is implied by Ramaré 2015 Thm 1.2, which
    arXiv:2408.05969 re-derives (that paper also proves `0.010032/log X` for `X ≥ 617 990`).
* Own computations reduced (goal 2026-11-01, items 1–7):
  * Item 1: `lemma7_numeric` and `GS_N0` were removed. Ramaré's (12.12) covers `r ≥ 21400`, and the
    kernel covers smaller `r` (`Prelim/SmallG.lean`: a DFS over subsets of primes, lower bound only,
    23 s, 7.5 GB peak). `ramare_Gq` moved to `Prelim/RamareGq.lean`; `MinorArcs.ramare_Gq` is now a
    theorem. 26 axioms (17 own, 9 published).
  * Item 2: `nonprime_small` was removed: analytic for `10⁶ ≤ n ≤ 10¹²` from `buthe_psi` and
    `ψ − θ ≤ θ(√n) + θ(n^{1/3}) + θ(n^{1/4}) + n^{1/5} log n` (`nonprime_sum_le4`), kernel below
    (`Prelim/SmallNonprime.lean`, 31 blocks, 9 s). 25 axioms (16 own, 9 published).
  * Item 3: `logsq_small` was removed: Abel summation against `θ` for `40000 ≤ n ≤ 10⁶`
    (`logsq_mid`), kernel below (`Prelim/SmallLogSq.lean`, 225 blocks, 78 s). 24 axioms (15 own).
    Kernel lesson: a single `decide` over a 4203-element `IsChain` hits deep recursion, so the
    table is kept in chunks and only upper bounds are used (no sortedness needed).
  * Item 4: `liouville_small` was removed: `Ω(n)` by trial division (proved correct), a kernel walk
    over `n ≤ 10⁵` with fixed-point partial sums and the state certified at 105 chunk boundaries
    (`Prelim/SmallLiouville.lean`, 4.7 min, 8.2 GB). 23 axioms (14 own).
  * Item 5: `lemma8_numeric` was removed: `lemma8_large` from `R ≥ 1000`, a weighted DFS lower bound
    for `6 ≤ R < 1000` (`Prelim/SmallW.lean`, 18 blocks), exact rationals for `R < 6`. 22 axioms (13 own).
  * Item 6: `sum_odd_mu_sq_div_totient` was removed: trial division for `φ` and squarefreeness, a
    kernel walk with 150 certified chunk states (`Prelim/SmallMuPhi.lean`, about 10 min, the slowest
    file). A DFS over the 13847 primes would recurse too deeply in the kernel. 21 axioms (12 own).
  * Item 7: `etaO_numerics` was removed: Taylor sandwich of `e^{−(t−1)²}` and exact polynomial and
    `tᵐ log t` integrals (`MajorArcs/EtaONum.lean`); crude polynomial bounds for `‖W₀''‖₂² ≤ 1000` and
    `‖W₁''‖₂² ≤ 60`, which still fit (9.94) after re-choosing `λ`. 20 axioms (11 own, 9 published).
* Published axiom `ramare_Gq` removed (goal 2026-11-02): Ramaré's (12.12) is proved
  (`Prelim/Ramare.lean`, from `RamareConv` → `RamareFo` → `RamareLocal` → `RamareBound` →
  `RamareMain` → `RamareLog`, plus `RamareConst`, `RamareWalk`, `RamareNum` for `c_E`). 19 axioms
  (11 own, 8 published). `RamareBound`, `RamareWalk` and `RamareNum` are generated by
  `scripts/ramare/gen_bound.py` and `gen_walk_num.py` (template `RamareNum.tmpl`).
  * `g_d = h_d ∗ v` with `v = [odd]/n`, `h_d = g_d ∗ (μ v)` (`wO_mul_vO : wO * vO = 1`), and
    `h_d(p^e) = 0` for `e ≥ 3`.
  * `GqP d R = (log R/2 + C)∑' h_d − ½∑' h_d log a + ∑' h_d(a) Fo(R/a)` (`GqP_decomp`), with
    `|Fo(x)| x^{1/3} ≤ 0.64` for all `x > 0` (`Fo_bound`, γ from `harm_bounds` at `n = 8`).
  * `∑ |h_d(a)| a^{1/3} ≤ 11 f₁(d)` (`sum_wD_le`): generated table `⌈10⁴ p^{1/3}⌉` for odd
    `p ≤ 1000`, kernel product `≤ 7.2863`, and the tail `∏_{p>1000} ≤ 1.494` from
    `∑_{n>1000} n^{−4/3} ≤ 0.3`. Error `0.64·11 = 7.04`.
  * Main terms via `EulerProduct.eulerProduct` (limit over `primesBelow`) and `tendsto_nhds_unique`;
    `∑' h_d log a` via `log a = ∑_q v_q(a) log q`, a fiberwise sum over `a = q^k b`, and `Bp` (the
    sum over `b` coprime to `q`).
  * Found [Ram95, (3.9)] false: `∏_p (1 + (p^{1/3}+p^{2/3})/(p(p−1))) ≈ 8.0845 > 8` (AXIOMS.md
    Finding 5). Ramaré's route would give about `7.36`.
  * `c_E ∈ [1.3325822734, 1.3325822894]` (`cR_bounds`; needed `[1.3325822, 1.3325823]`; the upper
    margin is `1.07·10⁻⁸`):
    * `∑ Λ(n)/n² = (∑ log n/n²)/ζ(2)` from `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
      `LSeries_deriv`, `LSeries_one_eq_riemannZeta` (complex `LSeries` → real `tsum` via `term`);
      the prime-power regrouping by `hasSum_iff_hasSum_of_ne_zero_bij` and `HasSum.prod_fiberwise`
      with a geometric series per prime.
    * `∑ log n/n² = 2X + log 2·ζ(2)` (`tsum_even_add_odd`, `hasSum_zeta_two`); the tail of `X` is
      bracketed by convexity alone (termwise `tsum_le_tsum` of paired differences), with no
      alternating-series lemma.
    * Kernel walk `RamareWalk.lean`: 10 fields at `D = 10³⁰` (log via 12 artanh terms, `H_n`, odd and
      even `log k/k²` to 2000, `log p/(p³−p)` with trial-division primality `isPr_iff`), 24 chunks
      to `n = 20001`, 125 s total. Kernel pitfall: `congr 1` on `aL (2 (j + 1000) + 1) = aL (2j + 2001)`
      hits max recursion (unary unfolding); use `add_right_inj` + `tsum_congr` + `ring`.
* `ramare_moebius` assessed (same goal) and left as an axiom.
  * arXiv:2408.05969 (Ramaré–Zuniga-Alterman, the sequel to Ram13) bootstraps from
    `μL² = μ⋆Λ⋆Λ − (μ⋆Λ)L`. Its inputs are `|M(x)| ≤ x/4345` for `x ≥ 2 160 535` (Cohen–Dress–El
    Marraki), `|M(x)| ≤ √x` for `x ≤ 10¹⁶` (Hurst), `ψ` bounds, and computed sums such as
    `∫₁^{10⁸} R(t)dt/t`.
  * At `x ≈ 10¹⁰` the binding input is `x/4345`. Our elementary `0.55/(log x − 0.75)` has no `μ`
    cancellation, and (5.31) needs about `0.1/log x`.
  * Ram13 (hal-02572812, a local copy from an earlier session) has the same kind of inputs:
    * `|M(x)| ≤ 0.571√x` for `33 ≤ x ≤ 10¹²` (Dress), `|M(x)| ≤ x/2360` and `x/4345` (El Marraki;
      Cohen–Dress–El Marraki), (4.5)–(4.7);
    * Pari/GP computations of `R₂*(D)` up to `1.8·10⁹` (Lemma 6.3), and Lemma 7.1 with
      `K = 462 848`.
  * Not feasible without large external computations.
* Own computations 11 → 6 (2026-11-02, items 1–3 of the follow-up):
  * Item 1: `K_pieces` and `K_blocks` were removed. `MoebiusBound.abs_sum_moebius_div_le` (`0.55/(log x −
    0.7521)`, `x ≥ 10¹⁰`) now follows from `ramare_moebius`, which moved to `Prelim/RamareMoebius.lean`
    so that `LiouvilleBound` can import it. The `K` route was deleted (old version in git history).
  * Item 2: `mertens_lower_small` and `mertens_point` were removed. (2.13)'s summation by parts now
    starts at `X = 10⁴`, with `buthe_psi`; the base value is `−1.57714` (needed `−1.6987`).
    `Prelim/SmallMertensLower.lean` (about 1 min) walks `n ≤ 10002`: `log n`, `∑ Λ(m)/m` and `ψ(n)`
    at `D = 10³⁰`. `Λ` comes from trial division and a kernel-complete table of the 51 proper prime
    powers. Generic walk lemmas (`incr_bounds`, `isPr_iff`, `floor_div_bounds`) moved to
    `Prelim/LogWalk.lean`. Generator: `scripts/gen_mertens_lower.py`.
  * Item 3: `eta2DD_small` was assessed and kept. The bound is nearly sharp (`31.52065`), and
    `c₀ = 31.521` is hard-coded in about 15 minor-arc files (e.g. `BaseGap2.fourier_const_le ≤ 1.0007`).
    `C_grid` was removed: `y G(y)` drops from `2.73` to `1.57`, so 17 adaptive intervals `[a, b]` with
    `b G(a) ≤ 2.8` suffice. `Prelim/SmallCGrid.lean` (21 s) runs one walk over `u ≤ 3000`: an upper
    bound for `log u`, squarefreeness by trial division, and fixed-point upper bounds for every grid
    point. Generator: `scripts/gen_c_grid.py`.
  * 14 axioms (6 own, 8 published).
* Own computations 6 → 4 (2026-11-02, follow-up):
  * `moebius_sqrt_small` removed. `ramare_moebius` is now stated over its published range `x ≥ 11815`
    (Ram13 Cor. 1.4; float check `scripts/moebius_ramare_check.py`: max `0.029496` at `k = 11820`).
    Below 11815 the kernel checks `(k+1) m(k)² ≤ 2` (`Prelim/SmallMoebius.lean`, 51 s; `μ` from
    trial division by squares and `SmallLiou.lamB`).
    * `LiouvilleBound`: `abs_ls_large` covers all `z ≥ 10⁵` with Ramaré for `z/u² ≥ 11815`
      (`log z/log(z/u²) ≤ 1 + (2/9) log u`), giving `0.056 + 0.32 ≤ 0.99`.
    * `G2Bound`: Rankin weight `u^{1/9}` instead of `u^{1/22}`. The `s = 1/9` Euler products are in
      `G2Numerics` (`P₀ = 30`, `p^{1/9}` table), and Lemma 5.1.2 becomes `0.0236/(log x)²`. The (5.31)
      tail is `0.0037`.
  * `mertens_product_small` removed.
    * `F_mid` (`10⁵ ≤ x ≤ 2·10⁸`, three subranges) uses `E1_var` (Büthe's `ψ` to `10¹⁹`, then `E1_diff`
      at `10¹⁹`) and `logF_le'`. The tail of `−log(1 − 1/p)` keeps its `1/(K+1)` factor, giving
      `7/(6⌊√x⌋)`. It also uses `e^η ≤ 1 + 1.02η` instead of `1 + 2η`.
    * Kernel for primes `≤ 10⁵` (`Prelim/SmallMertensProd.lean`, 5.5 min). `log θ = log m +
      log(θ/m)` uses an integer `m` advanced with `θ` and an artanh series for `log(1 + b/a)`.
      `e^γ` comes from a 22-term Taylor sum at `γ ≥ 0.5772156646` (from `RamareWalk`).
    * Kernel pitfall: if a proof term needs `(⟨…, (adv 30 …).1, …⟩).m = (adv 30 …).1`, the kernel
      evaluates `adv` with symbolic arguments and runs out of memory, even after `generalize` (the
      beta-redex is reduced). Fix: state the step lemma for an arbitrary `r` (`Inv_stepR`) and
      instantiate it.
  * 12 axioms (4 own, 8 published).
* Own computations 4 → 2 (2026-11-02): `T2_small` and `T2_mid` removed; (5.31) `T2_le` is proved.
  * `MinorArcs/SmallG2.lean` (kernel, 54 s): walks `n ≤ 10⁴` with `F(r) = μ(r)⌊10³⁰/σ(r)⌋` for odd
    `r`, a binary trie (`T2Kernel.Tr`) of `Ã_d(n) = ∑_{r≤n, d∣r} F(r)` keyed by `d/2`, and
    `G̃(n) = ∑_d μ(d) Ã_d(n)²`, updated at odd squarefree `n` through the divisors of `n` (trial
    division `oddPrimes`, subset products `dvs`). `|G̃(n) − 10⁶⁰ g₂(n)| ≤ 2·10³⁰ n³`.
    * `16 ≤ S < 700`: `T₂(S) = a(n) − a(n/2)/2 + (c(n) − c(n/2))/S` on `[n, n+1)` (`T2_eq_ac`), with
      `a(k) = ∑_{s≤k odd} g₂(k/s)/s`, `c(k) = ∑_{s≤k odd} (∑_{j<k/s} g₂(j) − (k/s) g₂(k/s))`.
      Both change only at odd `k`, by `∓∑_{t ∣ rad k} t Δg₂(t)` (`/k` for `a`); so the kernel needs
      `Δg₂` at squarefree divisors only. Max `0.3712486` at `S = 16`.
    * `700 ≤ S < 10⁴`: `¼ I(S) + J(S)/S`, `I`, `J` at the integers with 6-term artanh bounds for
      `log(1 + 1/n)`. Tightest at `n = 700`.
    * A first version with `O(n)` lookups per `n` for `α_n` hit the kernel's heartbeat limit at
      23 GB; the divisor form needs a few lookups per odd `n`.
  * `MinorArcs/G2Tail.lean`: `∫_{10⁴}^S |g₂|/y ≤ 0.0045` for all `S ≥ 10⁴`.
    * Pointwise `|g₂(y)| ≤ ∑_d f(d)² S_d(N/d)²` and `S_d = ∑_a H_d(a) m(·/a)`; Cauchy–Schwarz with
      weights `H_d(a) λ(da)` (Sedrakyan's form) gives
      `∫_X^S |g₂|/y ≤ ∑_d f(d)² (∑_a H_d(a) λ(da)) (∑_a H_d(a) V(X/(da))/λ(da))`,
      `V(Y) = ∫_Y^∞ m(⌊t⌋)²/t`; with `λ ≈ √V` this is Minkowski's inequality.
    * `V(k)` for `k ≤ 10⁴` (`G2TailNum.lean`, kernel 82 s together with the double sum) from `m(j)`,
      `j < 11815` (as in `SmallMoebius`), and Ramaré's `0.03/log j` beyond (telescoping
      `∑ log(1+1/j)/log²j ≤ 1.00001/log 11815`). `λ(k)` is a power of 2 near `√V(k)` (`Nat.log2`).
    * The kernel sums over odd squarefree `d ≤ 10⁴`, `a ≤ 10⁴/d` (`H_d(a) = σ((a,d))/den₁(a)`), and
      bounds `a > 10⁴/d` by `∑_a H_d(a) ≤ 2 ∏_{p>2} p²/(p²−1) σ(d)/d`, `∏ ≤ π²/8 < 1.2338`
      (Euler product over smooth numbers and `ζ(2) = π²/6`). Total `0.0039975 + 0.0004963` (`d > 10⁴`
      by `∑ 1/d² ≤ 10⁻⁴`).
    * The slack in `∏ p²/(p²−1)` matters: with `1.27` instead of `1.2338` the double sum is
      `0.0158` (the slack is weighted by `V(1) = 0.815`).
    * The pointwise route (Lemma 5.1.2) cannot reach `10⁴`: even with exact `m(k)` the bound is
      about `36/x`; the mean-square route gains `m(k)²` on average instead of its envelope.
  * `T₂(S) ≤ 0.3605763 + 0.000922 + (5/4)·0.0045 ≤ 0.3672` for `S ≥ 10⁴`.
  * [H, Lemma 5.1.2] (`G2Bound.lean`) stays proved but is no longer used.
  * 10 axioms (2 own, 8 published).
* Kernel limits measured (no `native_decide`):
  * about `10⁵` simple steps per declaration is fine and `10⁶` runs out of memory;
  * `Nat.primesBelow 10⁴` is too heavy; chunked checks and verified loops work.

## How small can the small-case computation be? (2026-11-02)

Binary Goldbach up to `B` covers odd `n ≤ C` (the start of the circle method) iff every `x ≤ C` has a
provable prime in `(x − B, x − 4]`. Needed `B` at the top of each range (`scripts`-style estimates):

| `x` | Büthe (`≤ 10¹⁹`) | our explicit formula | RH to `H = 3·10¹²`, ideal |
|---|---|---|---|
| `10¹⁹` | `1.5·10¹⁰` | `1.0·10¹³` | `4.8·10¹¹` |
| `10²¹` | — | `1.0·10¹⁴` | `5.9·10¹²` |
| `10²³` | — | `1.0·10¹⁵` | `7.1·10¹³` |
| `10²⁵` | — | `1.05·10¹⁶` | `8.3·10¹⁴` |
| `10²⁷` | — | `1.44·10¹⁷` | `1.0·10¹⁶` |

(ideal = `max(30x/H, √x log²x/(4π))`: unverified zeros force a smoothing width `≳ 1/H`, and the zero
sum is `≍ √x log² x` even under RH.) So `B ≈ 10¹⁰–10¹²` needs the circle method to start near
`10¹⁹–10²⁰`.

How low can the circle method start?
* [H]'s scheme (`minor_arc_total_numerics.py` at smaller `y`): minor arcs `1.04` at `N = 10²⁷`,
  `1.15` at `10²⁶`, `1.29` at `10²⁵` (needs `< 1.049`). The growing term is the tail (14.43) at
  `r₁ = (3/8)y^{4/15}`.
* Our repair 3 (levels up to `r₂ ≈ x^{0.3}`, `minor_arc_y_scale_repair.py`, ideal closed form):
  `Z = 0.873` (`N ≈ 10²⁷`), `0.929` (`10²⁶`), `1.004` (`10²⁵`), `1.109` (`10²⁴`), `2.65` (`10²³`).
  The Lean majorants (cells) lose about `0.09` at `10²⁵`, so realistically `C ≈ 10²⁶`, perhaps `10²⁵`.
  Major arcs, (14.7) and the non-prime terms would also have to be redone below `10²⁷`.
* Hard floors: `r₀ = 150000` is fixed by Platt's GRH range (`q ≤ 3·10⁵`); Thm 3.1.1 (as formalized)
  needs scale `≥ 2.16·10²⁰` and `r ≤ y^{1/3}/6`, so `y ≥ (6r₀)³ ≈ 7·10¹⁷` at the very least.
* No elementary bridge: one prime from a short interval plus binary Goldbach is the only route
  (ternary = binary on average needs the circle method again); a prime ladder with gaps `≤ B` up to
  `10²⁷` needs `10²⁷/B` certified primes (`10¹⁵` for `B = 10¹²`).

Conclusion: `B` can come down to about `10¹⁶` (start the circle method at `10²⁵–10²⁶`) and perhaps
`10¹⁵` (with a short-window smoothing near the RH-to-`H` floor), each a large rework; `10¹⁰–10¹²` is
out of reach with RH to `3·10¹²`, Platt's GRH range and [H]'s minor-arc method.

## One axiom per cited theorem; Büthe's θ bounds dropped (2026-11-02)

* `platt_odd`, `platt_even` → one axiom `platt_verification` (Platt's Thm 7.1, the two parities as a
  conjunction); `platt_odd`, `platt_even` are now theorems with the same statements. 8 axioms.
* `buthe_psi`, `buthe_theta` → one axiom `buthe_bounds` (Büthe's Thm 2: (1.5) and (1.6)–(1.7)). 7 axioms.
* Then **Büthe's `θ` bounds (1.6)–(1.7) dropped**: the axiom is (1.5) alone (`buthe_psi`), and every `θ`
  bound is derived from it via `|θ − n| ≤ 0.94√n + (ψ − θ)(n)`:
  * `ψ(N) − θ(N) ≤ √N (1.0054 + 0.048 log N)` on `[10⁹, 10¹⁹]` (`psi_sub_theta_le_buthe`: the squares
    give `θ(⌊√N⌋)`; a prime with `m³ ≤ N` has `961 m² ≤ N`, so `m ≤ ⌊√N⌋/31`; Büthe at both). With
    `cube_div_sqrt_le`/`quart_div_sqrt_le` at `log 10⁹`: `1.9454 L³/√x + 0.048 L⁴/√x ≤ 0.83 < 1`, so
    `theta_explicit` now starts at `10⁹` (was `2·10⁸`, where `n/log³n` is only `2.03 √n`).
  * `|θ(n) − n| ≤ 2.37 √n` for `12 ≤ n ≤ 10¹²` (`thetaN_close_small`, from `nonprime_small`).
  * `F_mid` covers `[10⁵, 10⁹]` with `2.37` (worst side condition `2.305 < 2.5`); `F_large`, `psi_err`,
    `E1_diff`, `thetaN_large`, `psi_upper_of` start at `10⁹`.
  * (2.19): `logsq_mid` (Abel summation with `thetaN_ge`) now covers `[40000, 10¹²]`; `logsq_large` only
    `N > 10¹²` (with `2.37` it would fail near `10⁶`: room `0.003N`), where `thetaN_close` is `thetaN_large`.
  * `SmallCases`: `θ ≤ ψ` and `ψ − θ ≤ 2.001 log n √n` below `10¹⁹`.

## Binary Goldbach needed only to `1.45·10¹⁷` (2026-11-02)

* The θ error at `10²⁷` sets the range: binary Goldbach up to `N` suffices if
  `(θ − x)⁺ + (x − θ)⁺ < N − 4` there. With `psi_plateau`'s old `15000√x` this was `9.96·10¹⁷`.
* The line-zero constant (`LineB`, `14990`) is replaced by `LineB2` (`ZetaZeroSums.lean`, "Sharper
  constants"; used by `SsumG_gsm_err` → `ErrG` → `psi_plateau` only; `PsiLarge`/`PsiRange1`/`PsiAsymp`
  keep `LineB`). Steps, with the binary Goldbach range each gave:
  * window weight `2/(1 + 3.48d)` → `1/max(½, hd)` (`|ρ| ≥ max(½, |γ|)`), about ×0.55;
  * `2e^{|a|}` → `e^{a/2} + e^{b/2}` with `e^{b/2} = √(y₀/x) ≤ 3.2·10⁻⁵` (`norm_Mg_line_le'`), ×0.5;
  * window height `h` and Jensen radius `r ≥ √(1.5² + (h/2)²)` as parameters: `h = 6`, `r = 3.36`
    (×0.88; `LineB2 ≤ 3658`, `N = 2.8·10¹⁷`);
  * the two windows at `|γ| ≤ 6` counted by Jensen at their centres `±3` (`35.9` zeros each instead
    of `274.7`; `LineB2 ≤ 2703`, `N = 2.2·10¹⁷`);
  * every window counted by Jensen at its own centre `(d + ½)·6` (`line_sum_leH`, `count_line_windowC`):
    `log(B(6d + 3)/0.355) ≤ 30.17 + 10 log d + 25.17/d` (`logB_window_le`, from `log_BPz2_le'` and
    `log(αd + β) ≤ log α + log d + β/(αd)`), summed by telescoping against `a log d + (b/2) log² d`
    (`sum_log_div_le`; the step uses `1/d ≤ log(d/(d − 1)) ≤ 1/(d − 1)`). The window sum is `≤ 765`
    (`window_sum_le`), `LineB2 ≤ 1531`.
  So `psi_plateau`: `|ψ(x) − x| ≤ 2.15·10⁻¹¹x + 1533√x + 4.2·10¹⁰` (`x ≥ 10¹⁹`).
* `theta_bound`: `−7.401·10¹⁶ ≤ θ(n) − n ≤ 7.003·10¹⁶` on `[1423, 10²⁷]` (the lower side has
  `ψ − θ ≤ 2.001·63·√n`); sum `1.4404·10¹⁷`, so `binary_goldbach_input : BinaryGoldbachUpTo (145 * 10 ^ 15)`.
* [OeSHP14] (PDF in hand): verification to `4·10¹⁸`, full double-check to `3·10¹⁷` (Table 1, §1.3;
  AXIOMS.md had `4·10¹⁷` from the project page). `1.45·10¹⁷` is inside the double-checked range.
* What is left: `2·1533√x ≈ 9.7·10¹⁶` and `2·2.15·10⁻¹¹x ≈ 4.3·10¹⁶` at `10²⁷`.
  * The `x` term (`Kδ = 64/H`, the Gaussian smoothing width needed to kill zeros above `H`) alone
    forces `N ≳ 4.3·10¹⁶`.
  * The `√x` term is Jensen's zero count, about 8 times the true density (`≈ (h/2π) log(t/2π)` per
    window). A smaller Jensen disc needs a polynomial bound for `ζ` on a smaller disc than
    `BPz2`'s radius `10` (about ×0.8); the Riemann–von Mangoldt formula with an explicit `S(T)`
    would be a large project.
* Other papers checked against the PDFs: Platt–Trudgian (abstract), Platt GRH (Thm 7.1), Büthe
  (Thm 2), Ramaré–Zuniga-Alterman (Cor. 1.2, 1.3), [Ram95] Lemma 3.4 and (3.9) (Finding 5 confirmed;
  product over primes `< 10⁷` recomputed: `8.07754`). [HP13]'s introduction describes the
  Ramaré–Saouter route (RH to a height + binary Goldbach), which `SmallCases.lean` now follows.

## Prime ladder replaced (2026-11-02): 9 axioms (2 own, 7 published)

* Assessment of the published axioms (user asked which could be formalized or weakened):
  * `prime_ladder_input`: replaceable, done below.
  * `binary_goldbach_input`: stays (an exhaustive search). With `|θ − x| ≤ 6·10¹⁷` it could be
    weakened to about `1.1·10¹⁸`, but it is the same kind of computation.
  * `rh_upto`, `platt_odd`, `platt_even`: stay. The heights and moduli are pinned by the explicit
    formula near `10¹⁹` and by the major arcs (`r₀ = 150000`, heights near `10⁸/q`).
  * `buthe_psi`, `buthe_theta`: stay. From `rh_upto` alone the explicit formula gives about
    `√x log²x/(8π)` below `10¹⁹`, 10–80 times `0.94√x`; (2.13), the Mertens product on
    `[10⁵, 2·10⁸]` and the θ bounds of [H, §2] are tight.
  * `ramare_moebius`: stays. Its proof rests on computations of `M(x)`; our uses need a constant
    near `0.05/log x` (g₂ tail). `MoebiusBound.lean`'s `0.55/(log x − 0.7521)` is derived from it
    (AXIOMS.md's Outlook called it elementary; fixed).
* `Helfgott/SmallCases.lean`: `theta_bound` (`|θ(n) − n| ≤ 6·10¹⁷` for `1423 ≤ n ≤ 10²⁷`):
  `buthe_theta` below `10¹⁹` (`1.95√n ≤ 7.8·10⁹`); above, `psi_plateau` (`2.15·10⁻¹¹ n + 15000√n +
  4.2·10¹⁰ ≤ 5·10¹⁷` at `10²⁷`, mostly `15000√n`) and `ψ − θ ≤ 2.001 log n √n ≤ 4.1·10¹⁵`. For odd `n > 4·10¹⁸ + 3`,
  `θ(n − 4) − θ(n − 4·10¹⁸) > 0` gives a prime `p ∈ (n − 4·10¹⁸, n − 4]`, and binary Goldbach takes
  `n − p`. Below, `n = 3 + (n − 3)`.
* `ternaryGoldbachUpTo : TernaryGoldbachUpTo (10 ^ 27)`; `Reduction.lean` and `PrattPrime.lean`
  (ladder reduction, certificates for `4·10¹⁸ + 2`) deleted. Stale docstrings in `Main.lean`
  ("still `sorry`") and `LambdaMu.lean` (Ramaré "for `x ≥ 10¹⁰`") fixed.

## Axiom audit (2026-11-01): `AXIOMS.md`

Every axiom has been checked against its source or script, and all scripts were re-run. Findings:

* **[H, (5.32)] is false for `v = 2`, so `integral_H2_le` ((5.36)) is false.**
  * Exactly, `∫₁⁴ T₂/S = 0.53344 > 0.37273 log 4`.
  * True version: `∫₁ᵀ H₂/S ≤ 0.15107 log T + 0.0231` (`scripts/h2_integral_check.py`; the supremum
    of the excess is `0.023059`, constant from `T = 16` on).
  * **Done.** The axiom is replaced by the corrected bound. `integral_H2_comp` gives
    `0.15107 log(x/UV) + 0.0231`, and the Type II totals have `0.60428 Λ₀ + 0.0924 + 8ζ³…`.
  * First case: our `ζ³` bound (`≤ 0.2355`) had room, so `B ≤ 0.30214 log t + 0.7468` (was
    `0.67506`). By AM–GM with the same `√ρ = 1.84332`, Thm 3.1.1's constant becomes `0.8764` (was
    `0.8103`); `R` is unchanged.
  * Second case: `a1B0 = 0.15107(L − 8.09) + 0.0501` (shift `7.7583`) and
    `bB0 = 0.15107(L − 9.4778) + 0.0366` (shift `9.2355`). The regenerated pieces stay below
    `1.413` (worst `1.3991` and `1.2789`).
  * The cells (`gen_cells.py`) have a worst total of `0.965`, so (14.49) stays `1.0376`.
  * New checks: `scripts/t2_check.py` ((5.31) on `[16, 10⁵]`, float, max `0.371249`),
    `scripts/eta_plus_check.py` ((9.94) via FFT, float), and `H2_le` exactly in
    `h2_integral_check.py`.
* **`prime_ladder_input` restated with gaps `≤ 4·10¹⁸`**, as in [HP13] and [H, §1.6]; before, it
  said `≤ 4·10¹⁸ − 4`. `ternaryUpTo_of_ladder_two` uses binary Goldbach up to `N`, `N + 2` as a sum
  of two primes, and gaps `≤ N`. `PrattPrime.lean` proves the two primes by kernel-checked Pratt
  certificates (`powModAux` and `lucas_primality`, with `decide +kernel`).
* Docstrings fixed: `eta2_fourier_bound'` is [H, Lemma B.1.2, (B.6)], and `rh_upto` notes that
  `γ ≤ 0` is classical.

## Dusart replaced: no `sorry` left (2026-11-01)

`dusart_theta` is gone. `Prelim/ThetaExplicit.lean` `theta_explicit`:
`|θ(n) − n| < n/log³n + ε_pl(n)·n` for `n ≥ 89 967 803`, `ε_pl = 2.2·10⁻¹¹` for `3400 < log n < 20000`
(`epl`), else `0`. Ranges:
* `n ≤ 10¹⁰`: `theta_cube_small` (numerical axiom, `scripts/theta_cube_check.py`, max ratio `0.99934`).
* `10¹⁰ < n ≤ 10¹⁹`: `buthe_theta` ([Büthe 2018, Thm 2], `|θ − n| ≤ 1.95√n`, numerical axiom).
* `10¹⁹ ≤ x < e²⁰⁰⁰⁰`: `Explicit/PsiPlateau.lean` `psi_plateau` (`|ψ − x| ≤ 2.15·10⁻¹¹x + 15000√x + 4.2·10¹⁰`;
  `δ = 8/H`, `K = 8`, `H = 3·10¹²`, RH to `H` = `rh_upto` [Platt–Trudgian 2021], numerical axiom).
* `e²⁰⁰⁰⁰ ≤ x < e³⁵⁰⁰⁰`: `Explicit/PsiRange1.lean` `psi_range1` (`2.1·10⁻¹⁴x`; `δ = 1.4·10⁻¹⁵`, `K = 9`,
  zero-free region up to `Γ = 6.43·10¹⁵`).
* `x ≥ e³⁵⁰⁰⁰`: `Explicit/PsiAsymp.lean` `psi_asymp` (`0.2x/log³x`; `K = ℓ+4`, `Γ = L⁴/5`, `δ = 5(ℓ+5)/L⁴`).
Machinery: `Explicit/GaussSmooth.lean` (Gaussian smoothing `gsm`, entire Mellin transform `Mg`),
`Explicit/PsiSandwich.lean` (`ψ` between two smoothed sums), `Explicit/ZetaZeroSums.lean` (line zeros by
`3.48`-windows, Gaussian tail), `Explicit/PsiExplicit.lean`, `Explicit/PsiLarge.lean` (zeros above `H` by
`zero_free`).

Consumers absorb `ε_pl`:
* `LambdaMu`: pointwise uses have slack (`psi_bounds` key `0.00039 + 2.2·10⁻¹¹`, `psi_lower_all`,
  `psi_upper_all` `0.000159`); `mertens_lower_nat` uses `sum_epl_div_le` (`Σ ε_pl(n)/(n+1) ≤ 3.66·10⁻⁷`);
  `logsq_large` ((2.19)) pays `log N · 2.2·10⁻¹¹ N ≤ 4.41·10⁻⁷N` (slack `≈ 0.0031N`).
* `MertensProduct`: `E1_diff` gains `Pth M` (`3.7·10⁻⁷` if `log M < 20000`, `epl_total_le`); `F_large`
  (`ηL² ≤ 0.4772`, `uL ≤ 0.0032`) still closes against `2.5/L`.
* `MoebiusBound`: `Dp` gains `Pth M`; `partC_pth` (`≤ 0.0074`: only blocks with `log M_j < 20000`, i.e.
  `j < 28827`); `K_partC ≤ 0.0452`, `K_bound ≤ 0.55` (`0.4259 + 0.0755 + 0.0452 = 0.5466`), so
  `|∑_{n≤x} μ(n)/n| ≤ 0.55/(log x − 0.7521)`.
* `LiouvilleBound`: `Σ_{u≤N} 1/u² ≤ π²/6 < 1.64495` (`sum_inv_sq_le_pi`, Mathlib `hasSum_zeta_two`) in
  `abs_ls_big`: `0.55(1.034·1.64495 + 0.09·1.0117) + 0.0042359 = 0.98980 ≤ 0.99`.

## Status (2026-11-01, final)

* `ternary_goldbach` depends on **no `sorry`** and 36 axioms (`#print axioms`: the 33 before plus
  `rh_upto`, `buthe_theta`, `theta_cube_small`). The audit later found `integral_H2_le` to be false
  (see "Axiom audit" above).

## Status (2026-11-01, latest)

* `ternary_goldbach` depends on 1 `sorry` — `dusart_theta` — and 33 numerical axioms. Props 9.3.2, 9.4.2,
  9.5.1 are proved (`Explicit/`, `MajorArcs/Prop932.lean`, `Prop942.lean`, `Prop715.lean`) with weaker
  constants; Cor 7.1.3, Thm 7.1.4, Prop 7.1.5, (14.7) restated; (14.27) still `1.049`.

## Status (2026-11-01, later)

* `ternary_goldbach` depends on 4 `sorry`s — `dusart_theta` and the three cited explicit formulas
  [H, Props 9.3.2, 9.4.2, 9.5.1] (conditional on GRH up to `T₀`) — and 33 numerical axioms.
  **(14.27) is proved** (`MajorArcs/MajorTotal.lean`, constant `1.049` for [H]'s `1.058259`), so all of
  `Helfgott/Inputs.lean` is proved; the final margin is `1.049 − 1.0376 = 0.0114 x²/κ`.

## Status (2026-11-01)

* `ternary_goldbach` depends on 5 `sorry`s — `major_arcs_input` ((14.27)), `dusart_theta`, and the three
  cited explicit formulas [H, Props 9.3.2, 9.4.2, 9.5.1] (conditional on GRH up to `T₀`) — and 33 numerical
  axioms. (14.7) is proved (`MajorArcs/L2Major.lean`), with a Cauchy–Schwarz-free error analysis that
  gives `8.688x … 8.709x` (so [H]'s `0.0754` slip is moot); it brought Prop 9.4.2 onto the main path and
  added the numerical axiom `Σ_{q≤150000 odd} μ²(q)/φ(q) = 6.798779…`.

## Status (2026-10-31)

* `ternary_goldbach` depends only on the 4 `sorry`s in `Helfgott/Inputs.lean`: the major arcs
  (14.27), the minor arcs (14.49), binary Goldbach up to 4·10¹⁸, and the prime ladder.
* **(14.49) is now stated with `1.0376` instead of [H]'s `1.00948`** (final margin `0.020659`
  instead of `0.048779`; `final_inequality(_crude)` re-proved). That is what [H, §14.3] gives
  when re-run with the Theorem 3.1.1 we actually proved (`0.8103`, `3.8 x^{5/6}` instead of
  `0.5`, `3.36`): `scripts/minor_arc_total_numerics.py` reproduces [H]'s `M ≤ 0.80508` as
  `0.80279` (slightly less rounding) and gives `M ≤ 0.82744`, `Z ≤ 1.037499 x²/κ` with the
  corrected constants. The changes come from `g(r₀)` in (14.37) (`0.38491 → 0.39761`), the `+0.5`
  term of `f₁` and `f₂` in (14.47) (`0.11438 → 0.11802`), and (14.43) (`0.30351 → 0.31181`).
  Lemma 11.2.1 still holds (`g/h ≤ 0.61`).
* **Decision (2026-10-30): option (a).** Keep `minor_arcs_input` as a cited input with the
  caveat below, and keep formalizing the parts of Part I, Ch. 11, Ch. 12 and Prop 13.1.2 that do
  not depend on the scale question.
* ✅ Prop 13.1.2 (`Prop1312.lean`): any measure space; nested measurable `M n`; conclusion
  `g(r₀)(H(r₀) − I₀) + Σ_{r₀<n≤r₁} g(n)(H(n) − H(n−1))` (discrete; `≤ ∫ g H'` for monotone `g`, `H`).
* ✅ **Ch. 12: Prop 12.1.2 proved** (`LargeSieveProof.lean`, no `sorry`), so Cor 12.2.5 (12.42)
  depends only on the trusted computation Prop 12.2.4. Route: Bombieri's identity in the form
  `φ(q) Σ_b^* |S(b/q+β)|² = Σ_{Ψ mod L, cond Ψ ∣ q} w(q, cond Ψ) |S_{Ψ⁻¹}(β)|²`. That uses
  Parseval over characters, `gaussSum_mulShift_eq`, `τ(χ↑) = μ(r)χ(r)τ(χ)` (ℕ-indexed Möbius proof),
  `|τ(χ)|² = N` for primitive `χ`, and the lift to one modulus `L = ∏_{q ≤ 2Q} q`, which avoids
  dependent types. Then `weight_sum` gives `Σ_{q̃ ≤ X} [c∣q] w/φ(q) = (c/φ(c)) κ_c G_{c̃}(X/c̃)`.
  The arcs part is periodization, covering, and Farey disjointness at level `Q`. Pointwise in `β`,
  the hypothesis on `G` is used with `s = 2Q₀/m_{Q₀}(β)`.
  **Change from [H]: `δ₀ ≥ 2` instead of `δ₀ ≥ 1`**. The proof needs primes `n > √x` to be coprime
  to every modulus `q ≤ 2Q = √(2x/δ₀)`, which needs `2Q ≤ √x`. [H] uses `δ₀ = 8`.
* ✅ **Thm 13.2.1, conditional** (`Thm1321.lean`, depends only on Prop 12.2.4):
  `thm_13_2_1_conditional` instantiates Prop 13.1.2 with `M n = 𝔐_{8,n}` at scale `x`, the ℓ²
  bound from Cor 12.2.5 (`Q₀ = n + 1`, `δ₀ = 8`) and Plancherel at the top level `r₁`. The ℓ∞ input
  is a **hypothesis** `hv`: `|S_{η_*}(α,x)| ≤ g(n)` off `𝔐_{8,n}(x)`. `OffArcs.lean` proves the exact
  arc criterion behind [H]'s ℓ∞ step: `2α = a/q + δ/y` with `q ≤ r`, `|δ|q < δ₀r` ⟹
  `α ∈ 𝔐_{δ₀,r}(y)`, for every parity case (`mem_majorArcs_of_approx`). So off `𝔐_{δ₀,r}(y)`,
  `r_α ≥ r` (`le_rAlpha_of_not_mem`), giving `norm_S_le_off_arcs`. `hv_of_split` reduces `hv` to that
  plus a bound on the **gap `𝔐_{8,n}(y) \ 𝔐_{8,n}(x)`**, the one missing ingredient. (Also still
  needed for (14.49): splitting `S_{η₊}` into primes `> √x` plus the rest [H, §13.2], and the
  numerics of §14.3 for an explicit `g`.)
* ✅✅ **(14.49) fully assembled, including the numerics** (2026-10-31). `numerics_M`
  (`MinorArcs/NumericsFinal.lean`) is proved: 9 generated cells for `x ∈ [4.9·10²⁶, 4.9·10¹⁰¹]`
  (`scripts/gen_cells.py` → `NumericsCells.lean`, worst `Mexpr ≤ 0.960`), and `asymp_goal`
  (`NumericsAsymp.lean`, `r₂ = ⌊y^{1/4}⌋`, `≈ 0.692`) beyond. `ternary_goldbach` now depends on
  28 explicitly labelled items (`scripts/sorry_deps.lean`): the 3 remaining `Helfgott/Inputs`
  items (major arcs (14.27), binary Goldbach ≤ 4·10¹⁸, prime ladder), the cited Part II results
  `cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7`, `E_le_14_28`, and the literature bounds in
  `Prelim/` ([RS62] etc., Lemma C.2.2): 16 `sorry`s now (large sieves proved) ((2.20) proved 2026-10-31, `Prelim/MoebiusCoprime.lean`). Plus 7 **numerical axioms** (Lean `axiom`s,
  2026-10-31, at the user's request; listed in README "Numerical axioms"): `prop_12_2_4`, the
  (B.6)/(B.2.3) Fourier bounds, `integral_H2_le`/`H2_le`/`T2_le`, `fsq_le`.
* ✅ **`minor_arcs_input` is now a theorem** (`Helfgott/Inputs.lean` → `MinorArcs/MinorTotal.lean:
  minor_total`). Its dependency closure: the trusted inputs of Thm 3.1.1, Prop 12.2.4 (trusted
  computation), the **cited Part II results** `cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7` (14.7),
  `E_le_14_28` (`MinorArcs/PartIICited.lean`), and **`numerics_M`** (the remaining numerical
  lemma: ∃ level `r₂` with the size conditions and `Mexpr x r₂ ≤ 1.037`, all `x ≥ 4.9·10²⁶`;
  checked by `scripts/minor_arc_cells_check.py`, to be formalized).
* ✅ **The Ch. 13 scale erratum is fixable** ("repair 3" in the erratum section below:
  everything at scale `y`, a fresh Dirichlet approximation per scale `wy`, levels up to
  `x^{0.3}`, and Cor 7.1.3 on the base gap). `Z ≤ 0.866 x²/κ < 1.058259`. Formalizing it is the
  current work.
* (Superseded.) **Blocker for (14.49): [H, Thm 13.2.1] mixes two scales of major arcs** (see the section
  "Ch. 13: scale erratum" below). As written, [H]'s minor-arc bound covers only the complement
  of the arcs at scale `y = x/κ`, while (14.27) and our `minor_arcs_input` use the arcs at scale
  `x`. The obvious repairs fail numerically. Decide how to proceed before formalizing Ch. 13.
* **Next: Ch. 11 (Prop 11.2.3), then Ch. 12, Ch. 13 → (14.49).** See the Prop 11.2.3 erratum
  below before formalizing it. Done so far: (11.9) `S_etaStar_eq`, `norm_S_etaStar_le`
  (`EtaStar.lean`, no `sorry`); Theorem 3.1.1 at scale `wy` with `δ ↦ wδ`
  (`theorem_3_1_1_scaled(_le_one)`, `EtaStarBound.lean`); (11.11) `norm_S_eta2_le_gx`
  (`GBound.lean`, `q/φ(q) ≤ Ϝ(r)` via the trusted Lemma C.2.2); **`gx_antitoneOn`**: `g_x(r)` is
  non-increasing on `[670, x^{1/3}/6]` (`GMono.lean`, no `sorry`; proved via
  `Q(log r) r^{-p}` with `Q' ≤ pQ`, not [H]'s (11.23)–(11.25)). **`prop_11_2_3`** (`Prop1123.lean`):
  Prop 11.2.3 in corrected form, `|S_{η_*}| ≤ y(∫_{w₀}^{w₁} Gφ + 17(∫_0^{w₀}φ + ∫_{w₁}^∞φ))` for
  any integrable majorant `G(w) ≥ g_{wy}(min(1,w) r)` (trivial bound `17z` from Mathlib's
  Chebyshev `ψ ≤ (log 4 + 4)x`; same 20 trusted items as Thm 3.1.1, checked with
  `scripts/sorry_deps.lean`). Still to do: closed-form/numerical majorants `G` (the analogue of
  [H]'s `g_{y,φ}`, via Lemma 11.2.2 convexity and `C_{φ,2,K}`). Old list, for reference: the region
  `w < 1/K` (trivial bound `|S_{η₂}(α,z)| ≤ S_{η₂}(0,z) ≤ 1.04488 z`, Cor. C.1.3, trusted), the
  large-`w` tail, and integrating against `φ` (convexity, Lemma 11.2.2; `C_{φ,2,K}`).
* Part I (minor arcs):
  * [H, §2.3] proved (`MinorArcs/FourierSums.lean`), [H, §4.1] proved (`MinorArcs/TrigSums.lean`).
  * [H, §4.2]: **Lemma 4.2.2** (`TypeIProof.lean: lemma_4_2_2`) and **Lemma 4.2.3**
    (`TypeILogProof.lean: lemma_4_2_3`, the case §6.2.1 uses) are proved. Their only non-standard
    dependencies are the trusted `eta2_fourier_bound'` ([H, (B.6)]) and `eta2log_fourier_bound`
    ([H, Lemma B.2.3]); checked by temporarily turning them into `axiom`s and running
    `#print axioms`.
  * **Lemma 4.2.4** (`TypeI2Rest.lean: lemma_4_2_4`) is proved, both cases. Its non-standard
    dependencies are `eta2_fourier_bound'`, (2.12), (2.15), (2.20) (checked with a script that
    walks the dependency closure for `sorryAx`; (2.16) turned out not to be needed).
  * Thm 3.1.1 is proved (see Ch. 6 below).
* **Lemma 4.2.4: how it was done / decisions** (all documented in the `bound_4_5x` docstrings):
  * `typeI2 = ∑_{a odd} c(a) T_{a,∘}`, `|c(a)| ≤ log a`; main term (4.50) with factor `3/2` (erratum
    in (4.55)).
  * Rest: weights `log m`; on each block of length `q` use `log` of the block's upper end
    (`sum_log_mul_le_blocks`), with the per-block bounds `block_R2`/`block_R3` extracted from
    Lemma 4.2.2. (R2): `∑(j+3/2) log((j+3/2)q)` via `t log t` increasing and `F(t)=(t²/2)(log t-1/2)`
    (upper limit `D'+2q`), giving `(2√c₀/π) D'(log D' - 1/2) + O(√x log D)`. (R3): `log(R+q)` for the
    first block, then `log(min(R+(j+1)q, D)) ≤ log y_j + q/y_j` and `∑ log y_j ≤ (G(D)-G(R))/q + …`,
    `G(t) = t(log t - 1)`. Case (a): weight `log M` on `(0, M]` (crude, costs `Bc·M ≤ Bc(1+ε)Y/2`),
    second approximation above `M` (`sum_R3W'`, general `q' ≤ 2(1+ε)M`).
  * **Errata/changes**: `c₁ = 1 + |η'|₁/(x/D)` (odd `n`; [H] prints the all-`n` value `2x/D`);
    (4.59)–(4.60) as printed is garbled ("`≤ x`" for "`≤ log x`") and its constant could not be
    reproduced — our (R2) gives `(2√c₀/π)√(2c₂x)(2 + 12 log 5D) + 5c₀/6π²` instead of
    `(25c₀/4π²)(2c₂)^{3/2}√x log x` (similar size); `log⁺(q/2)` for `log(q/2)` (negative at `q=1`).
    Leading terms are [H]'s: `(2√(c₀c₁)/π) D log(D/√e)` in (b), `D log(D/e)` in (a); the `q`- and
    `x/Q₀`-terms have the same shape but cruder constants (`bound_4_52` keeps `x/Q₀`, which is
    `≤ √x/2` when `Q₀ ≥ 2√x`). Hypotheses: `x ≥ 10`, `UV ≥ 2` (instead of `x ≥ e²c₂/2`);
    [H]'s `UV + (19/18)Q₀ ≤ x/5.6` is not needed.
  * **To check in Ch. 6** (§6.2.2): plug our `bound_4_51/52` in place of [H]'s; the lower-order
    changes should be harmless, but the corrected `c₁` and the (R2) constant must be re-run.
* **Ch. 5, §5.2 (S₂) done** (`MinorArcs/TypeII.lean`, `v = 2`, i.e. `m` odd):
  * Trusted (`Prelim/LargeSieveMV.lean`): optimal large sieve `(N - 1 + δ⁻¹)` (needs `δ ≤ 1` for a
    single point), MV weighted large sieve `∑ (N + (3/2)δ_r⁻¹)⁻¹|S|² ≤ ‖a‖²`, [MV73, Lemma 8]
    `∑_{r≤R}(1+r/R)⁻¹μ²/φ ≥ log R + 0.25068` (`R ≥ 2`, with [H]'s numerical check below 100).
  * Proved: Montgomery's inequality (ω(p)=1: Ramanujan sum `c_r(n) = μ(r)` + Cauchy–Schwarz),
    (5.41) via `rad`/σ-multiplicativity, Lemma 5.2.1 (both parts), Lemma 5.2.3 (5.50)–(5.52),
    Prop 5.2.4 (5.53)–(5.57).
  * **Errata/changes**: Lemma 5.2.1 needs `R ≤ W'` (primes `p > W'` coprime to `r ≤ R`) — we cap `R`
    (statement (ii) takes any `1 ≤ R ≤ W'` with `qR²(ν+υ) ≤ 1`, gain `(φ(q)/q) log R`);
    (5.52) must be over odd `m` (display omits it); (5.51)/(5.54): `#(W', W] ≤ W/2 + 1`, not
    `W/2`, so we assume `W ≥ 50000` (the slack `1 - 3σ/(1-σ/3.5) = 0.0054` absorbs the `+1`);
    `σ₀ = 0.30286` (rational) instead of `σ = e^{-0.50136}/2`. (5.56) is stated as (i) without and
    (ii) with the log gain (`R` capped at `W'`), avoiding `min(1, ·/log)` with `log ≤ 0`.
* **Ch. 5, §5.1 (S₁) done** modulo numerics (`Prelim/SqfreeCount.lean`, `MinorArcs/S1Lemma.lean`,
  `MinorArcs/TypeIIS1.lean`):
  * Proved: the reduction (5.7)–(5.8) (`S1_eq`, bijection `(m,d₁,d₂) ↔ (s,r₁,r₂,l)`); Lemma 5.1.1
    for `v = 2` (`lemma_5_1_1`; main-term constant `(6/π²)P/σ(P)` from Mathlib's
    `L(χ₀μ, 2) = 1/L(χ₀, 2)`); (5.19) (`integral_g2`); **(5.34) `S1_bound`**.
  * Numerical axioms: `fsq_le` (`f(X) ≤ 1.27X`, [H p. 83]; provable: reduce to integers `n ≤ 37` using
    `∑ μ²(m)/m² = 15/π²` — the extremal case `n = 2` needs `15/π² ≤ 1.52`, i.e. `π² ≥ 9.8684`);
    `T2_le` (`T₂(S) ≤ 0.37273` for `S ≥ 16`: Lemma 5.1.2 + the computations of [H pp. 90–92]);
    (5.36) `integral_H2_le`, (5.37) `H2_le`.
  * Changes: `S1_bound` assumes `U ≥ 1` (so `x/(WUs) ≤ x/W`; harmless in Ch. 6). `H₂` is defined
    with the exact triple sum `T₂` in place of the book's computable bound `G₂ ≥ T₂`. The error
    constant `1.27(1+1/√2)(1-2^{-3/2})³ ζ(3/2)³ ≈ 0.586 ζ(3/2)³` is rounded up to `1.27 ζ(3/2)³`
    as in [H]. `T₂(S) = 1 - 1/S` on `[1, 2)` (matches [H]'s `G_v`).
* **Ch. 6 in progress.**
  * Step 1 ✅ `MinorArcs/Decomposition.lean`: (3.11) `S_{η₂} = S_{I,1} - S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}`
    (`decomposition`, `U V : ℕ`), from Vaughan via `sum_odd_conv`; `S_{I,1} = typeILog`,
    `S_{I,2} = typeI2`.
  * Step 2 ✅ `MinorArcs/TypeIIReduction.lean`: (5.2)–(5.5): `η₂(mn/x) = 4∫ 1[…] dW/W`,
    `S_{II} = 4∫_V^{x/U} IIsum(W) dW/W`, `|IIsum| ≤ √S₁(√S₂ + √S₃)`, `S₃ ≤ (x/2W+1)·1.4262²W`
    (trusted [RS62, Thm. 13] in `LambdaMu.lean`); `norm_typeII_le` takes any integrable majorant
    `g(W)`. Needs `U ≥ 1`, `V ≥ 2`, `V ≤ x/U`.
  * Step 3a ✅ `MinorArcs/TypeIITools.lean`, `MinorArcs/TypeIITotal.lean`: **`typeII_637`**, our
    (6.37) (`q ≤ V/2e`, any `δ`, `U, V : ℕ`, `V ≥ 50000`, `Q ≥ 3.5x/U`). Main term exactly [H]'s
    `x/√(2φ) √((Λ₀+Φ)(0.60428Λ₀ + 8κ₀ζ³√(x/V)/U))`; secondary terms cruder:
    `4√(κ₁qx/2φ)(2√(x/U) + √log 2q (2e√(2q) + 4√((x/U)/log(x/2Uq))))` (vs [H]'s
    `√2κ₂√(q/φ)(1+1.15√…)x/√U`; we replace the numerical (6.22) `2.3√(T/log T)` by a split at `ce²`)
    and `8·1.4262 x√(κ₁(1/2+1/U))/√V` (vs `κ₉x/√V`). `κ₁ = 2/π² + κ₀ζ³√(x/V)/U` kept exact (no
    (6.17) needed). `H₂` now uses `max(T₂, 0)` (so `H₂ ≥ 0`); trusted inputs as listed by
    `#sorry_deps`, plus the TODO `intervalIntegrable_H2_div`.
  * Step 3b ✅ `MinorArcs/TypeIITotalGen.lean`: `typeII_gen` (any `c`, `m` with
    `S₂ ≤ (m x/(φL) + (q/φ)W/L)Σ`, `L = log(W/c)`), and **`typeII_640`** (our (6.40): `|δ| ≥ 8`,
    `c' = |δ|q(1+ε₁)/4`, `c'e ≤ V`, `x ≤ Q²`), with `S2_le_640` from (5.56)(ii) (`R = √(W/c')`).
    Main term `2x/√(|δ|φ) √((Λ₀+Φ)(0.60428Λ₀ + 8κ₀ζ³√(x/V)/U))` as [H]'s.
  * Step 3c ✅ `MinorArcs/Eta2LogFourier.lean`: (B.17) `|(log·η₂)^| ≤ 2 - log 4` and (B.18)
    `(2πt)²|(log·η₂)^(t)| ≤ 96 log 2`, **proved** (two integrations by parts on `[1/4,1/2]`, `[1/2,1]`).
  * Step 3d ✅ `MinorArcs/TypeITotal.lean`: **`typeI1_le`** (§6.2.1, `|S_{I,1}|` for `U ≤ Q₀/2`) from
    the corrected Lemma 4.2.3 with (2.20), (2.22), (2.23), (B.17), (B.18). Prefactor `x/2q`,
    `min(1, c₀/(πδ)²)`, sums over `(m, 2q) = 1` (cf. the (4.40) erratum).
  * Step 3e ✅ `MinorArcs/TypeI2Total.lean`, `GcdSums.lean`, `TypeI2Sum.lean`, `TypeI2Large.lean`
    (§6.2.2, `qV ≤ Q`): (6.5) `typeI2_eq_sum`; the induced approximation `approx2_mul`;
    (6.6)–(6.8) `typeI2_le_sum`; (6.9) `∑ Λ(v)(q,v)/v ≤ log N + log q` and
    `∑ Λ(v) v (q,v) ≤ ∑ Λ(v) v + N q log q` (proved via `(q,v) = ∑_{d|(q,v)} φ(d)`);
    **`typeI2_le_small`** ((6.12)+(6.13), `|δ| ≤ 1/2c₂`) and **`typeI2_le_large`** ((6.12)+(6.14)).
    Needs `V ≥ 2·10⁶` (for (2.14), (2.17)), `16V ≤ Q`, `UV ≤ x`. Differences from [H]:
    `U²V log V` → `U²V log q`; the `Q log(U/(q/2))` term → `Q (log⁺(2U/q) + 1/e)` (no `Q ≤ 2UV/e`);
    the `c_{5,I2} max(log(c₁₁q²V/x), 2) Q` term is ours from `bound_4_31`:
    `(2|η₂'|₁/π) max(1, log(c₀e³q²V/4π|η₂'|₁x)) Q` (to compare in §6.3); in (6.14) the `UV/e` term carries a factor `1 + V/Q`, and
    the coefficients are kept as exact expressions in `c₊` (no rounding to `c_{4,I2}` etc.).
  * Step 3 (next): Lemma 4.2.4 case `q > Q/V` of `S_{I,2}`; Type II (6.38)/(6.39)/(6.41) (larger
    `q`; second parameter choice); `S_{0,2}` (powers of 2, negligible), `S_{0,∞} = 0`.
  * Step 4 (in progress): §6.3 parameter choices and numerics → Theorem 3.1.1 (`PointwiseBound.lean`).
    `scripts/thm_3_1_1_numerics.py` evaluates the right-hand sides of our Lean bounds at the
    (6.49) parameters (U, V rounded down) against Thm 3.1.1 (corrected constant `0.8103`): worst
    ratio ≈ 0.95 at `x = 2.16·10²⁰`, → 1 slowly as `x → ∞` (along the curve where the AM–GM step
    (6.77) is tight; there the main terms match [H]'s exactly). Plan for `q ≤ x^{1/3}/6`
    (`FirstChoice.lean`, with `T = x^{1/3}`, `t = δ₀q`):
    * ✅ `typeII_main_le`: main term of (6.37)/(6.40) ≤ `√(C_{x,t}(log t + .002) + log(4t)/2)·
      √(0.30214 log t + 0.67506)` (needs `ζ(3/2) ≤ 2.77`, proved);
    * ✅ `FirstChoiceParams.lean`: parameter facts for `U = ⌊T²/9√t⌋`, `V = ⌊9T/2⌋`, `Q = 3T²/4`;
    * ✅ `FirstChoiceTypeII.lean`: `typeII_rest_le` (lower-order Type II terms ≤ `3.2 x^{5/6}`, vs
      [H]'s 2.74; uses Lemma C.2.2 `q/φ(q) < Ϝ(r)`, trusted, and `e^γ < e^{2/3}`) and
      **`typeII_first`**: `|S_{II}| ≤ x/√(δ₀φ) √(C_{x,t}(log t + .002) + log(4t)/2)
      √(0.30214 log t + 0.67506) + 3.2 x^{5/6}` for `q ≤ x^{1/3}/6` (both `|δ| < 8` via (6.37) and
      `|δ| ≥ 8` via (6.40)). So the theorem's `3.36 x^{5/6}` will likely become `≈ 4 x^{5/6}`;
    * ✅ `FirstChoiceMain.lean`: `C_{x,t} ≤ 0.1 log t + 0.14`; AM–GM (6.77) with `√ρ = 1.84332`
      gives `R_{x,t} log t + 0.8103` (margins ~5·10⁻⁷ in the `log t` coefficient!).
    * ✅ `FirstChoiceTypeI.lean`, `FirstChoiceTypeI1.lean`: `typeI1_first`,
      `|S_{I,1}| ≤ 1.80303·2x/(δ₀φ) + (log t + 1.63)·2x/t + 0.014 x^{5/6}` (via
      `μ L ≤ (4/5)(2q/φ(2q)) + max(L - log(M/2q²), 0)`, `min(1,c₀/(πδ)²) ≤ 2/δ₀`).
    * ✅ `FirstChoiceTypeI2*.lean`: `typeI2_first`,
      `|S_{I,2}| ≤ 2.4916 x/√t + 0.8·2x/(δ₀φ) + (15.163 log t + 21.296)·2x/t + 0.553 x^{5/6}`
      (`ε = 0.07` in (6.14); the `x/|δ|q` term via monotonicity of `(A + log⁺(cy))/y`).
    * ✅ `FirstChoiceFinal.lean`: **`theorem_3_1_1_first`**, and `PointwiseBound.lean` now proves
      the first case of `theorem_3_1_1` (corrected constants `0.8103` and `3.8 x^{5/6}`). Our own
      allocation: the `x/(δ₀q)`-terms total `16.163 log t + 22.93`, which fits into
      `13.66 log t + 37.55` plus the unused part `3.25 log t + 5.217` of the `x/(δ₀φ)` slot
      (`x/(δ₀q) ≤ x/(δ₀φ)`). `x^{5/6}`: `3.2 + 0.014 + 0.553 + 0.0001 = 3.767`.
  * ✅ §6.3.2 (`q > x^{1/3}/6`): **Theorem 3.1.1 is proved in full** (`PointwiseBound.lean`,
    `#sorry_deps theorem_3_1_1` = the same 20 trusted items as the first case). Files:
    `TypeIILarge.lean` ((6.20) split integral; (6.38), (6.39), (6.41)), `SecondChoice.lean`
    (Dirichlet, `approx_gap`, `second_case_split`), `SecondBridge.lean` (case (c)),
    `SecondParams.lean`, `SecondNumerics.lean` (Taylor exp/log bounds `log_le_num`/`le_log_num`,
    `e^γ ≤ 1.7882` via `H₁₂₈`), `SecondTypeIIa*.lean` (case (a1): reduction
    `typeII_a1` + 12 generated pieces + tail ≥ 70), `SecondTypeIIb*.lean` (cases (a2), (b)),
    `SecondTypeI1/2.lean` (Type I: `≤ (0.0716L² + 3175.9L + 8399.2)T²`), `SecondFinal.lean`.
    Choices: `U = ⌊1225T⌋`, `V = ⌊T/3⌋`, `Q₀ = T²/349 ≥ 3.5x/U`, `θ = 8` in (6.38) and (6.41).
    All Type II cases are `≤ 1.413 L^{3/2} T^{5/2}` (`L = log T`; target `0.276·3√3 = 1.4341`),
    Type I borrows `≤ 205 L T²` of the remaining slack. Piece generators:
    `scripts/gen_a1_pieces.py`, `scripts/gen_b_pieces.py` (exact rational checks first).
  * Re-check numerics for the (4.40), Lemma 4.2.4 and §5.2 corrections, and `U ≥ 1` in (5.34).
* Optional: prove `fsq_le`; Lemma 5.1.2 (Rankin trick with (2.21)).
* `Prelim/LambdaMu.lean`: trusted literature bounds [H (2.12), (2.15), (2.16), …]; (2.20) is proved in `Prelim/MoebiusCoprime.lean`.
* Lemma 4.2.3 notes: the last term of (4.41) uses `log(2ex/c₂)` (the book's step needs `q ≥ 2`);
  the weighted sums are in `SumTools.lean` (`S2_le`, `sum_odd_mul_log_le`) and `sum_R3L`.

## Removing the remaining `sorry`s (goal set 2026-10-31)

Policy (user): prove everything; finite computer checks may be stated as **numerical axioms**.
Done: (2.20) proved; `binary_goldbach_input`, `prime_ladder_input` are numerical axioms. Status 2026-10-31:
`ternary_goldbach` depends on 5 `sorry`s (`dusart_theta`, `major_arcs_input`, `l2_major_14_7`,
`MajorArcs.prop_9_3_2`, `MajorArcs.prop_9_5_1`) and 32 numerical axioms.
*Part II split (2026-11-01, user's choice "work on Part II"):* Platt's verification is now the numerical
axiom pair `platt_odd`/`platt_even` on Mathlib's `DirichletCharacter.LFunction` (`GRHUpTo χ T`); the analytic
explicit-formula results are cited *conditionally* on GRH up to `T₀` ([H, Prop 9.3.2], [H, Prop 9.5.1]);
Cor 9.3.3 → Cor 7.1.3 and Prop 7.1.5 are proved (`MajorArcs/`). [H]'s numerics check out:
`(1000/3)·log(10⁸/2π)·6.11·e^{−0.1598·1000/3} = 2.48404·10⁻¹⁹ ≤ 2.485·10⁻¹⁹`; for Prop 7.1.5 we use `T₀ = 440`
instead of `450` for margin. Thm 7.1.4 is proved from the cited Prop 9.4.2 + Platt (`MajorArcs/Thm714.lean`; book typo: (9.70)'s second line
has `x^{1/2}` for `x^{-1/2}`; [H]'s general-`q` constants `1.3482·10⁻¹⁴`, `1.617·10⁻¹⁰` are tight to ~10⁻⁵ relative,
we use `1.35·10⁻¹⁴`, `1.62·10⁻¹⁰` and `q = 1`: `4.78·10⁻¹¹` — check (14.1), (14.2) margins when used).
(14.7) needs the *lower* bound (MinorTotal uses `∫_𝔐 |S_{η₊}|² ≥ 8.6298x`), i.e. the full Lemma 10.3.1 with `η◦`.
**Roadmap for (14.7)** (Lemma 10.3.1 + §14.1), *revised 2026-11-01*: Cauchy–Schwarz on the principal-character
cross term (`∫_{|β|<w} 2|a||e| ≤ 2 sup|e| · √(2w) · (∫|a|²)^{1/2}` instead of [H]'s `sup|e| · 2w|η|₁`) makes that
error `≈ 3·10⁻⁴ x` instead of [H]'s `0.0755 x` (`scripts`-style check: lower `8.7029 x`, upper `8.7053 x`), so crude
constants suffice everywhere and `|η₊|₁` is not needed. Steps (files under `MajorArcs/`):
1. *Arcs* — **DONE** (`ArcsEq.lean`): `∫_{(0,1]∩𝔐} g = Σ_{q∈Qset, b∈Bset} ∫_{J_{q,b}} g`.
2. *`η◦` tail* — **DONE** (`EtaCirc.lean`, `tail_etaO_le`): `η◦(t) = h(t) t e^{-t²/2} = (1−u²)³e^{−u²/2}` (`u = t − 1`, `|u| ≤ 1`); two integrations
   by parts on `[0,2]` and Plancherel for `η◦''·1_{[0,2]}` (`|η◦''| ≤ 7`): `∫_{|δ|>T} |η̂◦|² ≤ 98/(2πT)⁴`.
3. *`η₊ − η◦`* — **DONE** (`HHFourier.lean`, `integral_sq_etaPlus_sub_etaO_le`: `≤ 19.5/(2·200²)`): with `g(u) = h(eᵘ)`, `h_H(eᵘ) = (g * sin(Hv)/(πv))(u) = ∫_{|ξ|≤H/2π} ĝ(ξ)e(ξu)dξ`
   (Fubini, `sin(Hv)/(πv) = ∫_{|ξ|≤H/2π} e(ξv)dξ`); L² Fourier (`fourierL2_ae_eq`) gives `|g − g_H|₂² = ∫_{|ξ|>H/2π}|ĝ|²
   ≤ |g'|₂²/H²`; then `|η₊ − η◦|₂ ≤ sup(s^{3/2}e^{−s²/2}) |g'|₂/H` (`|g'|₂² = ∫₀² t h'(t)² dt ≈ 6.92`).
4. *Main term* — **DONE** (`EtaPlusL2.lean`, `integral_fourier_etaPlus_Ioo_bounds`: `[0.6392, 0.640208]` for `T ≥ 4`): `|η₊|₂² = 0.640206 ± 1.95·10⁻⁶` from the axiom `integral_etaPlus_sq_log` (`x → ∞`);
   for `T ≥ 4`, `|η₊|₂² − tail ≤ ∫_{|δ|<T}|η̂₊|² ≤ |η₊|₂²`, `tail ≤ 2·98/(8π)⁴ + 2|η₊−η◦|₂²` (Plancherel, done).
5. *Coprime split* — **DONE** (`ArcChars.lean`, per modulus: `norm_S_sub_coprime_le`, `≤ 10⁻¹⁵x`): `|S − S'_q| ≤ B ≪ log x` (prime powers of `p ≤ 2r`), `S'_q` over `(n, q) = 1`;
   `|S|² ≤ (1+t)|S'|² + (1+1/t)B²` both ways.
6. *Characters per `q`* — **DONE** (`ArcChars.lean`, `arc_chars`): `totient_mul_sum_units`, `norm_sq_gaussSum`, `cond ψ⁻¹ = cond ψ`,
   `S'_ψ = S'_{ψ*}` and `|S'_{ψ*} − S_{ψ*}| ≤ B`; Thm 7.1.4 (`thm_7_1_4_one/odd/even`) on `ψ*`: principal part
   `μ²(q)/φ(q) |S'(β)|²`, non-principal `≤ (E x + √(2r) B)²`, `E ≤ 2.3992·10⁻⁸`.
7. *Assembly* — **DONE** (`L2Major.lean`, `l2_major_bounds`: `8.688x ≤ ∫ ≤ 8.709x`; `l2_major_14_7` is a theorem): translate arcs, `β = δ/x`, `T_q = δ₀r/q̃ ≥ 4`; parity pairing `Σ_{q∈Qset} μ²/φ =
   2 Σ_{q odd ≤ r} μ²/φ`; **numerical axiom** `Σ_{q≤150000 odd} μ²(q)/φ(q) ∈ [6.798779, 6.79878]` (finite sum).
Then (14.27) via Prop 10.4.1 + §14.2 (main term (10.23), Euler product `C₀`, `η◦`-triple integral (10.22)).
**(14.27): DONE** (`MajorArcs/MajorTotal.lean`, `major_total`; `major_arcs_input` is a theorem with `1.049`).
Final numbers (units `x²/κ`): main `1.314 · 0.800689 = 1.05211`; `η₊ → η◦` + `β`-tail `2.85 · 2.03·10⁻⁵ · 49 = 0.00283`;
residual terms `≈ 1.2·10⁻⁵` (`ρ₊ = 4.63·10⁻⁸x` in `ℓ²`, `|R_*| ≤ 3.15·10⁻⁷ x/κ` pointwise); total `≥ 1.04926`.
`final_inequality_crude` with margin `0.0114` needed `v = N^{1/64}` (the `N^{1/16}` + `log u ≤ u/e` argument loses
a factor `≈ 4.6`, too much at this margin).
**Roadmap for (14.27)** (Prop 10.4.1 + §14.2), *planned 2026-11-01* (kept for reference). Budget: `final_inequality_crude` only needs
`(major − 1.0376)/κ·x² > 6.7·10⁶ N^{3/2} log N`, i.e. major `≳ 1.0402` (not [H]'s `1.058259`); [H]'s main term is
`C₀ C_{η◦,η_*} x² ≥ 1.0583 x²/κ`, so ~`0.013 x²/κ` is available for crude constants. Pieces:
1. *Sharper `‖η₊ − η◦‖₂`* — **DONE** (`HHFourier2.lean`, `integral_sq_etaPlus_sub_etaO_le'`: `≤ 368/(2·200⁴)`): the (10.19) term costs `≈ 5.67 ε` (units `x²/κ`), so need `ε ≲ 5·10⁻⁴` (now `0.0156`): redo
   `HHFourier` with `g''` (`h` is `C²` on `(0,∞)`, `hP''(2) = 0`): `‖g − g_H‖₂ ≤ ‖g''‖₂/H²`, `‖g''‖₂² ≈ 142.6`.
2. *`C_{η◦,η_*}` (Ch. 11)* — **DONE** (`CMain.lean`, `Cmain_ge`, constant `8.82`; moments `integral_pow_mul_etaU`): polarization, `‖η◦(·+s)‖₂ = ‖η◦‖₂` ⇒ `(η◦∗η◦)(ρ) = ‖η◦‖₂² − ½‖η◦ − η◦(·+2−ρ)‖₂² ≥ ‖η◦‖₂² −
   ½(2−ρ)²‖η◦'‖₂²` (better than [H]'s `2.71`); moments `∫σᵏη_* = κ^{−k−1} Mₖ(η₂)Mₖ(φ)` (`M(η₂) = 1, 9/16, 49/144`;
   `M(φ) = √(π/2), 2, 3√(π/2)`); `N/x = 2 + c₁/κ`, `c₁ = 9/(4√(2π))`; tail of `η_*` beyond `N/x` negligible.
3. *Fourier identity (10.22)* — **DONE** (`FourierMain.lean`, `fourier_identity`): `h = η◦∗η◦∗η_*` continuous, integrable, `ĥ = η̂◦²η̂_*` (Fubini), `ĥ ∈ L¹` ⇒
   `∫ η̂◦²η̂_* e(tM) dt = h(M)` (`Continuous.fourier_inversion`).
4. *Main term (§10.2)* — singular series **DONE** (`Singular.lean`: `coef_eq`, `sum_Qset_coefN_ge` `≥ 1.314`, `sum_Qset_mPhi2_le` `≤ 2.85`; uses `mertens_product_small` at `150001`): per `(q, a)`, principal parts `M_η = μ(q)/φ(q) η̂(−βx)x`; Ramanujan sum
   `Σ_a e(−Na/q) = μ(q/(q,N))φ((q,N))`; complete `Σ_q` and `∫` (tails with crude `Σ_{q>Q} μ²/φ² ≤ C/Q`); Euler product
   `Σ_q … = C₀ ≥ 2∏_{p>2}(1 − 1/(p−1)²)` (finite product + `1 − 1/(P−1)` tail; Mathlib `EulerProduct`).
5. *Errors (§10.4)* — **DONE** (`MajorTotal.lean`: `resid_plus`, `resid_star`, `sum_cubic_error`, `pointwise_bound`, `per_modulus`): `S₊²S_* − M₊²M_* = R_* S₊² + M_* R₊(S₊ + M₊)`; `|R_*| ≤ E_*` pointwise (Cor 7.1.3 per character),
   `Σ_a |R₊|² ≤ E₊²` (Bombieri without the principal character); `∫_𝔐 |S₊|² ≤ 8.709x` ((14.7), done); Cauchy–Schwarz.
6. *Arcs for complex integrands* — **DONE** (`integral_majorArcs_eq` for real continuous periodic `g`, via `g⁺`, `g⁻`; applied to `Re f`): `∫_{(0,1]∩𝔐} f = Σ_{q,b} ∫_{J_{q,b}} f` (equality via indicators + periodization).
7. *Numerics* — **DONE**: `major_arcs_input` restated with `1.049`; `final_inequality{,_crude}` and `Main` use `1.049 − 1.0376`.
   *Assembly plan* (`MajorTotal.lean`): at `α = b/q + β`, `S_η = M_η + R_η` with `M_η = μ(q)/φ(q) η̂(−βx)x`;
   `Σ_b M₊²M_* e(−Nα) = coefN·η̂₊²η̂_* x³ e(−Nβ)` (`coef_eq`); error `R_* S₊² + M_* R₊ (S₊ + M₊)`, with
   `Σ_b |S'(b/q+β) − μ/φ S'(β)|² = Σ_b |S'|² − μ²/φ |S'(β)|² ≤ (2.41·10⁻⁸x)²` (`arc_chars` + `Σ_b S'(b/q+β) = μ(q)S'(β)`),
   pointwise `|R_*| ≤ max_{ψ≠1} |τ(ψ)||S_{ψ⁻¹}|` via orthogonality (Cor 7.1.3 for `η_*` at scale `x/κ`), AM–GM
   instead of Cauchy–Schwarz for the `β`-integrals; main term: `η₊ → η◦` costs `≲ 2·10⁻³ x²/κ`, completing
   `∫_{|β|<w}` to `ℝ` costs `≲ 10⁻³ x²/κ`; `x²·C_{η◦,η_*}(N/x)·1.314 ≥ 1.0521 x²/κ`. Target `(14.27)` with `1.045`.
   *Book note*: (14.17) prints `1.33805·10⁻⁸/κ`; the expression evaluates to `1.338·10⁻⁷/κ` (exponent slip; harmless).
Remaining `sorry`: `dusart_theta` (Props 9.3.2, 9.4.2, 9.5.1 proved since). No other `sorry`s: (2.16), (2.18) proved (`LambdaMuExtra.lean`,
three unused finite checks; since deleted), (2.24) proved for `x < 10¹⁰`, (2.21) (unused) not stated.
*Dusart (checked 2026-10-31):* PNT+ (same Mathlib commit 56a0058) now has `PrimeNumberTheoremAnd/IEANTN`
(Tao et al.'s explicit-ANT project). `TMEEMT.theta_improv_2` states exactly our `dusart_theta`, but it is
derived from `Dusart.theorem_4_2`, which is `sorry` there. Their sorry-free BKLNW chain (`thm_1a_table`,
`cor_2_1`, `bklnw_cor_8_1b`, table 11 bounds `|θ − x| ≤ B_k x/log^k x`) rests on `BKLNW_app.theorem_2`
(`|ψ(x) − x| ≤ ε(b) x`, Table 8) and Büthe's Theorem 2 (`θ(x) < x` for `x ≤ 10¹⁹`, etc.), both `sorry`, which in
turn need the explicit formula, zero-free regions (MT/MTY), `N(T)` bounds (HSW) and RH verification (Platt, GW,
PT; the numerical part). No complete chain exists yet; porting the BKLNW part would replace `dusart_theta` by
those (analytic) inputs. Watch IEANTN for progress.

**(2.23): DONE, elementary, weaker constant** (`Prelim/MoebiusLog.lean`): `|L_q(x)| ≤ q/φ(q) + 2.67` instead of
Ramaré's `1.00303 q/φ(q)`. Downstream: `typeI1_le`/`abs_muSum_log_le` carry `2q/φ(2q) + 2.67`; `typeI1_first`'s
`(log t + 1.63)·2x/t` becomes `(log t + 2.96)·2x/t` (Theorem 3.1.1 first case unchanged: its `2x/t` budget
`16.91 log t + 42.77` had room); `typeI1_second` `7.7 → 15.7`, `typeI_second` `8399.2 → 8407.2`, absorbed in
`theorem_3_1_1_second` (margin ≈ 1400 at `T = 6·10⁶`). The Python models (`thm_3_1_1_numerics.py`,
`prelim_sensitivity.py`) still use `1.00303`.

**(14.28): DONE** (`MinorArcs/EBound.lean`, `Helfgott/HHBound.lean`), constant `8·10⁻¹¹` instead of `8.4029·10⁻¹²`.
[H]'s constant is exactly tight at `x₊ = 4.9·10²⁶` and needs Appendix A's `|η₊|_∞ ≤ 1.079955`, `|tη₊|_∞ ≤ 1.19073`.
Our minor-arc assembly only needs `E ≲ 10⁻⁹ x` (`I0_ge` with `t = 10⁻⁵`; `minor_total` with `t = 5·10⁻⁴`: total
`1.0005·1.037 + 2001·22.75·8·10⁻¹¹ = 1.03752 ≤ 1.0376`). Sup norms: `h_H(t) = ∫_0^2 h(u)F_H(t/u)du/u`; with
`G_H(z) = ∫_0^z sin(Hv)/(πv)dv`, `|G_H| ≤ 3/π` (bound `1/π` on `[0,1/H]`, integrate by parts beyond), integrate by
parts on `[ε, 2]` against `−G_H(log(t/u))`: `|h_H| ≤ (3/π)·TV(h) + O(Hε²) = (6/π)e^{1/2} + O(Hε²) ≤ 3.15`.

**(2.22): DONE with constant `2.8`** (for [H]'s `4/5` from [Ramb]; `Prelim/MoebiusBound.lean`, `Liouville.lean`,
`LiouvilleBound.lean`). Ramaré's Liouville route (Ram14 = hal-02572851) with our own `q = 1` input:
1. `MoebiusBound`: `m(x)(log x + E(x)) = −∑_{n≤x} μ(n)/n (E(x/n) − E(x))` and
   `K = ∑_{n≤x}|E(x/n) − E(x)|/n ≤ 0.4259 + 0.0755 + 0.0378 ≤ 0.54` for `x ≥ 10¹⁰` (fine pieces below `1000`,
   dyadic blocks to `10⁹`: numerical axioms `K_pieces`, `K_blocks`; Dusart beyond), so
   `|m(x)| ≤ 0.54/(log x − 0.7521)` ((2.13) for `E(x) ≥ −log(3/√2)`).
2. `Liouville`: `λ = sq ∗ μ`, `μ = μ_sq ∗ λ`, `λχ_q = d_q ∗ λ` (multiplicativity, prime powers), `(Fχ_q) ∗ (Gχ_q) =
   (F ∗ G)χ_q`, and the `1/n`-weighted partial sums: Lemmas 2.3, 3.2, 2.5 of Ram14 for every `q`.
3. `LiouvilleBound`: `|ℓ(z)| log z ≤ 0.99` for all `z > 1` — `z ≤ 10⁵` by the kernel check `liouville_small` (`Prelim/SmallLiouville.lean`)
   (max `0.7831` at `z → 11⁻`); `10⁵ ≤ z < 10¹⁰` from `|m(y)| ≤ √(2/y)` (numerical axiom `moebius_sqrt_small`,
   a Möbius sieve to `10¹⁰`; max of `|m(k)|√((k+1)/2)` over `2 ≤ k < 10¹⁰` is `0.612` at `k = 2`, equality at
   `k = 1`); `z ≥ 10¹⁰` from step 1 for `z/u² ≥ 10¹⁰` (`∑ 1/u² ≤ 5/3`, `∑ log u/u² ≤ 1.0117`, total `0.984`).
   Then `|ℓ_q(x)| log(x/q) ≤ 0.99 q/φ(q)` (`∑_{d∣q} μ²(d)/d ≤ q/φ(q)` via `sum_factored_le`), `|ℓ_q| ≤ 5/3`.
4. `|m_q(x)| ≤ (q/φ(q)) ∑_{u² ≤ x} |μ(u)|/u² β(log(x/q), u)`, `β(y, u) = min(5/3, 0.99/(y − 2 log u))` (or `5/3`);
   `y·∑ ≤ 2.8` on `[2.8, 80)` by the grid axiom `C_grid` (step `0.01`, `u ≤ 3000`, max `2.7422`), for `y ≥ 80`
   analytically (split at `u ≤ e^{y/8}`: `≤ 2.2 + 0.007`), and `|m_q| ≤ 1` for `y ≤ 2.8`.
Downstream: `muBound` uses `2.8`; `typeI1_first` `1.80303 → 3.8`, `typeI2_first` `0.8 → 2.8`, and the
first-case spill `5.21697 → 1.22` (`3.8 + 2.8 + 1.22 = 7.82`), so Theorem 3.1.1's statement is unchanged.
*Remark on Ram14*: Lemma 2.4's first claim `|ℓ(x)| ≤ 0.55/log x` for all `x > 1` fails on `x ∈ (≈ 10.6, 11)`:
`ℓ(10) = 0.3266` and `0.3266 · log 11 = 0.783`. (We use `0.99`; Ram14's Theorem 1.1 constants are not used.)
**Original plan (as carried out, with the modelled constants).** Budget: Theorem 3.1.1 (first case) has `2x/(δ₀φ(q))(13/4 log t + 7.82)`;
the δ₀φ constant used is `1 + 2C` (typeI1 `1 + C`, typeI2 `C`, `C` = the (2.22) constant), so `C ≤ 3.4` keeps
the statement (and GBound/cells) unchanged. Route (Ram14 = hal-02572851, with our own q = 1 input):
1. `m(x)(log x + c₀) = −∑_{n≤x} μ(n)/n · r(x/n)`, `r(y) = ψ̃(y) − log y − c₀`, `c₀ = lim(ψ̃(y) − log y)` (exists by
   `E1_diff`; no need to identify `c₀ = −γ`). Numerically `∫_1^∞ |r(y)| dy/y ≈ 0.407`, so `|m(x)| ≲ 0.45/log x`
   (uniformity in real `x`: step-function `|r|` on `[1, 10⁴]`, `E1_diff`/`psi_sqrt` beyond, `x ≥ 10¹⁰`).
   (The Liouville analogue `ℓ(x)(log x − c′) = ∑ λ(n)/n r′(x/n)` gives only `≈ 3.70/log x`: too weak.)
2. Ram14 Lemma 2.4: `ℓ(x) = ∑_{u²≤x} m(x/u²)/u²` ⇒ `|ℓ(x)| ≤ c_ℓ/log x` (`c_ℓ ≈ 0.55–0.9`), with a finite check of
   `|ℓ(x)| log x` up to `1.1·10¹⁰` (Liouville sieve) and `|m(y)| ≤ √(2/y)` on a finite range (cf. (2.24)).
3. Lemma 2.5: `ℓ_q(x) = ∑_{d|q} μ²(d)/d ℓ(x/d)` ⇒ `|ℓ_q(x)| ≤ c_ℓ (q/φ(q))/log(x/q)`; Lemma 3.1 `|ℓ_q| ≤ π²/6`.
4. Lemma 3.2: `m_q(x) = ∑_{u²≤x,(u,q)=1} μ(u)/u² ℓ_q(x/u²)` and the `ρ(U, y)` optimisation ⇒ `C ≈ 2.4–3`.
5. Refactor `muBound` (`4/5 → C`) through `TypeITotal`, `FirstChoiceTypeI1/I2`, `TypeI2Sum`, `TypeI2Large`.

**(2.22), (2.23): sources (both now proved with weaker constants, above).** [H] cites [Ramb] = Ramaré, *Explicit estimates on several summatory
functions involving the Moebius function*, Math. Comp. 84 (2015) 1359–1387, with a **corrigendum** in Math. Comp. 88
(2019) 2383–2388 (check whether it touches `4/5` or `1.00303` before relying on them). Not on arXiv/HAL; the AMS PDF
could not be fetched from this environment. Open-access relatives (HAL): Ram13 = hal-02572812 (Acta Arith. 157:
`|∑_{n≤x} μ(n)/n| ≤ 0.03/log x`, `x ≥ 11815`, from explicit `ψ` bounds — derivable from Dusart + finite checks);
Ram14 = hal-02572851 (Acta Arith. 165: `log(x/q)|m_q(x)| ≤ 2 q/φ(q)` for `q < x`, `≤ (8/7) q/φ(q)` for
`x/q ≥ 3310`, `≤ (5/7) q/φ(q)` for `x/q ≥ 9960`, via the Liouville function and `|ℓ(x)| ≤ √(2/x)` for
`x ≤ 1.1·10¹⁰`); FA13 = hal-02573950 (`|∑ μ(d)/d log(x/d)| ≤ 1.4 + r/φ(r)` at `ε = 0`, weaker than 1.00303).
Options: (a) obtain [Ramb] and formalize Ram13 → [Ramb] from Dusart; (b) formalize Ram13 + Ram14 and redo the Type I
numerics (`TypeITotal.lean`, `muBound`, `c_{4,I} = 1.00303`) with the weaker constants.
*Slack* (`scripts/prelim_sensitivity.py`): the cell model is unchanged (worst `Z = 0.9646 ≤ 1.037`) with (2.23) up to
`≥ 6` and (2.22) up to `≈ 22.8`, so weaker constants suffice — but the Lean Type I chains (`FirstChoiceTypeI1`,
`SecondTypeI1`, `TypeI2Sum`, `TypeI2Large`, `TypeITotal`) hard-code `4/5` and `1.00303` and would need re-deriving.
*(2.23) elementary*: `∑_{(n,q)=1} μ(n)/n · H(x/n) = ∑_{k≤x, rad k | q} 1/k ∈ [1, q/φ(q)]`, `H(y) = log y + γ + O*(1/⌊y⌋)`
(Mathlib `eulerMascheroniSeq` bounds), `|m_q| ≤ 1` ⇒ `|∑ μ(n)/n log(x/n)| ≤ q/φ(q) + γ + 2 ≤ 3.58 q/φ(q)`.
*(2.22) sketch*: with `ψ̃_q(y) = ∑_{m≤y,(m,q)=1} Λ(m)/m = log y + c_q + r_q(y)` (any constant `c_q`; take the limit, which
exists by `E1_diff`), `μ*Λ = −μ log` gives `m_q(x)(log x + c_q) = −∑_{n≤x,(n,q)=1} μ(n)/n · r_q(x/n)`; `r_q = r + T_q`
with `T_q(y) = ∑_{p|q} ∑_{p^k>y} log p/p^k`, whose contribution is `≤ ∑_{p|q} (log²p · p/(p−1)² + log p/(p−1))` — this
grows like `(log log q)²` relative to `q/φ(q)`, so a uniform constant needs more care (Ram14 goes through Liouville).


**Lemma C.2.2: DONE** (`Prelim/MertensProduct.lean`). Route: PNT+'s sorry-free Mertens file (ported to
`Prelim/PNTMertens.lean`, same Mathlib commit) gives `∑_{d≤x} Λ(d)/(d log d) = log log x + γ + E₂Λ(x)`,
`E₂Λ(x) = E₁Λ(x)/log x − ∫_x^∞ E₁Λ(t)/(t log²t)`. Since `∫_x^∞ dt/(t log²t) = 1/log x`, any constant can be
subtracted from `E₁Λ`: `|E₂Λ(x)| ≤ 2 sup_{t≥x}|E₁Λ(t) − E₁Λ(x)|/log x`, and summation by parts with Dusart gives
`sup ≤ 2/log²x + O(1/log³x + 1/√x)`. With `log ∏ p/(p−1) ≤ ∑Λ(d)/(d log d) + 3/⌊√x⌋` (log series, prime powers
`p^k ≤ x` reindexed) this gives the bound for all `x ≥ 10⁸` with a factor ~1.4 to spare; primes `5 ≤ x ≤ 10⁸` by a
finite check (tight only at `x = 23`, margin `2.4·10⁻⁷`). Then the exchange argument (`Finset.induction_on_max`,
`Nat.nth_lt_of_lt_count`) and monotonicity of `t ↦ e^γ t + c/t` for `t ≥ log 4`.

**(2.13), (2.14), (2.17), (2.19): DONE** (`Prelim/LambdaMu.lean`). All of [H]'s `ψ`/`θ` inputs now rest on one
cited result, Dusart's `|θ(x) − x| < x/log³x` for `x ≥ 89 967 803` ([Dus18, Thm 4.2] = arXiv:1002.0442 Thm 5.2;
the table there also has `η₁ = 0.001` from `x ≥ 908 994 923`), plus finite checks (`scripts/psi_mid_check.py`, a
segmented sieve to `10¹⁰`, a few minutes, < 1 GB): `ψ ≤ 1.0004n` on `[2·10⁶, 10⁹]` (max 1.0003639), `|ψ − n| ≤ 0.95√n`
on `[11, 10¹⁰]` (max 0.7906), `|θ − n| ≤ 1.95√n` on `[5·10⁵, 10¹⁰]` (max 1.8071, `θ < n` throughout),
`∑Λ(m)m < 1.0008n²/2` on `[1.6·10⁶, 10⁸]`. Proofs:
* (2.14): strong induction, `ψ(n) ≤ θ(n) + ψ(√n) + n^{1/3} log n ≤ n(1 + 1/log³n) + 7.04√n` above `10⁹`.
* (2.13): summation by parts from `X = 10⁶` with `ψ(m) ≥ m − 0.95√m − m/log³m`; the tails telescope
  (`1/(√m(m+1)) ≤ 2/√m − 2/√(m+1)`, `1/((m+1)log³m) ≤ 2/log²m − 2/log²(m+1)`); total `≥ log(N+1) − 0.59`,
  versus `log(3/√2) = 0.752` (equality at `N = 2`).
* (2.17): `∑Λ(n)n = Nψ(N) − ∑_{m<N}ψ(m)` with uniform `(1 − 1/12000)m − 0.95√m − 11 ≤ ψ(m) ≤ 1.00016m + 0.95√m`.
* (2.19): split `(N/2, N]` at `3N/4`: saving `log(4/3)·(θ(3N/4) − θ(N/2)) ≈ 0.0719N` beats the errors for `N > 10⁶`
  (with `θ` within `1.95√n + n/log³n`; this is tight-ish, needs `c' ≤ 2.05`).

**(2.12), (2.15), (5.5): DONE** (in `Prelim/LambdaMu.lean`), from (2.14) `ψ(y) ≤ 1.0004y` (`y ≥ 2·10⁶`, still
`sorry`) and finite checks (`scripts/psi_checks.py`): (2.15) directly; (5.5) via
`ψ − θ ≤ ψ(√N) + N^{1/3} log N` (prime powers `p^k`, `k ≥ 2`, dominated by `∑_{p ≤ √N} ∑_{2 ≤ k ≤ log_p N}`), which is
`< 1.4262√N` for `N ≥ 10¹²`; (2.12) via `∑ Λ(n)⌊N/n⌋ = log N! ≤ N log N − N + 1 + log N` and Abel summation of
`∑ Λ(n){N/n}` over `(N/2, N]` (`≤ 1.03883 N log 2 + 2.08`), valid for `N ≥ 30`. Remaining LambdaMu `sorry`s
all need explicit-PNT input (RS62/RR96/Ramaré). PNT+ (AlexKontorovich/PrimeNumberTheoremAnd, `IEANTN/`, same
toolchain v4.35.0) is formalizing explicit estimates (RS, Dusart, FKS2, Mertens, Büthe); as of 2026-10-31 its
RS `theorem_12` (= our (2.15)) is still `sorry` and its FKS2 corollaries rest on trusted tables and sorried
Büthe/Dusart/Kadiri inputs; importing it would also mean building a very large project here.

**[MV73, Lemmas 7, 8]: DONE** (`Prelim/MVLemma7.lean`, `MVLemma8.lean`). Lemma 8 for `R > 10⁴` by Abel
summation against Lemma 7 (`G(r) ≥ log r + 1.07`, `r ≥ 6`), comparing `∑ f(r) log(r/(r−1))` with
`Φ(t) = log(t/(R+t))` via the monotonicity of `t log(1+1/t)` (margin 0.04); for `2 ≤ R ≤ 10⁴` from the book's
finite endpoint check plus a finite monotonicity condition (numerical axiom). Lemma 7: `h = (nμ²/φ) ∗ μ`
(`h(p) = 1/(p−1)`, `h(p²) = −p/(p−1)`), `G(N) = ∑_{d≤N} (h(d)/d) H(N/d)`, `∑ h(d)/d = 1` by Mathlib's
`EulerProduct`, Rankin with `σ = 2/3`: `P = ∑|h(d)|d^{−2/3} ≤ 7.99·exp(0.1426) ≤ 9.32` (the finite product over
`p < 10⁴` is a numerical axiom; the tail is bounded by an integral). Then
`|G(N) − log N − κ| ≤ (2 + 3/e + γ)P N^{−1/3}`; comparing with `N₀ = 3·10⁷` (numerical value of `G(N₀)`)
eliminates `κ`. Finite range `6 ≤ r < 3·10⁷` is a numerical axiom. Checks: `scripts/mv_lemma8_check.py`.
**Resource note:** the first `GS_asymp` proof (one big `nlinarith` over a large context) exhausted memory and
crashed WSL; keep proofs split, use `linarith only`/`nlinarith only`, compile with `lake env lean -M 10000`, and
rebuild many modules sequentially (`lake build M` one module at a time in topological order).

**Large sieves (`Prelim/LargeSieveMV.lean`): DONE 2026-10-31** (both proved; files Shan, HilbertIdentity, HilbertReal, HilbertCsc, LargeSieveMVProof). Achieved constants: weighted 4.66 (real line), csc 4.66/π ≤ 1.4834 ≤ 3/2. Sources: Yangjit, arXiv:2203.14950
(Shan's proof of the spacing lemma, Prop 3.1, Preissmann's Cauchy–Schwarz argument);
Preissmann–Lévêque, arXiv:1303.1085, Lemma 5(b) (the eigenvector identity).
1. Shan's lemma: for `λ` strictly increasing (a finite set) with `δ_k` the distance to the nearest other
   point, `∑_{k≠l} δ_k/|λ_k−λ_l|^σ ≤ 2ζ(σ)/δ_l^{σ−1}` (Yangjit Lemmas 2.3–2.5).
2. Eigenvector identity: for `H = [c_m c_n/(λ_m−λ_n)]` and `Hu = iμu`,
   `μ² = ∑_{m≠n} c_m²c_n²|u_n|²/Δ² + 2∑ c_m³c_n Re(u_m ū_n)/Δ²`. So `μ² ≤ S + 2T`.
3. Our replacement for Preissmann's Lemme 6, which we could not obtain:
   `∑_{k≠l,m} δ_k/(a_k² b_k²) ≤ (1/D²)[(π²/3)(1/δ_l+1/δ_m) − (δ_l+δ_m)/D² + (2/D)(F_l+F_m)]`. Here
   `1/(a²b²) = D⁻²(1/a² + 1/b² − 2/(ab))`, the cross terms of the outside points are dropped, and
   `F_l = ∑_{between} δ_k/|a_k| ≤ (1 − ½log 2) + log(D/δ_l)`. Each step of the last bound uses
   `min(a_n,a_{n+1})/λ_n ≤ ½ log(λ_{n+1}/λ_{n−1})` (from `artanh t ≥ t`), and the sum telescopes.
   Hence `κ = 1 + (3/π²) max_s [2(1 − ½log2 + log s)/s − 1/s²] = 1.3356`.
   Then `C(½) ≤ K + √(K² + π⁴/45) = 9.028` with `K = κπ²/3` (≤ 9.458 is needed), and
   `C₁ = √(π²/3 + 2C(½)) = 4.620 < 3π/2`. Checked numerically (`/tmp/test_l6.py`, ratio ≤ 0.68).
4. Periodization to the circle: apply the real-line inequality to `x_r + k`, `|k| ≤ K`, with
   `z_{r,k} = (−1)^k z_r`. The Cesàro kernel `(2K+1)⁻¹∑_{|j|≤2K}(2K+1−|j|)(−1)^j/(x+j) → π csc πx`
   (the paired series is absolutely convergent; `csc y = cot(y/2) − cot y`). Csc constants: `C₁/π ≤ 1.4706 ≤ 3/2`
   (weighted), `1` (unweighted, `μ² ≤ 3S`).
5. Large sieve by duality: `N + δ⁻¹`, resp. weights `(N + (3/2)δ_r⁻¹)⁻¹`. **Dilation trick for
   `N − 1 + δ⁻¹`**: apply the bound to `n ↦ kn` at the points `(α_r + j)/k`, `0 ≤ j < k`, which are
   `δ/k`-separated. This gives `k∑|S(α_r)|² ≤ (k(N−1)+1 + kδ⁻¹)‖a‖²`; let `k → ∞`.

## Prelim sensitivity: which literature bounds can be weakened (2026-10-31)

`scripts/prelim_sensitivity.py` (approximate models, not certified): it re-runs the Thm 3.1.1
first-case model (`thm_3_1_1_numerics.py`) with each `Prelim/` constant as a parameter, then
re-runs the repair-3 cell model (`minor_arc_cells_check.py`). Lean needs worst `Z ≤ 1.037`; the
baseline is `0.9646`. The second case (`0.276`, `1234`) is scaled heuristically: by `√` of the
factors on the S2 side and on C.2.2, and linearly by the ψ ratio.

The ✓ bounds can be weakened as shown, but the constants in Thm 3.1.1 change (`0.8103 → ≈1.07`),
so the Lean numerics (FirstChoice*, Second* pieces, cells) would have to be regenerated.

* ✓ (2.14)/(2.15)/(2.17) `ψ(y) ≤ a y`: anything up to `a ≈ 1.376` works (Chebyshev's elementary
  `1.10555` gives `Z = 0.985`). Note that `log 4 = 1.386` just fails.
* ✓ (2.12) `log x + 0.4`; (5.5) `2√y`; (2.23) `2 q/φ(q)`: no visible effect.
* ✓ (2.22): the constant `4/5` can go up to about 22. It cannot be dropped (`Z = 2.4`), and its
  `1/log(x/q)` decay is PNT-strength, so a crude explicit PNT is still needed.
* ✗ the large sieve: only 19% slack on the S2 side. Gallagher's form (factor ≥ π) fails, so the
  sharp Selberg / Montgomery–Vaughan forms are needed (pure analysis, no prime data).
* ✗ (2.19) `½ y log y`: the binomial-coefficient bound (`log 2`) fails. It needs
  `θ(y) − θ(y/2) ≲ 0.59 y`, i.e. a weak explicit PNT (Chebyshev's constants give ≈ 0.645).
* ✗ C.2.2: the coefficient of `log log r` can go up to 2.14 (`e^γ = 1.781`); a crude elementary
  Mertens (≈ 2.4) fails. Possible route: an exact primorial computation of `max_{q ≤ r} q/φ(q)` for
  the finite range of levels, plus an elementary Mertens bound for large `r`, where the asymptotic
  numerics have room.
* Not modelled: (2.13) (only in TypeI2Large), [MV73, Lemma 8]'s `0.25068`, (2.20) (now proved
  as stated).

## Ch. 13: scale erratum (the ℓ∞ and ℓ² inputs use arcs at different scales)

Prop 13.1.2 combines, **for one family of arcs** `𝔐_{δ₀,r}` ((10.5), defined with a parameter
`x`), an ℓ² bound `∫_{𝔐_{δ₀,r+1}} |S₁|² ≤ H(r) Σ|aₙ|²` (13.4) and an ℓ∞ bound
`|S₂(α)| ≤ g(r)` off `𝔐_{δ₀,r}` (13.5). In the proof of Thm 13.2.1 (pp. 249–252):

* the ℓ² input `H(r) = (log(r+1) + c⁺)/(log √x + c⁻)` comes from Cor 12.2.5 (12.42) with
  arcs at **scale `x`**: `c⁻ = 0.6394 < log(1/√(2·8)) + log 2 + 1.3325822` is `log 2Q + c_E` with
  `Q = √(x/16)`. `J` (14.7), the major arcs (14.27) and `E_{η_*,r,8}` (14.17) are also at
  scale `x`, and so is our `majorArcs 8 r₀ (xOf N)` in `minor_arcs_input`;
* the ℓ∞ input (13.14)–(13.17) is derived only for `α` outside the arcs at **scale
  `y = x/κ`**: "Let α ∉ 𝔐_{8,r} … where y is used instead of x to define 𝔐_{8,r}" (p. 249). The
  paper arXiv:1312.7748, p. 48, has the same sentence.

The `y`-arcs are `κ = 49` times wider. For `α` outside the `x`-arcs but inside the `y`-arcs
(`q ≤ r`, `8r/κ ≤ |δ_y| q < 8r`), Thm 3.1.1 at scale `y` gives only
`r_α = max(q, |δ_y|q/8) ≥ max(q, r/κ)`. For example, take `q = 1` and `α` just outside the
`x`-arc around `0` at level `r₀`: `δ_y ≈ 8r₀/κ`, so `r_α ≈ 3061` and the bound is `g(3061) ≈ 7 g(r₀)`.
(The true value there is tiny: it is a major-arc point for the shorter sum `S_{η_*}`.)

Repairs tried (`scripts/minor_arc_scale_check.py`; all at `x = 4.9·10²⁶`, our constants):
1. **Everything at scale `y`**: `c⁻ → c⁻ − log 7`, which gives `M ≈ 0.8497` and
   `Z ≈ 1.0654 x²/κ > 1.058259`. **Fails.** (With [H]'s `0.5`, `Z ≈ 1.049`, which would pass.)
   It also needs the major arcs to be `𝔐_{392,r₀}` at scale `x`, beyond Thm 7.1.4's range
   `|δ| ≤ 600000·gcd(q,2)/q`.
2. **Everything at scale `x`, with Part II on the gap**: Cor 7.1.3 (GRH-verified, `q ≤ 300000`,
   `|δ_y| ≤ 4·300000/q`) bounds `S_{η_*}` on the gap whenever `q ≤ 300000`, including all of level
   `r₀`. But for levels `r ∈ (300000, r₁]` the gap contains `q ∈ (300000, r]`, where only
   `g(q) ≥ g(300000)` is available. The tail (14.43) needs `g(r₁)`; with `g(3·10⁵) ≈ 0.0317`
   instead of `g(r₁) ≈ 0.0156` it grows from `0.312` to `0.636`. **Fails** by a wide margin.

**Resolution (2026-10-31): repair 3 works, with room to spare** (`scripts/minor_arc_y_scale_repair.py`):
* Prop 13.1.2 with the family `M_{r₀} = 𝔐_{8,r₀}(x)`, `M_n = 𝔐_{8,n}(y) = 𝔐_{392,n}(x)` for
  `n > r₀` (nested). The base term keeps [H]'s `I₀ ≥ (√J − √E)² ≥ 8.6297x`.
* ℓ² from (12.42) with `δ₀ = 392`.
* ℓ∞ off `𝔐_{8,n}(y)` from a **fresh Dirichlet approximation at each scale `wy`** in (11.9). Since
  `𝔐_{8,r}(wy) ⊆ 𝔐_{8,r}(y)` for `w ≥ 1` and `⊆ 𝔐_{8,r/w}(y)` for `w < 1`, this gives
  `r_w ≥ min(1,w) n`. Thm 3.1.1 at scale `wy` then gives `max(g_{wy}(min(1,w)n), h(wy))`.
  The first case always has `r_w ≤ (wy)^{1/3}/6`, so `gx_antitoneOn` applies. This
  "Prop 11.2.3′" also sidesteps the `δ ↦ wδ` erratum.
* **Levels up to `r₂ ≈ x^{0.3}`** (the range of (12.42)), not [H]'s `r₁ = (3/8)y^{4/15} ≈ 10⁶`.
  The tail (14.43) shrinks from `0.30` to `0.12`.
* The base gap `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)` (needed: `|S_{η_*}| ≤ |φ|₁ g(r₀) y ≈ 0.0555y`) is
  covered by [H, Cor 7.1.3]. Its range `q ≤ 300000`, `|δ| ≤ 1.2·10⁶/q` is exactly
  `𝔐_{8,r₀}(y)`. In the gap `|δ| ≥ 12245/q`, so `|S_{η_*}| ≤ (|η̂(δ)|/φ(q) + 1.3·10⁻⁷) y ≤ 0.02y`.

Result: `Z ≤ 0.866 x²/κ` at `y = 10²⁵` (decreasing: `0.823` at `10²⁶`, `0.617` at `10⁸⁰`), against
`1.058259`. That is better than [H]'s own `1.00948`, even with our corrected Thm 3.1.1. With
`r₂ = 10⁶` the same scheme gives `1.10`; the book's `r₁` was too small once the scale is handled
correctly. **So the flaw is fixable**; `minor_arcs_input` (`≤ 1.0376`) is true by this route.

Formalization plan (repair 3):
1. ✅ Prop 11.2.3′ (`Prop1123b.lean: prop_11_2_3'`, same 20 trusted items as Thm 3.1.1), and
   ✅ the repaired assembly `thm_13_2_1_repaired` (`Thm1321.lean`: mixed family `Mmix`, (12.42)
   with `δ₀ = 392`; uses only Prop 12.2.4).
   ✅ Per-level ℓ∞ in closed form (`LinftyLevels.lean: norm_S_etaStar_le_ghat`): off
   `𝔐_{8,n}(y)`, `|S_{η_*}| ≤ y·ghatY(y,n)`, `ghatY = 1.398·max(g_y(n), h(y)) + 17(670/n)³/3`
   (`w₀ = 670/n`, `w₁ = ∞`; `g_{wy}(min(1,w)n) ≤ g_y(n) max(1,1/w)`, `h(wy) ≤ h(y) max(1,1/w)`,
   `∫_{w₀}^∞ max(1,1/w)φ ≤ 1.398` in `PhiIntegrals.lean`). Numerics with exactly this majorant
   (`/tmp`-style check, to be turned into a script): cells in `y`, blocks of ratio 1.25 in the
   level, `r₂ = min((2√(x/784))^{0.6}/2 - 1, √(x/784)/20000)`: worst `Z ≈ 0.965` (cell
   `[1.01e25, 10^25.5]`), using `I₀ ≥ 8.6249x` and `E/x ≤ 10⁻⁶` with `t = 0.004` in
   `|a+b|² ≤ (1+t)|a|² + (1+1/t)|b|²`.
2. The base-gap bound from Cor 7.1.3 (a new cited Part II input) via the character expansion
   (`Bombieri.lean` tools, `gauss_induced`) and a bound on `η̂_*`.
3. Thm 13.2.1 assembly with the mixed family (generalize `thm_13_2_1_conditional`). Also the
   `S_{η₊} = S₁ + S₂` split (14.29)–(14.32), with [H]'s cited Part II constants `J`, `E`, (7.1.5).
4. Numerics for all `x ≥ 4.9·10²⁶`: closed-form majorants for `G`, then interval checks.

Earlier conclusion, kept for the record: neither [H]'s argument as written nor repairs 1–2
establishes (14.49) over the complement of the scale-`x` arcs. `minor_arcs_input` remains a cited-but-unverified input. Possible ways forward:
a finer ℓ² accounting of the gap region (by `q` and `δ`), different parameters (`κ`, `r₁`), or
checking whether a later version of [H] fixes this.

## Ch. 11: Prop 11.2.3 erratum (the proof ignores that `δ` scales with `w`)

Helfgott found this erratum himself around 2016 and reported it to the publisher and colleagues;
it is not new. He notes that the quickest repair is "dirty and duct-tape-y". Ours, Prop 11.2.3′
(`Prop1123b.lean`), is quick: a fresh Dirichlet approximation per scale `wy`, plus the crude majorant
`max(1, 1/w) g_y(n)`, which loses a factor `1.398`. A cleaner repair would follow the analysis below:
`r_w ≥ w r` for `|δ| > 8`, and the gain for `w > 1` offsets the loss for `w < 1`.

[H]'s proof writes `S_{η_*}(α,x) = ∫ S_{η₂}(α, wx) φ(w) dw/w` (11.9) and applies Thm 3.1.1 to
each `S_{η₂}(α, wx)` with the same `r = max(1, |δ|/8) q`. At scale `wx`, though,
`2α = a/q + δ_w/(wx)` with **`δ_w = wδ`**, so:

* for `w < 1` the parameter is `r_w = max(1, w|δ|/8) q ≤ r`, and the bound `g_{wx}(r_w)` is
  *weaker* than the `g_{wx}(r)` [H] uses (`g` is decreasing);
* for `w > 1`, Thm 3.1.1's hypothesis `|δ_w/(wx)| ≤ 1/(q Q_{wx})` does not follow from
  `|δ/x| ≤ 1/(q Q_x)`, because `Q_{wx} > Q_x`. It holds for `w ≤ ((4/3)x^{1/3}/(8r))^{3/2}`,
  which is `≥ 94` when `r ≤ r₁ = (3/8)x^{4/15}`, `x ≥ 10²⁵`. Beyond that, `φ(w) ≤ e^{-4400}`
  and the trivial bound suffices. (Alternatively, a Dirichlet re-approximation `a'/q' ≠ a/q` at
  level `Q_{wx}` has `q' ≥ Q_x(1 - q/Q_{wx})`, which is the `h` case.)

The statement survives. For `|δ| ≤ 8`, `r_w = q = r` and nothing changes. For `|δ| > 8`,
`r_w ≥ w r`, and `A(r) = ∫ g_{wy,1}(wr) φ(w) dw ≤ 0.89 ∫ g_{wy,1}(r) φ(w) dw = C(r)` (the gain
for `w > 1` outweighs the loss for `w < 1`; `scripts/prop_11_2_3_check.py`, `r₀ ≤ r ≤ r₁`,
`y ∈ [10²⁵, 10¹⁰⁰]`). **Plan for Lean:** state Prop 11.2.3 only for `r ≤ r₁` (all that Ch. 13
needs; for `r > r₁` Ch. 13 uses `g(r₁)`). Prove it with per-`w` bounds `g_{wy,1}(r)` (`|δ| ≤ 8`)
and `g_{wy,1}(wr)` (`|δ| > 8`). Then either show the `|δ| > 8` integral is `≤` [H]'s closed form
`g_{y,φ}(r)`, or carry a closed form for `∫ g_{wy,1}(wr)φ(w)dw` into Ch. 13 directly.
Also note that the case `r > r₁` of Ch. 13 needs, for `w ≤ 1`, `g_{wy}(max(q, wr')) ≤ g_{wy}(w r₁)`.
That is not `g_{wy}(r₁)`, so the `g(r₁)` of (13.13)/(14.43) must be read the same way.

## Prop 12.2.4 with `c₊ = 2` (removes `prop1224_check`)

[H]'s Prop 12.2.4 with `c₊ = 1.36` needed, for `q < 2.2·10¹⁰`, a computation over 88 million
`(q, n)`: our axiom `prop1224_check`. Weakening the constant alone does not shrink it enough (at
`c₊ = 2`, about 24 million checks remain, for smooth `q` up to `10⁹`). What works is a structural
reduction, which `c₊ = 2` makes possible:
* `Φ(q, n, L) = (q/φ) G_q(n) − log n − c − S_q + 0.1768 (q/φ) f₁ n^{−1/3} − (0.3414 (L − S_q) + 0.6674177)`;
  `Φ(q, ⌊R⌋, L) ≤ 0` with `L ≤ log sq` gives Prop 12.2.4 at `R` (`checkC2_suffices`, `LSQuot7`;
  `θ ≤ 0.6586`).
* **Removing a prime** (`LSQuotRed`): for squarefree `q < 2.2·10¹⁰` with largest prime `p ≥ 17`,
  `G_{q/p}(n) = G_q(n) + G_q(n/p)/(p − 1)`, `(q/φ(q)) G_q(x) ≥ G(x) ≥ log x` give
  `(1 − 1/p) Φ(q) ≤ Φ(q/p) + Δ(p)`, with `Δ(p) ≤ −0.12` (uses `S_q ≤ 2.322`, `K f₁ ≤ 8.4223` over
  `≤ 9` primes, `log q ≤ log p#` for `p ≤ 29`). `G(x) ≥ log x`: Ramaré for `x ≥ 200`, a kernel walk
  `H_n ≤ G(n)` below. So `Φ(q) ≤ 0` follows from `Φ(A) ≤ 0` for `A ∣ 30030` (radicals handle
  non-squarefree `q`).
* **The divisors of `30030`, `n ≥ 4`** (`LSQuot8`, `LSQuot8g`, generated by
  `scripts/gen_lsq_base.py`): Ramaré for `n ≥ 2600`; below, a kernel walk per `A` (trial-division
  `φ`, `⌈10¹²/φ(r)⌉` accumulators, 82 blocks with `2^j ≤ a⁶`, `v³ ≤ a`). Margin `≥ 0.33`; 90 s.
* **`n ≤ 3`** (`LSQuot9`): needs `log sq ≥ log(10⁵/(n+1))`, so no reduction; `G_q(n)` depends only on
  `2 ∣ q`, `3 ∣ q`; the primes `≥ 5` (at most 8) are bounded by exchange applied to `P' ∪ {2, 3}`;
  72 rational checks, worst `−0.051`.
* Downstream: `cL n = log 2(n+1) + 2`, Cor 12.2.5, Thm 13.2.1, the cells (worst `1.00666`, was
  `0.96534`) and `NumericsAsymp` (`cL 150000 ≤ 14.61155`).

## Lemma B.1.2 with `c₀ = 32` (removes `eta2DD_small`)

Helfgott suggested a slightly weaker constant. `|η̂₂''|_∞ ≤ 32` is now proved
(`Eta2DDExpand.lean`, `Eta2DDTaylor.lean`, `Eta2DDBound.lean`), and `c₀ := 32` (`InnerSums.lean`).
* `t ≥ 2`: `eta2DD t = F(z, w) + O*(6120 w³)`, `z = e(−t/4)`, `w = 1/2πt`, by three integrations by
  parts of `Jq`. `F` is a polynomial in `z, w` (`Fz`); `z` is treated as free on the circle,
  parametrised by `zm m = ((1−m²) + 2mi)/(1+m²)` for `m ∈ [−1, 1]` and sign `±`. `chk` bisects
  `(m, w) ∈ [−1,1] × [0, 2/25]` with Lipschitz constants `LzQ`, `LwQ` (`chk_sound`).
* `t ≤ 2`: `x = 2πt ≤ 12.6`, Taylor polynomials of degree `< 50` (`Complex.exp_bound'`), error
  `120 |x|^50/50!`; the coefficients `β_j` are rational (`βR_eq`), `PQ` evaluates the polynomial
  exactly over `ℚ`, and `chkC` bisects with the 24-Lipschitz bound `norm_eta2DD_sub_le`.
* The three `decide +kernel` checks take about 4 minutes in all.
* Downstream re-tuning (`√c₀ ∈ [5.6568, 5.6569]`, `c₂ ∈ [0.6664, 0.6665]`, `2√c₀/π ≤ 3.6015`):
  * `FirstChoiceTypeI`: `c₂^{3/2} ≤ √c₂·c₂ ≤ 0.545` (was `≤ c₂`) keeps `0.0139 x^{5/6}`.
  * `FirstChoiceTypeI2`/`2b`/`2c`: the `x/√t` coefficient of `S_{I,2}` is `2.5106` (was `2.4916`),
    the `2x/t` part `15.267 log t + 21.446` (was `15.163`, `21.296`).
  * Theorem 3.1.1 (first case): `2.511 x/√t` (was `2.5`); hence `gx`, `NumericsCore`,
    `LinftyLevels`, `EtaStarBound`, `PointwiseBound`, `MinorTotal`, `NumericsAsymp` and
    `scripts/gen_cells.py` (cells regenerated: worst total `0.96534` against `1.037`).
    `SecondBridge`: `2.511 √3.0001 ≤ 4.35`.
  * `BaseGap2`: `fourier_const_le ≤ 1.016`, gap `≤ 0.0121 y` (was `0.012 y`; `ghatY_r0_ge` has room).
  * Second case: `typeI_second ≤ (0.0717 L² + 3199.9 L + 8471.0) T²` (was `0.0716`, `3175.9`,
    `8407.2`); `SecondFinal` absorbs it with `502.1 L` for `526.1 L`.

## How the 4.2.2 proof is organised (reuse for 4.2.3, 4.2.4)

* Case (a) uses `second_approx` (Dirichlet via `Real.exists_rat_abs_sub_le_and_den_le`,
  `q' ≥ εQ/(1+ε)`), `sum_A1` (blocks from 0, Lemma 4.1.2) and `sum_R3'` with `(a', q')`.
  The proof gives (4.32) with the unrounded `x/|δq|` where [H] has `min(⌊x/|δq|⌋ + 1, 2D)`
  (never larger).

* `typeI = mainPart + restPart` (`typeI_eq_main_add_rest`): `mainPart` is `q ∣ m ≤ M`.
* `mainPart` via `Todd_main` (Poisson); `restPart` via `|T_{m,∘}|` bounds (`norm_Todd_le_minA`,
  `norm_Todd_le_min_sin`) and Lemmas 4.1.1'/4.1.2/4.1.3 applied to `2α ≈ a/q + δ/x`
  (`approx_of` with a *real* `Q = x/|δq|`).
* Index sums are over `ℤ` (`Ioc ⌊y₁⌋ ⌊y₂⌋`, `Tn α x n = ‖Todd α x n.toNat‖`), to match §4.1.
* `Mof` now uses the unrounded `Q = x/|δq|` (allowed by the statement `M ∈ [min(Q₀/2,D), D]`);
  with `⌊x/|δq|⌋` the book's `min(c₂x/q, D) ≤ Q/2` can fail by `< 1/2`.

## Decisions made

* Follow the book [H] = arXiv:1501.05438v2, not the 2013 papers. Its minor-arc bound is
  1.00948 (not 0.97392), so [H]'s final margin is 0.048779·x²/κ (ours is 0.020659, see Status).
* Where the final inequality has room, prove cruder constants instead of the book's sharp
  ones (e.g. non-prime terms: 6.7·10⁶ instead of 7.3306). Record each such change in the
  docstrings and the README.
* Computations (binary Goldbach, prime ladder, Platt's GRH check, "rigorous computations") are
  meant to end up as explicitly labelled trusted facts.
* Blueprint statements use the book's exact constants and are transcribed from the typeset PDF.
  In Lean, watch division by zero: write `min(1, c/δ²)` with an explicit `δ = 0` case
  (`minInv`). `C / sin² = C/0 = 0` is fine, because it only makes the left side smaller.
* Book errata found so far: (4.32) cites "(4.8)" where it means (4.29). The proof of Lemma 4.1.3
  doesn't give its `max(2, …)` form (see the `TrigSums.lean` docstring). The η₁ typo in §7
  disagrees with (4.10)/(11.10); we use η₁ = 2·1_{[1/2,1]}. (4.34) ends with a stray factor `x`.
  In the proof of 4.2.1/4.2.2, `Q = ⌊x/|δq|⌋` is too small by rounding for `c₂x/q ≤ Q/2`
  (we use the unrounded `Q`). Lean's `C/0 = 0` makes `min(A, C/sin²)` vanish where `sin = 0`,
  so Lemma 4.1.1 is also proved with the honest summand (`lemma_4_1_1'`, `minA`).
* Part II/III errata (2026-11-01): (9.70)'s second line has `x^{1/2}` for `x^{-1/2}`. In §14.1 the term
  `5.19 δ₀ r ET_{η₊,δ₀r/2} (|η₊|₁ + ET/2)` is printed as `≤ 0.075272`, but with [H]'s own (14.1)
  (`ET ≤ 1.1405·10⁻⁸`) and (14.3) (`|η₊|₁ ≤ 1.062319`) it is `0.075456`; so (14.7) holds with `O*(0.0756)`, not
  `O*(0.0754)`. We state `l2_major_14_7` with `0.0756`; MinorTotal then uses `∫_𝔐 |S_{η₊}|² ≥ 8.6296x` and
  `I₀ ≥ 8.6294x` (the numerics `Mexpr ≤ 1.037` keep a margin `0.34` in the asymptotic range, cells unchanged).
  The rest of §9.6 checks out (`2.48404·10⁻¹⁹ ≤ 2.485·10⁻¹⁹`; Thm 7.1.4's `q = 1` constants hold with
  `4.7712·10⁻¹¹`, `251385`).
  **(4.40) is inconsistent with its proof**: the statement has `x/q`, `η̂(-δ)` (so
  `min(1, c₀/(2πδ)²)`) and `(m,q) = 1`, the values for the all-`n` version; the proof (p. 67) gives
  `x/2q`, `η̂(-δ/2)` (so `min(1, c₀/(πδ)²)`) and `(m,2q) = 1`, as in (4.30). `bound_4_40` is the
  corrected form. **To check in Ch. 6**: §6.2.1 uses (4.40) for `S_{I,1}`; the corrected
  `δ`-decay is 4× weaker for large `δ` (the prefactor halves), so the final numerics there
  may need re-checking. Note §6.2.1 itself copies the uncorrected (4.40).
  **Theorem 3.1.1's constant `0.5` is not proved**: in §6.4, (6.77), the AM–GM step gives the
  constant `log 2/(2√ρ) + (√ρ/2)·0.67506 = 0.81020` (ρ = 3.397962), but [H] computes
  `(1/2)(log 2/√ρ + (√ρ/2)·0.67506) = 0.49911`. [H]'s own (6.63) exceeds the stated bound by up to
  ~2.6% (numerically, `q` prime, `δ₀q ~ 10⁵–10⁷`). `PointwiseBound.lean` now uses `0.8103`.
  ✅ Checked: the effect on Chs. 11, 13, §14.3 is `1.00948 → 1.0376` in (14.49) (see Status).
  **(6.12) understates the μ-sum for odd `q`**: the sum is over `(m, 2q) = 1`, so (2.22) applies
  with modulus `2q` and gives `(4/5)(2q/φ(2q))/log(M/2q²)`; [H] writes `q/φ(q)`. For odd `q`,
  `2q/φ(2q) = 2q/φ(q)`, so the term `(3/2 log q + 2.74) x/φ(q)` of (6.58) should be doubled.
  (It doesn't break Thm 3.1.1 numerically, but [H]'s slot-by-slot derivation of
  `L_{x,t,q}` doesn't go through as written; we use `min(1, a/ℓ)(ℓ + b) ≤ a + b` to move the `b`
  part into the `x/(δ₀q)` slot.)

  **§6.3.2 uses (5.54) outside its range**: Prop. 5.2.4 assumes `Q ≥ 3.5W`, but with [H]'s
  second choice `Q = x/U`, (6.38) applies (5.54) for `W` up to `x/U = Q`. Fix: re-approximate
  with `Q₀ ≥ 3.5x/U` (costs nothing visible; the `Q`-terms of `S_I` are lower order).
  **§6.3.2's case split has a gap**: [H] says that for the new approximation `a'/q'`, either
  `q' > y` or `|δ'| > 8y/q'`, "since otherwise `a'/q'` would already be a valid approximation under
  the first choice". But Thm 3.1.1's hypothesis is an *arbitrary* approximation `a/q` with
  `q > y`, and two approximations can coexist (e.g. `2α = 1/Q`: `1/1` with `δ = x/Q` and `1/⌊Q⌋`).
  Fix: in that case (`q' ≤ y`, `|δ'| ≤ 8y/q'`), `a'/q'` is an approximation for `Q = (3/4)x^{2/3}`
  and `1/qq' ≤ |a/q - a'/q'| ≤ 1/qQ + |δ'|/x` forces `δ₀'q' ∈ [2y(1 - y/Q), 2y]`, where the first
  case of the theorem gives `≈ 59 x^{5/6} ≤ 0.276 x^{5/6}(log x)^{3/2}`.

## Reading the book

* The arXiv PDF has 327 pages. **PDF page = printed page + 10.**
* Extracted text (`pypdf`) loses fraction structure. For formulas, render pages with PyMuPDF
  (`pip install pymupdf` in a venv, `page.get_pixmap(dpi=110).save(...)`) and read the images.
* Before formalizing any inequality, check it numerically (`mpmath`, high precision; float
  cancellation near 0 gives false negatives). This caught the Lemma 4.1.3 gap and picked the
  Taylor degrees.

## Lean 4 / Mathlib pitfalls hit so far

(Most were found on v4.15; we upgraded to v4.35 on 2026-10-30.)

* `linarith` can fail on decimal literals (`0.93`) and on `set`-introduced variables. Use
  fractions, and `obtain ⟨t, ht⟩ : ∃ t, t = … := ⟨_, rfl⟩` instead of `set`.
* `interval_cases q` does not update variables introduced by `set … := f q`, so handle small
  cases before any `set`.
* `rw [← integral_add_adjacent_intervals]` may rewrite the wrong side. Instead state
  `have e := integral_add_adjacent_intervals (a := …) (b := …) (c := …) (μ := volume) …` and
  use `linarith`.
* `∫ u in x / 2..y` misparses (`2..`): parenthesise the bounds.
* `ConvexOn.2 … (a := l)` clashes with local variables named `a`/`b`: give the expected type.
* Lemmas declared inside our namespace as `ConvexOn.foo` need `_root_.ConvexOn.foo` for
  dot notation.
* Opening `Set` and `Finset` together makes `mem_Icc` etc. ambiguous. Opening
  `ArithmeticFunction` makes `μ` mean Möbius. Use
  `open scoped ArithmeticFunction.vonMangoldt` instead.
* Big `nlinarith`/`linarith` calls time out in large contexts. Use `linarith only [...]`, split
  into explicit `have`s, or raise `maxHeartbeats` locally.
* Tight polynomial inequalities: reduce to one variable (replace C by its bound using the sign of
  its coefficient, then prove monotonicity in S via an explicit factorisation), then
  `nlinarith`. Alternatively, split into one-function inequalities (x cot x ≤ …, t²/sin²t ≤ …).
* Mathlib has `ConvexOn.comp_concaveOn`, `strictConcaveOn_sin_Icc`, `convexOn_zpow`,
  `monotone_arcsin`, `Real.cos_arcsin`, `primorial_le_4_pow`, `Real.lt_tan`.
* Reusable lemmas: `le_of_hasDerivAt_le` (compare functions via derivatives on [0,∞)), the sin/cos
  Taylor chain, `sum_range_pair`, `sum_Icc_low_high`, `sum_Icc_parity`, and the generic residue
  reduction `residue_form_gen` (any summand Φ(sin²(παn)) ≥ 0) in `TrigSums.lean`.

* `linarith` cannot use hypotheses with division by a decimal literal (`L / 2.9`, `x / 13.8`):
  rewrite as multiplication or with `div_le_iff₀` first. Unascribed numeral `have`s (`have : 4 * … ≤ 0.13`)
  may elaborate in the wrong type; write `(4 : ℝ)`. `set` does not abbreviate hypotheses created
  later, so `linarith` may see `Real.log …` and the `set` variable as different atoms.

## Environment

* Lean/Mathlib v4.35.0. Fetch the prebuilt Mathlib with `lake exe cache get` (the network
  allows it). Our own files build in a few minutes; `TrigSums.lean` is the slowest.
* Upgrade notes (v4.15 → v4.35), useful for the next bump:
  * Renames: `le_or_lt`→`le_or_gt`, `lt_or_le`→`lt_or_ge`, `Int.floor_add_int`→`Int.floor_add_intCast`,
    `Int.ediv_add_emod`→`Int.mul_ediv_add_emod`, `primorial_le_4_pow`→`primorial_le_four_pow`,
    `Finset.sum_eq_add_sum_diff_singleton`→`Finset.sum_eq_add_sum_sdiff_singleton_of_mem`,
    `Nat.Ico_succ_right`→`Finset.Ico_add_one_right_eq_Icc`, `left_mem_Ici`→`Set.self_mem_Ici`,
    `integral_finset_biUnion`→`integral_biUnion_finset`, `MeasureTheory.integral_mul_left`→
    `integral_const_mul`, `*_not_mem*`→`*_notMem*`, `if_pos/if_neg`→`ite_eq_left/right`,
    `push_neg`→`push Not`, `List.Chain R a l`→`List.IsChain R (a :: l)`.
  * `Complex.abs` is gone: use `‖·‖` (`Complex.norm_exp`, `Complex.abs_re_le_norm`, `Complex.norm_real`).
  * `setIntegral_const` now gives `volume.real s • c`: use `Real.volume_real_Ioc_of_le` etc.
    `integrableOn_const` takes the finiteness proofs as (auto)arguments.
  * `field_simp` is stronger: a trailing `ring` often errors with "no goals".
  * `convert … using 1` with `hasDerivAt_id`, `.sub`, `.add` now leaves function-equality goals
    (`(fun x => …) = id - …`): close them with `funext y; simp only [Pi.sub_apply, id_eq]`.
  * `ArithmeticFunction` notation needs `open scoped ArithmeticFunction.Moebius
    ArithmeticFunction.zeta` (Λ comes with `open ArithmeticFunction`).
  * `Real.sin_gt_sub_cube` is now `0 < x → x - x³/6 < sin x` (no `x ≤ 1`, sharper constant).
* Clone/push via SSH (`git@github.com:calr3/ternary-goldbach.git`). HTTPS has no credentials.
