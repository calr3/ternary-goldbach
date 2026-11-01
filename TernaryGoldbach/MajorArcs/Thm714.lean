import TernaryGoldbach.MajorArcs.Prop715

/-!
# [B, Thm 7.1.4] from [B, Prop 9.4.2] and Platt's verification

`η₊(t) = h₂₀₀(t) t e^{-t²/2}` ([B, (9.63)], our `etaPlus`, which vanishes on `t ≤ 0`).
[B, Prop 9.4.2] (cited, conditional on GRH up to `T₀ ≥ H + max(10π|δ|, 50)`, `H = 200`) with
`T₀ = 200 + 1.2·10⁷π` (`q = 1`, [B, §9.6]).

*Book note*: in (9.70) the second line reads `(1.634√T₀ log qT₀ + … + 34.51) x^{1/2}`; it is `x^{-1/2}` (the
statement is `O*(err) · x`, and §9.6 uses `1/√x`).
-/

open Real MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (e Schar)
open TernaryGoldbach.Helfgott (etaPlus)

/-- The error term (9.70) of [B, Prop 9.4.2] with `H = 200`, `T₀' = T₀ − 200`. -/
noncomputable def err942 (q : ℕ) (T0 δ x : ℝ) : ℝ :=
  (11.308 * √(T0 - 200) * Real.exp (-0.1598 * (T0 - 200)) + 16.147 * |δ| * expδ (T0 - 200) δ) *
      Real.log (q * T0 / (2 * π)) +
    (1.634 * √T0 * Real.log (q * T0) + 12.43 * √T0 + 1.321 * Real.log q + 34.51) / √x +
    (9 + 11 * |δ|) / x + Real.log q * (11 + 6 * |δ|) / (x * √x)

/-- **[B, Prop 9.4.2]** — *cited* (explicit formula, Lemmas 9.1.1, 9.1.4, 9.4.1), for `η₊` with `H = 200`:
if `x ≥ 10³`, `χ` is primitive mod `q` and GRH holds for `L(s, χ)` up to `T₀ ≥ 200 + max(10π|δ|, 50)`, then
`Σ Λ(n) χ(n) e(δn/x) η₊(n/x) = [q = 1] η̂₊(-δ) x + O*(err_{η₊,χ}(δ, x)) x`. -/
theorem prop_9_4_2 {x : ℝ} (hx : 1e3 ≤ x) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T0 : ℝ} (hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0) (hG : GRHUpTo χ T0) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤ err942 q T0 δ x * x := by
  sorry


/-- `11.308 √t e^{-0.1598 t}` is negligible for `t ≥ 10⁶`. -/
theorem sqrt_exp_tiny {t : ℝ} (ht : 1e6 ≤ t) : 11.308 * √t * Real.exp (-0.1598 * t) ≤ 1e-30 := by
  have h1 : √t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2 : t * Real.exp (-(0.1598 * t)) ≤ 1e6 * Real.exp (-(0.1598 * 1e6)) :=
    mul_exp_anti (by norm_num) (by norm_num) ht
  have h3 : Real.exp (-(0.1598 * 1e6)) ≤ Real.exp (-100) := Real.exp_le_exp.2 (by norm_num)
  have h4 : Real.exp (-100) ≤ 1e-40 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := exp_nat_ge 100
    norm_num at this ⊢; linarith
  have h5 : 11.308 * √t * Real.exp (-0.1598 * t) ≤ 11.308 * (t * Real.exp (-(0.1598 * t))) := by
    rw [show -0.1598 * t = -(0.1598 * t) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (by norm_num)
  have : 11.308 * (t * Real.exp (-(0.1598 * t))) ≤ 11.308 * (1e6 * 1e-40) :=
    mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left (h3.trans h4) (by norm_num)))
      (by norm_num)
  linarith

/-- **[B, Thm 7.1.4], `q = 1`**, from [B, Prop 9.4.2] with `T₀ = 200 + 1.2·10⁷π` and Platt's verification:
for `x ≥ 10¹²`, `|δ| ≤ 6·10⁵`, `S_{η₊}(δ/x, x) = η̂₊(-δ) x + E x`, `|E| ≤ 4.78·10⁻¹¹ + 251400/√x`
([B]: `4.772·10⁻¹¹`). -/
theorem thm_7_1_4_one {x : ℝ} (hx : 1e12 ≤ x) (χ : DirichletCharacter ℂ 1) {δ : ℝ}
    (hδ : |δ| ≤ 600000) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x‖ ≤ (4.78e-11 + 251400 / √x) * x := by
  have hχ : χ.IsPrimitive := by
    rw [Subsingleton.elim χ 1]; exact DirichletCharacter.isPrimitive_one_level_one
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  set T0 : ℝ := 200 + 1.2e7 * π with hT0def
  have hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0 := by
    have : 10 * π * |δ| ≤ 1.2e7 * π := by nlinarith [abs_nonneg δ]
    have : max (10 * π * |δ|) 50 ≤ 1.2e7 * π := max_le this (by nlinarith)
    linarith
  have hG : GRHUpTo χ T0 :=
    (platt_odd (q := 1) odd_one (by norm_num) χ hχ).mono (by norm_num; nlinarith)
  have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 hG
  simp only [if_true] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  unfold err942
  simp only [Nat.cast_one, one_mul, Real.log_one, zero_mul, zero_div, add_zero]
  have hx0 : 0 < x := by linarith
  have hsx : (1e6 : ℝ) ≤ √x := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsx0 : 0 < √x := by linarith
  have hT0' : T0 - 200 = 1.2e7 * π := by rw [hT0def]; ring
  rw [hT0']
  -- first line
  have hA1 := sqrt_exp_tiny (t := 1.2e7 * π) (by nlinarith)
  have hE : expδ (1.2e7 * π) δ ≤ 3.1556e-19 := by
    unfold expδ
    split_ifs with hδ0
    · norm_num
    · have hd : 0 < |δ| := abs_pos.2 hδ0
      have h400 : 400 ≤ (1.2e7 * π) ^ 2 / (π * δ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have : (π * δ) ^ 2 = π ^ 2 * |δ| ^ 2 := by rw [mul_pow, sq_abs]
        rw [this]
        have : |δ| ^ 2 ≤ 600000 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
        have : 0 < π ^ 2 := by positivity
        nlinarith
      have : Real.exp (-0.1065 * (1.2e7 * π) ^ 2 / (π * δ) ^ 2) ≤ Real.exp (-42.6) := by
        rw [Real.exp_le_exp, mul_div_assoc]; nlinarith
      refine this.trans ?_
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h := exp_split_ge 42 (u := 0.6) (by norm_num) 8
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      norm_num at h; linarith
  have hL : Real.log (T0 / (2 * π)) ≤ 15.6073 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := exp_split_ge 15 (u := 0.6073) (by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : T0 / (2 * π) ≤ 6000032 := by
      rw [div_le_iff₀ (by positivity), hT0def]; nlinarith
    norm_num at h ⊢; linarith
  have hL0 : 0 ≤ Real.log (T0 / (2 * π)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity), hT0def]; nlinarith)
  have hA : (11.308 * √(1.2e7 * π) * Real.exp (-0.1598 * (1.2e7 * π)) + 16.147 * |δ| * expδ (1.2e7 * π) δ) *
      Real.log (T0 / (2 * π)) ≤ 4.78e-11 := by
    have h16 : 16.147 * |δ| * expδ (1.2e7 * π) δ ≤ 16.147 * 600000 * 3.1556e-19 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hδ (by norm_num)) hE (expδ_nonneg _ _) (by positivity)
    have h0 : 0 ≤ 11.308 * √(1.2e7 * π) * Real.exp (-0.1598 * (1.2e7 * π)) := by positivity
    calc _ ≤ (1e-30 + 16.147 * 600000 * 3.1556e-19) * 15.6073 :=
          mul_le_mul (by linarith) hL hL0 (by norm_num)
      _ ≤ 4.78e-11 := by norm_num
  -- second line
  have hsT : √T0 ≤ 6140 := by
    rw [Real.sqrt_le_left (by norm_num), hT0def]; nlinarith
  have hlT : Real.log T0 ≤ 17.4452 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := exp_split_ge 17 (u := 0.4452) (by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : T0 ≤ 37699400 := by rw [hT0def]; nlinarith
    norm_num at h ⊢; linarith
  have hlT0 : 0 ≤ Real.log T0 := Real.log_nonneg (by rw [hT0def]; nlinarith)
  have hB : (1.634 * √T0 * Real.log T0 + 12.43 * √T0 + 1.321 * 0 + 34.51) / √x ≤ 251379 / √x := by
    apply div_le_div_of_nonneg_right _ hsx0.le
    have : √T0 * Real.log T0 ≤ 6140 * 17.4452 :=
      mul_le_mul hsT hlT hlT0 (by norm_num)
    have : 0 ≤ √T0 := Real.sqrt_nonneg _
    nlinarith
  have hC : (9 + 11 * |δ|) / x ≤ 6.61 / √x := by
    have hxs : x = √x * √x := (Real.mul_self_sqrt hx0.le).symm
    rw [div_le_div_iff₀ hx0 hsx0]
    have : (9 + 11 * |δ|) ≤ 6600009 := by linarith
    have : (9 + 11 * |δ|) * √x ≤ 6600009 * √x := mul_le_mul_of_nonneg_right this hsx0.le
    nlinarith
  have hfin : 251379 / √x + 6.61 / √x ≤ 251400 / √x := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hsx0.le
  linarith


/-- `√t e^{-ct}` is decreasing for `t ≥ 1/(2c)`. -/
theorem sqrt_mul_exp_anti {c t₀ t : ℝ} (hc : 0 < c) (ht₀ : 1 ≤ 2 * c * t₀) (ht : t₀ ≤ t) :
    √t * Real.exp (-(c * t)) ≤ √t₀ * Real.exp (-(c * t₀)) := by
  have ht₀0 : 0 < t₀ := by
    by_contra h; push_neg at h; nlinarith
  have h := mul_exp_anti (c := 2 * c) (by positivity) ht₀ ht
  have hsq : ∀ s, 0 ≤ s → (√s * Real.exp (-(c * s))) ^ 2 = s * Real.exp (-(2 * c * s)) := by
    intro s hs
    rw [mul_pow, Real.sq_sqrt hs, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h1 := hsq t (by linarith)
  have h2 := hsq t₀ ht₀0.le
  rw [← Real.sqrt_sq (by positivity : 0 ≤ √t * Real.exp (-(c * t))),
    ← Real.sqrt_sq (by positivity : 0 ≤ √t₀ * Real.exp (-(c * t₀))), h1, h2]
  exact Real.sqrt_le_sqrt h

set_option maxHeartbeats 2000000 in
/-- **[B, Thm 7.1.4], general `q`** (from [B, Prop 9.4.2] with `T₀ = 200 + 250r/q`): for `x ≥ 10¹²`,
`q ≤ r ≤ 3·10⁵`, `|δ| ≤ 4r/q`, if GRH holds for `L(s, χ)` up to `200 + 250r/q`, then the error is at most
`1.35·10⁻¹⁴ + 1.62·10⁻¹⁰/q + (499900/√q + 52)/√x` ([B]: `1.3482·10⁻¹⁴ + 1.617·10⁻¹⁰/q + …`). -/
theorem thm_7_1_4_gen {x : ℝ} (hx : 1e12 ≤ x) {q : ℕ} [NeZero q] {r : ℝ} (hr : r ≤ 300000)
    (hqr : (q : ℝ) ≤ r) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hG : GRHUpTo χ (200 + 250 * r / q)) {δ : ℝ} (hδ : |δ| ≤ 4 * r / q) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤
      (1.35e-14 + 1.62e-10 / q + (499900 / √q + 52) / √x) * x := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hr0 : 0 < r := by linarith
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  set T0 : ℝ := 200 + 250 * r / q with hT0def
  have hTp : T0 - 200 = 250 * r / q := by rw [hT0def]; ring
  have hTp250 : 250 ≤ 250 * r / q := by rw [le_div_iff₀ hq0]; nlinarith
  have hdel : 4 * r / q ≤ 1.2e6 * (1 / (q : ℝ)) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hT0 : 200 + max (10 * π * |δ|) 50 ≤ T0 := by
    have h1 : 10 * π * |δ| ≤ 250 * r / q := by
      have : 10 * π * |δ| ≤ 10 * 3.141593 * (4 * r / q) :=
        mul_le_mul (by linarith) hδ (abs_nonneg _) (by positivity)
      refine this.trans ?_
      rw [show (10 * 3.141593 * (4 * r / q) : ℝ) = 125.66372 * (r / q) by ring,
        show (250 * r / q : ℝ) = 250 * (r / q) by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    rw [hT0def]; have := max_le h1 (by linarith : (50 : ℝ) ≤ 250 * r / q); linarith
  have h := prop_9_4_2 (x := x) (by linarith) δ χ hχ hT0 hG
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  unfold err942
  rw [hTp]
  have hx0 : 0 < x := by linarith
  have hsx : (1e6 : ℝ) ≤ √x := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsx0 : 0 < √x := by linarith
  -- `qT₀ ≤ 1.35·10⁸`
  have hqT : (q : ℝ) * T0 ≤ 1.35e8 := by
    rw [hT0def, mul_add, show (q : ℝ) * (250 * r / q) = 250 * r by field_simp]; nlinarith
  have hqT1 : 2 * π ≤ (q : ℝ) * T0 := by
    have : 200 ≤ T0 := by linarith
    nlinarith
  -- first line
  have hA1 : 11.308 * √(250 * r / q) * Real.exp (-0.1598 * (250 * r / q)) ≤ 7.987e-16 := by
    have hm := sqrt_mul_exp_anti (c := 0.1598) (t₀ := 250) (by norm_num) (by norm_num) hTp250
    have he : Real.exp (-(0.1598 * 250)) ≤ 4.4662e-18 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h := exp_split_ge 39 (u := 0.95) (by norm_num) 9
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      norm_num at h; linarith
    have hs : √(250 : ℝ) ≤ 15.8114 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [show -0.1598 * (250 * r / q) = -(0.1598 * (250 * r / q)) by ring, mul_assoc]
    calc 11.308 * (√(250 * r / q) * Real.exp (-(0.1598 * (250 * r / q))))
        ≤ 11.308 * (15.8114 * 4.4662e-18) :=
          mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul hs he (Real.exp_pos _).le (by norm_num)))
            (by norm_num)
      _ ≤ 7.987e-16 := by norm_num
  have hA2 : 16.147 * |δ| * expδ (250 * r / q) δ ≤ 9.5889e-12 * (1 / (q : ℝ)) := by
    have hE : expδ (250 * r / q) δ ≤ 4.9487e-19 := by
      unfold expδ
      split_ifs with hδ0
      · norm_num
      · have hd : 0 < |δ| := abs_pos.2 hδ0
        have h395 : 395.78 ≤ (250 * r / q) ^ 2 / (π * δ) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have e1 : (π * δ) ^ 2 = π ^ 2 * |δ| ^ 2 := by rw [mul_pow, sq_abs]
          rw [e1]
          have h1 : |δ| ^ 2 ≤ (4 * r / q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
          have h2 : π ^ 2 ≤ 3.141593 ^ 2 := pow_le_pow_left₀ (by positivity) hπ2.le 2
          have e2 : (250 * r / q) ^ 2 = 3906.25 * (4 * r / q) ^ 2 := by ring
          rw [e2]
          have h3 : 0 ≤ (4 * r / q) ^ 2 := sq_nonneg _
          have : π ^ 2 * |δ| ^ 2 ≤ 3.141593 ^ 2 * (4 * r / q) ^ 2 :=
            mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
          nlinarith
        have : Real.exp (-0.1065 * (250 * r / q) ^ 2 / (π * δ) ^ 2) ≤ Real.exp (-42.15) := by
          rw [Real.exp_le_exp, mul_div_assoc]; nlinarith
        refine this.trans ?_
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        have h := exp_split_ge 42 (u := 0.15) (by norm_num) 6
        norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
        norm_num at h; linarith
    calc 16.147 * |δ| * expδ (250 * r / q) δ ≤ 16.147 * (1.2e6 * (1 / (q : ℝ))) * 4.9487e-19 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hδ.trans hdel) (by norm_num)) hE (expδ_nonneg _ _)
            (by positivity)
      _ ≤ 9.5889e-12 * (1 / (q : ℝ)) := by
          have : (0 : ℝ) ≤ 1 / q := by positivity
          nlinarith
  have hL : Real.log (q * T0 / (2 * π)) ≤ 16.883 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := exp_split_ge 16 (u := 0.883) (by norm_num) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : (q : ℝ) * T0 / (2 * π) ≤ 21485922 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    norm_num at h ⊢; linarith
  have hL0 : 0 ≤ Real.log (q * T0 / (2 * π)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hA : (11.308 * √(250 * r / q) * Real.exp (-0.1598 * (250 * r / q)) +
      16.147 * |δ| * expδ (250 * r / q) δ) * Real.log (q * T0 / (2 * π)) ≤
      1.35e-14 + 1.62e-10 / q := by
    have h0 : 0 ≤ 11.308 * √(250 * r / q) * Real.exp (-0.1598 * (250 * r / q)) +
        16.147 * |δ| * expδ (250 * r / q) δ := by
      have := expδ_nonneg (250 * r / q) δ; positivity
    calc _ ≤ (7.987e-16 + 9.5889e-12 * (1 / (q : ℝ))) * 16.883 :=
          mul_le_mul (by linarith) hL hL0 (by positivity)
      _ ≤ 1.35e-14 + 1.62e-10 / q := by
          rw [div_eq_mul_one_div (1.62e-10 : ℝ)]
          have : (0 : ℝ) ≤ 1 / q := by positivity
          nlinarith
  -- the `1/√x` terms
  set v : ℝ := 1 / √(q : ℝ) with hv
  set w : ℝ := 1 / (q : ℝ) with hw
  have hsq1 : 1 ≤ √(q : ℝ) := Real.one_le_sqrt.2 hq1'
  have hv0 : 0 < v := by positivity
  have hw0 : 0 < w := by positivity
  have hwv : w ≤ v := by
    rw [hw, hv]
    exact one_div_le_one_div_of_le (by positivity) (by
      calc √(q : ℝ) = √(q : ℝ) * 1 := (mul_one _).symm
        _ ≤ √(q : ℝ) * √(q : ℝ) := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
        _ = q := Real.mul_self_sqrt hq0.le)
  have hsT : √T0 ≤ 11619 * v := by
    rw [hv, ← div_eq_mul_one_div, le_div_iff₀ (by positivity), ← Real.sqrt_mul (by linarith)]
    calc √(T0 * q) ≤ √(11619 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 11619 := Real.sqrt_sq (by norm_num)
  have hlqT : Real.log (q * T0) ≤ 18.721 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := exp_split_ge 18 (u := 0.721) (by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hlqT0 : 0 ≤ Real.log (q * T0) := Real.log_nonneg (by nlinarith)
  have hlq : Real.log q ≤ 12.62 :=
    (Real.log_le_log hq0 (by linarith)).trans log_3e5_le
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1'
  have hB : (1.634 * √T0 * Real.log (q * T0) + 12.43 * √T0 + 1.321 * Real.log q + 34.51) / √x ≤
      (499852 * v + 51.19) / √x := by
    apply div_le_div_of_nonneg_right _ hsx0.le
    have h1 : √T0 * Real.log (q * T0) ≤ 11619 * v * 18.721 :=
      mul_le_mul hsT hlqT hlqT0 (by positivity)
    have : 0 ≤ √T0 := Real.sqrt_nonneg _
    linarith
  have hxs : x = √x * √x := (Real.mul_self_sqrt hx0.le).symm
  have hC : (9 + 11 * |δ|) / x ≤ (0.00001 + 13.2 * w) / √x := by
    rw [div_le_div_iff₀ hx0 hsx0]
    have hd : |δ| ≤ 1.2e6 * w := hδ.trans hdel
    have h1 : 9 + 11 * |δ| ≤ (0.00001 + 13.2 * w) * √x := by
      have : (0.00001 + 13.2 * w) * 1e6 ≤ (0.00001 + 13.2 * w) * √x :=
        mul_le_mul_of_nonneg_left hsx (by positivity)
      linarith
    calc (9 + 11 * |δ|) * √x ≤ (0.00001 + 13.2 * w) * √x * √x :=
          mul_le_mul_of_nonneg_right h1 hsx0.le
      _ = (0.00001 + 13.2 * w) * x := by rw [mul_assoc, ← hxs]
  have hD : Real.log q * (11 + 6 * |δ|) / (x * √x) ≤ (0.0001 * w + 0.000001) / √x := by
    rw [div_le_div_iff₀ (by positivity) hsx0]
    have hd : |δ| ≤ 1.2e6 * w := hδ.trans hdel
    have h1 : Real.log q * (11 + 6 * |δ|) ≤ 12.62 * (11 + 7.2e6 * w) :=
      mul_le_mul hlq (by linarith) (by positivity) (by norm_num)
    have h2 : 12.62 * (11 + 7.2e6 * w) ≤ (0.0001 * w + 0.000001) * x := by
      have : (0.0001 * w + 0.000001) * 1e12 ≤ (0.0001 * w + 0.000001) * x :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      linarith
    calc Real.log q * (11 + 6 * |δ|) * √x ≤ (0.0001 * w + 0.000001) * x * √x :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hsx0.le
      _ = (0.0001 * w + 0.000001) * (x * √x) := by ring
  have hfin : (499852 * v + 51.19) / √x + (0.00001 + 13.2 * w) / √x + (0.0001 * w + 0.000001) / √x ≤
      (499900 / √(q : ℝ) + 52) / √x := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hsx0.le
    rw [show (499900 / √(q : ℝ) : ℝ) = 499900 * v by rw [hv]; ring]
    linarith
  have hw' : (1.62e-10 : ℝ) / q = 1.62e-10 / q := rfl
  linarith


/-- **[B, Thm 7.1.4], odd `q ≤ 150000`** (Platt's verification at `10⁸/q`). -/
theorem thm_7_1_4_odd {x : ℝ} (hx : 1e12 ≤ x) {q : ℕ} [NeZero q] (hodd : Odd q) (hq : q ≤ 150000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 600000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤
      (1.35e-14 + 1.62e-10 / q + (499900 / √q + 52) / √x) * x := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (q : ℝ) ≤ 150000 := by exact_mod_cast hq
  have hG : GRHUpTo χ (200 + 250 * 150000 / q) := by
    refine (platt_odd hodd (by omega) χ hχ).mono ?_
    rw [show (200 + 250 * 150000 / q : ℝ) = (200 * q + 3.75e7) / q by field_simp; norm_num]
    exact div_le_div_of_nonneg_right (by nlinarith) hq0.le
  exact thm_7_1_4_gen hx (r := 150000) (by norm_num) hq' χ hχ hG
    (by rw [show (4 * 150000 / q : ℝ) = 600000 / q by ring]; exact hδ)

/-- **[B, Thm 7.1.4], even `q ≤ 300000`** (Platt's verification at `max(10⁸/q, 200 + 7.5·10⁷/q)`). -/
theorem thm_7_1_4_even {x : ℝ} (hx : 1e12 ≤ x) {q : ℕ} [NeZero q] (heven : Even q) (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 1200000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaPlus (n / x) : ℝ) : ℂ)) (δ / x) -
        (if q = 1 then 𝓕 (fun u => (etaPlus u : ℂ)) (-δ) * x else 0)‖ ≤
      (1.35e-14 + 1.62e-10 / q + (499900 / √q + 52) / √x) * x := by
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hG : GRHUpTo χ (200 + 250 * 300000 / q) := by
    refine (platt_even heven (by omega) χ hχ).mono ?_
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    ring
  exact thm_7_1_4_gen hx (r := 300000) le_rfl hq' χ hχ hG
    (by rw [show (4 * 300000 / q : ℝ) = 1200000 / q by ring]; exact hδ)

end TernaryGoldbach.MajorArcs
