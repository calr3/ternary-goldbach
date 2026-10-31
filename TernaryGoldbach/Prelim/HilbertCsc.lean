import TernaryGoldbach.Prelim.HilbertReal

/-!
# The Montgomery–Vaughan inequalities on the circle (`csc` form)

We periodize the real-line inequalities of `HilbertReal.lean`. For `x ∉ ℤ`,
`(1/P) ∑_{k,l<P} (−1)^{k+l}/(x + k − l) → π csc(πx)`, where `P → ∞` is the number of copies. This
is the Fejér mean of `1/x + ∑_{j≥1} (−1)^j 2x/(x² − j²) = π csc πx`, which follows from the
cotangent series and `csc y = cot(y/2) − cot y`. Applying the real-line inequality to the points
`α_r + k` (`k < P`) with weights `(−1)^k z_r` and letting `P → ∞` gives

* `|∑_{r≠s} z̄_r z_s csc π(α_r − α_s)| ≤ (4.66/π) ∑ |z_r|²/δ_r` (weighted; `4.66/π < 3/2`),
* `|∑_{r≠s} z̄_r z_s csc π(α_r − α_s)| ≤ δ⁻¹ ∑ |z_r|²` (uniform `δ`).
-/

open Finset Complex Filter Topology

namespace TernaryGoldbach.Prelim.Hilbert

/-- `c_j(x) = 2x/(x² − j²)`. -/
noncomputable def cj (x : ℝ) (j : ℕ) : ℝ := 2 * x / (x ^ 2 - (j : ℝ) ^ 2)

theorem one_div_add_one_div_eq_cj {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) (j : ℕ) :
    1 / ((x : ℂ) - j) + 1 / ((x : ℂ) + j) = (cj x j : ℂ) := by
  have h1 : (x : ℂ) - j ≠ 0 := by
    intro h; apply hx (j : ℤ); exact_mod_cast (sub_eq_zero.1 h)
  have h2 : (x : ℂ) + j ≠ 0 := by
    intro h; apply hx (-(j : ℤ)); push_cast; exact_mod_cast (eq_neg_of_add_eq_zero_left h)
  have h3 : (x : ℂ) ^ 2 - (j : ℂ) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]; exact mul_ne_zero h2 h1
  simp only [cj]; push_cast
  field_simp; ring

theorem mem_integerComplement {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  exact hx n (by exact_mod_cast hn.symm)

theorem summable_cj {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : Summable fun n : ℕ => cj x (n + 1) := by
  have h := summable_cotTerm (mem_integerComplement hx)
  have h2 : (fun n : ℕ => cotTerm (x : ℂ) n) = fun n : ℕ => (cj x (n + 1) : ℂ) := by
    funext n
    simp only [cotTerm]
    have := one_div_add_one_div_eq_cj hx (n + 1)
    push_cast at this
    rw [← this]
  rw [h2] at h
  exact (Complex.reCLM.summable h).congr fun n => by simp

/-- `csc y = cot(y/2) − cot y`. -/
theorem inv_sin_eq_cot_sub {y : ℂ} (h1 : Complex.sin (y / 2) ≠ 0) (h2 : Complex.sin y ≠ 0) :
    1 / Complex.sin y = Complex.cot (y / 2) - Complex.cot y := by
  have hy : y = 2 * (y / 2) := by ring
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  have hc : Complex.cos y = 2 * Complex.cos (y / 2) ^ 2 - 1 := by
    conv_lhs => rw [hy]
    rw [Complex.cos_two_mul]
  have hs : Complex.sin y = 2 * Complex.sin (y / 2) * Complex.cos (y / 2) := by
    conv_lhs => rw [hy]
    rw [Complex.sin_two_mul]
  rw [hc]
  rw [hs] at h2 ⊢
  have hcos : Complex.cos (y / 2) ≠ 0 := by
    intro h; apply h2; rw [h, mul_zero]
  field_simp
  ring

/-- **The `csc` series**: `∑_{j≥1} (−1)^j 2x/(x² − j²) = π csc(πx) − 1/x` for `x ∉ ℤ`. -/
theorem hasSum_csc {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    HasSum (fun n : ℕ => ((-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ)))
      (Real.pi / Complex.sin (Real.pi * x) - 1 / x) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    intro h; apply hx 0; exact_mod_cast h
  have hxc := mem_integerComplement hx
  have hx2 : ∀ n : ℤ, x / 2 ≠ n := by
    intro n h; apply hx (2 * n); push_cast; linarith
  have hx2c := mem_integerComplement hx2
  set f : ℕ → ℂ := fun n => (cj x (n + 1) : ℂ) with hf
  have hfs : Summable f := (summable_cj hx).map Complex.ofRealLI.toLinearMap.toAddMonoidHom
    Complex.continuous_ofReal |>.congr fun n => rfl
  -- the full series and the even-index series
  have hfull : ∑' n, f n = Real.pi * Complex.cot (Real.pi * x) - 1 / x := by
    rw [cot_series_rep' hxc]
    refine tsum_congr fun n => ?_
    have := one_div_add_one_div_eq_cj hx (n + 1); push_cast at this; rw [this]
  have hhalf : ∑' n, 2 * f (2 * n + 1) = Real.pi * Complex.cot (Real.pi * (x / 2 : ℝ)) -
      1 / (x / 2 : ℝ) := by
    rw [cot_series_rep' hx2c]
    refine tsum_congr fun n => ?_
    have h1 := one_div_add_one_div_eq_cj hx2 (n + 1)
    have h2 : (cj (x / 2) (n + 1) : ℂ) = 2 * f (2 * n + 1) := by
      simp only [hf, cj]; push_cast; field_simp; ring
    push_cast at h1 ⊢; rw [h1, h2]
  have hev : Summable fun k => f (2 * k) := hfs.comp_injective (mul_right_injective₀ two_ne_zero)
  have hod : Summable fun k => f (2 * k + 1) :=
    hfs.comp_injective fun a b h => by simpa using h
  have hsplit := tsum_even_add_odd hev hod
  -- the alternating series
  set g : ℕ → ℂ := fun n => (-1 : ℂ) ^ (n + 1) * f n with hg
  have hgev : (fun k => g (2 * k)) = fun k => -f (2 * k) := by
    funext k; simp only [hg, pow_succ, pow_mul]; simp
  have hgod : (fun k => g (2 * k + 1)) = fun k => f (2 * k + 1) := by
    funext k; simp only [hg, pow_succ, pow_mul]; simp
  have hgev' : Summable fun k => g (2 * k) := by rw [hgev]; exact hev.neg
  have hgod' : Summable fun k => g (2 * k + 1) := by rw [hgod]; exact hod
  have hgs : Summable g := hgev'.even_add_odd hgod'
  have hgsum := tsum_even_add_odd hgev' hgod'
  rw [hgev, hgod, tsum_neg] at hgsum
  refine hgs.hasSum_iff.2 ?_
  rw [← hgsum]
  -- `csc = cot(·/2) − cot`
  have hsin1 : Complex.sin (Real.pi * x / 2) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]; intro k hk
    apply hx2 k
    have : ((Real.pi * x / 2 : ℝ) : ℂ) = (k : ℂ) * Real.pi := by push_cast; rw [← hk]
    have h' : Real.pi * x / 2 = k * Real.pi := by exact_mod_cast this
    field_simp at h'; linarith [Real.pi_pos]
  have hsin2 : Complex.sin (Real.pi * x) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]; intro k hk
    apply hx k
    have : ((Real.pi * x : ℝ) : ℂ) = (k : ℂ) * Real.pi := by push_cast; rw [← hk]
    have h' : Real.pi * x = k * Real.pi := by exact_mod_cast this
    have := Real.pi_pos
    nlinarith
  have hcsc := inv_sin_eq_cot_sub (y := Real.pi * x) (by simpa using hsin1) hsin2
  have h2tsum : ∑' n, f (2 * n + 1) = (∑' n, 2 * f (2 * n + 1)) / 2 := by
    rw [tsum_mul_left]; ring
  have hcast : ((Real.pi : ℂ) * ((x / 2 : ℝ) : ℂ)) = Real.pi * x / 2 := by push_cast; ring
  have hA : ∑' n, f (2 * n) = (Real.pi * Complex.cot (Real.pi * x) - 1 / x) -
      (Real.pi * Complex.cot (Real.pi * x / 2) - 1 / (x / 2 : ℝ)) / 2 := by
    rw [← hfull, ← hsplit, h2tsum, hhalf, hcast]; ring
  rw [h2tsum, hhalf, hcast, hA]
  have hdiv : Real.pi / Complex.sin (Real.pi * x) = Real.pi * (1 / Complex.sin (Real.pi * x)) := by
    ring
  rw [hdiv, hcsc]
  push_cast
  field_simp
  ring

/-! ### The Fejér kernel -/

/-- `∑_{k,l<P} φ(k − l) = P φ(0) + ∑_{n<P} (P − n − 1)(φ(n+1) + φ(−n−1))`. -/
theorem pair_count (φ : ℤ → ℂ) (P : ℕ) :
    ∑ k ∈ range P, ∑ l ∈ range P, φ ((k : ℤ) - l) =
      P * φ 0 + ∑ n ∈ range P, ((P : ℂ) - (n + 1)) * (φ (n + 1) + φ (-(n + 1))) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have h1 : ∑ l ∈ range (P + 1), φ ((P : ℤ) - l) = φ 0 + ∑ n ∈ range P, φ (n + 1) := by
      rw [sum_range_succ, sub_self, add_comm]
      congr 1
      rw [← sum_range_reflect (fun n : ℕ => φ ((n : ℤ) + 1)) P]
      refine sum_congr rfl fun l hl => ?_
      have := mem_range.1 hl
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have h2 : ∑ k ∈ range P, φ ((k : ℤ) - P) = ∑ n ∈ range P, φ (-(n + 1)) := by
      rw [← sum_range_reflect (fun n : ℕ => φ (-((n : ℤ) + 1))) P]
      refine sum_congr rfl fun l hl => ?_
      have := mem_range.1 hl
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hsplit : ∑ k ∈ range (P + 1), ∑ l ∈ range (P + 1), φ ((k : ℤ) - l) =
        ∑ k ∈ range P, ∑ l ∈ range P, φ ((k : ℤ) - l) + ∑ k ∈ range P, φ ((k : ℤ) - P) +
          ∑ l ∈ range (P + 1), φ ((P : ℤ) - l) := by
      rw [sum_range_succ (fun k => ∑ l ∈ range (P + 1), φ ((k : ℤ) - l)) P]
      have : ∑ k ∈ range P, ∑ l ∈ range (P + 1), φ ((k : ℤ) - l) =
          ∑ k ∈ range P, (∑ l ∈ range P, φ ((k : ℤ) - l) + φ ((k : ℤ) - P)) :=
        sum_congr rfl fun k _ => sum_range_succ (fun l => φ ((k : ℤ) - l)) P
      rw [this, sum_add_distrib]
    rw [hsplit, ih, h1, h2]
    have : ∑ n ∈ range (P + 1), (((P + 1 : ℕ) : ℂ) - (n + 1)) * (φ (n + 1) + φ (-(n + 1))) =
        ∑ n ∈ range P, ((P : ℂ) - (n + 1)) * (φ (n + 1) + φ (-(n + 1))) +
          (∑ n ∈ range P, φ (n + 1) + ∑ n ∈ range P, φ (-(n + 1))) := by
      rw [sum_range_succ, ← sum_add_distrib, ← sum_add_distrib]
      push_cast
      rw [show (P : ℂ) + 1 - (P + 1) = 0 by ring, zero_mul, add_zero]
      refine sum_congr rfl fun n _ => by ring
    rw [this]; push_cast; ring

/-- The averaged kernel `(1/P) ∑_{k,l<P} (−1)^{k+l}/(x + k − l)`. -/
noncomputable def fejer (P : ℕ) (x : ℝ) : ℂ :=
  (1 / (P : ℂ)) * ∑ k ∈ range P, ∑ l ∈ range P, (-1 : ℂ) ^ (k + l) / ((x : ℂ) + k - l)

theorem fejer_eq {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) {P : ℕ} (hP : 1 ≤ P) :
    fejer P x = 1 / x + ∑ n ∈ range P, (1 - (n + 1 : ℂ) / P) * ((-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ)) := by
  set φ : ℤ → ℂ := fun j => (-1 : ℂ) ^ j.natAbs / ((x : ℂ) + j) with hφ
  have hpair := pair_count φ P
  have hlhs : ∑ k ∈ range P, ∑ l ∈ range P, (-1 : ℂ) ^ (k + l) / ((x : ℂ) + k - l) =
      ∑ k ∈ range P, ∑ l ∈ range P, φ ((k : ℤ) - l) := by
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    simp only [hφ]
    have hpow : (-1 : ℂ) ^ (k + l) = (-1 : ℂ) ^ ((k : ℤ) - l).natAbs := by
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := ((k : ℤ) - l).natAbs)]
      congr 1
      omega
    rw [hpow]; push_cast; ring_nf
  have hφpair : ∀ n : ℕ, φ (n + 1) + φ (-(n + 1)) = (-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ) := by
    intro n
    simp only [hφ]
    have h1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    have h2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [h1, h2, ← one_div_add_one_div_eq_cj hx (n + 1)]
    push_cast; ring
  rw [fejer, hlhs, hpair]
  simp only [hφpair]
  have hφ0 : φ 0 = 1 / x := by simp [hφ]
  rw [hφ0]
  have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast (by omega : P ≠ 0)
  rw [mul_add, mul_sum]
  congr 1
  · field_simp
  · refine sum_congr rfl fun n _ => ?_
    field_simp

/-- **`(1/P)∑_{k,l<P} (−1)^{k+l}/(x + k − l) → π csc(πx)`** for `x ∉ ℤ`. -/
theorem tendsto_fejer {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (fun P : ℕ => fejer P x) atTop (𝓝 (Real.pi / Complex.sin (Real.pi * x))) := by
  set F : ℕ → ℕ → ℂ := fun P n =>
    if n < P then (1 - (n + 1 : ℂ) / P) * ((-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ)) else 0 with hF
  have htsum : ∀ P, 1 ≤ P → fejer P x = 1 / x + ∑' n, F P n := by
    intro P hP
    rw [fejer_eq hx hP, tsum_eq_sum (s := range P) fun n hn => by
      simp only [hF, if_neg (fun h => hn (mem_range.2 h))]]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    simp only [hF, if_pos (mem_range.1 hn)]
  have hlim : Tendsto (fun P => ∑' n, F P n) atTop
      (𝓝 (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => |cj x (n + 1)|)
      (summable_abs_iff.2 (summable_cj hx)) (fun n => ?_) ?_
    · -- pointwise
      have h1 : Tendsto (fun P : ℕ => (1 - (n + 1 : ℂ) / P) * ((-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ)))
          atTop (𝓝 ((1 - 0) * ((-1 : ℂ) ^ (n + 1) * (cj x (n + 1) : ℂ)))) := by
        refine Tendsto.mul_const _ (Tendsto.const_sub _ ?_)
        have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa [div_eq_mul_one_div ((n : ℂ) + 1)] using this.const_mul ((n : ℂ) + 1)
      rw [sub_zero, one_mul] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop n] with P hP
      simp only [hF, if_pos hP]
    · filter_upwards [eventually_ge_atTop 1] with P hP n
      simp only [hF]
      split_ifs with h
      · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
        have : (1 - ((n : ℂ) + 1) / P) = ((1 - ((n : ℝ) + 1) / P : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor
        · have : ((n : ℝ) + 1) / P ≤ 1 := by
            rw [div_le_one hP0]; exact_mod_cast h
          have : 0 ≤ ((n : ℝ) + 1) / P := by positivity
          linarith
        · have : 0 ≤ ((n : ℝ) + 1) / P := by positivity
          linarith
      · simp
  have hsum := (hasSum_csc hx).tsum_eq
  rw [hsum] at hlim
  have := hlim.const_add (1 / (x : ℂ))
  rw [add_sub_cancel] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with P hP
  rw [htsum P hP]

/-! ### Periodization -/

section Periodize

variable {ι : Type*} [DecidableEq ι]

/-- The real-line form over the points `α_r + k` (`r ∈ s`, `k < P`) with weights `(−1)^k z_r`. -/
noncomputable def offP (s : Finset ι) (α : ι → ℝ) (z : ι → ℂ) (P : ℕ) : ℂ :=
  ∑ p ∈ s ×ˢ range P, ∑ q ∈ s ×ˢ range P,
    if p = q then 0 else starRingEnd ℂ ((-1 : ℂ) ^ p.2 * z p.1) * ((-1 : ℂ) ^ q.2 * z q.1) /
      ((α p.1 + p.2 - (α q.1 + q.2) : ℝ) : ℂ)

/-- The circle form `∑_{r ≠ r'} z̄_r z_{r'} π csc π(α_r − α_{r'})`. -/
noncomputable def cscForm (s : Finset ι) (α : ι → ℝ) (z : ι → ℂ) : ℂ :=
  ∑ r ∈ s, ∑ r' ∈ s, if r = r' then 0 else
    starRingEnd ℂ (z r) * z r' * (Real.pi / Complex.sin (Real.pi * (α r - α r' : ℝ)))

theorem offP_eq (s : Finset ι) (α : ι → ℝ) (z : ι → ℂ) (P : ℕ) :
    offP s α z P = P * ∑ r ∈ s, ∑ r' ∈ s, if r = r' then 0 else
      starRingEnd ℂ (z r) * z r' * fejer P (α r - α r') := by
  simp only [offP, sum_product, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun r' _ => ?_
  by_cases hrr : r = r'
  · subst hrr
    rw [if_pos rfl, mul_zero]
    -- antisymmetry in `(k, l)`
    set g : ℕ → ℕ → ℂ := fun k l => if (r, k) = (r, l) then 0 else
      starRingEnd ℂ ((-1 : ℂ) ^ k * z r) * ((-1 : ℂ) ^ l * z r) /
        ((α r + k - (α r + l) : ℝ) : ℂ) with hg
    have hanti : ∀ k l, g l k = -g k l := by
      intro k l
      simp only [hg, Prod.mk.injEq, true_and]
      by_cases hkl : k = l
      · subst hkl; simp
      · rw [if_neg hkl, if_neg (Ne.symm hkl)]
        have : ((α r + l - (α r + k) : ℝ) : ℂ) = -((α r + k - (α r + l) : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, div_neg]; congr 1
        simp only [map_mul, map_pow, map_neg, map_one]; ring
    have hS : ∑ k ∈ range P, ∑ l ∈ range P, g k l = -∑ k ∈ range P, ∑ l ∈ range P, g k l := by
      conv_lhs => rw [sum_comm]
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun l _ => by rw [← sum_neg_distrib]; exact sum_congr rfl fun k _ => hanti l k
    have h0 : ∑ k ∈ range P, ∑ l ∈ range P, g k l = 0 := by
      have := hS; linear_combination (1 / 2 : ℂ) * this
    simpa [hg] using h0
  · rw [if_neg hrr, fejer]
    have hne : ∀ k l : ℕ, (r, k) ≠ (r', l) := fun k l h => hrr (Prod.mk.inj h).1
    rw [sum_comm]
    simp only [if_neg (hne _ _)]
    by_cases hP : P = 0
    · subst hP; simp
    have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast hP
    have key : ∀ X Y : ℂ, (P : ℂ) * (X * (1 / (P : ℂ) * Y)) = X * Y := by
      intro X Y; field_simp
    rw [key, mul_sum, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one]
    push_cast
    rw [show (-1 : ℂ) ^ (k + l) = (-1) ^ k * (-1) ^ l by rw [pow_add]]
    ring_nf

/-- From bounds `|offP P| ≤ P·B` for all `P ≥ 1` to `|cscForm| ≤ B`. -/
theorem cscForm_le (s : Finset ι) (α : ι → ℝ) (z : ι → ℂ)
    (hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n) {B : ℝ}
    (hP : ∀ P : ℕ, 1 ≤ P → ‖offP s α z P‖ ≤ P * B) : ‖cscForm s α z‖ ≤ B := by
  have hlim : Tendsto (fun P : ℕ => ∑ r ∈ s, ∑ r' ∈ s, if r = r' then (0 : ℂ) else
      starRingEnd ℂ (z r) * z r' * fejer P (α r - α r')) atTop (𝓝 (cscForm s α z)) := by
    refine tendsto_finsetSum _ fun r hr => tendsto_finsetSum _ fun r' hr' => ?_
    by_cases h : r = r'
    · simp only [if_pos h]; exact tendsto_const_nhds
    · simp only [if_neg h]
      exact (tendsto_fejer (hdist r hr r' hr' h)).const_mul _
  refine le_of_tendsto (hlim.norm) ?_
  filter_upwards [eventually_ge_atTop 1] with P hP1
  have h := hP P hP1
  rw [offP_eq, norm_mul, Complex.norm_natCast] at h
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP1
  exact le_of_mul_le_mul_left h hPpos

/-- `offP` is the real-line form `hform` over the image set. -/
theorem offP_eq_hform (s : Finset ι) (α : ι → ℝ) (z : ι → ℂ)
    (hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n) (P : ℕ) :
    let pt : ι × ℕ → ℝ := fun p => α p.1 + p.2
    let w : ℝ → ℂ := fun y => ∑ p ∈ s ×ˢ range P, if pt p = y then (-1 : ℂ) ^ p.2 * z p.1 else 0
    (Set.InjOn pt ↑(s ×ˢ range P)) ∧ (∀ p ∈ s ×ˢ range P, w (pt p) = (-1 : ℂ) ^ p.2 * z p.1) ∧
      offP s α z P = hform ((s ×ˢ range P).image pt) w := by
  intro pt w
  have hinj : Set.InjOn pt ↑(s ×ˢ range P) := by
    rintro ⟨r, k⟩ hp ⟨r', l⟩ hq h
    simp only [pt] at h
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hq
    by_cases hrr : r = r'
    · subst hrr
      have : (k : ℝ) = l := by linarith
      simp only [Prod.mk.injEq, true_and]; exact_mod_cast this
    · exfalso
      exact hdist r hp.1 r' hq.1 hrr ((l : ℤ) - k) (by push_cast; linarith)
  have hw : ∀ p ∈ s ×ˢ range P, w (pt p) = (-1 : ℂ) ^ p.2 * z p.1 := by
    intro p hp
    simp only [w]
    rw [sum_eq_single p]
    · simp
    · intro q hq hqp; rw [if_neg]; exact fun h => hqp (hinj hq hp h)
    · intro h; exact absurd hp h
  refine ⟨hinj, hw, ?_⟩
  simp only [hform, offP]
  rw [sum_image hinj]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_image hinj]
  refine sum_congr rfl fun q hq => ?_
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq, if_neg (fun h => hpq (hinj hp hq h)), hw p hp, hw q hq]

end Periodize

section Circle

variable {ι : Type*} [DecidableEq ι]

theorem dist_of_sep {x δ : ℝ} (hδ : 0 < δ) (h : δ ≤ |x - round x|) (n : ℤ) : x ≠ n := by
  rintro rfl; simp at h; linarith

omit [DecidableEq ι] in
/-- The data for the real-line application: `δ'(α_r + k) = δ_r`. -/
theorem image_data (s : Finset ι) (α δ : ι → ℝ) (P : ℕ)
    (hinj : Set.InjOn (fun p : ι × ℕ => α p.1 + p.2) ↑(s ×ˢ range P)) :
    ∀ p ∈ s ×ˢ range P,
      (∑ q ∈ s ×ˢ range P, if α q.1 + q.2 = α p.1 + p.2 then δ q.1 else 0) = δ p.1 := by
  intro p hp
  rw [sum_eq_single p]
  · simp
  · intro q hq hqp; rw [if_neg]; exact fun h => hqp (hinj hq hp h)
  · intro h; exact absurd hp h

/-- **Weighted Hilbert inequality on the circle**:
`|∑_{r≠r'} z̄_r z_{r'} π csc π(α_r − α_{r'})| ≤ 4.66 ∑ |z_r|²/δ_r`. -/
theorem csc_weighted (s : Finset ι) (α δ : ι → ℝ) (hδ : ∀ r ∈ s, 0 < δ r)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ r ≤ |(α r - α r') - round (α r - α r')|) (z : ι → ℂ) :
    ‖cscForm s α z‖ ≤ 4.66 * ∑ r ∈ s, ‖z r‖ ^ 2 / δ r := by
  have hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n :=
    fun r hr r' hr' h => dist_of_sep (hδ r hr) (hsep r hr r' hr' h)
  by_cases htwo : ∃ a ∈ s, ∃ b ∈ s, a ≠ b
  swap
  · push Not at htwo
    have : cscForm s α z = 0 := by
      refine sum_eq_zero fun r hr => sum_eq_zero fun r' hr' => ?_
      rw [if_pos (htwo r hr r' hr')]
    rw [this, norm_zero]
    exact mul_nonneg (by norm_num) (sum_nonneg fun r hr => div_nonneg (sq_nonneg _) (hδ r hr).le)
  obtain ⟨a, ha, b, hb, hab⟩ := htwo
  have hhalf : ∀ r ∈ s, δ r ≤ 1 := by
    intro r hr
    by_cases hra : r = a
    · subst hra
      have := hsep r hr b hb hab
      linarith [abs_sub_round (α r - α b)]
    · have := hsep r hr a ha hra
      linarith [abs_sub_round (α r - α a)]
  refine cscForm_le s α z hdist fun P hP => ?_
  obtain ⟨hinj, hw, heq⟩ := offP_eq_hform s α z hdist P
  rw [heq]
  set pt : ι × ℕ → ℝ := fun p => α p.1 + p.2
  set δ' : ℝ → ℝ := fun y => ∑ p ∈ s ×ˢ range P, if pt p = y then δ p.1 else 0 with hδ'
  have hδ'pt : ∀ p ∈ s ×ˢ range P, δ' (pt p) = δ p.1 := image_data s α δ P hinj
  have hpos : ∀ y ∈ (s ×ˢ range P).image pt, 0 < δ' y := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
    rw [hδ'pt p hp]; exact hδ _ (mem_product.1 hp).1
  have hsep' : ∀ y ∈ (s ×ˢ range P).image pt, ∀ y' ∈ (s ×ˢ range P).image pt, y' ≠ y →
      δ' y ≤ |y - y'| := by
    intro y hy y' hy' hne
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hy'
    rw [hδ'pt p hp]
    have hp1 := (mem_product.1 hp).1
    have hq1 := (mem_product.1 hq).1
    simp only [pt]
    by_cases hpq : p.1 = q.1
    · have hk : p.2 ≠ q.2 := by
        intro h; apply hne; simp only [pt, hpq, h]
      rw [hpq, show α q.1 + (p.2 : ℝ) - (α q.1 + q.2) = (p.2 : ℝ) - q.2 by ring]
      have : (1 : ℝ) ≤ |(p.2 : ℝ) - q.2| := by
        rcases Nat.lt_or_gt_of_ne hk with h | h
        · have : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast h
          rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
        · have : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast h
          exact le_trans (by linarith) (le_abs_self _)
      linarith [hhalf q.1 hq1]
    · have h1 := hsep p.1 hp1 q.1 hq1 hpq
      have h2 := round_le (α p.1 - α q.1) ((q.2 : ℤ) - p.2)
      refine h1.trans (h2.trans (le_of_eq ?_))
      congr 1; push_cast; ring
  have hH := hilbert_weighted ((s ×ˢ range P).image pt) δ' hpos hsep'
    (fun y => ∑ p ∈ s ×ˢ range P, if pt p = y then (-1 : ℂ) ^ p.2 * z p.1 else 0)
  refine hH.trans (le_of_eq ?_)
  rw [sum_image hinj, mul_comm (P : ℝ), mul_assoc]
  congr 1
  rw [sum_product, sum_mul]
  refine sum_congr rfl fun r hr => ?_
  have : ∀ k ∈ range P, ‖∑ p ∈ s ×ˢ range P, if pt p = pt (r, k) then (-1 : ℂ) ^ p.2 * z p.1 else 0‖ ^ 2 /
      δ' (pt (r, k)) = ‖z r‖ ^ 2 / δ r := by
    intro k hk
    have hp : (r, k) ∈ s ×ˢ range P := mem_product.2 ⟨hr, hk⟩
    rw [show (∑ p ∈ s ×ˢ range P, if pt p = pt (r, k) then (-1 : ℂ) ^ p.2 * z p.1 else 0) =
      (-1 : ℂ) ^ k * z r from hw (r, k) hp, hδ'pt (r, k) hp]
    simp [norm_mul, norm_pow]
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_comm]

/-- **The Hilbert inequality on the circle for `δ`-spaced points**:
`|∑_{r≠r'} z̄_r z_{r'} π csc π(α_r − α_{r'})| ≤ (π/δ) ∑ |z_r|²`. -/
theorem csc_uniform (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(α r - α r') - round (α r - α r')|) (z : ι → ℂ) :
    ‖cscForm s α z‖ ≤ Real.pi / δ * ∑ r ∈ s, ‖z r‖ ^ 2 := by
  have hdist : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ n : ℤ, α r - α r' ≠ n :=
    fun r hr r' hr' h => dist_of_sep hδ (hsep r hr r' hr' h)
  refine cscForm_le s α z hdist fun P hP => ?_
  obtain ⟨hinj, hw, heq⟩ := offP_eq_hform s α z hdist P
  rw [heq]
  set pt : ι × ℕ → ℝ := fun p => α p.1 + p.2
  have hsep' : ∀ y ∈ (s ×ˢ range P).image pt, ∀ y' ∈ (s ×ˢ range P).image pt, y' ≠ y →
      δ ≤ |y - y'| := by
    intro y hy y' hy' hne
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hy'
    have hp1 := (mem_product.1 hp).1
    have hq1 := (mem_product.1 hq).1
    simp only [pt]
    by_cases hpq : p.1 = q.1
    · have hk : p.2 ≠ q.2 := by
        intro h; apply hne; simp only [pt, hpq, h]
      rw [hpq, show α q.1 + (p.2 : ℝ) - (α q.1 + q.2) = (p.2 : ℝ) - q.2 by ring]
      have : (1 : ℝ) ≤ |(p.2 : ℝ) - q.2| := by
        rcases Nat.lt_or_gt_of_ne hk with h | h
        · have : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast h
          rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
        · have : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast h
          exact le_trans (by linarith) (le_abs_self _)
      linarith
    · have h1 := hsep p.1 hp1 q.1 hq1 hpq
      have h2 := round_le (α p.1 - α q.1) ((q.2 : ℤ) - p.2)
      refine h1.trans (h2.trans (le_of_eq ?_))
      congr 1; push_cast; ring
  have hH := hilbert_uniform ((s ×ˢ range P).image pt) hδ hsep'
    (fun y => ∑ p ∈ s ×ˢ range P, if pt p = y then (-1 : ℂ) ^ p.2 * z p.1 else 0)
  refine hH.trans (le_of_eq ?_)
  rw [sum_image hinj, mul_comm (P : ℝ), mul_assoc]
  congr 1
  rw [sum_product, sum_mul]
  refine sum_congr rfl fun r hr => ?_
  have : ∀ k ∈ range P, ‖∑ p ∈ s ×ˢ range P, if pt p = pt (r, k) then (-1 : ℂ) ^ p.2 * z p.1 else 0‖ ^ 2
      = ‖z r‖ ^ 2 := by
    intro k hk
    have hp : (r, k) ∈ s ×ˢ range P := mem_product.2 ⟨hr, hk⟩
    rw [show (∑ p ∈ s ×ˢ range P, if pt p = pt (r, k) then (-1 : ℂ) ^ p.2 * z p.1 else 0) =
      (-1 : ℂ) ^ k * z r from hw (r, k) hp]
    simp [norm_mul, norm_pow]
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_comm]

end Circle

end TernaryGoldbach.Prelim.Hilbert
