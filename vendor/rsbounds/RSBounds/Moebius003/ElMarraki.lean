/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Schoenfeld
import RSBounds.Moebius003.MofN

/-!
# Lemma 3 of the note: El Marraki's inequality

For natural `x ≥ 1`,
`|m(x)| ≤ |M(x)|/x + (1/x) ∑_{1 ≤ t < x} |M(t)| log(1 + 1/t) + (log x)/x`.

The note integrates `∑_{n ≤ y} M(y/n) = 1` against `dy/y`. Here the same identity is proved with
finite sums only: `log x = ∑_{jk ≤ x} μ(k) log(x/(jk))`, followed by Abel summation in `k` and an
elementary estimate of the resulting weights (each weight is `∫_i^{i+1} {x/t} dt/t`, but we never
write the integral).
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `φ(u, i) = log(clamp(u, i, i+1)) − log i`. -/
noncomputable def φ (u : ℝ) (i : ℕ) : ℝ := Real.log (max (i : ℝ) (min u (i + 1))) - Real.log i

/-- Abel summation of `∑_{k ≤ u} μ(k) log(u/k)`, with `u = x/j`. -/
theorem sum_moebius_log_div (x j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Icc 1 (x / j), (μ k : ℝ) * Real.log (((x : ℝ) / j) / k) =
      ∑ i ∈ Icc 1 (x / j), M i * φ ((x : ℝ) / j) i := by
  set u : ℝ := (x : ℝ) / j with hu
  set K := x / j with hK
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hKu : (K : ℝ) ≤ u := by
    rw [hu, le_div_iff₀ hj']; exact_mod_cast Nat.div_mul_le_self x j
  have huK : u < K + 1 := by
    rw [hu, div_lt_iff₀ hj']
    have := Nat.lt_div_mul_add (a := x) hj
    have h2 : x < (K + 1) * j := by rw [hK]; nlinarith [Nat.div_add_mod x j, Nat.mod_lt x hj]
    exact_mod_cast h2
  have key := sum_mul_sub_eq (fun k => (μ k : ℝ)) (fun i => Real.log (min (i : ℝ) u)) K
  have hl : ∀ k ∈ Icc 1 K, (μ k : ℝ) * Real.log (u / k) =
      (μ k : ℝ) * (Real.log (min ((K + 1 : ℕ) : ℝ) u) - Real.log (min (k : ℝ) u)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
    have hk' : (k : ℝ) ≤ u := (by exact_mod_cast hk2 : (k : ℝ) ≤ K).trans hKu
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [min_eq_left hk', min_eq_right (by push_cast; linarith),
      Real.log_div (by linarith) hkpos.ne']
  have hr : ∀ i ∈ Icc 1 K, M i * φ u i =
      (∑ k ∈ Icc 1 i, (μ k : ℝ)) * (Real.log (min ((i + 1 : ℕ) : ℝ) u) - Real.log (min (i : ℝ) u)) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    have hi' : (i : ℝ) ≤ u := (by exact_mod_cast hi2 : (i : ℝ) ≤ K).trans hKu
    rw [φ, M, min_eq_left hi', max_eq_right (le_min hi' (by linarith))]
    push_cast
    rw [min_comm]
  rw [sum_congr rfl hl, sum_congr rfl hr, key]

/-- `∑_{j ≤ x} ∑_{k ≤ x/j} μ(k) log((x/j)/k) = log x` for `x ≥ 1`. -/
theorem sum_sum_moebius_log (x : ℕ) (hx : 1 ≤ x) :
    ∑ j ∈ Icc 1 x, ∑ k ∈ Icc 1 (x / j), (μ k : ℝ) * Real.log (((x : ℝ) / j) / k) = Real.log x := by
  have hexp : ∀ j ∈ Icc 1 x, ∑ k ∈ Icc 1 (x / j), (μ k : ℝ) * Real.log (((x : ℝ) / j) / k) =
      Real.log x * M (x / j) - Real.log j * M (x / j) - N (x / j) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.1 hj).1
    rw [M, N, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
    rw [Real.log_div (by positivity) hkpos.ne', Real.log_div hxpos.ne' hjpos.ne']
    ring
  rw [sum_congr rfl hexp, sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_M_div x hx, mul_one]
  -- `∑ log j M(x/j) = ψ(x) = −∑ N(x/j)`
  have h1 := sum_Ioc_mul_eq_sum_sum (log : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ) x
  have h2 := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℝ)
    (pmul (μ : ArithmeticFunction ℝ) log) x
  have hz : (ζ : ArithmeticFunction ℝ) * pmul (μ : ArithmeticFunction ℝ) log = -Λ := by
    rw [mul_comm]; ext k
    rw [coe_mul_zeta_apply]
    simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply]
    exact sum_moebius_mul_log_eq
  rw [log_mul_moebius_eq_vonMangoldt] at h1
  rw [hz] at h2
  have e1 : ∑ j ∈ Icc 1 x, Real.log j * M (x / j) = ∑ n ∈ Ioc 0 x, Λ n := by
    rw [h1, Icc_one_eq_Ioc_zero]
    refine sum_congr rfl fun j _ => ?_
    simp [M, Icc_one_eq_Ioc_zero, log_apply, intCoe_apply]
  have e2 : ∑ j ∈ Icc 1 x, N (x / j) = -∑ n ∈ Ioc 0 x, Λ n := by
    have : ∑ n ∈ Ioc 0 x, (-Λ : ArithmeticFunction ℝ) n = -∑ n ∈ Ioc 0 x, Λ n := by
      simp [ArithmeticFunction.neg_apply]
    rw [← this, h2, Icc_one_eq_Ioc_zero]
    refine sum_congr rfl fun j hj => ?_
    have hj1 : 0 < j := (mem_Ioc.1 hj).1
    rw [natCoe_apply, zeta_apply, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    simp [N, Icc_one_eq_Ioc_zero, pmul_apply, intCoe_apply, log_apply]
  rw [e1, e2]; ring

theorem φ_nonneg (u : ℝ) (i : ℕ) (hi : 1 ≤ i) : 0 ≤ φ u i := by
  rw [φ, sub_nonneg]
  have : (0 : ℝ) < i := by exact_mod_cast hi
  exact Real.log_le_log this (le_max_left _ _)

theorem φ_eq_zero {u : ℝ} {i : ℕ} (hu : u ≤ i) : φ u i = 0 := by
  rw [φ]
  have : min u ((i : ℝ) + 1) ≤ i := (min_le_left _ _).trans hu
  rw [max_eq_left this, sub_self]

theorem sum_Icc_eq_sum_Ico_add (f : ℕ → ℝ) {x : ℕ} (hx : 1 ≤ x) :
    ∑ i ∈ Icc 1 x, f i = ∑ i ∈ Ico 1 x, f i + f x := by
  rw [← Ico_insert_right hx, sum_insert (by simp), add_comm]

/-- `log x = ∑_{1 ≤ i < x} M(i) w_i(x)` with `w_i(x) = ∑_{j ≤ x} φ(x/j, i)`. -/
theorem log_eq_sum_M_mul_w (x : ℕ) (hx : 1 ≤ x) :
    Real.log x = ∑ i ∈ Ico 1 x, M i * ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i := by
  rw [← sum_sum_moebius_log x hx]
  rw [sum_congr rfl fun j hj => sum_moebius_log_div x j (mem_Icc.1 hj).1]
  -- swap the double sum over `ij ≤ x`
  have hswap : ∑ j ∈ Icc 1 x, ∑ i ∈ Icc 1 (x / j), M i * φ ((x : ℝ) / j) i =
      ∑ i ∈ Icc 1 x, ∑ j ∈ Icc 1 (x / i), M i * φ ((x : ℝ) / j) i := by
    rw [sum_comm' (t' := Icc 1 x) (s' := fun i => Icc 1 (x / i))]
    intro j i
    simp only [mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, hi1, hi2⟩
      have := (Nat.le_div_iff_mul_le (by omega)).1 hi2
      refine ⟨⟨hj1, (Nat.le_div_iff_mul_le (by omega)).2 (by linarith [mul_comm i j])⟩, hi1, ?_⟩
      nlinarith
    · rintro ⟨⟨hj1, hj2⟩, hi1, hi2⟩
      have := (Nat.le_div_iff_mul_le (by omega)).1 hj2
      refine ⟨⟨hj1, ?_⟩, hi1, (Nat.le_div_iff_mul_le (by omega)).2 (by linarith [mul_comm i j])⟩
      nlinarith
  rw [hswap]
  -- extend the inner sum to `j ≤ x` and drop the term `i = x`
  have hext : ∀ i ∈ Icc 1 x, ∑ j ∈ Icc 1 (x / i), M i * φ ((x : ℝ) / j) i =
      M i * ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    rw [← mul_sum]
    congr 1
    have hsub : Icc 1 (x / i) ⊆ Icc 1 x := Icc_subset_Icc le_rfl (Nat.div_le_self x i)
    rw [← sum_subset hsub]
    intro j hj hjn
    simp only [mem_Icc, not_and, not_le] at hj hjn
    have hlt : x / i < j := hjn hj.1
    apply φ_eq_zero
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    rw [div_le_iff₀ hjpos]
    have : x < j * i := by
      have := (Nat.div_lt_iff_lt_mul (by omega)).1 hlt; linarith
    exact_mod_cast (by nlinarith : x ≤ i * j)
  rw [sum_congr rfl hext]
  rw [sum_Icc_eq_sum_Ico_add (fun i => M i * ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i) hx]
  have hlast : ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) x = 0 := by
    refine sum_eq_zero fun j hj => ?_
    obtain ⟨hj1, _⟩ := mem_Icc.1 hj
    apply φ_eq_zero
    have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hx0 : (0 : ℝ) ≤ x := by positivity
    calc (x : ℝ) / j ≤ x / 1 := by gcongr
      _ = x := div_one _
  rw [hlast, mul_zero, add_zero]

/-- `x m(x) = M(x) + ∑_{1 ≤ i < x} M(i) (x/i − x/(i+1))`. -/
theorem mul_msum_eq (x : ℕ) :
    (x : ℝ) * msum x = M x + ∑ i ∈ Ico 1 x, M i * ((x : ℝ) / i - x / (i + 1)) := by
  have key := sum_mul_sub_eq (fun k => (μ k : ℝ)) (fun k => -((x : ℝ) / k)) x
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [msum, M]
  have hl : ∑ k ∈ Icc 1 x, (μ k : ℝ) * (-((x : ℝ) / ((x + 1 : ℕ) : ℝ)) - -((x : ℝ) / k)) =
      x * msum x - ((x : ℝ) / (x + 1)) * M x := by
    rw [msum, M, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [hl, sum_Icc_eq_sum_Ico_add _ hx] at key
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have : ∀ i ∈ Ico 1 x, (∑ k ∈ Icc 1 i, (μ k : ℝ)) * (-((x : ℝ) / ((i + 1 : ℕ) : ℝ)) - -((x : ℝ) / i)) =
      M i * ((x : ℝ) / i - x / (i + 1)) := by
    intro i _; rw [M]; push_cast; ring
  rw [sum_congr rfl this] at key
  rw [show (∑ k ∈ Icc 1 x, (μ k : ℝ)) = M x from rfl] at key
  have h2 : M x * (-((x : ℝ) / ((x + 1 : ℕ) : ℝ)) - -((x : ℝ) / x)) = M x - (x / (x + 1)) * M x := by
    rw [div_self hxpos.ne']; push_cast; ring
  rw [h2] at key
  linarith

/-- The core inequality: for `p = clamp(x/(l+1), i, i+1) ≤ q = clamp(x/l, i, i+1)`,
`0 ≤ x/p − x/q − l log(q/p) ≤ log(q/p)`. -/
theorem term_bounds {x : ℝ} {i : ℕ} {l : ℕ} (hx : 0 < x) (hi : 1 ≤ i) (hl : 1 ≤ l) :
    0 ≤ x / max (i : ℝ) (min (x / (l + 1)) (i + 1)) - x / max (i : ℝ) (min (x / l) (i + 1))
        - l * (Real.log (max (i : ℝ) (min (x / l) (i + 1))) -
          Real.log (max (i : ℝ) (min (x / (l + 1)) (i + 1)))) ∧
    x / max (i : ℝ) (min (x / (l + 1)) (i + 1)) - x / max (i : ℝ) (min (x / l) (i + 1))
        - l * (Real.log (max (i : ℝ) (min (x / l) (i + 1))) -
          Real.log (max (i : ℝ) (min (x / (l + 1)) (i + 1)))) ≤
      Real.log (max (i : ℝ) (min (x / l) (i + 1))) -
        Real.log (max (i : ℝ) (min (x / (l + 1)) (i + 1))) := by
  set q := max (i : ℝ) (min (x / l) (i + 1)) with hq
  set p := max (i : ℝ) (min (x / (l + 1)) (i + 1)) with hp
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hp1 : (i : ℝ) ≤ p := le_max_left _ _
  have hq1 : (i : ℝ) ≤ q := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hdiv : x / (l + 1) ≤ x / l := div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
  have hpq : p ≤ q := max_le_max le_rfl (min_le_min hdiv le_rfl)
  rcases hpq.lt_or_eq with hlt | heq
  · -- `p < q`: then `l ≤ x/q` and `x/p ≤ l + 1`
    have hql : q ≤ x / l := by
      by_contra hcon
      push Not at hcon
      have : q = i := by
        rw [hq]; apply max_eq_left
        by_contra h2; push Not at h2
        have : min (x / l) ((i : ℝ) + 1) ≤ x / l := min_le_left _ _
        have : q = min (x / l) ((i : ℝ) + 1) := max_eq_right h2.le
        linarith
      linarith
    have hpl : x / (l + 1) ≤ p := by
      by_contra hcon
      push Not at hcon
      have h1 : min (x / (l + 1)) ((i : ℝ) + 1) = i + 1 := by
        apply min_eq_right
        by_contra h2; push Not at h2
        have : min (x / (l + 1)) ((i : ℝ) + 1) = x / (l + 1) := min_eq_left h2.le
        have : x / (l + 1) ≤ p := by rw [hp]; exact le_max_of_le_right (le_of_eq this.symm)
        linarith
      have : p = i + 1 := by rw [hp, h1]; exact max_eq_right (by linarith)
      have : q ≤ i + 1 := max_le (by linarith) (min_le_right _ _)
      linarith
    have hlq : (l : ℝ) ≤ x / q := by rw [le_div_iff₀ hq0]; rwa [le_div_iff₀ (by linarith), mul_comm] at hql
    have hpl' : x / p ≤ l + 1 := by rw [div_le_iff₀ hp0]; rwa [div_le_iff₀ (by linarith), mul_comm] at hpl
    have hlog1 : Real.log q - Real.log p ≤ (q - p) / p := by
      rw [← Real.log_div hq0.ne' hp0.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
      rw [sub_div, div_self hp0.ne'] at *; linarith
    have hlog2 : (q - p) / q ≤ Real.log q - Real.log p := by
      rw [← Real.log_div hq0.ne' hp0.ne']
      have := Real.one_sub_inv_le_log_of_pos (div_pos hq0 hp0)
      rw [inv_div] at this
      rw [sub_div, div_self hq0.ne']; linarith
    have hxpq : x / p - x / q = (x / q) * ((q - p) / p) := by field_simp
    have hxpq' : x / p - x / q = (x / p) * ((q - p) / q) := by field_simp
    have hqp : 0 ≤ (q - p) / p := div_nonneg (by linarith) hp0.le
    have hqp' : 0 ≤ (q - p) / q := div_nonneg (by linarith) hq0.le
    have hlpos : 0 ≤ Real.log q - Real.log p := le_trans hqp' hlog2
    constructor
    · rw [hxpq]
      have : (l : ℝ) * (Real.log q - Real.log p) ≤ (x / q) * ((q - p) / p) :=
        mul_le_mul hlq hlog1 hlpos (le_trans (by linarith) hlq)
      linarith
    · rw [hxpq']
      have : (x / p) * ((q - p) / q) ≤ ((l : ℝ) + 1) * (Real.log q - Real.log p) :=
        mul_le_mul hpl' hlog2 hqp' (by linarith)
      linarith
  · rw [heq]; simp

/-- The weight `c_i = x/i − x/(i+1) − w_i(x)` lies in `[0, log(1 + 1/i)]`. -/
theorem weight_bounds (x i : ℕ) (hi : 1 ≤ i) (hix : i < x) :
    0 ≤ ((x : ℝ) / i - x / (i + 1)) - ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i ∧
    ((x : ℝ) / i - x / (i + 1)) - ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i ≤ Real.log (1 + 1 / (i : ℝ)) := by
  set u : ℕ → ℝ := fun l => max (i : ℝ) (min ((x : ℝ) / l) (i + 1)) with hu
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hu1 : u 1 = i + 1 := by
    simp only [hu, Nat.cast_one, div_one]
    rw [min_eq_right (by exact_mod_cast hix), max_eq_right (by linarith)]
  have hux : u (x + 1) = i := by
    simp only [hu]
    apply max_eq_left
    refine (min_le_left _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]; push_cast; nlinarith
  have hupos : ∀ l, 0 < u l := fun l => by simp only [hu]; exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  -- `w = ∑_l l (log u_l − log u_{l+1})`
  have hw : ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i =
      ∑ l ∈ Icc 1 x, (l : ℝ) * (Real.log (u l) - Real.log (u (l + 1))) := by
    have key := sum_mul_sub_eq (fun _ => (1 : ℝ)) (fun l => -Real.log (u l)) x
    simp only [one_mul, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one] at key
    rw [hux] at key
    have : ∀ j ∈ Icc 1 x, φ ((x : ℝ) / j) i = -Real.log (i : ℝ) - -Real.log (u j) := by
      intro j _; simp only [φ, hu]; ring
    rw [sum_congr rfl this, key]
    refine sum_congr rfl fun l _ => ?_
    ring
  -- `x/i − x/(i+1) = ∑_l (x/u_{l+1} − x/u_l)`
  have hd : ((x : ℝ) / i - x / (i + 1)) = ∑ l ∈ Icc 1 x, ((x : ℝ) / u (l + 1) - x / u l) := by
    rw [sum_Icc_sub_telescope (fun l => (x : ℝ) / u l) x, hux, hu1]
  have hlogsum : Real.log (1 + 1 / (i : ℝ)) = ∑ l ∈ Icc 1 x, (Real.log (u l) - Real.log (u (l + 1))) := by
    have := sum_Icc_sub_telescope (fun l => -Real.log (u l)) x
    rw [show ∑ l ∈ Icc 1 x, (Real.log (u l) - Real.log (u (l + 1))) =
      ∑ l ∈ Icc 1 x, (-Real.log (u (l + 1)) - -Real.log (u l)) from sum_congr rfl fun _ _ => by ring,
      this, hux, hu1, ← log_succ_sub_log hi]
    ring
  rw [hw, hd, hlogsum, ← sum_sub_distrib]
  constructor
  · refine sum_nonneg fun l hl => ?_
    have hl1 : 1 ≤ l := (mem_Icc.1 hl).1
    have := (term_bounds (x := (x : ℝ)) (i := i) hxpos hi hl1).1
    simp only [hu]; push_cast at this ⊢; linarith
  · refine sum_le_sum fun l hl => ?_
    have hl1 : 1 ≤ l := (mem_Icc.1 hl).1
    have := (term_bounds (x := (x : ℝ)) (i := i) hxpos hi hl1).2
    simp only [hu]; push_cast at this ⊢; linarith

/-- **Lemma 3** (El Marraki), discrete form. -/
theorem el_marraki {x : ℕ} (hx : 1 ≤ x) :
    |msum x| ≤ |M x| / x + S x / x + Real.log x / x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hid : (x : ℝ) * msum x - M x - Real.log x =
      ∑ i ∈ Ico 1 x, M i * (((x : ℝ) / i - x / (i + 1)) - ∑ j ∈ Icc 1 x, φ ((x : ℝ) / j) i) := by
    rw [mul_msum_eq, log_eq_sum_M_mul_w x hx]
    simp only [mul_sub, sum_sub_distrib]; ring
  have hbound : |(x : ℝ) * msum x - M x - Real.log x| ≤ S x := by
    rw [hid, S]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    obtain ⟨hi1, hi2⟩ := mem_Ico.1 hi
    obtain ⟨h0, h1⟩ := weight_bounds x i hi1 hi2
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have : |(x : ℝ) * msum x| ≤ |M x| + S x + Real.log x := by
    have := abs_add_three (x * msum x - M x - Real.log x) (M x) (Real.log x)
    rw [abs_of_nonneg hlog] at this
    calc |(x : ℝ) * msum x| = |((x : ℝ) * msum x - M x - Real.log x) + M x + Real.log x| := by ring_nf
      _ ≤ _ := this
      _ ≤ _ := by linarith
  rw [abs_mul, abs_of_pos hxpos] at this
  rw [← add_div, ← add_div, le_div_iff₀ hxpos]
  linarith

end TernaryGoldbach.RSBounds.Moebius003
