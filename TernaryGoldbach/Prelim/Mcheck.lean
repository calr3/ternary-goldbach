import Mathlib

/-!
# `m̌(x) = ∑_{n ≤ x} μ(n)/n · log(x/n)`: an identity and a bound in terms of `M`

With `m(x) = ∑_{n ≤ x} μ(n)/n`, `M(x) = ∑_{n ≤ x} μ(n)`, `H` the harmonic numbers and
`R(y) = y (H(⌊y⌋) − log y − γ) − 1/2 + {y}`:

  `m̌(x) − 1 = (1 − γ)(m(x) − M(x)/x) − (1 + I(x))/x`,  `I(x) = ∑_{n ≤ x} μ(n) (R(x/n) − R(1))`

(`mcheck_sub_one_eq`), from `∑_{n ≤ x} μ(n)/n · H(x/n) = 1` and `∑_{n ≤ x} μ(n) ⌊x/n⌋ = 1`.
`R` is continuous, and `|R'(t)| = |H(⌊t⌋) − log t − γ| ≤ 1/t`; so `|R(b) − R(a)| ≤ log(b/a)` and,
by summation by parts, `|I(x)| ≤ ∑_{j < ⌊x⌋} |M(j)| log(1 + 1/j) + |M(x)| log(x/⌊x⌋)`
(`= ∫₁ˣ |M(u)| du/u`). This replaces the identities of [Ramb, §3] (from Balazard), which give
the sharper kernel `(7/4 − γ)/t²`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim

local notation "γ" => Real.eulerMascheroniConstant

/-- `m̌(x) = ∑_{n ≤ x} μ(n)/n · log(x/n)` [Ramb, (1.2)]. -/
noncomputable def mcheck (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * Real.log (x / n)

/-- `m(x) = ∑_{n ≤ x} μ(n)/n`. -/
noncomputable def msumR (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n

/-- `M(x) = ∑_{n ≤ x} μ(n)`. -/
noncomputable def mertR (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)

/-- `R(y) = y (H(⌊y⌋) − log y − γ) − 1/2 + {y}`. -/
noncomputable def Rfun (y : ℝ) : ℝ :=
  y * ((harmonic ⌊y⌋₊ : ℝ) - Real.log y - γ) - 1 / 2 + (y - ⌊y⌋₊)

theorem Rfun_one : Rfun 1 = 1 / 2 - γ := by
  simp [Rfun]; ring

/-! ### Two convolution identities -/

/-- `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1` for `N ≥ 1`. -/
theorem sum_moebius_mul_div {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (μ n : ℝ) * ((N / n : ℕ) : ℝ) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) N
  rw [coe_moebius_mul_coe_zeta] at h
  have hL : ∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℝ) n = 1 := by
    rw [sum_eq_single 1 (fun b hb hb1 => by rw [one_apply_ne hb1]) (fun h1 => absurd
      (mem_Ioc.2 ⟨Nat.one_pos, hN⟩) h1), one_one]
  rw [hL] at h
  rw [show Icc 1 N = Ioc 0 N from rfl, h]
  refine sum_congr rfl fun n _ => ?_
  rw [intCoe_apply]
  congr 1
  rw [sum_congr rfl fun m hm => by
    rw [natCoe_apply, zeta_apply, ite_eq_right (mem_Ioc.1 hm).1.ne', Nat.cast_one]]
  rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one]

/-- `∑_{n ≤ N} μ(n)/n · H(N/n) = 1` for `N ≥ 1`. -/
theorem sum_moebius_div_harmonic {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (μ n : ℝ) / n * (harmonic (N / n) : ℝ) = 1 := by
  let a : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩
  have hsum := sum_Ioc_mul_eq_sum_sum a g N
  have hR : ∑ n ∈ Ioc 0 N, a n * ∑ m ∈ Ioc 0 (N / n), g m =
      ∑ n ∈ Icc 1 N, (μ n : ℝ) / n * (harmonic (N / n) : ℝ) := by
    refine sum_congr rfl fun n _ => ?_
    congr 1
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hL : ∀ k ∈ Ioc 0 N, (a * g) k = (if k = 1 then 1 else 0) := by
    intro k hk
    have hk0 : k ≠ 0 := (mem_Ioc.1 hk).1.ne'
    have hconv : (a * g) k = ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k / k := by
      rw [mul_apply, mul_apply, sum_div]
      refine sum_congr rfl fun x hx => ?_
      have hx' := Nat.mem_divisorsAntidiagonal.1 hx
      have h1 : (x.1 : ℝ) ≠ 0 := by
        have : x.1 ≠ 0 := fun h => hk0 (by rw [← hx'.1, h, zero_mul])
        exact_mod_cast this
      have h2 : x.2 ≠ 0 := fun h => hk0 (by rw [← hx'.1, h, mul_zero])
      have h2' : (x.2 : ℝ) ≠ 0 := by exact_mod_cast h2
      have hk : (k : ℝ) = x.1 * x.2 := by exact_mod_cast hx'.1.symm
      show (μ x.1 : ℝ) / x.1 * (x.2 : ℝ)⁻¹ = (μ x.1 : ℝ) * (ζ : ArithmeticFunction ℝ) x.2 / k
      rw [natCoe_apply, zeta_apply, ite_eq_right h2, Nat.cast_one, hk]
      field_simp
    rw [hconv, coe_moebius_mul_coe_zeta]
    by_cases h1 : k = 1
    · rw [h1, one_one, ite_eq_left rfl]; norm_num
    · rw [one_apply_ne h1, ite_eq_right h1, zero_div]
  rw [← hR, ← hsum, sum_congr rfl hL, sum_ite_eq' (Ioc 0 N) 1 (fun _ => (1 : ℝ)),
    ite_eq_left (mem_Ioc.2 ⟨Nat.one_pos, hN⟩)]

/-! ### The identity -/

/-- `m̌(x) − 1 = (1 − γ)(m(x) − M(x)/x) − (1 + I(x))/x` with
`I(x) = ∑_{n ≤ x} μ(n)(R(x/n) − R(1))`. -/
theorem mcheck_sub_one_eq {x : ℝ} (hx : 1 ≤ x) :
    mcheck x - 1 = (1 - γ) * (msumR x - mertR x / x) -
      (1 + ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Rfun (x / n) - Rfun 1)) / x := by
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hx0 : 0 < x := by linarith
  have hterm : ∀ n ∈ Icc 1 N, (μ n : ℝ) / n * Real.log (x / n) - (μ n : ℝ) / n * (harmonic (N / n) : ℝ) =
      (1 - γ) * ((μ n : ℝ) / n - (μ n : ℝ) / x) -
        ((μ n : ℝ) * ((N / n : ℕ) : ℝ) + (μ n : ℝ) * (Rfun (x / n) - Rfun 1)) / x := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    have hfl : ⌊x / n⌋₊ = N / n := Nat.floor_div_natCast x n
    rw [Rfun_one, Rfun, hfl]
    field_simp
    ring
  calc mcheck x - 1
      = ∑ n ∈ Icc 1 N, (μ n : ℝ) / n * Real.log (x / n) -
          ∑ n ∈ Icc 1 N, (μ n : ℝ) / n * (harmonic (N / n) : ℝ) := by
        rw [mcheck, sum_moebius_div_harmonic hN]
    _ = ∑ n ∈ Icc 1 N, ((1 - γ) * ((μ n : ℝ) / n - (μ n : ℝ) / x) -
          ((μ n : ℝ) * ((N / n : ℕ) : ℝ) + (μ n : ℝ) * (Rfun (x / n) - Rfun 1)) / x) := by
        rw [← sum_sub_distrib]; exact sum_congr rfl hterm
    _ = (1 - γ) * (∑ n ∈ Icc 1 N, (μ n : ℝ) / n - (∑ n ∈ Icc 1 N, (μ n : ℝ)) / x) -
          (∑ n ∈ Icc 1 N, (μ n : ℝ) * ((N / n : ℕ) : ℝ) +
            ∑ n ∈ Icc 1 N, (μ n : ℝ) * (Rfun (x / n) - Rfun 1)) / x := by
        rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib, ← sum_div, ← sum_div, sum_add_distrib]
    _ = _ := by
        rw [sum_moebius_mul_div hN, msumR, mertR]

/-! ### `|R(b) − R(a)| ≤ log(b/a)` -/

/-- `R` on the cell `[k, k+1]`: `t (H(k) − log t − γ) − 1/2 + (t − k)`. -/
noncomputable def Rcell (k : ℕ) (t : ℝ) : ℝ :=
  t * ((harmonic k : ℝ) - Real.log t - γ) - 1 / 2 + (t - k)

theorem Rfun_eq_Rcell {k : ℕ} {t : ℝ} (h1 : (k : ℝ) ≤ t) (h2 : t ≤ k + 1) : Rfun t = Rcell k t := by
  rcases h2.lt_or_eq with h2 | h2
  · have hfl : ⌊t⌋₊ = k := (Nat.floor_eq_iff ((Nat.cast_nonneg k).trans h1)).2 ⟨h1, h2⟩
    simp only [Rfun, Rcell, hfl]
  · have hfl : ⌊t⌋₊ = k + 1 := by rw [h2]; exact_mod_cast Nat.floor_natCast (k + 1)
    rw [Rfun, Rcell, hfl, harmonic_succ, h2]
    push_cast
    field_simp
    ring

theorem hasDerivAt_Rcell (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Rcell k) ((harmonic k : ℝ) - Real.log t - γ) t := by
  have h := (((hasDerivAt_id' t).fun_mul ((hasDerivAt_const t ((harmonic k : ℝ) - γ)).fun_sub
    (Real.hasDerivAt_log ht.ne'))).sub_const (1 / 2)).fun_add ((hasDerivAt_id' t).sub_const (k : ℝ))
  convert h using 1
  · funext s; simp only [Rcell]; ring
  · field_simp; ring

/-- On `(k, k+1)`: `|H(k) − log t − γ| ≤ 1/t`. -/
theorem abs_harmonic_sub_log_sub_le {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (h1 : (k : ℝ) ≤ t)
    (h2 : t ≤ k + 1) : |(harmonic k : ℝ) - Real.log t - γ| ≤ 1 / t := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < t := by linarith
  have hlo : (harmonic k : ℝ) - Real.log ((k : ℝ) + 1) < γ := by
    have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant k
    rwa [Real.eulerMascheroniSeq] at this
  have hhi : γ < (harmonic (k + 1) : ℝ) - Real.log ((k : ℝ) + 1) := by
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (k + 1)
    rw [Real.eulerMascheroniSeq', ite_eq_right (Nat.succ_ne_zero k)] at this
    push_cast at this
    exact this
  rw [harmonic_succ] at hhi
  push_cast at hhi
  have hlt : Real.log t ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log ht h2
  have hup : Real.log (((k : ℝ) + 1) / t) ≤ ((k : ℝ) + 1) / t - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) ht.ne'] at hup
  have hk1t : ((k : ℝ) + 1) / t - 1 ≤ 1 / t := by
    rw [div_sub_one ht.ne', div_le_div_iff_of_pos_right ht]; linarith
  have hinv : 1 / ((k : ℝ) + 1) ≤ 1 / t := one_div_le_one_div_of_le ht h2
  rw [abs_le]
  constructor
  · have : ((k : ℝ) + 1)⁻¹ = 1 / ((k : ℝ) + 1) := by rw [one_div]
    rw [this] at hhi
    linarith
  · linarith

/-- If `f` is monotone on every cell `[k, k+1]`, `k ≥ 1`, it is monotone on `[1, ∞)`. -/
theorem monotoneOn_Ici_of_cells {f : ℝ → ℝ}
    (h : ∀ k : ℕ, 1 ≤ k → MonotoneOn f (Set.Icc (k : ℝ) (k + 1))) : MonotoneOn f (Set.Ici 1) := by
  have hcell : ∀ k : ℕ, 1 ≤ k → ∀ a b : ℝ, (k : ℝ) ≤ a → a ≤ b → b ≤ k + 1 → f a ≤ f b :=
    fun k hk a b h1 h2 h3 => h k hk ⟨h1, by linarith⟩ ⟨by linarith, h3⟩ h2
  have hnat : Monotone (fun j : ℕ => f ((j : ℝ) + 1)) := by
    refine monotone_nat_of_le_succ fun j => ?_
    have := hcell (j + 1) (by omega) ((j : ℝ) + 1) ((j : ℝ) + 1 + 1) (by push_cast; rfl)
      (by linarith) (by push_cast; rfl)
    simpa [add_assoc] using this
  intro a ha b hb hab
  have ha1 : (1 : ℝ) ≤ a := ha
  set ka := ⌊a⌋₊ with hka
  set kb := ⌊b⌋₊ with hkb
  have hka1 : 1 ≤ ka := Nat.le_floor (by exact_mod_cast ha1)
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have haf : (ka : ℝ) ≤ a := Nat.floor_le ha0
  have haf' : a < ka + 1 := Nat.lt_floor_add_one a
  have hbf : (kb : ℝ) ≤ b := Nat.floor_le hb0
  have hbf' : b < kb + 1 := Nat.lt_floor_add_one b
  have hkab : ka ≤ kb := Nat.floor_le_floor hab
  rcases hkab.lt_or_eq with hlt | heq
  · have h1 : f a ≤ f ((ka : ℝ) + 1) := hcell ka hka1 a _ haf haf'.le le_rfl
    have h2 : f ((ka : ℝ) + 1) ≤ f (((kb - 1 : ℕ) : ℝ) + 1) := hnat (by omega)
    have hkb1 : (((kb - 1 : ℕ) : ℝ) + 1) = kb := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hkb1] at h2
    have h3 : f (kb : ℝ) ≤ f b := hcell kb (by omega) _ b le_rfl hbf hbf'.le
    linarith
  · exact hcell ka hka1 a b haf hab (by rw [heq]; exact hbf'.le)

/-- `|R(b) − R(a)| ≤ log b − log a` for `1 ≤ a ≤ b`. -/
theorem abs_Rfun_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |Rfun b - Rfun a| ≤ Real.log b - Real.log a := by
  have hmono : ∀ s : ℝ, s = 1 ∨ s = -1 →
      MonotoneOn (fun t => Real.log t + s * Rfun t) (Set.Ici 1) := by
    intro s hs
    refine monotoneOn_Ici_of_cells fun k hk => ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have heq : Set.EqOn (fun t => Real.log t + s * Rfun t) (fun t => Real.log t + s * Rcell k t)
        (Set.Icc (k : ℝ) (k + 1)) := fun t ht => by
      simp only [Rfun_eq_Rcell ht.1 ht.2]
    refine MonotoneOn.congr ?_ heq.symm
    have hpos : ∀ t ∈ Set.Icc (k : ℝ) (k + 1), 0 < t := fun t ht => by linarith [ht.1]
    have hderiv : ∀ t ∈ Set.Icc (k : ℝ) (k + 1), HasDerivAt (fun t => Real.log t + s * Rcell k t)
        (1 / t + s * ((harmonic k : ℝ) - Real.log t - γ)) t := fun t ht => by
      have := (Real.hasDerivAt_log (hpos t ht).ne').fun_add ((hasDerivAt_Rcell k (hpos t ht)).const_mul s)
      simpa [one_div] using this
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(hderiv t ht').deriv]
    have hb := abs_le.1 (abs_harmonic_sub_log_sub_le hk ht'.1 ht'.2)
    rcases hs with rfl | rfl <;> linarith [hb.1, hb.2]
  have h1 := hmono 1 (Or.inl rfl) (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab
  have h2 := hmono (-1) (Or.inr rfl) (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab
  simp only at h1 h2
  rw [abs_le]; constructor <;> linarith

/-! ### Summation by parts, and the bound -/

/-- `∫₁ˣ |M(u)| du/u` as a sum: `∑_{j < ⌊x⌋} |M(j)| log((j+1)/j) + |M(x)| log(x/⌊x⌋)`. -/
noncomputable def mertAbsInt (x : ℝ) : ℝ :=
  ∑ j ∈ Ico 1 ⌊x⌋₊, |mertR j| * Real.log (((j : ℝ) + 1) / j) + |mertR x| * Real.log (x / ⌊x⌋₊)

theorem mertR_natCast (j : ℕ) : mertR j = ∑ n ∈ Icc 1 j, (μ n : ℝ) := by
  rw [mertR, Nat.floor_natCast]

/-- Telescoping: `∑_{j ∈ [n, n+m)} (r j − r (j+1)) = r n − r (n+m)`. -/
theorem sum_Ico_sub_succ (r : ℕ → ℝ) (n m : ℕ) :
    ∑ j ∈ Ico n (n + m), (r j - r (j + 1)) = r n - r (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    ring

/-- `|I(x)| ≤ ∫₁ˣ |M(u)| du/u`. -/
theorem abs_sum_Rfun_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Rfun (x / n) - Rfun 1)| ≤ mertAbsInt x := by
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hx0 : 0 < x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  set r : ℕ → ℝ := fun j => if j ≤ N then Rfun (x / j) else Rfun 1 with hr
  set D : ℕ → ℝ := fun j => r j - r (j + 1) with hD
  have htel : ∀ n ∈ Icc 1 N, Rfun (x / n) - Rfun 1 = ∑ j ∈ Icc n N, D j := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.1 hn
    have h := sum_Ico_sub_succ r n (N + 1 - n)
    rw [show n + (N + 1 - n) = N + 1 by omega] at h
    rw [show Icc n N = Ico n (N + 1) from rfl, h]
    have hnot : ¬ N + 1 ≤ N := by omega
    simp only [hr, hnN, hnot, ↓reduceIte]
  -- swap the sums
  have hswap : ∑ n ∈ Icc 1 N, (μ n : ℝ) * (Rfun (x / n) - Rfun 1) =
      ∑ j ∈ Icc 1 N, mertR j * D j := by
    rw [sum_congr rfl fun n hn => by rw [htel n hn, mul_sum]]
    rw [sum_comm' (s' := fun j => Icc 1 j) (t' := Icc 1 N)
      (h := fun n j => by simp only [mem_Icc]; omega)]
    refine sum_congr rfl fun j _ => ?_
    rw [mertR_natCast, sum_mul]
  rw [hswap]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.Ico_insert_right hN, sum_insert (by simp)]
  rw [mertAbsInt, add_comm]
  refine add_le_add (sum_le_sum fun j hj => ?_) ?_
  · obtain ⟨hj1, hjN⟩ := mem_Ico.1 hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hjx : ((j : ℝ) + 1) ≤ x := le_trans (by exact_mod_cast hjN) hNx
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : j ≤ N := hjN.le
    have h2 : j + 1 ≤ N := by omega
    simp only [hD, hr, h1, h2, ↓reduceIte]
    push_cast
    have ha : 1 ≤ x / ((j : ℝ) + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hab : x / ((j : ℝ) + 1) ≤ x / j := div_le_div_of_nonneg_left hx0.le hj0 (by linarith)
    refine (abs_Rfun_sub_le ha hab).trans (le_of_eq ?_)
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  · rw [abs_mul]
    have hmN : mertR (N : ℝ) = mertR x := by rw [mertR, mertR, Nat.floor_natCast]
    rw [hmN]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hnot : ¬ N + 1 ≤ N := by omega
    simp only [hD, hr, le_refl, hnot, ↓reduceIte]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have ha : (1 : ℝ) ≤ x / N := by rw [le_div_iff₀ hN0]; linarith
    refine (abs_Rfun_sub_le le_rfl ha).trans (le_of_eq ?_)
    rw [Real.log_one, sub_zero]

/-- **The bound on `m̌`**: `|m̌(x) − 1| ≤ (1 − γ)|m(x) − M(x)/x| + (1 + ∫₁ˣ |M(u)| du/u)/x`. -/
theorem abs_mcheck_sub_one_le {x : ℝ} (hx : 1 ≤ x) :
    |mcheck x - 1| ≤ (1 - γ) * |msumR x - mertR x / x| + (1 + mertAbsInt x) / x := by
  have hx0 : 0 < x := by linarith
  have hγ : γ < 1 := Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hI := abs_sum_Rfun_le hx
  rw [mcheck_sub_one_eq hx]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by linarith)]
  · rw [abs_div, abs_of_pos hx0]
    refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans ?_) hx0.le
    rw [abs_one]; linarith

end TernaryGoldbach.Prelim
