import TernaryGoldbach.Prelim.MoebiusLogCoprime

/-!
# [H, (2.22)]: from the coprime sum to `S(y) = ∑_{w ≤ √y} |m(y/w²)|/w²`

Ramaré's reduction ([Ramb, Lemma 1.9 and §9], for `m` instead of `m̌`): `μ · 1_{(·,q)=1} = c_q * μ`
gives `m_q(x) = ∑_{a ≤ x} c_q(a)/a · m(x/a)`, with `m(y) = ∑_{n ≤ y} μ(n)/n` and `c_q` the indicator
of the `q`-factored numbers. Writing `a = d w²` with `d` squarefree (so `d ∣ q`),

  `|m_q(x)| ≤ ∑_{d ∣ q, d squarefree} S(x/d)/d`, where `S(y) = ∑_{w ≤ √y} |m(y/w²)|/w²`.

So `S(y) log y ≤ C` for all `y ≥ 1` gives `|m_q(x)| ≤ C (q/φ(q))/log(x/q)` for `1 ≤ q < x`, since
`∑_{d ∣ q squarefree} 1/d ≤ q/φ(q)`. `S` is [Ramb, (7.1)]'s `m*` without the maximum, which we do not
need since `S` depends on `y` only through `⌊y⌋`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- `S(y) = ∑_{1 ≤ w ≤ √⌊y⌋} |m(y/w²)|/w²`. -/
noncomputable def Sm (y : ℝ) : ℝ :=
  ∑ w ∈ Icc 1 (Nat.sqrt ⌊y⌋₊), |msumR (y / (w * w : ℕ))| / (w * w : ℕ)

theorem Sm_nonneg (y : ℝ) : 0 ≤ Sm y :=
  sum_nonneg fun _ _ => by positivity

/-- `m(z) = 0` for `z < 1`. -/
theorem msumR_of_lt_one {z : ℝ} (hz : z < 1) : msumR z = 0 := by
  rw [msumR, Nat.floor_eq_zero.2 hz]
  simp

/-- **The reduction for `m`**: `∑_{n ≤ x, (n,q)=1} μ(n)/n = ∑_{a ≤ x} c_q(a)/a · m(x/a)`. -/
theorem sum_coprime_eq (x : ℝ) (q : ℕ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0) =
      ∑ a ∈ Icc 1 ⌊x⌋₊, cq q a / a * msumR (x / a) := by
  set N := ⌊x⌋₊
  have hIcc : ∀ m, Icc 1 m = Ioc 0 m := fun m => rfl
  set F : ℕ → ℕ → ℝ := fun a k => cq q a / a * ((μ k : ℝ) / k) with hF
  have hL : ∀ n ∈ Ioc 0 N, (if Nat.Coprime n q then (μ n : ℝ) / n else 0) =
      ∑ y ∈ n.divisorsAntidiagonal, F y.1 y.2 := by
    intro n hn
    have hn0 : n ≠ 0 := (mem_Ioc.1 hn).1.ne'
    have hterm : ∀ y ∈ n.divisorsAntidiagonal,
        F y.1 y.2 = cq q y.1 * (μ y.2 : ℝ) * (1 / n) := by
      intro y hy
      obtain ⟨hyn, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
      have h1 : (y.1 : ℝ) ≠ 0 := by
        have : y.1 ≠ 0 := fun h => hn0 (by rw [← hyn, h, zero_mul])
        exact_mod_cast this
      have h2 : (y.2 : ℝ) ≠ 0 := by
        have : y.2 ≠ 0 := fun h => hn0 (by rw [← hyn, h, mul_zero])
        exact_mod_cast this
      have hn : (n : ℝ) = y.1 * y.2 := by exact_mod_cast hyn.symm
      simp only [hF]
      rw [hn]
      field_simp
    rw [sum_congr rfl hterm, ← sum_mul]
    have hconv : ∑ y ∈ n.divisorsAntidiagonal, cq q y.1 * (μ y.2 : ℝ) = muq q n := by
      rw [← cq_mul_moebius, mul_apply]
      rfl
    rw [hconv]
    simp only [muq, pmul_apply, intCoe_apply, chiq_apply, ne_eq, hn0, not_false_eq_true, true_and]
    split_ifs <;> ring
  rw [hIcc, sum_congr rfl hL, sum_Ioc_sum_divisorsAntidiagonal F N]
  refine sum_congr rfl fun a ha => ?_
  rw [msumR, Nat.floor_div_natCast, hIcc, mul_sum]

/-- A squarefree `d` whose prime factors all divide `q ≠ 0` divides `q`. -/
theorem dvd_of_squarefree_of_primeFactors {d q : ℕ} (hd : Squarefree d) (hq : q ≠ 0)
    (h : ∀ p, p.Prime → p ∣ d → p ∣ q) : d ∣ q := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  refine (Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_).trans (Nat.prod_primeFactors_dvd q)
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact Nat.mem_primeFactors.2 ⟨hpp, h p hpp (Nat.dvd_of_mem_primeFactors hp), hq⟩

/-- Extending the range of `S`'s sum: the terms with `w² > y` vanish. -/
theorem sum_Icc_eq_Sm {y : ℝ} {N : ℕ} (hN : Nat.sqrt ⌊y⌋₊ ≤ N) :
    ∑ w ∈ Icc 1 N, |msumR (y / (w * w : ℕ))| / (w * w : ℕ) = Sm y := by
  rw [Sm]
  symm
  refine sum_subset (Icc_subset_Icc_right hN) fun w hw hw' => ?_
  have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
  have hlt : Nat.sqrt ⌊y⌋₊ < w := by
    by_contra h
    exact hw' (mem_Icc.2 ⟨hw1, not_lt.1 h⟩)
  have hfl : ⌊y⌋₊ < w * w := by have := Nat.sqrt_lt'.1 hlt; rwa [sq] at this
  have hz : y / (w * w : ℕ) < 1 := by
    have hpos : (0 : ℝ) < (w * w : ℕ) := by exact_mod_cast Nat.mul_pos hw1 hw1
    rw [div_lt_one hpos]
    rcases lt_or_ge y 0 with hy | hy
    · linarith
    · exact lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hfl)
  rw [msumR_of_lt_one hz, abs_zero, zero_div]

/-- **The bound by `S`**: `|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ ∑_{d ∣ q squarefree} S(x/d)/d`. -/
theorem abs_sum_coprime_le_Sm {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      ∑ d ∈ q.divisors.filter Squarefree, Sm (x / d) / d := by
  classical
  set N := ⌊x⌋₊
  have hq0 : q ≠ 0 := by omega
  set A := (Icc 1 N).filter (· ∈ Nat.factoredNumbers q.primeFactors)
  set f : ℕ → ℝ := fun a => |msumR (x / a)| / a with hf
  have hf0 : ∀ a, 0 ≤ f a := fun a => by simp only [hf]; positivity
  -- step 1: `|m_q(x)| ≤ ∑_{a ∈ A} |m(x/a)|/a`
  have h1 : |∑ n ∈ Icc 1 N, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤ ∑ a ∈ A, f a := by
    rw [sum_coprime_eq x q]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_filter]
    refine sum_le_sum fun a ha => ?_
    have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    rw [cq_apply_eq hq0 (by omega)]
    split_ifs
    · simp only [hf, abs_mul, abs_div, abs_one, Nat.abs_cast]
      rw [div_mul_eq_mul_div, one_mul]
    · simp
  -- step 2: `a = w² d` with `d` squarefree
  have hdec : ∀ a : ℕ, ∃ d w : ℕ, w ^ 2 * d = a ∧ Squarefree d := fun a => by
    obtain ⟨w, d, h1, h2⟩ := exists_sq_mul_squarefree a
    exact ⟨d, w, h1, h2⟩
  choose dd ww hdw hsq using hdec
  set g : ℕ → ℕ × ℕ := fun a => (dd a, ww a)
  set D := q.divisors.filter Squarefree
  have hinj : Set.InjOn g A := by
    intro a _ b _ hab
    simp only [g, Prod.mk.injEq] at hab
    rw [← hdw a, ← hdw b, hab.1, hab.2]
  have hsub : A.image g ⊆ D ×ˢ Icc 1 N := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨haI, haq⟩ := mem_filter.1 ha
    obtain ⟨ha1, haN⟩ := mem_Icc.1 haI
    have ha0 : a ≠ 0 := by omega
    have hda : dd a ∣ a := ⟨ww a ^ 2, by rw [mul_comm]; exact (hdw a).symm⟩
    have hwa : ww a ^ 2 ∣ a := ⟨dd a, (hdw a).symm⟩
    have hd0 : dd a ≠ 0 := fun h => ha0 (by rw [← hdw a, h, mul_zero])
    have hw0 : ww a ≠ 0 := fun h => ha0 (by rw [← hdw a, h]; ring)
    show (dd a, ww a) ∈ D ×ˢ Icc 1 N
    refine mem_product.2 ⟨mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, hq0⟩, hsq a⟩, mem_Icc.2 ⟨?_, ?_⟩⟩
    · refine dvd_of_squarefree_of_primeFactors (hsq a) hq0 fun p hp hpd => ?_
      have := (Nat.mem_factoredNumbers'.1 haq) p hp (hpd.trans hda)
      exact Nat.dvd_of_mem_primeFactors this
    · omega
    · have h1 : ww a ≤ ww a ^ 2 := by nlinarith [Nat.pos_of_ne_zero hw0]
      exact h1.trans ((Nat.le_of_dvd (by omega) hwa).trans haN)
  have hval : ∀ a ∈ A, f a = f ((g a).2 ^ 2 * (g a).1) := fun a _ => by simp only [g, hdw]
  -- step 3: sum over the pairs `(d, w)`
  have h2 : ∑ a ∈ A, f a ≤ ∑ p ∈ D ×ˢ Icc 1 N, f (p.2 ^ 2 * p.1) := by
    rw [sum_congr rfl hval, ← sum_image (f := fun p : ℕ × ℕ => f (p.2 ^ 2 * p.1)) hinj]
    exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf0 _
  -- step 4: regroup as `∑_d S(x/d)/d`
  have h3 : ∑ p ∈ D ×ˢ Icc 1 N, f (p.2 ^ 2 * p.1) = ∑ d ∈ D, Sm (x / d) / d := by
    rw [sum_product]
    refine sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pos_of_mem_divisors (mem_filter.1 hd).1))
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hN : Nat.sqrt ⌊x / d⌋₊ ≤ N := by
      refine (Nat.sqrt_le_self _).trans (Nat.floor_le_floor ?_)
      exact div_le_self hx.le (by exact_mod_cast hd1)
    rw [← sum_Icc_eq_Sm hN, sum_div]
    refine sum_congr rfl fun w _ => ?_
    simp only [hf]
    push_cast
    rw [div_div, div_div]
    congr 2
    · ring_nf
    · ring
  rw [h3] at h2
  exact h1.trans h2

/-- **[H, (2.22)] from a bound on `S`**: if `S(y) log y ≤ C` for all `y ≥ 1`, then
`|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ C (q/φ(q))/log(x/q)` for `1 ≤ q < x`. -/
theorem abs_sum_coprime_le_of_Sm {C : ℝ} (hC : ∀ y : ℝ, 1 ≤ y → Sm y * Real.log y ≤ C)
    {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqx : (q : ℝ) < x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      C * (q / Nat.totient q) / Real.log (x / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 0 < x := by linarith
  have hxq : 1 < x / q := by rw [one_lt_div hq0]; exact hqx
  have hL : 0 < Real.log (x / q) := Real.log_pos hxq
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl
    rw [Real.log_one, mul_zero] at this
    exact this
  refine (abs_sum_coprime_le_Sm hx hq).trans ?_
  have hterm : ∀ d ∈ q.divisors.filter Squarefree,
      Sm (x / d) / d ≤ C / Real.log (x / q) * (d : ℝ)⁻¹ := by
    intro d hd
    have hdq : d ≤ q := Nat.divisor_le (mem_filter.1 hd).1
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (mem_filter.1 hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hxd : x / q ≤ x / d := div_le_div_of_nonneg_left hx.le hd0 (by exact_mod_cast hdq)
    have hLd : Real.log (x / q) ≤ Real.log (x / d) := Real.log_le_log (by linarith) hxd
    have hS := hC (x / d) (by linarith)
    have hSm : Sm (x / d) ≤ C / Real.log (x / q) := by
      rw [le_div_iff₀ hL]
      calc Sm (x / d) * Real.log (x / q) ≤ Sm (x / d) * Real.log (x / d) :=
            mul_le_mul_of_nonneg_left hLd (Sm_nonneg _)
        _ ≤ C := hS
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hSm (by positivity)
  have hsum : ∑ d ∈ q.divisors.filter Squarefree, (d : ℝ)⁻¹ ≤ q / Nat.totient q := by
    refine le_trans ?_ (sum_factored_le hq q)
    refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun _ _ _ => by positivity
    have hdq := Nat.mem_divisors.1 (mem_filter.1 hd).1
    refine mem_filter.2 ⟨mem_Ioc.2 ⟨Nat.pos_of_dvd_of_pos hdq.1 (by omega),
      Nat.le_of_dvd (by omega) hdq.1⟩, ?_⟩
    rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    exact Nat.mem_primeFactors.2 ⟨hp, hpd.trans hdq.1, by omega⟩
  have hfac : 0 ≤ C / Real.log (x / q) := div_nonneg hC0 hL.le
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  calc (C / Real.log (x / q)) * ∑ d ∈ q.divisors.filter Squarefree, (d : ℝ)⁻¹
      ≤ (C / Real.log (x / q)) * (q / Nat.totient q) := mul_le_mul_of_nonneg_left hsum hfac
    _ = C * (q / Nat.totient q) / Real.log (x / q) := by ring

end TernaryGoldbach.Prelim
