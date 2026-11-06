import TernaryGoldbach.Prelim.RamareMain

/-!
# `∑_a h_d(a) log a = (2φ(d)/d)(log 2 − ∑_p log p/(p(p−1)) − ∑_{p∣d} log p/p)`

* Splitting `a = p^k b` with `p ∤ b` (`hasSum_split`): `∑_a h_d(a) = S₀(p) B_p` and
  `∑_a h_d(a) v_p(a) = S₁(p) B_p` with `B_p = ∑_{p ∤ b} h_d(b)`;
* `log a = ∑_{p ∣ a} v_p(a) log p`, and the double sum is absolutely convergent.
-/

open Finset Real ArithmeticFunction Function

namespace TernaryGoldbach.Prelim.RamPf

open TernaryGoldbach.Prelim (SqP)

/-- Splitting `a = p^k b`, `p ∤ b`. -/
theorem hasSum_split {p : ℕ} (hp : p.Prime) {F : ℕ → ℝ} (hF0 : F 0 = 0) {s : ℝ} (hF : HasSum F s) :
    HasSum (fun kb : ℕ × ℕ => if Nat.Coprime p kb.2 then F (p ^ kb.1 * kb.2) else 0) s := by
  haveI := Fact.mk hp
  set g : ℕ × ℕ → ℝ := fun kb => if Nat.Coprime p kb.2 then F (p ^ kb.1 * kb.2) else 0 with hg
  have hsupp : ∀ kb : ℕ × ℕ, g kb ≠ 0 → Nat.Coprime p kb.2 ∧ F (p ^ kb.1 * kb.2) ≠ 0 := by
    intro kb h
    by_cases hc : Nat.Coprime p kb.2
    · simp only [hg, if_pos hc] at h; exact ⟨hc, h⟩
    · simp only [hg, if_neg hc, ne_eq, not_true_eq_false] at h
  have hval : ∀ {k b : ℕ}, Nat.Coprime p b → b ≠ 0 → padicValNat p (p ^ k * b) = k := by
    intro k b hc hb
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hb, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc), add_zero]
  refine (hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := g) (fun x => p ^ x.1.1 * x.1.2) ?_ ?_ ?_).1 hF
  · rintro ⟨⟨k, b⟩, hx⟩ ⟨⟨k', b'⟩, hy⟩ hxy
    obtain ⟨hb, hFb⟩ := hsupp _ hx
    obtain ⟨hb', hFb'⟩ := hsupp _ hy
    simp only at hxy hb hb' hFb hFb'
    have hb0 : b ≠ 0 := by rintro rfl; simp [hF0] at hFb
    have hb0' : b' ≠ 0 := by rintro rfl; simp [hF0] at hFb'
    have hk : k = k' := by rw [← hval (k := k) hb hb0, hxy, hval hb' hb0']
    subst hk
    have : b = b' := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) hxy
    subst this; rfl
  · intro a ha
    have ha0 : a ≠ 0 := by rintro rfl; exact ha hF0
    refine ⟨⟨(a.factorization p, ordCompl[p] a), ?_⟩, ?_⟩
    · show g _ ≠ 0
      simp only [hg, if_pos (Nat.coprime_ordCompl hp ha0), Nat.ordProj_mul_ordCompl_eq_self]
      exact ha
    · exact Nat.ordProj_mul_ordCompl_eq_self a p
  · rintro ⟨⟨k, b⟩, hx⟩
    obtain ⟨hb, -⟩ := hsupp _ hx
    simp only [hg, if_pos hb]

/-- `h_d(a) = 0` when `v_p(a) ≥ 3`. -/
theorem hD_eq_zero_of_val {d p a : ℕ} (hp : p.Prime) (h : 3 ≤ padicValNat p a) : hD d a = 0 := by
  haveI := Fact.mk hp
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self a p
  rw [← hsplit, (isMult_hD d).map_mul_of_coprime (Nat.Coprime.pow_left _
    (Nat.coprime_ordCompl hp ha.ne')), hD_pk hp (by rwa [Nat.factorization_def a hp]), zero_mul]

theorem summable_hD_val {d : ℕ} (hd : 1 ≤ d) (p : ℕ) (hp : p.Prime) :
    Summable fun a => hD d a * (padicValNat p a : ℝ) :=
  Summable.of_norm_bounded ((summable_abs_hD hd).mul_left 2) fun a => by
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    by_cases h : 3 ≤ padicValNat p a
    · rw [hD_eq_zero_of_val hp h, abs_zero, zero_mul]; positivity
    · have : (padicValNat p a : ℝ) ≤ 2 := by exact_mod_cast (by omega : padicValNat p a ≤ 2)
      nlinarith [abs_nonneg (hD d a)]

/-- `B_p = ∑_{p ∤ b} h_d(b)`. -/
noncomputable def Bp (d p : ℕ) : ℝ := ∑' b, if Nat.Coprime p b then hD d b else 0

theorem summable_Bp {d : ℕ} (hd : 1 ≤ d) (p : ℕ) :
    Summable fun b => if Nat.Coprime p b then hD d b else 0 :=
  Summable.of_norm_bounded (summable_abs_hD hd) fun b => by
    rw [Real.norm_eq_abs]; split_ifs <;> simp

theorem fiber {d p k : ℕ} (hd : 1 ≤ d) (c : ℝ) :
    HasSum (fun b => if Nat.Coprime p b then hD d (p ^ k * b) * c else 0)
      (hD d (p ^ k) * c * Bp d p) := by
  have h := ((summable_Bp hd p).hasSum).mul_left (hD d (p ^ k) * c)
  rw [Bp]
  convert h using 1
  funext b
  by_cases hb : Nat.Coprime p b
  · rw [if_pos hb, if_pos hb, (isMult_hD d).map_mul_of_coprime (Nat.Coprime.pow_left _ hb)]; ring
  · rw [if_neg hb, if_neg hb, mul_zero]

theorem tsum_hD_eq {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) :
    ∑' a, hD d a = S0 d p * Bp d p := by
  have h := hasSum_split hp (hD_zero d) (summable_hD hd).hasSum
  have hfib := h.prod_fiberwise (g := fun k => hD d (p ^ k) * 1 * Bp d p) fun k => by
    have := fiber (p := p) (k := k) hd 1
    simp only [mul_one] at this ⊢
    exact this
  have hloc := (hasSum_local (d := d) hp (fun _ => 1)).mul_right (Bp d p)
  simp only [one_mul, mul_one] at hloc hfib
  rw [hfib.unique hloc, S0]

theorem tsum_hD_val {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) :
    ∑' a, hD d a * (padicValNat p a : ℝ) = S1 d p * Bp d p := by
  haveI := Fact.mk hp
  have h := hasSum_split hp (by simp) (summable_hD_val hd p hp).hasSum
  have hfib := h.prod_fiberwise (g := fun (k : ℕ) => hD d (p ^ k) * (k : ℝ) * Bp d p) fun (k : ℕ) => by
    have := fiber (p := p) (k := k) hd (k : ℝ)
    convert this using 1
    funext b
    by_cases hb : Nat.Coprime p b
    · rw [if_pos hb, if_pos hb]
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; simp
      · rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) h0.ne', padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hb), add_zero]
    · rw [if_neg hb, if_neg hb]
  have hloc := (hasSum_local (d := d) hp (fun e => (e : ℝ))).mul_right (Bp d p)
  rw [hfib.unique (by convert hloc using 1; funext k; ring), S1]
  push_cast; ring

theorem S0_pos {d p : ℕ} (hp : p.Prime) : 0 < S0 d p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [S0_split hp]
  apply mul_pos
  · split_ifs
    · have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
      linarith
    · norm_num
  · split_ifs <;> norm_num

/-- **`∑_a h_d(a) v_p(a) = (S₁/S₀)(2φ(d)/d)`.** -/
theorem tsum_hD_val' {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) :
    ∑' a, hD d a * (padicValNat p a : ℝ) = S1 d p / S0 d p * (2 * ((Nat.totient d : ℝ) / d)) := by
  rw [tsum_hD_val hd hp, ← tsum_hD hd, tsum_hD_eq hd hp]
  have := (S0_pos (d := d) hp).ne'
  field_simp

/-! ### `log a = ∑_p v_p(a) log p` and the double sum -/

/-- `G(a, q) = [q prime] h_d(a) v_q(a) log q`. -/
noncomputable def Gaq (d a q : ℕ) : ℝ :=
  if q.Prime then hD d a * (padicValNat q a : ℝ) * Real.log q else 0

theorem log_eq_sum {a : ℕ} (ha : a ≠ 0) :
    Real.log a = ∑ q ∈ a.primeFactors, (padicValNat q a : ℝ) * Real.log q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ha]
  rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod,
    Real.log_prod (fun q hq => by
      have := (Nat.prime_of_mem_primeFactors hq).pos
      positivity)]
  refine sum_congr rfl fun q hq => ?_
  rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def a (Nat.prime_of_mem_primeFactors hq)]

theorem hasSum_Gaq_a (d a : ℕ) : HasSum (fun q => Gaq d a q) (hD d a * Real.log a) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : (fun q => Gaq d 0 q) = fun _ => 0 := by funext q; simp [Gaq]
    rw [this]; simpa using hasSum_zero
  have h : HasSum (fun q => Gaq d a q) (∑ q ∈ a.primeFactors, Gaq d a q) :=
    hasSum_sum_of_ne_finset_zero fun q hq => by
      unfold Gaq
      split_ifs with hqp
      · have hnd : ¬ q ∣ a := fun h => hq (Nat.mem_primeFactors.2 ⟨hqp, h, ha.ne'⟩)
        rw [padicValNat.eq_zero_of_not_dvd hnd]; simp
      · rfl
  convert h using 1
  rw [log_eq_sum ha.ne', mul_sum]
  refine sum_congr rfl fun q hq => ?_
  rw [Gaq, if_pos (Nat.prime_of_mem_primeFactors hq)]; ring

theorem abs_Gaq_hasSum (d a : ℕ) : HasSum (fun q => |Gaq d a q|) (|hD d a| * Real.log a) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : (fun q => |Gaq d 0 q|) = fun _ => 0 := by funext q; simp [Gaq]
    rw [this]; simpa using hasSum_zero
  have e : (fun q => |Gaq d a q|) = fun q =>
      if q.Prime then |hD d a| * (padicValNat q a : ℝ) * Real.log q else 0 := by
    funext q; unfold Gaq
    split_ifs with hq
    · rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg (Real.log_natCast_nonneg q)]
    · simp
  rw [e]
  have h := hasSum_Gaq_a d a
  have h' : HasSum (fun q => if q.Prime then (padicValNat q a : ℝ) * Real.log q else 0) (Real.log a) := by
    have hs : HasSum (fun q => if q.Prime then (padicValNat q a : ℝ) * Real.log q else 0)
        (∑ q ∈ a.primeFactors, (if q.Prime then (padicValNat q a : ℝ) * Real.log q else 0)) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by
        split_ifs with hqp
        · have hnd : ¬ q ∣ a := fun h => hq (Nat.mem_primeFactors.2 ⟨hqp, h, ha.ne'⟩)
          rw [padicValNat.eq_zero_of_not_dvd hnd]; simp
        · rfl
    convert hs using 1
    rw [log_eq_sum ha.ne']
    exact sum_congr rfl fun q hq => by rw [if_pos (Nat.prime_of_mem_primeFactors hq)]
  convert h'.mul_left |hD d a| using 1
  funext q; split_ifs <;> ring

theorem summable_Gaq {d : ℕ} (hd : 1 ≤ d) : Summable (uncurry (Gaq d)) := by
  refine Summable.of_norm ?_
  have hnn : 0 ≤ fun x : ℕ × ℕ => ‖uncurry (Gaq d) x‖ := fun x => norm_nonneg _
  refine (summable_prod_of_nonneg hnn).2 ⟨fun a => ?_, ?_⟩
  · simp only [uncurry, Real.norm_eq_abs]; exact (abs_Gaq_hasSum d a).summable
  · simp only [uncurry, Real.norm_eq_abs]
    simp_rw [(abs_Gaq_hasSum d _).tsum_eq]
    exact Summable.of_nonneg_of_le (fun a => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg a))
      (abs_hD_log_le d) ((summable_wD hd).mul_left 3)

/-- `r_q = S₁(q)/S₀(q)` plus `1/(q(q−1))`: non-zero only for `q ∣ 2d`. -/
theorem r_eq {d q : ℕ} (hq : q.Prime) :
    Real.log q * (S1 d q / S0 d q) = -(Real.log q / ((q : ℝ) * ((q : ℝ) - 1))) +
      (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
        (if q ∣ d then -(Real.log q / q) else 0)) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  rw [S1_eq hq, S0_eq hq]
  by_cases h2 : q = 2
  · subst h2; by_cases hd : 2 ∣ d <;> simp [hd] <;> norm_num <;> ring
  · have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hq10 : (q : ℝ) - 1 ≠ 0 := by linarith
    have hq11 : 1 - 1 / (q : ℝ) ≠ 0 := by
      have : 1 / (q : ℝ) < 1 := (div_lt_one (by linarith)).2 hq1
      exact (by linarith : (0 : ℝ) < 1 - 1 / (q : ℝ)).ne'
    by_cases hd : q ∣ d <;> simp only [h2, hd, if_true, if_false]
    · field_simp; ring
    · field_simp; ring

/-- `∑' q, [q prime] log q/(q(q−1))`. -/
noncomputable def sumP : ℝ :=
  ∑' q : ℕ, if q.Prime then Real.log q / ((q : ℝ) * ((q : ℝ) - 1)) else 0

theorem summable_sumP :
    Summable fun q : ℕ => if q.Prime then Real.log q / ((q : ℝ) * ((q : ℝ) - 1)) else 0 := by
  have hs : Summable fun q : ℕ => 4 * (q : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hs
  · split_ifs with hq
    · have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
      exact div_nonneg (Real.log_natCast_nonneg q) (by nlinarith)
    · exact le_rfl
  · split_ifs with hq
    · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
      have hq0 : (0 : ℝ) < q := by linarith
      have hr := Real.rpow_pos_of_pos hq0 ((1 : ℝ) / 2)
      -- `log q ≤ 2 √q`
      have hlog : Real.log q ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 2) := by
        have := Real.log_le_sub_one_of_pos hr
        rw [Real.log_rpow hq0] at this
        linarith
      have e : 4 * (q : ℝ) ^ (-(3 / 2 : ℝ)) = 4 * (q : ℝ) ^ ((1 : ℝ) / 2) / (q * q) := by
        rw [show (-(3 / 2 : ℝ)) = (1 / 2) - 2 by norm_num, Real.rpow_sub hq0, Real.rpow_two]; ring
      rw [e, div_le_div_iff₀ (by nlinarith) (by positivity)]
      have h1 : Real.log q * (q * q) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 2) * (q * q) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      have h2 : 2 * (q : ℝ) ^ ((1 : ℝ) / 2) * (q * q) ≤ 4 * (q : ℝ) ^ ((1 : ℝ) / 2) * ((q : ℝ) * ((q : ℝ) - 1)) := by
        have : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / 2) * q := by positivity
        nlinarith
      linarith
    · positivity

/-- **`∑_a h_d(a) log a = (2φ(d)/d)(log 2 − ∑_p log p/(p(p−1)) − S_d)`.** -/
theorem tsum_hD_log {d : ℕ} (hd : 1 ≤ d) :
    ∑' a, hD d a * Real.log a = 2 * ((Nat.totient d : ℝ) / d) * (Real.log 2 - sumP - SqP d) := by
  have hcomm := Summable.tsum_comm' (summable_Gaq hd) (fun a => (hasSum_Gaq_a d a).summable)
    (fun q => by
      by_cases hq : q.Prime
      · have := (summable_hD_val hd q hq).mul_right (Real.log q)
        simpa [Gaq, hq] using this
      · simpa [Gaq, hq] using summable_zero)
  rw [show (fun a => hD d a * Real.log a) = fun a => ∑' q, Gaq d a q from
    funext fun a => (hasSum_Gaq_a d a).tsum_eq.symm, ← hcomm]
  have hq : ∀ q, ∑' a, Gaq d a q = if q.Prime then
      Real.log q * (S1 d q / S0 d q) * (2 * ((Nat.totient d : ℝ) / d)) else 0 := by
    intro q
    by_cases hqp : q.Prime
    · simp only [Gaq, if_pos hqp]
      rw [tsum_mul_right, tsum_hD_val' hd hqp]; ring
    · simp [Gaq, hqp]
  simp_rw [hq]
  -- the prime sum
  set K := 2 * ((Nat.totient d : ℝ) / d)
  have hsplit : ∀ q : ℕ, (if q.Prime then Real.log q * (S1 d q / S0 d q) * K else 0) =
      K * (-(if q.Prime then Real.log q / ((q : ℝ) * ((q : ℝ) - 1)) else 0)) +
      K * (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
        (if q ∣ d then -(Real.log q / q) else 0)) else 0) := by
    intro q
    by_cases hqp : q.Prime
    · simp only [if_pos hqp]; rw [r_eq hqp]; ring
    · simp [hqp]
  simp_rw [hsplit]
  have hfin : HasSum (fun q : ℕ => (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
      (if q ∣ d then -(Real.log q / q) else 0)) else 0))
      (∑ q ∈ (2 * d).primeFactors, (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
      (if q ∣ d then -(Real.log q / q) else 0)) else 0)) :=
    hasSum_sum_of_ne_finset_zero fun q hq => by
      split_ifs with hqp h2 hqd hqd' <;> try rfl
      · exfalso; subst h2; exact hq (Nat.mem_primeFactors.2 ⟨hqp, dvd_mul_right 2 d, by omega⟩)
      · exfalso; subst h2; exact hq (Nat.mem_primeFactors.2 ⟨hqp, dvd_mul_right 2 d, by omega⟩)
      · exfalso; exact hq (Nat.mem_primeFactors.2 ⟨hqp, hqd'.trans (dvd_mul_left d 2), by omega⟩)
  rw [Summable.tsum_add ((summable_sumP.neg).mul_left K) (hfin.summable.mul_left K),
    tsum_mul_left, tsum_mul_left, tsum_neg, hfin.tsum_eq]
  -- the finite sum is `log 2 − S_d`
  have hfs : ∑ q ∈ (2 * d).primeFactors, (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
      (if q ∣ d then -(Real.log q / q) else 0)) else 0) = Real.log 2 - SqP d := by
    have hpf : (2 * d).primeFactors = insert 2 d.primeFactors := by
      rw [Nat.primeFactors_mul (by norm_num) (by omega), Nat.Prime.primeFactors Nat.prime_two]; rfl
    rw [hpf, SqP]
    by_cases h2d : 2 ∣ d
    · have h2m : 2 ∈ d.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2d, by omega⟩
      rw [insert_eq_of_mem h2m, ← add_sum_erase _ _ h2m, ← add_sum_erase _ _ h2m]
      rw [if_pos Nat.prime_two, if_pos rfl, if_pos h2d]
      have : ∑ q ∈ d.primeFactors.erase 2, (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
          (if q ∣ d then -(Real.log q / q) else 0)) else 0) =
          -∑ q ∈ d.primeFactors.erase 2, Real.log q / q := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun q hq => ?_
        have hq2 := ne_of_mem_erase hq
        have hqm := mem_of_mem_erase hq
        rw [if_pos (Nat.prime_of_mem_primeFactors hqm), if_neg hq2,
          if_pos (Nat.dvd_of_mem_primeFactors hqm)]
      rw [this]; push_cast; ring
    · have h2m : 2 ∉ d.primeFactors := fun h => h2d (Nat.dvd_of_mem_primeFactors h)
      rw [sum_insert h2m, if_pos Nat.prime_two, if_pos rfl, if_neg h2d]
      have : ∑ q ∈ d.primeFactors, (if q.Prime then (if q = 2 then (if q ∣ d then Real.log 2 / 2 else Real.log 2) else
          (if q ∣ d then -(Real.log q / q) else 0)) else 0) =
          -∑ q ∈ d.primeFactors, Real.log q / q := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun q hq => ?_
        have hq2 : q ≠ 2 := fun h => h2m (h ▸ hq)
        rw [if_pos (Nat.prime_of_mem_primeFactors hq), if_neg hq2,
          if_pos (Nat.dvd_of_mem_primeFactors hq)]
      rw [this]; ring
  rw [hfs, sumP]; ring

/-! ### Assembly (without the numerical value of the constant) -/

/-- `c_E = γ + ∑_p log p/(p(p−1))`. -/
noncomputable def cR : ℝ := eulerMascheroniConstant + sumP

theorem f1qP_nonneg (d : ℕ) : 0 ≤ TernaryGoldbach.Prelim.f1qP d := by
  unfold TernaryGoldbach.Prelim.f1qP
  refine prod_nonneg fun p hp => ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  unfold TernaryGoldbach.Prelim.f1pP
  have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  positivity

/-- **[Ram95, Lemma 3.4] with `c = c_E`**: for `d ≥ 1`, `R > 0`,
`|G_d(R) − (φ(d)/d)(log R + c_E + S_d)| ≤ 7.284 R^{−1/3} f₁(d)` (in fact `≤ 7.04 …`). -/
theorem ramare_bound {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    |GqP d R - (Nat.totient d / d) * (Real.log R + cR + SqP d)| ≤
      7.284 * R ^ (-(1 / 3 : ℝ)) * TernaryGoldbach.Prelim.f1qP d := by
  have hE := abs_E_le hd hR
  have hdec := GqP_decomp hd hR
  rw [tsum_hD hd, tsum_hD_log hd] at hdec
  have e : GqP d R - (Nat.totient d / d) * (Real.log R + cR + SqP d) =
      ∑' a, hD d a * Fo (R / a) := by
    rw [hdec, cR, Cg]; ring
  rw [e]
  have h1 : 0 ≤ R ^ (-(1 / 3 : ℝ)) * TernaryGoldbach.Prelim.f1qP d :=
    mul_nonneg (by positivity) (f1qP_nonneg d)
  nlinarith

end TernaryGoldbach.Prelim.RamPf
