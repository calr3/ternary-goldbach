import TernaryGoldbach.MinorArcs.LSQuot3

/-!
# [B, Prop 12.2.4], part 4: large `q`

For `q ≥ 2.2·10¹⁰` and `1 ≤ R < λ(q)`: `log q + 1.039 R ≤ 1.03 (qR)^{2/9}` (`large_q_hS`), so
`regionS` applies. This replaces [B, (12.34)–(12.40)].

* `λ(q)^7 ≤ a⁹ q²` (`a = 1.03/1.2`; `lamQ_pow_le`), from `λ(q)^{1/3} = 7.4527 ∏_{p∣q} g(p)/κ(q)`,
  `g(p) = (p/(p−1)) f₁(p)`, an antitone majorant `ĝ` of `g` and the exchange argument (the `k`
  primes of `q` may be replaced by the first `k` primes, and `q ≥ p₁⋯p_k`):
  for `k ≤ 10` a check at `q = 2.2·10¹⁰`; for `k ≥ 11` induction over primorials, since
  `ĝ(p)^{21} ≤ p²` for `p ≥ 37`.
* then `R^{7/9} ≤ a q^{2/9}`, so `R ≤ a (qR)^{2/9}`, and `log q ≤ (1.03 − 1.039a) q^{2/9}`.
-/

open Real Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `g(p) = (p/(p−1)) f₁(p)`. -/
noncomputable def gp (p : ℕ) : ℝ := (p : ℝ) / (p - 1) * f1p p

/-- An antitone majorant of `g` on the primes. -/
noncomputable def gHatQ (p : ℕ) : ℝ :=
  if p ≤ 3 then 1.39953 else if p ≤ 5 then 1.36194 else if p ≤ 7 then 1.3115 else
  if p ≤ 11 then 1.24148 else if p ≤ 13 then 1.21777 else if p ≤ 17 then 1.18326 else
  if p ≤ 19 then 1.17031 else if p ≤ 23 then 1.14988 else if p ≤ 29 then 1.12806 else
  if p ≤ 31 then 1.12235 else (p : ℝ) / (p - 1) * (1 + (p : ℝ) ^ (-(2 / 3 : ℝ)))

/-- An antitone majorant of `log p/p` on the primes. -/
noncomputable def shat (p : ℕ) : ℝ := if p ≤ 2 then Real.log 3 / 3 else Real.log p / p

/-! ### `f₁(p)` via cube roots -/

theorem f1p_eq {p : ℕ} (hp : 2 ≤ p) :
    f1p p = (1 + 1 / ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 2) /
      (1 + ((p : ℝ) ^ (1 / 3 : ℝ) + ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 2) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have e1 : (p : ℝ) ^ (2 / 3 : ℝ) = ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have e2 : (p : ℝ) ^ (-(2 / 3 : ℝ)) = 1 / ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [Real.rpow_neg hp0.le, e1, inv_eq_one_div]
  unfold f1p; rw [e1, e2]

/-- `f₁(p) ≤ (1 + 1/u²)/(1 + (u + u²)/(p(p−1)))` for `0 < u`, `u³ ≤ p`. -/
theorem f1p_le_of {p : ℕ} (hp : 2 ≤ p) {u : ℝ} (hu0 : 0 < u) (hu : u ^ 3 ≤ p) :
    f1p p ≤ (1 + 1 / u ^ 2) / (1 + (u + u ^ 2) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set v := (p : ℝ) ^ (1 / 3 : ℝ)
  have huv : u ≤ v := by
    calc u = (u ^ 3) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
      _ ≤ v := Real.rpow_le_rpow (by positivity) hu (by norm_num)
  have hv0 : 0 < v := by linarith
  rw [f1p_eq hp]
  have hpp : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  apply div_le_div₀ (by positivity)
  · have : 1 / v ^ 2 ≤ 1 / u ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith
  · positivity
  · have : u + u ^ 2 ≤ v + v ^ 2 := by nlinarith
    have := div_le_div_of_nonneg_right this hpp.le
    linarith

/-- `f₁(p) ≤ 1 + p^{−2/3}`. -/
theorem f1p_le_one_add {p : ℕ} (hp : 2 ≤ p) : f1p p ≤ 1 + (p : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold f1p
  apply div_le_self (by positivity)
  have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  have : 0 ≤ ((p : ℝ) ^ (1 / 3 : ℝ) + (p : ℝ) ^ (2 / 3 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    positivity
  linarith

/-! ### `ĝ` -/

theorem ghat_of_gt {p : ℕ} (hp : 31 < p) :
    gHatQ p = (p : ℝ) / (p - 1) * (1 + (p : ℝ) ^ (-(2 / 3 : ℝ))) := by
  unfold gHatQ
  repeat rw [if_neg (by omega)]

theorem gp_le_ghat {p : ℕ} (hp : p.Prime) : gp p ≤ gHatQ p := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge 31 p with h | h
  · -- `p > 31`
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    rw [ghat_of_gt h]; unfold gp
    exact mul_le_mul_of_nonneg_left (f1p_le_one_add hp2) (div_nonneg (by linarith) (by linarith))
  · -- `p ≤ 31`: the explicit values
    have key : ∀ (u : ℝ), 0 < u → u ^ 3 ≤ p → ∀ (U : ℝ),
        (p : ℝ) / (p - 1) * ((1 + 1 / u ^ 2) / (1 + (u + u ^ 2) / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ U →
        gp p ≤ U := by
      intro u hu0 hu U hU
      have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      unfold gp
      exact (mul_le_mul_of_nonneg_left (f1p_le_of hp2 hu0 hu)
        (div_nonneg (by linarith) (by linarith))).trans hU
    interval_cases p
    all_goals first
      | (exfalso; revert hp; decide)
      | skip
    · exact (key 1.259921 (by norm_num) (by norm_num) 1.39953 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 1.442249 (by norm_num) (by norm_num) 1.39953 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 1.709975 (by norm_num) (by norm_num) 1.36194 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 1.912931 (by norm_num) (by norm_num) 1.3115 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 2.223980 (by norm_num) (by norm_num) 1.24148 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 2.351334 (by norm_num) (by norm_num) 1.21777 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 2.571281 (by norm_num) (by norm_num) 1.18326 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 2.668401 (by norm_num) (by norm_num) 1.17031 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 2.843866 (by norm_num) (by norm_num) 1.14988 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 3.072316 (by norm_num) (by norm_num) 1.12806 (by norm_num)).trans (by norm_num [gHatQ])
    · exact (key 3.141380 (by norm_num) (by norm_num) 1.12235 (by norm_num)).trans (by norm_num [gHatQ])

/-- `ĝ(p) ≤ 1.1208` for `p ≥ 37`. -/
theorem ghat_tail_le {p : ℕ} (hp : 37 ≤ p) :
    (p : ℝ) / (p - 1) * (1 + (p : ℝ) ^ (-(2 / 3 : ℝ))) ≤ 1.1208 := by
  have hp' : (37 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) / (p - 1) ≤ 37 / 36 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 : (p : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.0905 := by
    have h37 : (11.06 : ℝ) ≤ (37 : ℝ) ^ (2 / 3 : ℝ) := by
      calc (11.06 : ℝ) = ((11.06 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ ((37 : ℝ) ^ (2 : ℕ)) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = (37 : ℝ) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have : (37 : ℝ) ^ (2 / 3 : ℝ) ≤ (p : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hp' (by norm_num)
    rw [Real.rpow_neg (by linarith), ← one_div]
    calc 1 / (p : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 11.06 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ ≤ 0.0905 := by norm_num
  have h0 : 0 ≤ (p : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  calc (p : ℝ) / (p - 1) * (1 + (p : ℝ) ^ (-(2 / 3 : ℝ))) ≤ 37 / 36 * (1 + 0.0905) :=
        mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
    _ ≤ 1.1208 := by norm_num

theorem ghat_tail_anti {a b : ℕ} (hb : 37 ≤ b) (hab : b ≤ a) :
    (a : ℝ) / (a - 1) * (1 + (a : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      (b : ℝ) / (b - 1) * (1 + (b : ℝ) ^ (-(2 / 3 : ℝ))) := by
  have hb' : (37 : ℝ) ≤ b := by exact_mod_cast hb
  have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
  have h1 := TernaryGoldbach.Prelim.frac_anti (by omega : 2 ≤ b) hab
  have h2 : (a : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (b : ℝ) ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hab' (by norm_num)
  exact mul_le_mul h1 (by linarith) (by positivity) (div_nonneg (by linarith) (by linarith))

theorem one_le_ghat (p : ℕ) : 1 ≤ gHatQ p := by
  unfold gHatQ
  split_ifs <;> try norm_num
  rename_i h
  have hp : (31 : ℝ) < p := by exact_mod_cast (by omega : 31 < p)
  have h1 : 1 ≤ (p : ℝ) / (p - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : (0 : ℝ) ≤ (p : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  nlinarith

set_option maxHeartbeats 2000000 in
theorem ghat_anti {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : b ≤ a) : gHatQ a ≤ gHatQ b := by
  rcases Nat.lt_or_ge 31 b with hb31 | hb31
  · -- both `> 31`, so both `≥ 37`
    have hb37 : 37 ≤ b := by
      by_contra h; interval_cases b <;> norm_num at hb
    have ha31 : 31 < a := by omega
    rw [ghat_of_gt ha31, ghat_of_gt hb31]
    exact ghat_tail_anti hb37 hab
  · rcases Nat.lt_or_ge 31 a with ha31 | ha31
    · -- `b ≤ 31 < a`
      have ha37 : 37 ≤ a := by
        by_contra h; interval_cases a <;> norm_num at ha
      have h1 : gHatQ a ≤ 1.1208 := by
        rw [ghat_of_gt ha31]; exact ghat_tail_le ha37
      have h2 : 1.12235 ≤ gHatQ b := by
        unfold gHatQ; split_ifs <;> norm_num
      linarith
    · unfold gHatQ
      split_ifs <;> first | omega | norm_num


/-! ### `ŝ` -/

theorem shat_nonneg (p : ℕ) : 0 ≤ shat p := by
  unfold shat
  split_ifs
  · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem le_shat {p : ℕ} (hp : p.Prime) : Real.log p / p ≤ shat p := by
  unfold shat
  split_ifs with h
  · have hp2 : p = 2 := le_antisymm h hp.two_le
    subst hp2
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : Real.log 8 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have e9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    push_cast; linarith
  · exact le_rfl

theorem log_div_anti {a b : ℝ} (hb : 3 ≤ b) (hab : b ≤ a) : Real.log a / a ≤ Real.log b / b := by
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 (he.trans hb))
    (Set.mem_Ici.2 (he.trans (hb.trans hab))) hab

theorem shat_anti {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : b ≤ a) : shat a ≤ shat b := by
  unfold shat
  split_ifs with h1 h2 h2
  · exact le_rfl
  · omega
  · have : (3 : ℝ) ≤ a := by exact_mod_cast (by have := ha.two_le; omega : 3 ≤ a)
    exact log_div_anti (le_refl 3) this |>.trans (by push_cast; exact le_rfl)
  · have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast (by have := hb.two_le; omega : 3 ≤ b)
    exact log_div_anti hb3 (by exact_mod_cast hab)

/-! ### The exchange argument -/

theorem exch_gen (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hanti : ∀ a b : ℕ, a.Prime → b.Prime → b ≤ a → f a ≤ f b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, f p ≤ ∏ i ∈ range P.card, f (Nat.nth Nat.Prime i) ∧
      ∑ p ∈ P, f p ≤ ∑ i ∈ range P.card, f (Nat.nth Nat.Prime i) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hP a (mem_insert_self a s)
    have ih := ih (fun p hp => hP p (mem_insert_of_mem hp))
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcount : s.card < Nat.count Nat.Prime (a + 1) := by
      rw [Nat.count_eq_card_filter_range]
      have : insert a s ⊆ (range (a + 1)).filter (fun x => Nat.Prime x) := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨mem_range.2 (by omega), ha⟩
        · exact mem_filter.2 ⟨mem_range.2 (by have := hlt x hx; omega),
            hP x (mem_insert_of_mem hx)⟩
      have := card_le_card this
      rw [card_insert_of_notMem has] at this
      omega
    have hnth : Nat.nth Nat.Prime s.card ≤ a := by
      have := Nat.nth_lt_of_lt_count hcount; omega
    have h1 := hanti a _ ha (Nat.prime_nth_prime _) hnth
    rw [card_insert_of_notMem has, prod_insert has, sum_insert has, prod_range_succ, sum_range_succ]
    constructor
    · rw [mul_comm]
      exact mul_le_mul ih.1 h1 (hf0 _) (prod_nonneg fun _ _ => hf0 _)
    · linarith [ih.2]

/-! ### `λ(q)` via the first `k` primes -/

noncomputable def Gk (k : ℕ) : ℝ := ∏ i ∈ range k, gHatQ (Nat.nth Nat.Prime i)
noncomputable def Sk (k : ℕ) : ℝ := ∑ i ∈ range k, shat (Nat.nth Nat.Prime i)
noncomputable def primk (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i
noncomputable def kapk (k : ℕ) (x : ℝ) : ℝ := 0.3726 * (Real.log x - Sk k) + 0.0274177

theorem qphi_f1q_eq {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / Nat.totient q * f1q q = ∏ p ∈ q.primeFactors, gp p := by
  rw [TernaryGoldbach.Prelim.div_totient_eq_prod hq, f1q, ← prod_mul_distrib]; rfl

/-- `λ(q) ≤ (7.4527 G_k/κ_k(q))³`, `k = ω(q)`, and `p₁⋯p_k ≤ q`. -/
theorem lamQ_le_k {q : ℕ} (hq : 1 ≤ q) (hκ : 0 < kapk q.primeFactors.card q) :
    lamQ q ≤ (7.4527 * Gk q.primeFactors.card / kapk q.primeFactors.card q) ^ 3 ∧
      (primk q.primeFactors.card : ℝ) ≤ q := by
  set P := q.primeFactors
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hg := (exch_gen gHatQ (fun n => by linarith [one_le_ghat n])
    (fun a b ha hb hab => ghat_anti ha hb hab) P hPp).1
  have hs := (exch_gen shat shat_nonneg (fun a b ha hb hab => shat_anti ha hb hab) P hPp).2
  have hG : ∏ p ∈ P, gp p ≤ Gk P.card :=
    (prod_le_prod₀ (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      unfold gp; have := f1p_pos p
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) this.le)
      fun p hp => gp_le_ghat (hPp p hp)).trans hg
  have hS : Sq q ≤ Sk P.card := (sum_le_sum fun p hp => le_shat (hPp p hp)).trans hs
  have hkap : kapk P.card q ≤ kapQ q := by unfold kapk kapQ; linarith
  have hX0 : 0 ≤ ∏ p ∈ P, gp p := by
    rw [← qphi_f1q_eq hq]; exact (mul_pos (qphi_pos hq) (f1q_pos q)).le
  constructor
  · unfold lamQ
    rw [show (q : ℝ) / Nat.totient q * 7.4527 * f1q q = 7.4527 * ((q : ℝ) / Nat.totient q * f1q q)
      by ring, qphi_f1q_eq hq]
    apply pow_le_pow_left₀ (div_nonneg (mul_nonneg (by norm_num) hX0)
      (by linarith [kapQ_pos hq]))
    exact div_le_div₀ (by have := le_trans hX0 hG; positivity) (by linarith) hκ hkap
  · have h2 := (TernaryGoldbach.Prelim.exch P hPp).2
    have h3 : ∏ p ∈ P, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
    unfold primk; exact_mod_cast h2.trans h3

/-! ### The first primes -/

theorem nth_prime_of_count {p i : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = i) :
    Nat.nth Nat.Prime i = p := hc ▸ Nat.nth_count hp

theorem nth_primes :
    Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3 ∧ Nat.nth Nat.Prime 2 = 5 ∧
    Nat.nth Nat.Prime 3 = 7 ∧ Nat.nth Nat.Prime 4 = 11 ∧ Nat.nth Nat.Prime 5 = 13 ∧
    Nat.nth Nat.Prime 6 = 17 ∧ Nat.nth Nat.Prime 7 = 19 ∧ Nat.nth Nat.Prime 8 = 23 ∧
    Nat.nth Nat.Prime 9 = 29 ∧ Nat.nth Nat.Prime 10 = 31 ∧ Nat.nth Nat.Prime 11 = 37 := by
  refine ⟨nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide),
    nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide),
    nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide),
    nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide),
    nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide),
    nth_prime_of_count (by norm_num) (by decide), nth_prime_of_count (by norm_num) (by decide)⟩

end TernaryGoldbach.MinorArcs
