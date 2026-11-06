import TernaryGoldbach.MinorArcs.LSQuot8g

/-!
# [H, Prop 12.2.4] with `c₊ = 2`, part 5: `n ≤ 3`

For `n ≤ 3`, `G_q(n)` depends only on whether `2 ∣ q` and `3 ∣ q`, and `log sq ≥ log(10⁵/(n + 1))`.
Write the primes of `q` as `{2, 3} ∩ P` and `P'` (primes `≥ 5`, `k = |P'| ≤ 8`). By the exchange
argument applied to `P' ∪ {2, 3}`, the products over `P'` are at most those over the `k` primes
`5, 7, 11, …`, and `∏_{P'} p` is at least their product. A finite rational check (`smallOK`)
finishes.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-- `G_q(n)` for `n ≤ 3`. -/
def Gsm (n : ℕ) (d2 d3 : Bool) : ℚ :=
  1 + (if 2 ≤ n ∧ d2 = false then 1 else 0) + (if 3 ≤ n ∧ d3 = false then 1 / 2 else 0)

theorem gf_one' : gf 1 = 1 := by simp [gf]

theorem Gq_small {q n : ℕ} (hn1 : 1 ≤ n) (hn3 : n ≤ 3) :
    Gq q n = (Gsm n (decide (2 ∣ q)) (decide (3 ∣ q)) : ℝ) := by
  rw [Gq_eq, Nat.floor_natCast]
  have c2 : Nat.Coprime 2 q ↔ ¬ 2 ∣ q := Nat.Prime.coprime_iff_not_dvd Nat.prime_two
  have c3 : Nat.Coprime 3 q ↔ ¬ 3 ∣ q := Nat.Prime.coprime_iff_not_dvd Nat.prime_three
  have g2 : gf 2 = 1 := by rw [gf_prime Nat.prime_two]; norm_num
  have g3 : gf 3 = 1 / 2 := by rw [gf_prime Nat.prime_three]; norm_num
  interval_cases n
  · rw [show Icc 1 1 = {1} by rfl, filter_singleton, if_pos (Nat.coprime_one_left q)]
    simp [Gsm, gf_one']
  · rw [show Icc 1 2 = {1, 2} by rfl, filter_insert, filter_singleton, if_pos (Nat.coprime_one_left q)]
    by_cases h2 : 2 ∣ q
    · rw [if_neg (fun h => (c2.1 h) h2)]; simp [Gsm, gf_one', h2]
    · rw [if_pos (c2.2 h2)]; simp [Gsm, gf_one', g2, h2]
  · rw [show Icc 1 3 = {1, 2, 3} by rfl, filter_insert, filter_insert, filter_singleton,
      if_pos (Nat.coprime_one_left q)]
    by_cases h2 : 2 ∣ q <;> by_cases h3 : 3 ∣ q
    · rw [if_neg (fun h => (c2.1 h) h2), if_neg (fun h => (c3.1 h) h3)]; simp [Gsm, gf_one', h2, h3]
    · rw [if_neg (fun h => (c2.1 h) h2), if_pos (c3.2 h3)]; simp [Gsm, gf_one', g3, h2, h3]
    · rw [if_pos (c2.2 h2), if_neg (fun h => (c3.1 h) h3)]; simp [Gsm, gf_one', g2, h2, h3]
    · rw [if_pos (c2.2 h2), if_pos (c3.2 h3)]
      simp [Gsm, gf_one', g2, g3, h2, h3]; norm_num

/-! ### The primes of `q` below `5` -/

theorem mem_low {q p : ℕ} (hq : q ≠ 0) :
    p ∈ q.primeFactors.filter (· < 5) ↔ (p = 2 ∧ 2 ∣ q) ∨ (p = 3 ∧ 3 ∣ q) := by
  rw [mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hpq, -⟩, h5⟩
    have := hp.two_le
    interval_cases p
    · exact Or.inl ⟨rfl, hpq⟩
    · exact Or.inr ⟨rfl, hpq⟩
    · exact absurd hp (by decide)
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨⟨Nat.prime_two, h, hq⟩, by norm_num⟩
    · exact ⟨⟨Nat.prime_three, h, hq⟩, by norm_num⟩

theorem low_subset {q : ℕ} (hq : q ≠ 0) : q.primeFactors.filter (· < 5) ⊆ {2, 3} := by
  intro p hp
  rcases (mem_low hq).1 hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- A product over the primes of `q` below `5`. -/
theorem prod_low {q : ℕ} (hq : q ≠ 0) (f : ℕ → ℝ) :
    ∏ p ∈ q.primeFactors.filter (· < 5), f p =
      (if 2 ∣ q then f 2 else 1) * (if 3 ∣ q then f 3 else 1) := by
  rw [← inter_eq_right.2 (low_subset hq), ← prod_ite_mem, prod_insert (by decide), prod_singleton]
  congr 1
  · by_cases h : 2 ∣ q
    · rw [if_pos ((mem_low hq).2 (Or.inl ⟨rfl, h⟩)), if_pos h]
    · rw [if_neg (fun hm => by rcases (mem_low hq).1 hm with ⟨-, h'⟩ | ⟨h3, -⟩ <;> omega), if_neg h]
  · by_cases h : 3 ∣ q
    · rw [if_pos ((mem_low hq).2 (Or.inr ⟨rfl, h⟩)), if_pos h]
    · rw [if_neg (fun hm => by rcases (mem_low hq).1 hm with ⟨h2, -⟩ | ⟨-, h'⟩ <;> omega), if_neg h]

theorem sum_low {q : ℕ} (hq : q ≠ 0) (f : ℕ → ℝ) :
    ∑ p ∈ q.primeFactors.filter (· < 5), f p =
      (if 2 ∣ q then f 2 else 0) + (if 3 ∣ q then f 3 else 0) := by
  rw [← inter_eq_right.2 (low_subset hq), ← sum_ite_mem, sum_insert (by decide), sum_singleton]
  congr 1
  · by_cases h : 2 ∣ q
    · rw [if_pos ((mem_low hq).2 (Or.inl ⟨rfl, h⟩)), if_pos h]
    · rw [if_neg (fun hm => by rcases (mem_low hq).1 hm with ⟨-, h'⟩ | ⟨h3, -⟩ <;> omega), if_neg h]
  · by_cases h : 3 ∣ q
    · rw [if_pos ((mem_low hq).2 (Or.inr ⟨rfl, h⟩)), if_pos h]
    · rw [if_neg (fun hm => by rcases (mem_low hq).1 hm with ⟨h2, -⟩ | ⟨-, h'⟩ <;> omega), if_neg h]

/-! ### The primes `≥ 5`: shifted exchange -/

/-- The primes of `q` that are `≥ 5`. -/
def highP (q : ℕ) : Finset ℕ := q.primeFactors.filter (fun p => ¬ p < 5)

theorem high_prime {q p : ℕ} (hp : p ∈ highP q) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1

theorem high_ge5 {q p : ℕ} (hp : p ∈ highP q) : 5 ≤ p := by
  have := (mem_filter.1 hp).2; omega

theorem disj_high (q : ℕ) : Disjoint (highP q) {2, 3} := by
  rw [disjoint_left]; intro p hp h23
  have := high_ge5 hp
  simp only [mem_insert, mem_singleton] at h23; omega

theorem card_T (q : ℕ) : (highP q ∪ {2, 3}).card = (highP q).card + 2 := by
  rw [card_union_of_disjoint (disj_high q)]; rfl

theorem T_prime (q : ℕ) : ∀ p ∈ highP q ∪ {2, 3}, p.Prime := by
  intro p hp
  rcases mem_union.1 hp with h | h
  · exact high_prime h
  · simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

theorem nth01 : Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3 := by
  obtain ⟨h0, h1, -⟩ := nth_primes; exact ⟨h0, h1⟩

/-- The shifted exchange: for `f` antitone and positive on the primes,
`∏_{P'} f ≤ ∏_{i < k} f(p_{i+2})`. -/
theorem exch_high (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (h23 : 0 < f 2 * f 3)
    (hanti : ∀ a b : ℕ, a.Prime → b.Prime → b ≤ a → f a ≤ f b) (q : ℕ) :
    ∏ p ∈ highP q, f p ≤ ∏ x ∈ range (highP q).card, f (Nat.nth Nat.Prime (2 + x)) := by
  have h := (exch_gen f hf0 hanti _ (T_prime q)).1
  rw [card_T, add_comm, prod_range_add, prod_union (disj_high q), prod_insert (by decide),
    prod_singleton, prod_range_succ, prod_range_one, nth01.1, nth01.2] at h
  rw [mul_comm (f 2 * f 3)] at h
  exact le_of_mul_le_mul_right h h23

theorem exch_high_nat (q : ℕ) :
    ∏ x ∈ range (highP q).card, Nat.nth Nat.Prime (2 + x) ≤ ∏ p ∈ highP q, p := by
  have h := (TernaryGoldbach.Prelim.exch _ (T_prime q)).2
  rw [card_T, add_comm, prod_range_add, prod_union (disj_high q), prod_insert (by decide),
    prod_singleton, prod_range_succ, prod_range_one, nth01.1, nth01.2] at h
  omega

theorem ratio_anti : ∀ a b : ℕ, a.Prime → b.Prime → b ≤ a →
    (a : ℝ) / (a - 1) ≤ (b : ℝ) / (b - 1) := by
  intro a b ha hb hab
  have ha1 : (1 : ℝ) < a := by exact_mod_cast ha.one_lt
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb.one_lt
  have : (b : ℝ) ≤ a := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem high_card_le {q : ℕ} (hq1 : 1 ≤ q) (hq : q < 22000000000) : (highP q).card ≤ 8 := by
  by_contra h
  push Not at h
  have h1 := exch_high_nat q
  have h2 : ∏ p ∈ highP q, p ≤ q := by
    refine Nat.le_of_dvd (by omega) ((prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans ?_)
    exact Nat.prod_primeFactors_dvd q
  have h3 : ∏ x ∈ range 9, Nat.nth Nat.Prime (2 + x) ≤ ∏ x ∈ range (highP q).card,
      Nat.nth Nat.Prime (2 + x) :=
    prod_le_prod_of_subset_of_one_le (range_subset_range.2 h)
      (fun i _ _ => (Nat.prime_nth_prime _).one_lt.le)
  obtain ⟨-, -, h2', h3', h4', h5', h6', h7', h8', h9', h10', -⟩ := nth_primes
  simp only [prod_range_succ, range_zero, prod_empty, h2', h3', h4', h5', h6', h7', h8', h9', h10',
    show 2 + 0 = 2 from rfl] at h3
  norm_num at h3
  omega

/-! ### Tables for `5, 7, …, 29` -/

def primes5 : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29]

theorem prod_first5 (f : ℕ → ℝ) {k : ℕ} (hk : k ≤ 8) :
    ∏ x ∈ range k, f (Nat.nth Nat.Prime (2 + x)) = ((primes5.take k).map f).prod := by
  obtain ⟨-, -, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := nth_primes
  interval_cases k <;>
    simp [prod_range_succ, primes5, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

theorem prod_first5_nat {k : ℕ} (hk : k ≤ 8) :
    ∏ x ∈ range k, Nat.nth Nat.Prime (2 + x) = (primes5.take k).prod := by
  obtain ⟨-, -, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := nth_primes
  interval_cases k <;> simp [prod_range_succ, primes5, h2, h3, h4, h5, h6, h7, h8, h9]

/-- `gHatQ` on `5, …, 29`. -/
def ghQ (p : ℕ) : ℚ :=
  if p ≤ 5 then 1.36194 else if p ≤ 7 then 1.3115 else if p ≤ 11 then 1.24148 else
  if p ≤ 13 then 1.21777 else if p ≤ 17 then 1.18326 else if p ≤ 19 then 1.17031 else
  if p ≤ 23 then 1.14988 else 1.12806

/-- Lower bounds for `log p`, `p ∈ {5, …, 29}`. -/
def lp5Q (p : ℕ) : ℚ :=
  if p = 5 then 1.609437 else if p = 7 then 1.945909 else if p = 11 then 2.397895 else
  if p = 13 then 2.564949 else if p = 17 then 2.833212 else if p = 19 then 2.944438 else
  if p = 23 then 3.135494 else if p = 29 then 3.367295 else 0

theorem ghQ_eq {p : ℕ} (hp : p ∈ primes5) : gHatQ p = (ghQ p : ℝ) := by
  simp only [primes5, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [gHatQ, ghQ]

theorem lp5Q_le {p : ℕ} (hp : p ∈ primes5) : (lp5Q p : ℝ) ≤ Real.log p := by
  have u := fun (z : ℝ) (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : 2.7182818286 ^ n * (taylor6 f + f ^ 7 / 4410) ≤ z) => le_log_num (z := z) n f h0 h1 h
  simp only [primes5, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := u 5 1 0.609437 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 7 1 0.945909 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 11 2 0.397895 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 13 2 0.564949 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 17 2 0.833212 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 19 2 0.944438 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 23 3 0.135494 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith
  · have := u 29 3 0.367295 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num [lp5Q]; push_cast at this; linarith

/-! ### The finite check -/

def Mq (k : ℕ) : ℚ := ((primes5.take k).map (fun p : ℕ => (p : ℚ) / ((p : ℚ) - 1))).prod
def Nq (k : ℕ) : ℚ := ((primes5.take k).map ghQ).prod
def Lq5 (k : ℕ) : ℚ := ((primes5.take k).map lp5Q).sum

/-- `n^{1/3}` from below, `log n` from below, `log(10⁵/(n + 1))` from below. -/
def n3Q (n : ℕ) : ℚ := if n = 1 then 1 else if n = 2 then 1.2599 else 1.4422
def lnQ (n : ℕ) : ℚ := if n = 1 then 0 else if n = 2 then 0.693146 else 1.098612
def ellQ (n : ℕ) : ℚ := if n = 1 then 10.819777 else if n = 2 then 10.414313 else 10.126631

def smallQ (n : ℕ) (d2 d3 : Bool) (k : ℕ) : ℚ :=
  let K23 : ℚ := (if d2 then 2 else 1) * (if d3 then 3 / 2 else 1)
  let Z23 : ℚ := (if d2 then 2 * fupQ 2 else 1) * (if d3 then 3 / 2 * fupQ 3 else 1)
  let S23 : ℚ := (if d2 then 0.693146 / 2 else 0) + (if d3 then 1.098612 / 3 else 0)
  let L23 : ℚ := (if d2 then 0.693146 else 0) + (if d3 then 1.098612 else 0)
  K23 * Mq k * Gsm n d2 d3 + 0.1768 * Z23 * Nq k / n3Q n - lnQ n - 1.3325822 - 0.6586 * S23 -
    0.3414 * max (ellQ n) (L23 + Lq5 k) - 0.6674177

theorem smallOK : ∀ n ∈ ({1, 2, 3} : Finset ℕ), ∀ d2 d3 : Bool, ∀ k ∈ range 9,
    smallQ n d2 d3 k ≤ 0 := by decide +kernel

/-! ### Lists -/

theorem list_cast_prod (l : List ℕ) (g : ℕ → ℚ) :
    (((l.map g).prod : ℚ) : ℝ) = (l.map (fun p => (g p : ℝ))).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem list_cast_sum (l : List ℕ) (g : ℕ → ℚ) :
    (((l.map g).sum : ℚ) : ℝ) = (l.map (fun p => (g p : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem take_sub (k : ℕ) : ∀ p ∈ primes5.take k, p ∈ primes5 := fun p hp => List.mem_of_mem_take hp

theorem Lq5_le (k : ℕ) : (Lq5 k : ℝ) ≤ Real.log ((primes5.take k).prod : ℕ) := by
  rw [Lq5, list_cast_sum]
  have : ∀ l : List ℕ, (∀ p ∈ l, p ∈ primes5) →
      (l.map (fun p => (lp5Q p : ℝ))).sum ≤ Real.log (l.prod : ℕ) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha := h a (List.mem_cons_self ..)
      have hpos : ∀ p ∈ a :: t, 0 < p := fun p hp => by
        have := h p hp
        simp only [primes5, List.mem_cons, List.not_mem_nil, or_false] at this; omega
      have ht0' : 0 < t.prod := List.prod_pos fun p hp => hpos p (List.mem_cons_of_mem _ hp)
      have ht0 : (0 : ℝ) < ((t.prod : ℕ) : ℝ) := by exact_mod_cast ht0'
      have ha0 : (0 : ℝ) < a := by exact_mod_cast hpos a (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons, List.prod_cons, Nat.cast_mul]
      rw [Real.log_mul ha0.ne' ht0.ne']
      have := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      linarith [lp5Q_le ha]
  exact this _ (take_sub k)

/-! ### `n ≤ 3` -/

set_option maxHeartbeats 1000000 in
/-- **`Φ(q, n, max(log q, log(10⁵/(n+1)))) ≤ 0`** for `n ≤ 3`, `q < 2.2·10¹⁰`. -/
theorem Phi2_small {q n : ℕ} (hq1 : 1 ≤ q) (hq : q < 22000000000) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) :
    Phi2 q n (max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1)))) ≤ 0 := by
  have hq0 : q ≠ 0 := by omega
  set k := (highP q).card with hkdef
  have hk := high_card_le hq1 hq
  have hS := smallOK n (by simp; omega) (decide (2 ∣ q)) (decide (3 ∣ q)) k
    (mem_range.2 (by omega))
  have hS' : ((smallQ n (decide (2 ∣ q)) (decide (3 ∣ q)) k : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hS
  set P := q.primeFactors
  have hsplit : ∀ f : ℕ → ℝ, ∏ p ∈ P, f p =
      (∏ p ∈ P.filter (· < 5), f p) * ∏ p ∈ highP q, f p := fun f =>
    (prod_filter_mul_prod_filter_not P (· < 5) f).symm
  -- `K`
  have hK : (q : ℝ) / Nat.totient q = ((if 2 ∣ q then (2 : ℝ) else 1) * (if 3 ∣ q then 3 / 2 else 1)) *
      ∏ p ∈ highP q, ((p : ℝ) / (p - 1)) := by
    rw [TernaryGoldbach.Prelim.div_totient_eq_prod hq1, hsplit, prod_low hq0]; norm_num
  have hKh : ∏ p ∈ highP q, ((p : ℝ) / (p - 1)) ≤ (Mq k : ℝ) := by
    refine (exch_high (fun p => (p : ℝ) / (p - 1)) (fun n => ?_) (by norm_num) ratio_anti q).trans
      (le_of_eq ?_)
    · rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> simp
      · have : (2 : ℝ) ≤ n := by exact_mod_cast h
        exact div_nonneg (by linarith) (by linarith)
    · have e := prod_first5 (fun p : ℕ => (p : ℝ) / (p - 1)) hk
      rw [e, Mq, list_cast_prod]
      congr 1
      exact List.map_congr_left fun p _ => by push_cast; rfl
  have hKh0 : 0 ≤ ∏ p ∈ highP q, ((p : ℝ) / (p - 1)) := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (high_prime hp).two_le
    exact div_nonneg (by linarith) (by linarith)
  -- `K f₁`
  have hKF : (q : ℝ) / Nat.totient q * f1q q = ((if 2 ∣ q then gp 2 else 1) * (if 3 ∣ q then gp 3 else 1)) *
      ∏ p ∈ highP q, gp p := by
    rw [qphi_f1q_eq hq1, hsplit, prod_low hq0]
  have hgp0 : ∀ n, 0 ≤ gp n := fun n => by
    unfold gp
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have : (2 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (f1p_pos n).le
  have hFh : ∏ p ∈ highP q, gp p ≤ (Nq k : ℝ) := by
    have h1 : ∏ p ∈ highP q, gp p ≤ ∏ p ∈ highP q, gHatQ p :=
      prod_le_prod₀ (fun p _ => hgp0 p) fun p hp => gp_le_ghat (high_prime hp)
    refine h1.trans ((exch_high gHatQ (fun n => by linarith [one_le_ghat n])
      (by nlinarith [one_le_ghat 2, one_le_ghat 3]) (fun a b ha hb hab => ghat_anti ha hb hab) q).trans
      (le_of_eq ?_))
    rw [prod_first5 _ hk, Nq, list_cast_prod]
    congr 1
    exact List.map_congr_left fun p hp => ghQ_eq (take_sub k p hp)
  have hFh0 : 0 ≤ ∏ p ∈ highP q, gp p := prod_nonneg fun p _ => hgp0 p
  have g2 : gp 2 ≤ 2 * (fupQ 2 : ℝ) := by
    have := f1p_le_fupQ (p := 2) (Or.inl rfl); unfold gp; norm_num; linarith
  have g3 : gp 3 ≤ 3 / 2 * (fupQ 3 : ℝ) := by
    have := f1p_le_fupQ (p := 3) (Or.inr (Or.inl rfl)); unfold gp; norm_num; linarith
  -- `S`
  have hSq : Sq q = ((if 2 ∣ q then Real.log 2 / 2 else 0) + (if 3 ∣ q then Real.log 3 / 3 else 0)) +
      ∑ p ∈ highP q, Real.log p / p := by
    unfold Sq
    rw [← sum_filter_add_sum_filter_not P (· < 5), sum_low hq0]; simp only [Nat.cast_ofNat]; rfl
  have hSh : 0 ≤ ∑ p ∈ highP q, Real.log p / p := sum_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (high_prime hp).one_lt.le
    exact div_nonneg (Real.log_nonneg this) (by linarith)
  have l2 := lpQ_le (p := 2) (Or.inl rfl)
  have l3 := lpQ_le (p := 3) (Or.inr (Or.inl rfl))
  have e2 : (lpQ 2 : ℝ) = 0.693146 := by norm_num [lpQ]
  have e3 : (lpQ 3 : ℝ) = 1.098612 := by norm_num [lpQ]
  rw [e2] at l2; rw [e3] at l3
  -- `log q`
  have hlq : Real.log ((if 2 ∣ q then (2 : ℝ) else 1) * (if 3 ∣ q then 3 else 1)) +
      (Lq5 k : ℝ) ≤ Real.log q := by
    set A : ℝ := (if 2 ∣ q then (2 : ℝ) else 1) * (if 3 ∣ q then 3 else 1)
    set B : ℝ := (((primes5.take k).prod : ℕ) : ℝ)
    have h1 : (primes5.take k).prod ≤ ∏ p ∈ highP q, p := by
      rw [← prod_first5_nat hk]; exact exch_high_nat q
    have h1' : B ≤ ∏ p ∈ highP q, (p : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 h1; rw [Nat.cast_prod] at this; exact this
    have hP : ∏ p ∈ P, (p : ℝ) ≤ q := by
      have := (Nat.cast_le (α := ℝ)).2 (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
      rw [Nat.cast_prod] at this; exact this
    rw [hsplit, prod_low hq0] at hP
    simp only [Nat.cast_ofNat] at hP
    have hA0 : (0 : ℝ) < A := by simp only [A]; split_ifs <;> norm_num
    have hB0 : (0 : ℝ) < B := by
      have : 0 < (primes5.take k).prod := List.prod_pos fun p hp => by
        have := take_sub k p hp
        simp only [primes5, List.mem_cons, List.not_mem_nil, or_false] at this; omega
      simp only [B]; exact_mod_cast this
    have h2 : A * B ≤ q := by
      have := mul_le_mul_of_nonneg_left h1' hA0.le
      linarith
    have hLB := Lq5_le k
    have := Real.log_le_log (mul_pos hA0 hB0) h2
    rw [Real.log_mul hA0.ne' hB0.ne'] at this
    linarith
  -- `n`
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn3' : (n3Q n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) ∧ (lnQ n : ℝ) ≤ Real.log n ∧
      (ellQ n : ℝ) ≤ Real.log (1e5 / ((n : ℝ) + 1)) := by
    have u := fun (z : ℝ) (m : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
      (h : 2.7182818286 ^ m * (taylor6 f + f ^ 7 / 4410) ≤ z) => le_log_num (z := z) m f h0 h1 h
    have cube : ∀ (v : ℝ) (m : ℝ), 0 ≤ v → v ^ 3 ≤ m → v ≤ m ^ (1 / 3 : ℝ) := by
      intro v m hv hm
      calc v = (v ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hv]; norm_num
        _ ≤ m ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hm (by norm_num)
    interval_cases n
    · refine ⟨by norm_num [n3Q], by norm_num [lnQ], ?_⟩
      have := u (1e5 / ((1 : ℕ) + 1 : ℝ)) 10 0.819777 (by norm_num) (by norm_num)
        (by unfold taylor6; norm_num)
      norm_num [ellQ] at this ⊢; linarith
    · refine ⟨by norm_num [n3Q]; exact cube _ _ (by norm_num) (by norm_num), by norm_num [lnQ]; linarith, ?_⟩
      have := u (1e5 / ((2 : ℕ) + 1 : ℝ)) 10 0.414313 (by norm_num) (by norm_num)
        (by unfold taylor6; norm_num)
      norm_num [ellQ] at this ⊢; linarith
    · refine ⟨by norm_num [n3Q]; exact cube _ _ (by norm_num) (by norm_num), by norm_num [lnQ]; linarith, ?_⟩
      have := u (1e5 / ((3 : ℕ) + 1 : ℝ)) 10 0.126631 (by norm_num) (by norm_num)
        (by unfold taylor6; norm_num)
      norm_num [ellQ] at this ⊢; linarith
  obtain ⟨hc3, hlnn, hell⟩ := hn3'
  have hn3pos : (0 : ℝ) < n3Q n := by unfold n3Q; split_ifs <;> norm_num
  have hG := Gq_small (q := q) hn1 hn3
  have hG0 : (0 : ℝ) ≤ Gsm n (decide (2 ∣ q)) (decide (3 ∣ q)) := by
    unfold Gsm; push_cast; split_ifs <;> norm_num
  -- assemble
  have hKF0 := mul_pos (qphi_pos hq1) (f1q_pos q)
  have hcoef : 0.1768 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) ≤
      0.1768 * ((q : ℝ) / Nat.totient q * f1q q) / (n3Q n : ℝ) := by
    rw [mul_assoc]; exact div_le_div_of_nonneg_left (by positivity) hn3pos hc3
  set L := max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1)))
  have hL1 : Real.log (1e5 / ((n : ℝ) + 1)) ≤ L := le_max_right _ _
  have hL2 : Real.log q ≤ L := le_max_left _ _
  unfold Phi2
  rw [hG]
  set K23 : ℝ := (if 2 ∣ q then (2 : ℝ) else 1) * (if 3 ∣ q then 3 / 2 else 1)
  set Z23 : ℝ := (if 2 ∣ q then 2 * (fupQ 2 : ℝ) else 1) * (if 3 ∣ q then 3 / 2 * (fupQ 3 : ℝ) else 1)
  set S23 : ℝ := (if 2 ∣ q then (0.693146 : ℝ) / 2 else 0) + (if 3 ∣ q then (1.098612 : ℝ) / 3 else 0)
  set L23 : ℝ := (if 2 ∣ q then (0.693146 : ℝ) else 0) + (if 3 ∣ q then (1.098612 : ℝ) else 0)
  set Gs : ℝ := ((Gsm n (decide (2 ∣ q)) (decide (3 ∣ q)) : ℚ) : ℝ)
  have hK23 : 0 ≤ K23 := by simp only [K23]; split_ifs <;> norm_num
  have hKG : (q : ℝ) / Nat.totient q * Gs ≤ K23 * (Mq k : ℝ) * Gs := by
    rw [hK]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKh hK23) hG0
  have hlow : (if 2 ∣ q then gp 2 else 1) * (if 3 ∣ q then gp 3 else 1) ≤ Z23 := by
    have f2 : (0 : ℝ) ≤ gp 2 := hgp0 2
    have f3 : (0 : ℝ) ≤ gp 3 := hgp0 3
    simp only [Z23]; split_ifs <;> nlinarith
  have hZ0 : 0 ≤ Z23 := le_trans (by have := hgp0 2; have := hgp0 3; split_ifs <;> positivity) hlow
  have hKF2 : (q : ℝ) / Nat.totient q * f1q q ≤ Z23 * (Nq k : ℝ) := by
    rw [hKF]
    exact mul_le_mul hlow hFh hFh0 hZ0
  have hcoef2 : 0.1768 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) ≤
      0.1768 * (Z23 * (Nq k : ℝ)) / (n3Q n : ℝ) := by
    refine hcoef.trans (div_le_div_of_nonneg_right (by linarith) hn3pos.le)
  have hS23 : S23 ≤ Sq q := by
    rw [hSq]
    have : S23 ≤ (if 2 ∣ q then Real.log 2 / 2 else 0) + (if 3 ∣ q then Real.log 3 / 3 else 0) := by
      simp only [S23]; split_ifs <;> linarith
    linarith
  have hL23 : L23 ≤ Real.log ((if 2 ∣ q then (2 : ℝ) else 1) * (if 3 ∣ q then 3 else 1)) := by
    simp only [L23]
    split_ifs
    · rw [Real.log_mul (by norm_num) (by norm_num)]; linarith
    · simp; linarith
    · simp; linarith
    · simp
  have hLm : max (ellQ n : ℝ) (L23 + Lq5 k) ≤ L :=
    max_le (hell.trans hL1) (by linarith)
  have hfin : ((smallQ n (decide (2 ∣ q)) (decide (3 ∣ q)) k : ℚ) : ℝ) =
      K23 * (Mq k : ℝ) * Gs + 0.1768 * (Z23 * (Nq k : ℝ)) / (n3Q n : ℝ) - (lnQ n : ℝ) - 1.3325822 -
        0.6586 * S23 - 0.3414 * max (ellQ n : ℝ) (L23 + Lq5 k) - 0.6674177 := by
    simp only [smallQ, K23, Z23, S23, L23, Gs]
    by_cases h2 : 2 ∣ q <;> by_cases h3 : 3 ∣ q <;> simp [h2, h3] <;> push_cast <;> ring
  rw [hfin] at hS'
  have hmax : 0.3414 * max (ellQ n : ℝ) (L23 + Lq5 k) ≤ 0.3414 * L := by linarith
  linarith

end TernaryGoldbach.MinorArcs
