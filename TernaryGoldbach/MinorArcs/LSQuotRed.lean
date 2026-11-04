import TernaryGoldbach.MinorArcs.LSQuot7

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# [H, Prop 12.2.4] with `c₊ = 2`, part 2: removing large primes from `q`

For `q` squarefree, `q < 2.2·10¹⁰`, and a prime `p > 13` with `p ∣ q`, all of whose prime factors
are at most `p`: `Φ(q/p, n, log(q/p)) ≤ 0 ⟹ Φ(q, n, log q) ≤ 0` (`Phi2_step`). The identity
`G_{q'}(n) = G_{q'p}(n) + G_{q'p}(n/p)/(p − 1)` (`Gq_split`) and `(q/φ(q)) G_q(x) ≥ G(x) ≥ log x`
give `(1 − 1/p) Φ(q) ≤ Φ(q/p) + Δ(p)` with `Δ(p) < 0`.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

theorem gf_prime {p : ℕ} (hp : p.Prime) : gf p = 1 / ((p : ℝ) - 1) := by
  unfold gf
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  push_cast [Nat.cast_sub hp.one_lt.le]; ring

theorem gf_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) : gf (p * m) = 0 := by
  unfold gf
  have : ¬ Squarefree (p * m) := by
    intro h
    obtain ⟨k, rfl⟩ := hpm
    have := h p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]

/-- **`G_{q'}(n) = G_{q'p}(n) + G_{q'p}(n/p)/(p − 1)`** for a prime `p ∤ q'`. -/
theorem Gq_split {q' p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q') (n : ℕ) :
    Gq q' n = Gq (q' * p) n + Gq (q' * p) ((n : ℝ) / p) / ((p : ℝ) - 1) := by
  rw [Gq_eq, Gq_eq, Gq_eq, Nat.floor_natCast, Nat.floor_div_eq_div]
  set S := (Icc 1 n).filter (fun r => Nat.Coprime r q')
  rw [← sum_filter_add_sum_filter_not S (fun r => p ∣ r), add_comm]
  congr 1
  · -- `p ∤ r`
    congr 1; ext r
    simp only [S, mem_filter, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h3))⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_comm.1 h3) h⟩
  · -- `p ∣ r`, `r = p m`
    set T := (Icc 1 (n / p)).filter (fun m => Nat.Coprime m q')
    have himg : S.filter (fun r => p ∣ r) = T.image (fun m => p * m) := by
      ext r
      simp only [S, T, mem_filter, mem_image, mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        obtain ⟨m, rfl⟩ := h4
        refine ⟨m, ⟨⟨?_, ?_⟩, Nat.Coprime.coprime_mul_left h3⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at h1
          · exact h
        · rw [Nat.le_div_iff_mul_le hp.pos]; linarith
      · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        refine ⟨⟨⟨by nlinarith [hp.pos], ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · have := (Nat.le_div_iff_mul_le hp.pos).1 h2; linarith
        · exact Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd hp).2 hpq, h3⟩
    rw [himg, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    rw [← sum_filter_add_sum_filter_not T (fun m => p ∣ m)]
    rw [sum_eq_zero (fun m hm => gf_prime_mul hp (mem_filter.1 hm).2), zero_add, sum_div]
    refine sum_congr ?_ fun m hm => ?_
    · ext m
      simp only [T, mem_filter, Nat.coprime_mul_iff_right]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h3)⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_comm.1 h3) h⟩
    · have hpm : ¬ p ∣ m := fun h => (Nat.Prime.coprime_iff_not_dvd hp).1
        (Nat.coprime_comm.1 (Nat.coprime_mul_iff_right.1 (mem_filter.1 hm).2).2) h
      rw [gf_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm), gf_prime hp]; ring

/-! ### `G(x) ≥ log x` -/

/-- `μ²(r)/φ(r)` over `ℚ`. -/
def gQ (r : ℕ) : ℚ := if Squarefree r then 1 / (Nat.totient r : ℚ) else 0

theorem gf_eq_gQ (r : ℕ) : gf r = (gQ r : ℝ) := by
  unfold gf gQ
  split_ifs with h
  · have h1 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    rw [h1]; push_cast; ring
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

/-- A walk checking `H_r ≤ G(r)` step by step. -/
def GHwalk : ℕ → ℕ → ℚ → ℚ → Bool
  | 0, _, _, _ => true
  | f + 1, r, G, H =>
    let G' := G + gQ r; let H' := H + 1 / (r : ℚ); decide (H' ≤ G') && GHwalk f (r + 1) G' H'

theorem GHwalk_spec : ∀ (f r : ℕ) (G H : ℚ), GHwalk f r G H = true → ∀ k, k < f →
    H + ∑ i ∈ range (k + 1), 1 / ((r + i : ℕ) : ℚ) ≤ G + ∑ i ∈ range (k + 1), gQ (r + i) := by
  intro f
  induction f with
  | zero => intro r G H _ k hk; omega
  | succ f ih =>
    intro r G H h k hk
    simp only [GHwalk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases k with _ | k
    · rw [sum_range_one, sum_range_one, Nat.add_zero]; exact h1
    · have := ih (r + 1) _ _ h2 k (by omega)
      rw [sum_range_succ', sum_range_succ' (fun i => gQ (r + i))]
      simp only [add_zero] at this ⊢
      have e1 : ∑ i ∈ range (k + 1), 1 / ((r + (i + 1) : ℕ) : ℚ) =
          ∑ i ∈ range (k + 1), 1 / ((r + 1 + i : ℕ) : ℚ) :=
        sum_congr rfl fun i _ => by rw [show r + (i + 1) = r + 1 + i by ring]
      have e2 : ∑ i ∈ range (k + 1), gQ (r + (i + 1)) = ∑ i ∈ range (k + 1), gQ (r + 1 + i) :=
        sum_congr rfl fun i _ => by rw [show r + (i + 1) = r + 1 + i by ring]
      rw [e1, e2]
      linarith

set_option maxRecDepth 100000 in
theorem GHwalk_199 : GHwalk 199 1 0 0 = true := by decide +kernel

theorem Gq_one_nat (n : ℕ) : Gq 1 n = ((∑ i ∈ range n, gQ (1 + i) : ℚ) : ℝ) := by
  rw [Gq_eq, Nat.floor_natCast]
  have : (Icc 1 n).filter (fun r => Nat.Coprime r 1) = Icc 1 n := by
    ext r; simp
  have hI : Icc 1 n = Ico 1 (n + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [this, hI, sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
  push_cast; simp only [gf_eq_gQ]

theorem harmonic_le_G {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 199) : (harmonic n : ℝ) ≤ Gq 1 n := by
  have h := GHwalk_spec 199 1 0 0 GHwalk_199 (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at h
  simp only [zero_add] at h
  rw [Gq_one_nat, harmonic_eq_sum_Icc]
  have e : ∑ i ∈ Icc 1 n, (i : ℚ)⁻¹ = ∑ i ∈ range n, 1 / ((1 + i : ℕ) : ℚ) := by
    have hI : Icc 1 n = Ico 1 (n + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]; simp [one_div]
  rw [e]; exact_mod_cast h

/-- **`G(x) ≥ log x`** for `x ≥ 1`. -/
theorem log_le_G {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Gq 1 x := by
  rcases lt_or_ge x 200 with h | h
  · set n := ⌊x⌋₊
    have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
    have hn : n ≤ 199 := by
      have := Nat.floor_le (show 0 ≤ x by linarith); have : (n : ℝ) < 200 := by linarith
      exact_mod_cast (show (n : ℝ) ≤ 199 by
        have h2 : n < 200 := by exact_mod_cast this
        exact_mod_cast (show n ≤ 199 by omega))
    have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have h1 : Real.log x ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have h2 := log_add_one_le_harmonic n
    have h3 := harmonic_le_G hn1 hn
    have h4 : Gq 1 x = Gq 1 n := by unfold Gq; rw [Nat.floor_natCast]
    rw [h4]; linarith
  · obtain ⟨c, hc1, -, hram⟩ := ramare_Gq
    have h := (abs_le.1 (hram 1 le_rfl x hx)).1
    have hS : Sq 1 = 0 := by simp [Sq]
    have hf : f1q 1 = 1 := by simp [f1q]
    rw [hS, hf, Nat.totient_one] at h
    push_cast at h
    have hx3 : x ^ (-(1 / 3 : ℝ)) ≤ 0.171 := by
      have h1 : (5.848 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
        calc (5.848 : ℝ) = ((5.848 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ x ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
      rw [Real.rpow_neg (by linarith), ← one_div]
      calc 1 / x ^ (1 / 3 : ℝ) ≤ 1 / 5.848 := one_div_le_one_div_of_le (by norm_num) h1
        _ ≤ 0.171 := by norm_num
    nlinarith

/-! ### Bounds for `q < 2.2·10¹⁰` -/

theorem primk_mono {a b : ℕ} (h : a ≤ b) : primk a ≤ primk b := by
  unfold primk
  exact prod_le_prod_of_subset_of_one_le (range_subset_range.2 h)
    (fun i _ _ => (Nat.prime_nth_prime i).one_lt.le)

theorem card_primeFactors_le_10 {q : ℕ} (hq1 : 1 ≤ q) (hq : q < 22000000000) :
    q.primeFactors.card ≤ 10 := by
  by_contra h
  push Not at h
  have h1 := (TernaryGoldbach.Prelim.exch q.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)).2
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h3 : primk 11 ≤ primk q.primeFactors.card := primk_mono h
  rw [primk_11] at h3
  unfold primk at h3
  have := h3.trans (h1.trans h2)
  omega

theorem Gk_mono {a b : ℕ} (h : a ≤ b) : Gk a ≤ Gk b := by
  unfold Gk
  rw [← prod_range_mul_prod_Ico _ h]
  exact le_mul_of_one_le_right (prod_nonneg fun i _ => by linarith [one_le_ghat (Nat.nth Nat.Prime i)])
    (one_le_prod₀ fun i _ => one_le_ghat _)

theorem Gk_9_le : Gk 9 ≤ 8.4223 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -, -, -⟩ := nth_primes
  simp only [Gk, prod_range_succ, range_zero, prod_empty, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num [gHatQ]

theorem Sk_mono {a b : ℕ} (h : a ≤ b) : Sk a ≤ Sk b := by
  unfold Sk
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) (fun i _ _ => shat_nonneg _)

theorem Sq_le_2322 {q : ℕ} (hq1 : 1 ≤ q) (hq : q < 22000000000) : Sq q ≤ 2.322 := by
  have hPp : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hs := (exch_gen shat shat_nonneg (fun a b ha hb hab => shat_anti ha hb hab) _ hPp).2
  have h1 : Sq q ≤ Sk q.primeFactors.card := (sum_le_sum fun p hp => le_shat (hPp p hp)).trans hs
  have := Sk_mono (card_primeFactors_le_10 hq1 hq)
  have := Sk_10_le
  have : (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 + 2.564952 / 13 +
    2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29 : ℝ) ≤ 2.322 := by norm_num
  linarith

theorem qphi_f1q_le {q : ℕ} (hq1 : 1 ≤ q) (hc : q.primeFactors.card ≤ 9) :
    (q : ℝ) / Nat.totient q * f1q q ≤ 8.4223 := by
  rw [qphi_f1q_eq hq1]
  have hPp : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hg := (exch_gen gHatQ (fun n => by linarith [one_le_ghat n])
    (fun a b ha hb hab => ghat_anti ha hb hab) _ hPp).1
  have h1 : ∏ p ∈ q.primeFactors, gp p ≤ ∏ p ∈ q.primeFactors, gHatQ p :=
    prod_le_prod₀ (fun p hp => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
      unfold gp; exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (f1p_pos p).le)
      fun p hp => gp_le_ghat (hPp p hp)
  exact h1.trans (hg.trans ((Gk_mono hc).trans Gk_9_le))

/-- A squarefree `q` with all prime factors `≤ p` is at most `p#`. -/
theorem le_primorial {q p : ℕ} (hq : Squarefree q) (hmax : ∀ r ∈ q.primeFactors, r ≤ p) :
    q ≤ primorial p := by
  rw [← Nat.prod_primeFactors_of_squarefree hq, primorial]
  refine prod_le_prod_of_subset_of_one_le (fun r hr => ?_) (fun r hr _ => ?_)
  · simp only [mem_filter, mem_range]
    exact ⟨by have := hmax r hr; omega, Nat.prime_of_mem_primeFactors hr⟩
  · exact (mem_filter.1 hr).2.one_lt.le

/-! ### Adding a prime -/

theorem primeFactors_mul_prime {q' p : ℕ} (hq' : q' ≠ 0) (hp : p.Prime) :
    (q' * p).primeFactors = insert p q'.primeFactors := by
  rw [Nat.primeFactors_mul hq' hp.ne_zero, hp.primeFactors, union_comm]; rfl

theorem not_mem_primeFactors {q' p : ℕ} (hpq : ¬ p ∣ q') : p ∉ q'.primeFactors :=
  fun h => hpq (Nat.dvd_of_mem_primeFactors h)

theorem qphi_mul_prime {q' p : ℕ} (hq' : 1 ≤ q') (hp : p.Prime) (hpq : ¬ p ∣ q') :
    ((q' * p : ℕ) : ℝ) / Nat.totient (q' * p) = (q' : ℝ) / Nat.totient q' * ((p : ℝ) / (p - 1)) := by
  rw [TernaryGoldbach.Prelim.div_totient_eq_prod (by nlinarith [hp.pos]),
    TernaryGoldbach.Prelim.div_totient_eq_prod hq', primeFactors_mul_prime (by omega) hp,
    prod_insert (not_mem_primeFactors hpq), mul_comm]

theorem Sq_mul_prime {q' p : ℕ} (hq' : 1 ≤ q') (hp : p.Prime) (hpq : ¬ p ∣ q') :
    Sq (q' * p) = Sq q' + Real.log p / p := by
  unfold Sq
  rw [primeFactors_mul_prime (by omega) hp, sum_insert (not_mem_primeFactors hpq), add_comm]

theorem f1q_mul_prime {q' p : ℕ} (hq' : 1 ≤ q') (hp : p.Prime) (hpq : ¬ p ∣ q') :
    f1q (q' * p) = f1q q' * f1p p := by
  unfold f1q
  rw [primeFactors_mul_prime (by omega) hp, prod_insert (not_mem_primeFactors hpq), mul_comm]

/-! ### The step -/

theorem primorial_17 : primorial 17 = 510510 := by decide
theorem primorial_19 : primorial 19 = 9699690 := by decide
theorem primorial_23 : primorial 23 = 223092870 := by decide
theorem primorial_29 : primorial 29 = 6469693230 := by decide

/-- **`Δ(p) < 0`** for primes `p ≥ 17`. -/
theorem delta_neg {p : ℕ} (hp : p.Prime) (h17 : 17 ≤ p) {S L : ℝ} (hS : S ≤ 2.322)
    (hL1 : L ≤ Real.log (primorial p)) (hL2 : L ≤ 23.8144) :
    (0.3414 * Real.log p + 0.6586 * S + 0.3414 * L + 2) / p - 0.3414 * Real.log p +
      0.1768 * 8.4223 * (gHatQ p - 1) ≤ 0 := by
  have hp0 : (17 : ℝ) ≤ p := by exact_mod_cast h17
  have t := fun (z : ℝ) (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h : z ≤ 2.7182818283 ^ n * taylor6 f)
    (hz : 0 < z) => log_le_num n f hz h0 h
  have u := fun (z : ℝ) (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : 2.7182818286 ^ n * (taylor6 f + f ^ 7 / 4410) ≤ z) => le_log_num (z := z) n f h0 h1 h
  rcases lt_or_ge p 31 with hlt | hge
  · -- `p ∈ {17, 19, 23, 29}`
    have hcases : p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 := by
      interval_cases p <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
        (right; right; right; rfl) | (exfalso; revert hp; decide)
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [primorial_17] at hL1
      have h1 := t 510510 13 0.15 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      have h2 := u 17 2 0.833 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
      have h3 := t 17 2 0.833241 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      push_cast at h1 h2 h3 hL1 ⊢; norm_num [gHatQ]
      nlinarith
    · rw [primorial_19] at hL1
      have h1 := t 9699690 16 0.1 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      have h2 := u 19 2 0.944 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
      have h3 := t 19 2 0.944498 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      push_cast at h1 h2 h3 hL1 ⊢; norm_num [gHatQ]
      nlinarith
    · rw [primorial_23] at hL1
      have h1 := t 223092870 19 0.25 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      have h2 := u 23 3 0.135 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
      have h3 := t 23 3 0.135495 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      push_cast at h1 h2 h3 hL1 ⊢; norm_num [gHatQ]
      nlinarith
    · rw [primorial_29] at hL1
      have h1 := t 6469693230 22 0.6 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      have h2 := u 29 3 0.367 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
      have h3 := t 29 3 0.367296 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
      push_cast at h1 h2 h3 hL1 ⊢; norm_num [gHatQ]
      nlinarith
  · have h31 : (31 : ℝ) ≤ p := by exact_mod_cast hge
    have hg : gHatQ p ≤ 1.12235 := by
      have := ghat_anti hp (by norm_num : Nat.Prime 31) hge
      simpa [gHatQ] using this
    have hl : 3.43 ≤ Real.log p := by
      have h2 := u 31 3 0.43 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
      push_cast at h2
      linarith [Real.log_le_log (by norm_num) h31]
    have hnum : 0 ≤ 0.3414 * Real.log p + 0.6586 * S + 0.3414 * L + 2 ∨
        0.3414 * Real.log p + 0.6586 * S + 0.3414 * L + 2 < 0 := le_or_gt _ _
    have hp0' : (0 : ℝ) < p := by linarith
    have hfrac : (0.3414 * Real.log p + 0.6586 * S + 0.3414 * L + 2) / p ≤
        (0.3414 * Real.log p + 0.6586 * 2.322 + 0.3414 * 23.8144 + 2) / 31 := by
      rcases hnum with h | h
      · calc _ ≤ (0.3414 * Real.log p + 0.6586 * 2.322 + 0.3414 * 23.8144 + 2) / p := by
              gcongr
          _ ≤ _ := div_le_div_of_nonneg_left (by nlinarith) (by norm_num) h31
      · have : (0.3414 * Real.log p + 0.6586 * S + 0.3414 * L + 2) / p < 0 := div_neg_of_neg_of_pos h hp0'
        have : (0 : ℝ) ≤ (0.3414 * Real.log p + 0.6586 * 2.322 + 0.3414 * 23.8144 + 2) / 31 := by
          apply div_nonneg _ (by norm_num); nlinarith
        linarith
    nlinarith

/-- The algebra of the step. -/
theorem step_alg {p K K' Gn Gm Gn' S S' lq lq' lp ln F F' f n3 P P' : ℝ} (hp : 1 < p) (hn3 : 1 ≤ n3)
    (hP : P = K * Gn - ln - 1.3325822 - S + 0.1768 * K * F / n3 - (0.3414 * (lq - S) + 0.6674177))
    (hP' : P' = K' * Gn' - ln - 1.3325822 - S' + 0.1768 * K' * F' / n3 -
      (0.3414 * (lq' - S') + 0.6674177))
    (hGn' : Gn' = Gn + Gm / (p - 1)) (hK : K = K' * (p / (p - 1))) (hS : S = S' + lp / p)
    (hF : F = F' * f) (hL : lq = lq' + lp) :
    P - P' = (K * Gn - K * Gm) / p - 0.6586 * lp / p - 0.3414 * lp +
      0.1768 * (K' * F') * (p / (p - 1) * f - 1) / n3 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hn0 : n3 ≠ 0 := by linarith
  subst hP hP' hGn' hK hS hF hL
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **The step**: removing the largest prime `p ≥ 17` of a squarefree `q < 2.2·10¹⁰` cannot make
`Φ` positive. -/
theorem Phi2_step {q p n : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (h17 : 17 ≤ p) (hsq : Squarefree q)
    (hpq : p ∣ q) (hq : q < 22000000000) (hmax : ∀ r ∈ q.primeFactors, r ≤ p)
    (h' : Phi2 (q / p) n (Real.log ((q / p : ℕ) : ℝ)) ≤ 0) : Phi2 q n (Real.log q) ≤ 0 := by
  obtain ⟨q', hq'def⟩ : ∃ q', q' = q / p := ⟨_, rfl⟩
  rw [← hq'def] at h'
  have hqq : q = q' * p := by rw [hq'def]; exact (Nat.div_mul_cancel hpq).symm
  have hq0 : q ≠ 0 := hsq.ne_zero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 hq0
  have hq'0 : q' ≠ 0 := by rintro h; rw [h, zero_mul] at hqq; exact hq0 hqq
  have hq'1 : 1 ≤ q' := Nat.one_le_iff_ne_zero.2 hq'0
  have hpq' : ¬ p ∣ q' := by
    rintro ⟨k, hk⟩
    have := hsq p ⟨k, by rw [hqq, hk]; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp17 : (17 : ℝ) ≤ p := by exact_mod_cast h17
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK := qphi_mul_prime hq'1 hp hpq'
  have hS := Sq_mul_prime hq'1 hp hpq'
  have hF := f1q_mul_prime hq'1 hp hpq'
  have hG := Gq_split hp hpq' n
  rw [← hqq] at hK hS hF hG
  have hL : Real.log q = Real.log q' + Real.log p := by
    rw [hqq]; push_cast; exact Real.log_mul (by exact_mod_cast hq'0) (by linarith)
  have hn3 : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hdiff := step_alg (p := p) (P := Phi2 q n (Real.log q)) (P' := Phi2 q' n (Real.log q'))
    (K := (q : ℝ) / Nat.totient q) (K' := (q' : ℝ) / Nat.totient q') (Gn := Gq q n)
    (Gm := Gq q ((n : ℝ) / p)) (Gn' := Gq q' n) (S := Sq q) (S' := Sq q') (lq := Real.log q)
    (lq' := Real.log q') (lp := Real.log p) (ln := Real.log n) (F := f1q q) (F' := f1q q')
    (f := f1p p) (n3 := (n : ℝ) ^ (1 / 3 : ℝ))
    hp1 hn3 (by unfold Phi2; ring) (by unfold Phi2; ring) hG hK hS hF hL
  have hK0 := qphi_pos hq1
  have hK'0 := qphi_pos hq'1
  have hF'0 := f1q_pos q'
  have hGm0 : 0 ≤ Gq q ((n : ℝ) / p) := Gq_nonneg_q _ _
  -- `log n − K G_q(n/p) ≤ log p`
  have hlow : Real.log n - (q : ℝ) / Nat.totient q * Gq q ((n : ℝ) / p) ≤ Real.log p := by
    rcases lt_or_ge n p with h | h
    · have : Real.log n ≤ Real.log p := Real.log_le_log hn0 (by exact_mod_cast h.le)
      have : 0 ≤ (q : ℝ) / Nat.totient q * Gq q ((n : ℝ) / p) := mul_nonneg hK0.le hGm0
      linarith
    · have h1 : (1 : ℝ) ≤ n / p := by
        rw [le_div_iff₀ (by linarith), one_mul]; exact_mod_cast h
      have h2 := log_le_G h1
      have h3 := G_le_mul_Gq hsq (t := (n : ℝ) / p)
      rw [Real.log_div hn0.ne' (by linarith)] at h2
      linarith
  -- bounds
  have hc := card_primeFactors_le_10 hq1 hq
  have hc' : q'.primeFactors.card ≤ 9 := by
    have : q.primeFactors.card = q'.primeFactors.card + 1 := by
      rw [hqq, primeFactors_mul_prime hq'0 hp, card_insert_of_notMem (not_mem_primeFactors hpq')]
    omega
  have hKF' := qphi_f1q_le hq'1 hc'
  have hSb := Sq_le_2322 hq1 hq
  have hgp : gp p ≤ gHatQ p := gp_le_ghat hp
  have hLq1 : Real.log q ≤ Real.log (primorial p) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq0) (by exact_mod_cast le_primorial hsq hmax)
  have hLq2 : Real.log q ≤ 23.8144 := by
    have h1 : Real.log (22000000000 : ℝ) ≤ 23.8144 := by
      have := log_le_num (z := 22000000000) 23 0.8144 (by norm_num) (by norm_num)
        (by unfold taylor6; norm_num)
      push_cast at this; linarith
    exact (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq0) (by exact_mod_cast hq.le)).trans h1
  have hΔ := delta_neg hp h17 (le_refl 2.322) hLq1 hLq2
  -- `K G_q(n) ≤ Φ(q) + log n + 0.6586 S + 0.3414 log q + 2`
  have hX : (q : ℝ) / Nat.totient q * Gq q n ≤ Phi2 q n (Real.log q) + Real.log n + 0.6586 * Sq q +
      0.3414 * Real.log q + 2 := by
    have : 0 ≤ 0.1768 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) := by
      have := f1q_pos q; positivity
    unfold Phi2; linarith
  -- the `f₁` term
  have hgp' : (p : ℝ) / (p - 1) * f1p p = gp p := rfl
  rw [hgp'] at hdiff
  have hCK : 0.1768 * ((q' : ℝ) / Nat.totient q' * f1q q') * (gp p - 1) / (n : ℝ) ^ (1 / 3 : ℝ) ≤
      0.1768 * 8.4223 * (gHatQ p - 1) := by
    have hKF0 := mul_pos hK'0 hF'0
    rcases le_or_gt 1 (gp p) with h | h
    · have hpos : 0 ≤ 0.1768 * ((q' : ℝ) / Nat.totient q' * f1q q') * (gp p - 1) := by
        have : 0 ≤ gp p - 1 := by linarith
        positivity
      calc _ ≤ 0.1768 * ((q' : ℝ) / Nat.totient q' * f1q q') * (gp p - 1) := div_le_self hpos hn3
        _ ≤ 0.1768 * 8.4223 * (gHatQ p - 1) := by
          have : 0 ≤ gp p - 1 := by linarith
          gcongr
    · have : 0.1768 * ((q' : ℝ) / Nat.totient q' * f1q q') * (gp p - 1) / (n : ℝ) ^ (1 / 3 : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
        have : gp p - 1 < 0 := by linarith
        nlinarith
      have : 0 ≤ gHatQ p - 1 := by linarith [one_le_ghat p]
      nlinarith
  -- conclude: `(1 − 1/p) Φ(q) ≤ Φ(q') + Δ(p) ≤ 0`
  set P := Phi2 q n (Real.log q)
  have e : ((q : ℝ) / Nat.totient q * Gq q n - (q : ℝ) / Nat.totient q * Gq q ((n : ℝ) / p)) / p ≤
      (P + Real.log p + 0.6586 * Sq q + 0.3414 * Real.log q + 2) / p := by
    apply div_le_div_of_nonneg_right _ (by linarith); linarith
  have hmono : (0.3414 * Real.log p + 0.6586 * Sq q + 0.3414 * Real.log q + 2) / p ≤
      (0.3414 * Real.log p + 0.6586 * 2.322 + 0.3414 * Real.log q + 2) / p := by
    apply div_le_div_of_nonneg_right _ (by linarith); linarith
  have e2 : (P + Real.log p + 0.6586 * Sq q + 0.3414 * Real.log q + 2) / p - 0.6586 * Real.log p / p =
      P / p + (0.3414 * Real.log p + 0.6586 * Sq q + 0.3414 * Real.log q + 2) / p := by ring
  have hfin : P - P / p ≤ 0 := by linarith
  have h1p : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have : P * (1 - 1 / p) ≤ 0 := by
    have : P * (1 - 1 / p) = P - P / p := by ring
    linarith
  by_contra hc
  push Not at hc
  have := mul_pos hc h1p
  linarith

/-! ### The reduction -/

/-- `rad q = ∏_{p ∣ q} p`. -/
def radQ (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

theorem radQ_primeFactors (q : ℕ) : (radQ q).primeFactors = q.primeFactors :=
  Nat.primeFactors_prod_primeFactors q

theorem radQ_ne_zero (q : ℕ) : radQ q ≠ 0 :=
  prod_ne_zero_iff.2 fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem radQ_squarefree (q : ℕ) : Squarefree (radQ q) := by
  unfold radQ
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree)
  rw [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha) (Nat.prime_of_mem_primeFactors hb)).2 hab

theorem radQ_le {q : ℕ} (hq : q ≠ 0) : radQ q ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq)
  (Nat.prod_primeFactors_dvd q)

theorem Gq_radQ {q : ℕ} (hq : q ≠ 0) (x : ℝ) : Gq q x = Gq (radQ q) x := by
  rw [Gq_eq, Gq_eq]
  refine sum_congr (filter_congr fun r hr => ?_) fun _ _ => rfl
  have hr0 : r ≠ 0 := by have := (mem_Icc.1 hr).1; omega
  rw [← Nat.disjoint_primeFactors hr0 hq, ← Nat.disjoint_primeFactors hr0 (radQ_ne_zero q),
    radQ_primeFactors]

/-- `Φ` only improves when `q` is replaced by its radical. -/
theorem Phi2_radQ {q n : ℕ} (hq : q ≠ 0) :
    Phi2 q n (Real.log q) ≤ Phi2 (radQ q) n (Real.log (radQ q)) := by
  have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 hq
  have h2 : 1 ≤ radQ q := Nat.one_le_iff_ne_zero.2 (radQ_ne_zero q)
  have hK : (q : ℝ) / Nat.totient q = (radQ q : ℝ) / Nat.totient (radQ q) := by
    rw [TernaryGoldbach.Prelim.div_totient_eq_prod h1, TernaryGoldbach.Prelim.div_totient_eq_prod h2,
      radQ_primeFactors]
  have hS : Sq q = Sq (radQ q) := by unfold Sq; rw [radQ_primeFactors]
  have hF : f1q q = f1q (radQ q) := by unfold f1q; rw [radQ_primeFactors]
  have hL : Real.log (radQ q) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast radQ_le hq)
  refine le_trans ?_ (Phi2_anti _ _ hL)
  unfold Phi2; rw [hK, hS, hF, Gq_radQ hq]

theorem dvd_30030 {A : ℕ} (hA : Squarefree A) (h : ∀ r ∈ A.primeFactors, r ≤ 13) : A ∣ 30030 := by
  rw [← Nat.prod_primeFactors_of_squarefree hA, show (30030 : ℕ) = primorial 13 by decide, primorial]
  refine prod_dvd_prod_of_subset _ _ _ fun r hr => ?_
  simp only [mem_filter, mem_range]
  exact ⟨by have := h r hr; omega, Nat.prime_of_mem_primeFactors hr⟩

/-- **The reduction**: if `Φ(A, n, log A) ≤ 0` for every `A ∣ 30030`, then `Φ(q, n, log q) ≤ 0`
for every `q < 2.2·10¹⁰`. -/
theorem Phi2_reduce {n : ℕ} (hn : 1 ≤ n) (base : ∀ A, A ∣ 30030 → Phi2 A n (Real.log A) ≤ 0) :
    ∀ q, 1 ≤ q → q < 22000000000 → Phi2 q n (Real.log q) ≤ 0 := by
  -- squarefree `q` first, by strong induction
  have hsf : ∀ q, Squarefree q → q < 22000000000 → Phi2 q n (Real.log q) ≤ 0 := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hsq hq
      by_cases hsmall : ∀ r ∈ q.primeFactors, r ≤ 13
      · exact base q (dvd_30030 hsq hsmall)
      push Not at hsmall
      have hne : q.primeFactors.Nonempty := by
        obtain ⟨r, hr, -⟩ := hsmall; exact ⟨r, hr⟩
      set p := q.primeFactors.max' hne
      have hpmem : p ∈ q.primeFactors := max'_mem _ _
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hpmem
      have hmax : ∀ r ∈ q.primeFactors, r ≤ p := fun r hr => le_max' _ _ hr
      have h17 : 17 ≤ p := by
        obtain ⟨r, hr, hr13⟩ := hsmall
        have h14 : 14 ≤ p := le_trans hr13 (hmax r hr)
        by_contra hlt
        push Not at hlt
        interval_cases p <;> revert hp <;> decide
      have hq0 : q ≠ 0 := hsq.ne_zero
      have hlt : q / p < q := Nat.div_lt_self (Nat.pos_of_ne_zero hq0) hp.one_lt
      have h' := ih (q / p) hlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpq)) (by omega)
      exact Phi2_step hn hp h17 hsq hpq hq hmax h'
  intro q hq1 hq
  have hq0 : q ≠ 0 := by omega
  exact (Phi2_radQ hq0).trans (hsf _ (radQ_squarefree q) (lt_of_le_of_lt (radQ_le hq0) hq))

end TernaryGoldbach.MinorArcs
