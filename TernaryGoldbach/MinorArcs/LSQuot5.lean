import TernaryGoldbach.MinorArcs.LSQuot4

/-!
# [B, Prop 12.2.4], part 5: `λ(q)⁷ ≤ a⁹ q²` for `q ≥ 2.2·10¹⁰`, and `large_q_hS`
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

theorem Gk_succ (k : ℕ) : Gk (k + 1) = Gk k * gHatQ (Nat.nth Nat.Prime k) := by
  unfold Gk; rw [prod_range_succ]
theorem Sk_succ (k : ℕ) : Sk (k + 1) = Sk k + shat (Nat.nth Nat.Prime k) := by
  unfold Sk; rw [sum_range_succ]
theorem primk_succ (k : ℕ) : primk (k + 1) = primk k * Nat.nth Nat.Prime k := by
  unfold primk; rw [prod_range_succ]

theorem Gk_10 : Gk 10 = 1.39953 * 1.39953 * 1.36194 * 1.3115 * 1.24148 * 1.21777 * 1.18326 *
    1.17031 * 1.14988 * 1.12806 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := nth_primes
  simp only [Gk, prod_range_succ, range_zero, prod_empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num [gHatQ]

theorem Gk_11 : Gk 11 = Gk 10 * 1.12235 := by
  rw [Gk_succ, nth_primes.2.2.2.2.2.2.2.2.2.2.1]; norm_num [gHatQ]

theorem primk_11 : primk 11 = 200560490130 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := nth_primes
  simp only [primk, prod_range_succ, range_zero, prod_empty, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10]
  norm_num

/-- Upper bounds for `log p`, `p ≤ 31`. -/
theorem log_primes_le :
    Real.log 3 ≤ 1.098613 ∧ Real.log 5 ≤ 1.609442 ∧ Real.log 7 ≤ 1.94597 ∧
    Real.log 11 ≤ 2.397896 ∧ Real.log 13 ≤ 2.564952 ∧ Real.log 17 ≤ 2.833241 ∧
    Real.log 19 ≤ 2.944498 ∧ Real.log 23 ≤ 3.135495 ∧ Real.log 29 ≤ 3.367296 ∧
    Real.log 31 ≤ 3.433988 := by
  have t := fun (z : ℝ) (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h : z ≤ 2.7182818283 ^ n * taylor6 f) (hz : 0 < z) =>
    log_le_num n f hz h0 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := t 3 1 0.098613 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 5 1 0.609442 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 7 1 0.94597 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 11 2 0.397896 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 13 2 0.564952 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 17 2 0.833241 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 19 2 0.944498 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 23 3 0.135495 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 29 3 0.367296 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith
  · have := t 31 3 0.433988 (by norm_num) (by unfold taylor6; norm_num) (by norm_num)
    push_cast at this; linarith

/-- `S_10 ≤ 2·1.098613/3 + 1.609442/5 + ⋯`. -/
theorem Sk_10_le : Sk 10 ≤ 2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 +
    2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := nth_primes
  obtain ⟨l3, l5, l7, l11, l13, l17, l19, l23, l29, -⟩ := log_primes_le
  simp only [Sk, sum_range_succ, range_zero, sum_empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [shat]
  norm_num
  linarith

theorem Sk_11_le : Sk 11 ≤ 2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 +
    2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29 +
    3.433988 / 31 := by
  rw [Sk_succ, nth_primes.2.2.2.2.2.2.2.2.2.2.1]
  have := Sk_10_le
  have l31 := log_primes_le.2.2.2.2.2.2.2.2.2
  simp only [shat]; norm_num
  linarith

/-! ### The base cases -/

/-- `k ≤ 10`, at `q = 2.2·10¹⁰`. -/
theorem base_10 {κ : ℝ} (hκ : 0.3726 * (23.8143 - (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 +
    2.397896 / 11 + 2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 +
    3.367296 / 29)) + 0.0274177 ≤ κ) :
    (7.4527 * Gk 10) ^ 21 ≤ (103 / 120 : ℝ) ^ 9 * (22000000000 : ℝ) ^ 2 * κ ^ 21 := by
  rw [Gk_10]
  have hκ0 : 0 ≤ 0.3726 * (23.8143 - (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 +
    2.397896 / 11 + 2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 +
    3.367296 / 29)) + (0.0274177 : ℝ) := by norm_num
  calc _ ≤ (103 / 120 : ℝ) ^ 9 * (22000000000 : ℝ) ^ 2 * (0.3726 * (23.8143 - (2 * 1.098613 / 3 +
        1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 + 2.564952 / 13 + 2.833241 / 17 +
        2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29)) + 0.0274177) ^ 21 := by norm_num
    _ ≤ _ := by gcongr

theorem log_Q1_ge : 23.8143 ≤ Real.log (22000000000 : ℝ) := by
  have := le_log_num (z := 22000000000) 23 0.8143 (by norm_num) (by norm_num)
    (by unfold taylor6; norm_num)
  push_cast at this; linarith

theorem log_prim11_ge : 26.024 ≤ Real.log (200560490130 : ℝ) := by
  have := le_log_num (z := 200560490130) 26 0.024 (by norm_num) (by norm_num)
    (by unfold taylor6; norm_num)
  push_cast at this; linarith

/-- The induction hypothesis for `k ≥ 11`. -/
def IHk (k : ℕ) : Prop :=
  0 < kapk k (primk k) ∧
    (7.4527 * Gk k) ^ 21 ≤ (103 / 120 : ℝ) ^ 9 * ((primk k : ℕ) : ℝ) ^ 2 * kapk k (primk k) ^ 21

theorem IHk_11 : IHk 11 := by
  have hS := Sk_11_le
  have hl := log_prim11_ge
  have hκ : 0.3726 * (26.024 - (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 +
      2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29 +
      3.433988 / 31)) + 0.0274177 ≤ kapk 11 ((200560490130 : ℕ) : ℝ) := by
    unfold kapk; push_cast; nlinarith
  unfold IHk
  rw [primk_11]
  refine ⟨lt_of_lt_of_le (by norm_num) hκ, ?_⟩
  rw [Gk_11, Gk_10]
  calc _ ≤ (103 / 120 : ℝ) ^ 9 * ((200560490130 : ℕ) : ℝ) ^ 2 * (0.3726 * (26.024 -
        (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 + 2.397896 / 11 + 2.564952 / 13 +
        2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 + 3.367296 / 29 + 3.433988 / 31)) +
        0.0274177) ^ 21 := by norm_num
    _ ≤ _ := by gcongr

/-! ### The induction step: `ĝ(p)^{21} ≤ p²` for `p ≥ 37` -/

theorem ghat_pow_le {p : ℕ} (hp : 37 ≤ p) : gHatQ p ^ 21 ≤ (p : ℝ) ^ 2 := by
  have hp' : (37 : ℝ) ≤ p := by exact_mod_cast hp
  rw [ghat_of_gt (by omega)]
  set y := (p : ℝ) ^ (-(2 / 3 : ℝ))
  have hy0 : 0 ≤ y := by positivity
  have hy : y ≤ 0.0905 := by
    have h37 : (11.06 : ℝ) ≤ (37 : ℝ) ^ (2 / 3 : ℝ) := by
      calc (11.06 : ℝ) = ((11.06 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ ((37 : ℝ) ^ (2 : ℕ)) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = (37 : ℝ) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have : (37 : ℝ) ^ (2 / 3 : ℝ) ≤ (p : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hp' (by norm_num)
    simp only [y]
    rw [Real.rpow_neg (by linarith), ← one_div]
    calc 1 / (p : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 11.06 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ ≤ 0.0905 := by norm_num
  have hpos : 0 < (p : ℝ) / (p - 1) * (1 + y) := by
    have : 0 < (p : ℝ) / (p - 1) := div_pos (by linarith) (by linarith)
    positivity
  -- logs
  have hl1 : Real.log ((p : ℝ) / (p - 1)) ≤ 1 / 36 := by
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p) (by linarith : (0 : ℝ) < p - 1))
    have e : (p : ℝ) / (p - 1) - 1 = 1 / (p - 1) := by rw [div_sub_one (by linarith)]; ring
    have : 1 / ((p : ℝ) - 1) ≤ 1 / 36 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hl2 : Real.log (1 + y) ≤ 0.0905 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + y); linarith
  have hlp : 3.6 ≤ Real.log p := by
    have h37 := le_log_num (z := 37) 3 0.6 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at h37
    have := Real.log_le_log (by norm_num) hp'
    linarith
  have key : Real.log (((p : ℝ) / (p - 1) * (1 + y)) ^ 21) ≤ Real.log ((p : ℝ) ^ 2) := by
    rw [Real.log_pow, Real.log_pow, Real.log_mul (div_pos (by linarith) (by linarith)).ne'
      (by linarith : (0 : ℝ) < 1 + y).ne']
    push_cast; linarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).1 key

theorem IHk_step {k : ℕ} (hk : 11 ≤ k) (ih : IHk k) : IHk (k + 1) := by
  obtain ⟨hκ, hmain⟩ := ih
  set p := Nat.nth Nat.Prime k
  have hpp : p.Prime := Nat.prime_nth_prime k
  have hp37 : 37 ≤ p := by
    have := Nat.nth_monotone Nat.infinite_setOfPred_prime hk
    rw [nth_primes.2.2.2.2.2.2.2.2.2.2.2] at this; exact this
  have hp' : (37 : ℝ) ≤ p := by exact_mod_cast hp37
  have hprim0 : (0 : ℝ) < primk k := by
    unfold primk; push_cast
    exact prod_pos fun i _ => by exact_mod_cast (Nat.prime_nth_prime i).pos
  -- `κ` increases
  have hκ' : kapk k (primk k) ≤ kapk (k + 1) (primk (k + 1)) := by
    unfold kapk
    rw [Sk_succ, primk_succ]
    have hsh : shat p = Real.log p / p := by unfold shat; rw [if_neg (by omega)]
    rw [hsh]; push_cast
    rw [Real.log_mul hprim0.ne' (by positivity)]
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have : Real.log p / p ≤ Real.log p := div_le_self hlp (by linarith)
    linarith
  refine ⟨lt_of_lt_of_le hκ hκ', ?_⟩
  rw [Gk_succ]
  have hg := ghat_pow_le hp37
  have hg0 : 0 ≤ gHatQ p := by linarith [one_le_ghat p]
  have hsq : ((primk (k + 1) : ℕ) : ℝ) ^ 2 = ((primk k : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
    rw [primk_succ]; push_cast; ring
  rw [hsq]
  calc (7.4527 * (Gk k * gHatQ p)) ^ 21 = (7.4527 * Gk k) ^ 21 * gHatQ p ^ 21 := by ring
    _ ≤ ((103 / 120 : ℝ) ^ 9 * ((primk k : ℕ) : ℝ) ^ 2 * kapk k (primk k) ^ 21) * (p : ℝ) ^ 2 :=
        mul_le_mul hmain hg (by positivity) (by positivity)
    _ ≤ (103 / 120 : ℝ) ^ 9 * (((primk k : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ 2) *
          kapk (k + 1) (primk (k + 1)) ^ 21 := by
        have := pow_le_pow_left₀ hκ.le hκ' 21
        have h0 : 0 ≤ (103 / 120 : ℝ) ^ 9 * ((primk k : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ 2 := by positivity
        nlinarith

theorem IHk_all {k : ℕ} (hk : 11 ≤ k) : IHk k := by
  induction k, hk using Nat.le_induction with
  | base => exact IHk_11
  | succ k hk ih => exact IHk_step hk ih

/-! ### `λ(q)⁷ ≤ a⁹ q²` -/

theorem lamQ_pow_le {q : ℕ} (hq : 22000000000 ≤ q) :
    lamQ q ^ 7 ≤ (103 / 120 : ℝ) ^ 9 * (q : ℝ) ^ 2 := by
  have hq1 : 1 ≤ q := by omega
  have hq' : (22000000000 : ℝ) ≤ q := by exact_mod_cast hq
  set k := q.primeFactors.card
  have hlq : 23.8143 ≤ Real.log q := log_Q1_ge.trans (Real.log_le_log (by norm_num) hq')
  have hlam0 : 0 ≤ lamQ q := by
    unfold lamQ
    have := kapQ_pos hq1; have := qphi_pos hq1; have := f1q_pos q
    positivity
  rcases Nat.lt_or_ge k 11 with hk | hk
  · -- `k ≤ 10`
    have hG : Gk k ≤ Gk 10 := by
      unfold Gk
      exact prod_le_prod_of_subset_of_one_le₀ (range_subset_range.2 (by omega))
        (fun i _ => by linarith [one_le_ghat (Nat.nth Nat.Prime i)]) fun i _ _ => one_le_ghat _
    have hS : Sk k ≤ Sk 10 := by
      unfold Sk
      exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
        fun i _ _ => shat_nonneg _
    set κ0 : ℝ := 0.3726 * (23.8143 - (2 * 1.098613 / 3 + 1.609442 / 5 + 1.94597 / 7 +
      2.397896 / 11 + 2.564952 / 13 + 2.833241 / 17 + 2.944498 / 19 + 3.135495 / 23 +
      3.367296 / 29)) + 0.0274177 with hκ0def
    have hκ0 : 0 < κ0 := by norm_num [hκ0def]
    have hκ : κ0 ≤ kapk k q := by
      unfold kapk; have := Sk_10_le; rw [hκ0def]; nlinarith
    obtain ⟨hlam, -⟩ := lamQ_le_k hq1 (lt_of_lt_of_le hκ0 hκ)
    have hG0 : 0 ≤ Gk k := by
      unfold Gk; exact prod_nonneg fun i _ => by linarith [one_le_ghat (Nat.nth Nat.Prime i)]
    have h1 : lamQ q ≤ (7.4527 * Gk 10 / κ0) ^ 3 :=
      hlam.trans (pow_le_pow_left₀ (div_nonneg (mul_nonneg (by norm_num) hG0) (hκ0.le.trans hκ))
        (div_le_div₀ (mul_nonneg (by norm_num) (hG0.trans hG)) (by linarith) hκ0 hκ) 3)
    have h2 := base_10 (κ := κ0) le_rfl
    calc lamQ q ^ 7 ≤ ((7.4527 * Gk 10 / κ0) ^ 3) ^ 7 := pow_le_pow_left₀ hlam0 h1 7
      _ = (7.4527 * Gk 10) ^ 21 / κ0 ^ 21 := by rw [← pow_mul, div_pow]
      _ ≤ (103 / 120 : ℝ) ^ 9 * (22000000000 : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]; exact h2
      _ ≤ (103 / 120 : ℝ) ^ 9 * (q : ℝ) ^ 2 := by gcongr
  · -- `k ≥ 11`
    obtain ⟨hκ, hmain⟩ := IHk_all hk
    have hprim : ((primk k : ℕ) : ℝ) ≤ q := by
      have hPp : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
      have h2 := (TernaryGoldbach.Prelim.exch q.primeFactors hPp).2
      have h3 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
      unfold primk; exact_mod_cast h2.trans h3
    have hprim0 : (0 : ℝ) < primk k := by
      unfold primk; push_cast
      exact prod_pos fun i _ => by exact_mod_cast (Nat.prime_nth_prime i).pos
    have hκq : kapk k (primk k) ≤ kapk k q := by
      unfold kapk; have := Real.log_le_log hprim0 hprim; linarith
    obtain ⟨hlam, -⟩ := lamQ_le_k hq1 (lt_of_lt_of_le hκ hκq)
    have hG0 : 0 ≤ Gk k := by
      unfold Gk; exact prod_nonneg fun i _ => by linarith [one_le_ghat (Nat.nth Nat.Prime i)]
    have h1 : lamQ q ≤ (7.4527 * Gk k / kapk k (primk k)) ^ 3 :=
      hlam.trans (pow_le_pow_left₀ (div_nonneg (mul_nonneg (by norm_num) hG0) (hκ.le.trans hκq))
        (div_le_div₀ (mul_nonneg (by norm_num) hG0) le_rfl hκ hκq) 3)
    calc lamQ q ^ 7 ≤ ((7.4527 * Gk k / kapk k (primk k)) ^ 3) ^ 7 := pow_le_pow_left₀ hlam0 h1 7
      _ = (7.4527 * Gk k) ^ 21 / kapk k (primk k) ^ 21 := by rw [← pow_mul, div_pow]
      _ ≤ (103 / 120 : ℝ) ^ 9 * ((primk k : ℕ) : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]; exact hmain
      _ ≤ (103 / 120 : ℝ) ^ 9 * (q : ℝ) ^ 2 := by gcongr

/-! ### `large_q_hS` -/

/-- `log q ≤ 0.13819 q^{2/9}` for `q ≥ 2.2·10¹⁰`. -/
theorem log_le_rpow29 {q : ℝ} (hq : 22000000000 ≤ q) : Real.log q ≤ 0.13819 * q ^ ((2 : ℝ) / 9) := by
  have hq0 : 0 < q := by linarith
  have hx : 23.8143 ≤ Real.log q := log_Q1_ge.trans (Real.log_le_log (by norm_num) hq)
  have e : q ^ ((2 : ℝ) / 9) = Real.exp (2 * Real.log q / 9) := by
    rw [Real.rpow_def_of_pos hq0]; ring_nf
  set x := Real.log q
  rw [e]
  -- `exp(y) ≥ exp(5.292)(1 + (y − 5.292))` and `exp(5.292) ≥ 198.7`
  have h1 : (198.7 : ℝ) ≤ Real.exp 5.292 := by
    have := exp_ge_aux 5 (f := 0.292) (by norm_num)
    have e2 : ((5 : ℕ) : ℝ) + 0.292 = 5.292 := by norm_num
    rw [e2] at this
    refine le_trans ?_ this
    unfold taylor6; norm_num
  have h2 : Real.exp 5.292 * (1 + (2 * x / 9 - 5.292)) ≤ Real.exp (2 * x / 9) := by
    have := Real.add_one_le_exp (2 * x / 9 - 5.292)
    have e3 : Real.exp (2 * x / 9) = Real.exp 5.292 * Real.exp (2 * x / 9 - 5.292) := by
      rw [← Real.exp_add]; ring_nf
    rw [e3]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h3 : 0 ≤ 1 + (2 * x / 9 - 5.292) := by linarith
  nlinarith

/-- **Large `q`**: for `q ≥ 2.2·10¹⁰` and `1 ≤ R < λ(q)`, `log q + 1.039 R ≤ 1.03 (qR)^{2/9}`. -/
theorem large_q_hS {q : ℕ} (hq : 22000000000 ≤ q) {R : ℝ} (hR1 : 1 ≤ R) (hR : R < lamQ q) :
    Real.log q + 1.039 * R ≤ 1.03 * ((q : ℝ) * R) ^ ((2 : ℝ) / 9) := by
  have hq' : (22000000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hR0 : 0 < R := by linarith
  have hlam := lamQ_pow_le hq
  have hR7 : R ^ 7 ≤ (103 / 120 : ℝ) ^ 9 * (q : ℝ) ^ 2 :=
    (pow_le_pow_left₀ hR0.le hR.le 7).trans hlam
  -- `R^{7/9} ≤ (103/120) q^{2/9}`
  have h79 : R ^ ((7 : ℝ) / 9) ≤ (103 / 120 : ℝ) * (q : ℝ) ^ ((2 : ℝ) / 9) := by
    have h := Real.rpow_le_rpow (by positivity) hR7 (by norm_num : (0 : ℝ) ≤ 1 / 9)
    have eL : (R ^ 7) ^ ((1 : ℝ) / 9) = R ^ ((7 : ℝ) / 9) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; norm_num
    have eR : ((103 / 120 : ℝ) ^ 9 * (q : ℝ) ^ 2) ^ ((1 : ℝ) / 9) =
        (103 / 120 : ℝ) * (q : ℝ) ^ ((2 : ℝ) / 9) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (q : ℝ), ← Real.rpow_mul hq0.le]
      norm_num
    rwa [eL, eR] at h
  have hsplit : R = R ^ ((2 : ℝ) / 9) * R ^ ((7 : ℝ) / 9) := by
    rw [← Real.rpow_add hR0]; norm_num
  have hqR : ((q : ℝ) * R) ^ ((2 : ℝ) / 9) = (q : ℝ) ^ ((2 : ℝ) / 9) * R ^ ((2 : ℝ) / 9) :=
    Real.mul_rpow hq0.le hR0.le
  have hRle : R ≤ (103 / 120 : ℝ) * ((q : ℝ) * R) ^ ((2 : ℝ) / 9) := by
    rw [hqR]
    calc R = R ^ ((2 : ℝ) / 9) * R ^ ((7 : ℝ) / 9) := hsplit
      _ ≤ R ^ ((2 : ℝ) / 9) * ((103 / 120 : ℝ) * (q : ℝ) ^ ((2 : ℝ) / 9)) :=
          mul_le_mul_of_nonneg_left h79 (by positivity)
      _ = _ := by ring
  have hlog := log_le_rpow29 hq'
  have hR29 : 1 ≤ R ^ ((2 : ℝ) / 9) := Real.one_le_rpow hR1 (by norm_num)
  have hq29 : 0 ≤ (q : ℝ) ^ ((2 : ℝ) / 9) := by positivity
  have hlog' : Real.log q ≤ 0.13819 * ((q : ℝ) * R) ^ ((2 : ℝ) / 9) := by
    rw [hqR]; nlinarith
  nlinarith

end TernaryGoldbach.MinorArcs
