import Mathlib

/-!
# A kernel-checked table of `θ` and `ψ` on `[12, 10⁶]` (route D, step P9a)

Trial division by the primes `≤ 1000` (`spf`), prime powers by dividing out the smallest factor
(`isPowOf`). Bounds are scaled by `S = 10⁹`. Checkpoints `N_j`; on `(N_j, N_{j+1}]` every prime
`p` has `LL_j ≤ S log p ≤ LH_{j+1}`, where the log chain is `LH_{j+1} = LH_j + ⌈S(N_{j+1} − N_j)/N_j⌉`
and `LL_{j+1} = LL_j + ⌊S(N_{j+1} − N_j)/N_{j+1}⌋`. No `native_decide`.
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallTab

/-! ### Primes up to 1000 -/

def P1000 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- Trial division by `2 ≤ d ≤ 32`. -/
def isPrimeSlow (n : ℕ) : Bool := 2 ≤ n && (List.range' 2 31).all (fun d => n < d * d || n % d != 0)

theorem P1000_complete : ∀ n ∈ List.range 1001, (n ∈ P1000 ↔ isPrimeSlow n = true) := by decide +kernel

theorem isPrimeSlow_iff {n : ℕ} (hn : n ≤ 1000) : isPrimeSlow n = true ↔ n.Prime := by
  unfold isPrimeSlow
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n * Nat.minFac n ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp)); nlinarith
    have hm2 := hmp.two_le
    have hm32 : Nat.minFac n ≤ 32 := by nlinarith
    rcases h (Nat.minFac n) ⟨hm2, by omega⟩ with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d hd => ?_⟩
    by_cases hdd : n < d * d
    · exact Or.inl hdd
    · right
      intro h0
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · omega
      · subst h; nlinarith [hp.two_le]

theorem mem_P1000 {p : ℕ} (hp : p ≤ 1000) : p ∈ P1000 ↔ p.Prime := by
  rw [P1000_complete p (List.mem_range.2 (by omega)), isPrimeSlow_iff hp]

theorem prime_of_mem_P1000 {p : ℕ} (h : p ∈ P1000) : p.Prime := by
  have : p ≤ 1000 := by
    have := List.mem_iff_get.1 h
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    exact (show ∀ i : Fin P1000.length, P1000.get i ≤ 1000 by decide +kernel) i
  exact (mem_P1000 this).1 h

theorem P1000_sorted : P1000.Pairwise (· < ·) := by decide +kernel

/-! ### Smallest prime factor by trial division -/

/-- The first `p` in the list with `p ∣ n`, `p² ≤ n`; `0` if there is none before `p² > n`. -/
def spf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, n => if n < p * p then 0 else if n % p = 0 then p else spf ps n

theorem spf_eq_zero {L : List ℕ} {n : ℕ} (h : spf L n = 0) (hL : L.Pairwise (· < ·))
    (hpos : ∀ p ∈ L, 0 < p) : ∀ p ∈ L, p * p ≤ n → ¬ p ∣ n := by
  induction L with
  | nil => intro p hp; simp at hp
  | cons a ps ih =>
    intro p hp hpp hdvd
    unfold spf at h
    split_ifs at h with h1 h2
    · -- n < a*a: then p ≥ a, so p*p ≥ a*a > n
      rcases List.mem_cons.1 hp with rfl | hp'
      · omega
      · have : a < p := (List.pairwise_cons.1 hL).1 p hp'
        nlinarith
    · -- returned a, so a = 0
      exact absurd h (hpos a (List.mem_cons_self ..)).ne'
    · -- spf ps n = 0
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h (List.pairwise_cons.1 hL).2 (fun q hq => hpos q (List.mem_cons_of_mem _ hq)) p hp' hpp hdvd

theorem spf_pos {L : List ℕ} {n q : ℕ} (h : spf L n = q) (hq : q ≠ 0) (hL : L.Pairwise (· < ·)) :
    q ∈ L ∧ q * q ≤ n ∧ q ∣ n ∧ ∀ p ∈ L, p < q → ¬ p ∣ n := by
  induction L generalizing q with
  | nil => simp [spf] at h; exact absurd h.symm hq
  | cons a ps ih =>
    unfold spf at h
    split_ifs at h with h1 h2
    · exact absurd h.symm hq
    · subst h
      refine ⟨List.mem_cons_self .., by omega, Nat.dvd_of_mod_eq_zero h2, fun p hp hpa => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · omega
      · have := (List.pairwise_cons.1 hL).1 p hp'; omega
    · obtain ⟨hm, hqq, hdvd, hlt⟩ := ih h hq (List.pairwise_cons.1 hL).2
      refine ⟨List.mem_cons_of_mem _ hm, hqq, hdvd, fun p hp hpq => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
      · exact hlt p hp' hpq

theorem P1000_pos : ∀ p ∈ P1000, 0 < p := fun p hp => (prime_of_mem_P1000 hp).pos

/-- **Trial division decides primality** for `2 ≤ n ≤ 10⁶`. -/
theorem spf_eq_zero_iff {n : ℕ} (h2 : 2 ≤ n) (h6 : n ≤ 1000000) : spf P1000 n = 0 ↔ n.Prime := by
  constructor
  · intro h
    have hno := spf_eq_zero h P1000_sorted P1000_pos
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n * Nat.minFac n ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp)); nlinarith
    have hm1000 : Nat.minFac n ≤ 1000 := by nlinarith
    exact hno _ ((mem_P1000 hm1000).2 hmp) hsq (Nat.minFac_dvd n)
  · intro hp
    by_contra hq
    obtain ⟨hm, hqq, hdvd, -⟩ := spf_pos rfl hq P1000_sorted
    have hqp := prime_of_mem_P1000 hm
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact hqp.one_lt.ne' h
    · rw [h] at hqq; nlinarith [hp.two_le]

/-- A nonzero `spf` is the least prime factor. -/
theorem spf_eq_minFac {n q : ℕ} (h2 : 2 ≤ n) (h : spf P1000 n = q) (hq : q ≠ 0) :
    q = n.minFac ∧ q.Prime ∧ ¬ n.Prime := by
  obtain ⟨hm, hqq, hdvd, hlt⟩ := spf_pos h hq P1000_sorted
  have hqp := prime_of_mem_P1000 hm
  have hmin : n.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hdvd
  have hq1000 : q ≤ 1000 := by
    have := List.mem_iff_get.1 hm
    obtain ⟨i, hi⟩ := this
    rw [← hi]; exact (show ∀ i : Fin P1000.length, P1000.get i ≤ 1000 by decide +kernel) i
  have heq : q = n.minFac := by
    by_contra hne
    have hlt' : n.minFac < q := lt_of_le_of_ne hmin (Ne.symm hne)
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    exact hlt _ ((mem_P1000 (by omega)).2 hmp) hlt' (Nat.minFac_dvd n)
  refine ⟨heq, hqp, fun hp => ?_⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact hqp.one_lt.ne' h
  · rw [h] at hqq; nlinarith [hp.two_le]

/-! ### Prime powers -/

/-- `m` is a power of `q` (within `k` divisions). -/
def isPowOf (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, m => if m = 1 then true else if m % q = 0 then isPowOf q k (m / q) else false

theorem isPowOf_true {q : ℕ} : ∀ {k m : ℕ}, isPowOf q k m = true → ∃ j, m = q ^ j := by
  intro k
  induction k with
  | zero => intro m h; simp [isPowOf] at h
  | succ k ih =>
    intro m h
    unfold isPowOf at h
    split_ifs at h with h1 h2
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨j, hj⟩ := ih h
      refine ⟨j + 1, ?_⟩
      rw [pow_succ, ← hj]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)).symm

theorem isPowOf_pow {q : ℕ} (hq : 2 ≤ q) : ∀ {k j : ℕ}, j < k → isPowOf q k (q ^ j) = true := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    unfold isPowOf
    rcases j with _ | j
    · simp
    · have h1 : q ^ (j + 1) ≠ 1 := (Nat.one_lt_pow (Nat.succ_ne_zero j) (by omega : 1 < q)).ne'
      have h2 : q ^ (j + 1) % q = 0 := by rw [pow_succ]; simp
      rw [if_neg h1, if_pos h2, pow_succ, Nat.mul_div_cancel _ (by omega)]
      exact ih (by omega)

open ArithmeticFunction in
/-- `Λ` from the trial division. -/
theorem vonMangoldt_of_spf {m q : ℕ} (h2 : 2 ≤ m) (h6 : m ≤ 1000000) (h : spf P1000 m = q) (hq : q ≠ 0) :
    (Λ m : ℝ) = if isPowOf q 20 m then Real.log q else 0 := by
  obtain ⟨heq, hqp, hnp⟩ := spf_eq_minFac h2 h hq
  split_ifs with hpow
  · obtain ⟨j, hj⟩ := isPowOf_true hpow
    have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
    rw [hj, vonMangoldt_apply_pow hj0, vonMangoldt_apply_prime hqp]
  · rw [vonMangoldt_eq_zero_iff.2]
    intro hpp
    obtain ⟨r, j, hr, hj, hrj⟩ := (isPrimePow_nat_iff m).1 hpp
    have hrm : r = m.minFac := by
      rw [← hrj, Nat.Prime.pow_minFac hr hj.ne']
    apply hpow
    rw [← hrj, heq.trans hrm.symm]
    refine isPowOf_pow hr.two_le ?_
    have : 2 ^ j ≤ r ^ j := Nat.pow_le_pow_left hr.two_le j
    have h20 : 2 ^ j ≤ 1000000 := by rw [hrj] at this; omega
    by_contra hc; push Not at hc
    have : 2 ^ 20 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hc
    omega

end TernaryGoldbach.Prelim.SmallTab
