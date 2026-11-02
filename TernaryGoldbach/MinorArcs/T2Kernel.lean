import TernaryGoldbach.Prelim.RamareHarm

/-!
# Kernel tools for the `T₂` computations

Data structures and functions evaluated by the kernel (`decide +kernel`) in `SmallG2.lean` and
`G2TailNum.lean`, with their specifications:
* `Tr`: a binary trie on `ℕ` keys (`Tr.get_set`);
* `oddPrimes a`: the odd prime factors of `a` by trial division (`mem_oddPrimes`);
* `dvs ps`: the divisors of a product of distinct primes, with their Möbius signs (`sum_dvs`);
* `lloN/lloD ≤ log(1 + 1/k) ≤ lhiN/lhiD` (six terms of the artanh series).
-/

open Finset

namespace TernaryGoldbach.MinorArcs.T2K

/-! ### A binary trie -/

/-- A binary trie: key `0` at the root, odd keys `k` in the left subtree at `k / 2`, even keys
`k ≠ 0` in the right subtree at `k / 2`. -/
inductive Tr (α : Type) where
  | nil
  | node (v : α) (l r : Tr α)

variable {α : Type}

/-- The value at key `k` (default `z`). -/
def Tr.get (z : α) : Tr α → ℕ → α
  | .nil, _ => z
  | .node v l r, k => if k = 0 then v else if k % 2 = 1 then l.get z (k / 2) else r.get z (k / 2)

/-- Root value and subtrees. -/
def Tr.view (z : α) : Tr α → α × Tr α × Tr α
  | .nil => (z, .nil, .nil)
  | .node v l r => (v, l, r)

/-- Set key `k` to `x` (fuel `f`; enough if `2k + 1 < 2^f`). -/
def Tr.set (z : α) : ℕ → Tr α → ℕ → α → Tr α
  | 0, t, _, _ => t
  | f + 1, t, k, x =>
    let w := t.view z
    if k = 0 then .node x w.2.1 w.2.2
    else if k % 2 = 1 then .node w.1 (Tr.set z f w.2.1 (k / 2) x) w.2.2
    else .node w.1 w.2.1 (Tr.set z f w.2.2 (k / 2) x)

theorem Tr.get_view (z : α) (t : Tr α) (k : ℕ) :
    t.get z k = if k = 0 then (t.view z).1 else if k % 2 = 1 then (t.view z).2.1.get z (k / 2)
      else (t.view z).2.2.get z (k / 2) := by
  cases t <;> simp [Tr.get, Tr.view]

theorem Tr.get_node (z v : α) (l r : Tr α) (k : ℕ) :
    (Tr.node v l r).get z k = if k = 0 then v else if k % 2 = 1 then l.get z (k / 2)
      else r.get z (k / 2) := rfl

theorem Tr.get_set (z : α) : ∀ (f : ℕ) (t : Tr α) (k j : ℕ) (x : α), 2 * k + 1 < 2 ^ f →
    (Tr.set z f t k x).get z j = if j = k then x else t.get z j := by
  intro f
  induction f with
  | zero => intro t k j x h; simp at h
  | succ f ih =>
    intro t k j x hk
    rw [Tr.get_view z t j]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Tr.set, ite_true, Tr.get_node]
      by_cases hj : j = 0 <;> simp [hj]
    · have hk' : 2 * (k / 2) + 1 < 2 ^ f := by
        have h1 : k < 2 ^ f := by rw [pow_succ] at hk; omega
        have h2 : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
        have h3 : 2 ^ f % 2 = 0 ∨ f = 0 := by
          rcases f with _ | f
          · right; rfl
          · left; rw [pow_succ]; simp
        rcases h3 with h3 | h3
        · omega
        · subst h3; simp at h1; omega
      by_cases hko : k % 2 = 1
      · simp only [Tr.set, hk0, ite_false, hko, ite_true, Tr.get_node]
        by_cases hj : j = 0
        · simp [hj, Ne.symm hk0]
        · simp only [hj, ite_false]
          by_cases hjo : j % 2 = 1
          · simp only [hjo, ite_true]
            rw [ih _ _ _ _ hk']
            have : j / 2 = k / 2 ↔ j = k := by omega
            simp [this]
          · have : j ≠ k := by omega
            simp [hjo, this]
      · simp only [Tr.set, hk0, ite_false, hko, Tr.get_node]
        by_cases hj : j = 0
        · simp [hj, Ne.symm hk0]
        · simp only [hj, ite_false]
          by_cases hjo : j % 2 = 1
          · have : j ≠ k := by omega
            simp [hjo, this]
          · simp only [hjo, ite_false]
            rw [ih _ _ _ _ hk']
            have : j / 2 = k / 2 ↔ j = k := by omega
            simp [this]

theorem Tr.get_nil (z : α) (k : ℕ) : (Tr.nil : Tr α).get z k = z := rfl

/-! ### Trial division -/

/-- Divide out all factors `p` (fuel `f`). -/
def strip : ℕ → ℕ → ℕ → ℕ
  | 0, m, _ => m
  | f + 1, m, p => if m % p = 0 then strip f (m / p) p else m

theorem strip_spec {p : ℕ} (hp : p.Prime) : ∀ (f m : ℕ), 0 < m → m < 2 ^ f →
    0 < strip f m p ∧ strip f m p ∣ m ∧ ∀ q, q.Prime → (q ∣ strip f m p ↔ q ∣ m ∧ q ≠ p) := by
  intro f
  induction f with
  | zero => intro m h0 h1; simp at h1; omega
  | succ f ih =>
    intro m h0 h1
    simp only [strip]
    split_ifs with hd
    · have hpd : p ∣ m := Nat.dvd_of_mod_eq_zero hd
      have h2 := hp.two_le
      have hm0 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd h0 hpd) hp.pos
      have hm1 : m / p < 2 ^ f := by
        rw [Nat.div_lt_iff_lt_mul hp.pos]; rw [pow_succ] at h1; nlinarith
      obtain ⟨a1, a2, a3⟩ := ih (m / p) hm0 hm1
      refine ⟨a1, a2.trans (Nat.div_dvd_of_dvd hpd), fun q hq => ?_⟩
      rw [a3 q hq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.trans (Nat.div_dvd_of_dvd hpd), h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hc : Nat.Coprime q p := (Nat.coprime_primes hq hp).2 h2
        obtain ⟨k, hk⟩ := hpd
        rw [hk, Nat.mul_div_cancel_left _ hp.pos]
        rw [hk] at h1
        exact hc.dvd_of_dvd_mul_left h1
    · refine ⟨h0, dvd_rfl, fun q hq => ⟨fun h => ⟨h, fun e => hd ?_⟩, fun h => h.1⟩⟩
      subst e; exact Nat.mod_eq_zero_of_dvd h

theorem strip_spec' {p : ℕ} (hp : p.Prime) {m : ℕ} (h0 : 0 < m) :
    0 < strip m m p ∧ strip m m p ∣ m ∧ ∀ q, q.Prime → (q ∣ strip m m p ↔ q ∣ m ∧ q ≠ p) :=
  strip_spec hp m m h0 Nat.lt_two_pow_self

/-- The primes `≥ d` dividing `m`, by trial division with odd `d` (fuel `f`). -/
def opr : ℕ → ℕ → ℕ → List ℕ
  | 0, m, _ => if m ≤ 1 then [] else [m]
  | f + 1, m, d => if m ≤ 1 then [] else if m < d * d then [m]
      else if m % d = 0 then d :: opr f (strip m m d) (d + 2) else opr f m (d + 2)

/-- The odd prime factors of `a`. -/
def oddPrimes (a : ℕ) : List ℕ := opr a (strip a a 2) 3

theorem prime_of_small {m d : ℕ} (h1 : 1 < m) (hd : ∀ q, q.Prime → q ∣ m → d ≤ q) (hm : m < d * d) :
    m.Prime := by
  by_contra hnp
  have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
  have h1' := hd _ hmf (Nat.minFac_dvd m)
  have := Nat.minFac_sq_le_self (by omega) hnp
  nlinarith

theorem opr_spec : ∀ (f m d : ℕ), 3 ≤ d → d % 2 = 1 → 0 < m → m % 2 = 1 →
    (∀ q, q.Prime → q ∣ m → d ≤ q) → m < (d + 2 * f) * (d + 2 * f) →
    (∀ q, q ∈ opr f m d ↔ q.Prime ∧ q ∣ m) ∧ (opr f m d).Nodup ∧ ∀ q ∈ opr f m d, d ≤ q := by
  have single : ∀ m d : ℕ, 0 < m → (∀ q, q.Prime → q ∣ m → d ≤ q) → m < d * d →
      (∀ q, q ∈ (if m ≤ 1 then [] else [m]) ↔ q.Prime ∧ q ∣ m) ∧
        (if m ≤ 1 then [] else [m]).Nodup ∧ ∀ q ∈ (if m ≤ 1 then [] else [m]), d ≤ q := by
    intro m d h0 hd hm
    split_ifs with h1
    · have : m = 1 := by omega
      subst this
      refine ⟨fun q => ?_, List.nodup_nil, fun q h => by simp at h⟩
      simp only [List.not_mem_nil, false_iff, not_and]
      exact fun hq hq1 => hq.one_lt.ne' (Nat.dvd_one.1 hq1)
    · have hp := prime_of_small (by omega) hd hm
      refine ⟨fun q => ?_, List.nodup_singleton _, fun q hq => ?_⟩
      · simp only [List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨hp, dvd_rfl⟩
        · rintro ⟨hq, hqm⟩; exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqm)
      · rw [List.mem_singleton.1 hq]; exact hd m hp dvd_rfl
  intro f
  induction f with
  | zero =>
    intro m d _ _ h0 _ hd hm
    simp only [opr]
    exact single m d h0 hd (by simpa using hm)
  | succ f ih =>
    intro m d h3 hdo h0 hmo hd hm
    simp only [opr]
    by_cases h1 : m ≤ 1
    · simp only [h1, ↓reduceIte]
      have := single m d h0 hd
      simp only [h1, ite_true] at this
      exact this (by nlinarith)
    simp only [h1, ↓reduceIte]
    by_cases hsm : m < d * d
    · simp only [hsm, ↓reduceIte]
      have := single m d h0 hd hsm
      simp only [h1, ite_false] at this
      exact this
    simp only [hsm, ↓reduceIte]
    have hodd : ∀ q, q.Prime → q ∣ m → q % 2 = 1 := by
      intro q hq hqm
      rcases hq.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    by_cases hdm : m % d = 0
    · simp only [hdm, ↓reduceIte]
      have hdd : d ∣ m := Nat.dvd_of_mod_eq_zero hdm
      have hdp : d.Prime := by
        have hmf := Nat.minFac_prime (show d ≠ 1 by omega)
        have := hd _ hmf ((Nat.minFac_dvd d).trans hdd)
        have hle := Nat.minFac_le (show 0 < d by omega)
        rw [← le_antisymm hle this]; exact hmf
      obtain ⟨s0, s1, s2⟩ := strip_spec' hdp h0
      set m' := strip m m d
      have hm'o : m' % 2 = 1 := by
        rcases Nat.even_or_odd m' with he | ho
        · exfalso; have := (even_iff_two_dvd.1 he).trans s1; omega
        · exact Nat.odd_iff.1 ho
      have hd' : ∀ q, q.Prime → q ∣ m' → d + 2 ≤ q := by
        intro q hq hqm
        obtain ⟨hqm', hqd⟩ := (s2 q hq).1 hqm
        have := hd q hq hqm'
        have := hodd q hq hqm'
        omega
      have hm' : m' < (d + 2 + 2 * f) * (d + 2 + 2 * f) := by
        have := Nat.le_of_dvd h0 s1
        nlinarith
      obtain ⟨i1, i2, i3⟩ := ih m' (d + 2) (by omega) (by omega) s0 hm'o hd' hm'
      refine ⟨fun q => ?_, ?_, ?_⟩
      · rw [List.mem_cons, i1]
        constructor
        · rintro (rfl | ⟨hq, hqm⟩)
          · exact ⟨hdp, hdd⟩
          · exact ⟨hq, hqm.trans s1⟩
        · rintro ⟨hq, hqm⟩
          by_cases hqd : q = d
          · left; exact hqd
          · right; exact ⟨hq, (s2 q hq).2 ⟨hqm, hqd⟩⟩
      · refine List.nodup_cons.2 ⟨fun h => ?_, i2⟩
        have := i3 d h; omega
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact le_rfl
        · have := i3 q hq; omega
    · simp only [hdm, ↓reduceIte]
      have hd' : ∀ q, q.Prime → q ∣ m → d + 2 ≤ q := by
        intro q hq hqm
        have h1 := hd q hq hqm
        have h2 := hodd q hq hqm
        have h3 : q ≠ d := by rintro rfl; exact hdm (Nat.mod_eq_zero_of_dvd hqm)
        omega
      obtain ⟨i1, i2, i3⟩ := ih m (d + 2) (by omega) (by omega) h0 hmo hd' (by nlinarith)
      exact ⟨i1, i2, fun q hq => by have := i3 q hq; omega⟩

theorem oddPrimes_spec {a : ℕ} (ha : 0 < a) :
    (∀ q, q ∈ oddPrimes a ↔ q.Prime ∧ q ∣ a ∧ q ≠ 2) ∧ (oddPrimes a).Nodup := by
  obtain ⟨s0, s1, s2⟩ := strip_spec' Nat.prime_two ha
  set m := strip a a 2
  have hmo : m % 2 = 1 := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso; have := (s2 2 Nat.prime_two).1 (even_iff_two_dvd.1 he); exact this.2 rfl
    · exact Nat.odd_iff.1 ho
  have hd : ∀ q, q.Prime → q ∣ m → 3 ≤ q := by
    intro q hq hqm
    have := ((s2 q hq).1 hqm).2
    have := hq.two_le
    omega
  have hm : m < (3 + 2 * a) * (3 + 2 * a) := by
    have := Nat.le_of_dvd ha s1; nlinarith
  obtain ⟨i1, i2, -⟩ := opr_spec a m 3 le_rfl rfl s0 hmo hd hm
  refine ⟨fun q => ?_, i2⟩
  unfold oddPrimes
  rw [i1]
  constructor
  · rintro ⟨hq, hqm⟩; exact ⟨hq, ((s2 q hq).1 hqm).1, ((s2 q hq).1 hqm).2⟩
  · rintro ⟨hq, hqa, hq2⟩; exact ⟨hq, (s2 q hq).2 ⟨hqa, hq2⟩⟩

theorem mem_oddPrimes {a q : ℕ} (ha : 0 < a) : q ∈ oddPrimes a ↔ q.Prime ∧ q ∣ a ∧ q ≠ 2 :=
  (oddPrimes_spec ha).1 q

theorem nodup_oddPrimes {a : ℕ} (ha : 0 < a) : (oddPrimes a).Nodup := (oddPrimes_spec ha).2

theorem toFinset_oddPrimes {a : ℕ} (ha : 0 < a) :
    (oddPrimes a).toFinset = a.primeFactors.filter (· ≠ 2) := by
  ext q
  rw [List.mem_toFinset, mem_oddPrimes ha, mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- For odd `n`, `∏ (oddPrimes n) = ∏_{p ∣ n} p`. -/
theorem prod_oddPrimes {n : ℕ} (hn : Odd n) : (oddPrimes n).prod = ∏ p ∈ n.primeFactors, p := by
  have hn0 : 0 < n := hn.pos
  have h := List.prod_toFinset (fun p : ℕ => p) (nodup_oddPrimes hn0)
  rw [List.map_id'] at h
  rw [← h, toFinset_oddPrimes hn0, filter_true_of_mem]
  intro p hp h2
  subst h2
  exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))

theorem squarefree_iff_prod_oddPrimes {n : ℕ} (hn : Odd n) :
    Squarefree n ↔ (oddPrimes n).prod = n := by
  rw [prod_oddPrimes hn]
  constructor
  · exact Nat.prod_primeFactors_of_squarefree
  · intro h
    rw [← h]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq

/-! ### Divisors of a product of distinct primes -/

/-- The divisors of `∏ ps` with signs: `true` for `μ = 1`. -/
def dvs : List ℕ → List (ℕ × Bool)
  | [] => [(1, true)]
  | p :: ps => let r := dvs ps; r ++ r.map (fun x => (x.1 * p, !x.2))

open ArithmeticFunction in
theorem dvs_spec : ∀ ps : List ℕ, ps.Nodup → (∀ p ∈ ps, p.Prime) →
    ((dvs ps).map Prod.fst).Nodup ∧ (∀ d, d ∈ (dvs ps).map Prod.fst ↔ d ∣ ps.prod) ∧
      ∀ x ∈ dvs ps, (moebius x.1 : ℤ) = if x.2 then 1 else -1 := by
  intro ps
  induction ps with
  | nil =>
    intro _ _
    refine ⟨by simp [dvs], fun d => by simp [dvs], fun x hx => ?_⟩
    simp only [dvs, List.mem_singleton] at hx
    subst hx; simp
  | cons p ps ih =>
    intro hnd hpr
    obtain ⟨hp_nin, hnd'⟩ := List.nodup_cons.1 hnd
    have hp : p.Prime := hpr p List.mem_cons_self
    obtain ⟨i1, i2, i3⟩ := ih hnd' fun q hq => hpr q (List.mem_cons_of_mem _ hq)
    have hpP : ¬ p ∣ ps.prod := by
      intro h
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.prime).1 h
      have hq' : q.Prime := hpr q (List.mem_cons_of_mem _ hq)
      rw [(Nat.prime_dvd_prime_iff_eq hp hq')] at hpq
      subst hpq; exact hp_nin hq
    have hnotdvd : ∀ e, e ∣ ps.prod → ¬ p ∣ e := fun e he hpe => hpP (hpe.trans he)
    simp only [dvs, List.map_append, List.map_map]
    have hfun : (Prod.fst ∘ fun x : ℕ × Bool => (x.1 * p, !x.2)) = (fun e => e * p) ∘ Prod.fst := by
      funext x; rfl
    rw [hfun, ← List.map_map]
    refine ⟨?_, fun d => ?_, fun x hx => ?_⟩
    · refine List.nodup_append.2 ⟨i1, (i1.map (fun a b h => Nat.eq_of_mul_eq_mul_right hp.pos h)), ?_⟩
      intro a ha b hb hab
      subst hab
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
      exact hnotdvd _ ((i2 _).1 ha) (dvd_mul_left p e)
    · rw [List.mem_append, i2, List.mem_map, List.prod_cons]
      constructor
      · rintro (h | ⟨e, he, rfl⟩)
        · exact h.mul_left p
        · rw [mul_comm e p]; exact Nat.mul_dvd_mul_left p ((i2 e).1 he)
      · intro h
        by_cases hpd : p ∣ d
        · right
          obtain ⟨e, rfl⟩ := hpd
          refine ⟨e, (i2 e).2 ((Nat.mul_dvd_mul_iff_left hp.pos).1 h), mul_comm _ _⟩
        · left
          exact ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))).dvd_of_dvd_mul_left h
    · rcases List.mem_append.1 hx with hx | hx
      · exact i3 x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have hyd : y.1 ∣ ps.prod := (i2 y.1).1 (List.mem_map_of_mem hy)
        have hc : Nat.Coprime y.1 p :=
          Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (hnotdvd _ hyd))
        simp only
        rw [isMultiplicative_moebius.map_mul_of_coprime hc, moebius_apply_prime hp]
        rw [i3 y hy]
        cases y.2 <;> simp

theorem toFinset_dvs {ps : List ℕ} (hnd : ps.Nodup) (hpr : ∀ p ∈ ps, p.Prime) :
    ((dvs ps).map Prod.fst).toFinset = ps.prod.divisors := by
  have h0 : ps.prod ≠ 0 := List.prod_ne_zero (fun h => (Nat.not_prime_zero (hpr 0 h)))
  ext d
  rw [List.mem_toFinset, (dvs_spec ps hnd hpr).2.1, Nat.mem_divisors]
  exact ⟨fun h => ⟨h, h0⟩, fun h => h.1⟩

/-- Sums over `dvs ps` are sums over the divisors of `∏ ps`. -/
theorem sum_dvs {β : Type*} [AddCommMonoid β] (g : ℕ → β) {ps : List ℕ} (hnd : ps.Nodup)
    (hpr : ∀ p ∈ ps, p.Prime) :
    ((dvs ps).map (fun x => g x.1)).sum = ∑ d ∈ ps.prod.divisors, g d := by
  rw [← toFinset_dvs hnd hpr, List.sum_toFinset _ (dvs_spec ps hnd hpr).1, List.map_map]
  rfl

theorem coprime_prod_of_not_mem {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hpr : ∀ q ∈ ps, q.Prime)
    (hn : p ∉ ps) : Nat.Coprime p ps.prod := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.prime).1 h
  rw [Nat.prime_dvd_prime_iff_eq hp (hpr q hq)] at hpq
  subst hpq; exact hn hq

open ArithmeticFunction in
theorem sigma_prod_primes : ∀ ps : List ℕ, ps.Nodup → (∀ p ∈ ps, p.Prime) →
    sigma 1 ps.prod = (ps.map (· + 1)).prod := by
  intro ps
  induction ps with
  | nil => intro _ _; simp
  | cons p ps ih =>
    intro hnd hpr
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    have hp := hpr p List.mem_cons_self
    have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hpr q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons, isMultiplicative_sigma.map_mul_of_coprime
      (coprime_prod_of_not_mem hp hpr' hn), ih hnd' hpr', List.map_cons, List.prod_cons]
    have := sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one] at this
    rw [this]
    simp [Finset.sum_range_succ, add_comm]

open ArithmeticFunction in
theorem moebius_prod_primes : ∀ ps : List ℕ, ps.Nodup → (∀ p ∈ ps, p.Prime) →
    moebius ps.prod = (-1) ^ ps.length := by
  intro ps
  induction ps with
  | nil => intro _ _; simp
  | cons p ps ih =>
    intro hnd hpr
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    have hp := hpr p List.mem_cons_self
    have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hpr q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons, isMultiplicative_moebius.map_mul_of_coprime
      (coprime_prod_of_not_mem hp hpr' hn), ih hnd' hpr', moebius_apply_prime hp, List.length_cons,
      pow_succ]
    ring

/-! ### `log(1 + 1/k)`: six terms of `2 artanh(1/(2k+1))` -/

def lnum (q : ℕ) : ℕ := 2 * (3465 * q ^ 10 + 1155 * q ^ 8 + 693 * q ^ 6 + 495 * q ^ 4 + 385 * q ^ 2 + 315)
def lloN (k : ℕ) : ℕ := lnum (2 * k + 1)
def lloD (k : ℕ) : ℕ := 3465 * (2 * k + 1) ^ 11
def lhiN (k : ℕ) : ℕ := 13 * (4 * k * (k + 1)) * lnum (2 * k + 1) + 6930
def lhiD (k : ℕ) : ℕ := 45045 * (2 * k + 1) ^ 11 * (4 * k * (k + 1))

theorem log_bounds {k : ℕ} (hk : 1 ≤ k) :
    (lloN k : ℝ) / lloD k ≤ Real.log (1 + 1 / k) ∧ Real.log (1 + 1 / k) ≤ (lhiN k : ℝ) / lhiD k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨h1, h2⟩ := TernaryGoldbach.Prelim.RamPf.log_one_add_inv_bounds hk0 6
  rw [one_div]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2
  have hq : (0 : ℝ) < 2 * k + 1 := by positivity
  have hkk : (0 : ℝ) < 4 * k * (k + 1) := by positivity
  constructor
  · refine le_trans (le_of_eq ?_) h1
    simp only [lloN, lloD, lnum]
    push_cast
    field_simp
    ring
  · refine h2.trans (le_of_eq ?_)
    simp only [lhiN, lhiD, lnum]
    push_cast
    have : (1 : ℝ) - (1 / (2 * k + 1)) ^ 2 = 4 * k * (k + 1) / (2 * k + 1) ^ 2 := by
      field_simp; ring
    rw [this]
    field_simp
    ring

end TernaryGoldbach.MinorArcs.T2K
