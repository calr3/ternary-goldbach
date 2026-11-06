import TernaryGoldbach.MinorArcs.T2Kernel
import TernaryGoldbach.MinorArcs.G2Moebius

/-!
# `g₂(n)` for `n ≤ 10⁴`, checked by the kernel

With `f(r) = μ(r)/σ(r)` for odd `r` (`fo`), `g₂(n) = ∑_{d ≤ n} μ(d) A_d(n)²`,
`A_d(n) = ∑_{r ≤ n, d ∣ r} f(r)` ([H, (5.20)], `g2_eq_sum_dvd`). The kernel walks `n = 1, …, 10⁴`
with `F(r) = μ(r) ⌊D/σ(r)⌋` (`D = 10³⁰`) in place of `D f(r)`, keeping `Ã_d(n) = ∑_{r ≤ n, d ∣ r} F(r)`
for odd `d` in a trie and `G̃(n) = ∑_d μ(d) Ã_d(n)²`; at odd squarefree `n` it updates `Ã_d` for
the divisors `d` of `n` (`dvs`). Then `|G̃(n) − D² g₂(n)| ≤ 2 D n³` (`abs_Gtil_sub_le`).

Along the way it checks (`walkA`):
* for `16 ≤ n < 700`: `T₂ ≤ 0.37273` on `[n, n+1]`, using `T₂(S) = α_n + β_n/S` with
  `α_n = a(n) − a(⌊n/2⌋)/2`, `β_n = c(n) − c(⌊n/2⌋)` (`T2Small.lean`), where `a`, `c` are updated
  through the squarefree divisors of `n` only;
* for `700 ≤ n < 10⁴`: `¼ I(S) + J(S)/S ≤ 0.37273` on `[n, n+1]`, `I(S) = ∫₁^S g₂/y`,
  `J(S) = ∫₁^S |g₂|`;
and returns upper bounds for `D² I(10⁴)` and `D² J(10⁴)`.
-/

open Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs.SmallG2

open TernaryGoldbach.MinorArcs.T2K

/-! ### Definitions -/

def D : ℕ := 10 ^ 30
def S0 : ℕ := 700
def XX : ℕ := 10000

/-- `F(r) = μ(r) ⌊D/σ(r)⌋` for odd `r`. -/
def Fq (r : ℕ) : ℤ := if r % 2 = 1 then μ r * ((D / σ 1 r : ℕ) : ℤ) else 0

/-- `Ã_d(n) = ∑_{r ≤ n, d ∣ r} F(r)`. -/
def Atil (n d : ℕ) : ℤ := ∑ r ∈ (Icc 1 n).filter (d ∣ ·), Fq r

/-- `G̃(n) = ∑_{d ≤ n} μ(d) Ã_d(n)²`. -/
def Gtil (n : ℕ) : ℤ := ∑ d ∈ Icc 1 n, μ d * Atil n d ^ 2

/-- `ΔG̃(k) = G̃(k) − G̃(k − 1)`. -/
def dG (k : ℕ) : ℤ := Gtil k - Gtil (k - 1)

/-- `∑_{t ∣ rad j} t ΔG̃(t)`. -/
def sigS (j : ℕ) : ℤ := ∑ t ∈ (∏ p ∈ j.primeFactors, p).divisors, (t : ℤ) * dG t

/-- `c̃(k) = −∑_{j ≤ k odd} sigS j`. -/
def ctil (k : ℕ) : ℤ := -∑ j ∈ Icc 1 k, if j % 2 = 1 then sigS j else 0

/-- `ã(k) = ∑_{j ≤ k odd} ⌊sigS j / j⌋`. -/
def atil (k : ℕ) : ℤ := ∑ j ∈ Icc 1 k, if j % 2 = 1 then sigS j / (j : ℤ) else 0

/-! ### The walk -/

/-- Add `F` to `Ã_d` for the listed `d` (keys `d/2`); also return `∑ ±F(2Ã_d + F)`. -/
def upd (F : ℤ) : Tr ℤ → List (ℕ × Bool) → Tr ℤ × ℤ
  | t, [] => (t, 0)
  | t, (d, s) :: rest =>
    let a := t.get 0 (d / 2)
    let r := upd F (Tr.set 0 20 t (d / 2) (a + F)) rest
    (r.1, r.2 + (if s then F * (2 * a + F) else -(F * (2 * a + F))))

/-- `(trie, G̃)` at `n` from `n − 1`, given `ps = oddPrimes n`. -/
def stepG (n : ℕ) (ps : List ℕ) (t : Tr ℤ) (G : ℤ) : Tr ℤ × ℤ :=
  if n % 2 = 0 then (t, G) else
  if ps.prod = n then
    let F : ℤ := (if ps.length % 2 = 0 then 1 else -1) * ((D / (ps.map (· + 1)).prod : ℕ) : ℤ)
    let u := upd F t (dvs ps)
    (u.1, G + u.2)
  else (t, G)

/-- `∑_{x ∈ L} x.1 ΔG̃(x.1)`. -/
def sigD (td : Tr ℤ) : List (ℕ × Bool) → ℤ
  | [] => 0
  | (t, _) :: rest => sigD td rest + (t : ℤ) * td.get 0 t

def EA : ℤ := 10 ^ 19 * (D : ℤ)
def EIJ : ℤ := 10 ^ 17 * (D : ℤ)

/-- `T₂ ≤ 0.37273` at `S = n` and `S = n + 1` from `ã(n)`, `c̃(n)`, `ã(⌊n/2⌋)`, `c̃(⌊n/2⌋)`. -/
def chkABv (a c a' c' : ℤ) (n : ℕ) : Bool :=
  let a2 := 2 * a - a' + 3 * EA
  let b := c - c' + EA
  decide ((a2 * n + 2 * b) * 100000 ≤ 2 * 37273 * (D : ℤ) ^ 2 * n) &&
  decide ((a2 * (n + 1) + 2 * b) * 100000 ≤ 2 * 37273 * (D : ℤ) ^ 2 * (n + 1))

def chkAB (a c : ℤ) (ta tc : Tr ℤ) (n : ℕ) : Bool :=
  chkABv a c (ta.get 0 (n / 2)) (tc.get 0 (n / 2)) n

/-- `¼ max(I(n), I(n+1)) + max(J(n)/n, J(n+1)/(n+1)) ≤ 0.37273`. -/
def chkIJ (n : ℕ) (I I' : ℤ) (J J' : ℕ) : Bool :=
  decide (((max I I' + EIJ) * n * (n + 1) + 4 * max ((J + EIJ) * (n + 1)) ((J' + EIJ) * n)) * 100000
    ≤ 4 * 37273 * (D : ℤ) ^ 2 * n * (n + 1))

def cdivI (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))

structure SA where
  t : Tr ℤ
  G : ℤ
  I : ℤ
  J : ℕ
  td : Tr ℤ
  ta : Tr ℤ
  tc : Tr ℤ
  a : ℤ
  c : ℤ

/-- One step `n → n + 1`. -/
def stepA (n : ℕ) (s : SA) : Option SA :=
  if 16 ≤ n ∧ n < S0 ∧ chkAB s.a s.c s.ta s.tc n = false then none else
  let m := n + 1
  let ps := oddPrimes m
  let u := stepG m ps s.t s.G
  let dI : ℤ := if n = 0 then 0 else if 0 ≤ s.G then cdivI (s.G * lhiN n) (lhiD n)
    else cdivI (s.G * lloN n) (lloD n)
  let I' := s.I + dI
  let J' := s.J + s.G.natAbs
  if S0 ≤ n ∧ chkIJ n s.I I' s.J J' = false then none else
  if m < S0 then
    let td := Tr.set 0 12 s.td m (u.2 - s.G)
    let sg := if m % 2 = 1 then sigD td (dvs ps) else 0
    let c' := s.c - sg
    let a' := s.a + sg / (m : ℤ)
    some ⟨u.1, u.2, I', J', td, Tr.set 0 12 s.ta m a', Tr.set 0 12 s.tc m c', a', c'⟩
  else some ⟨u.1, u.2, I', J', s.td, s.ta, s.tc, s.a, s.c⟩

def walkA : ℕ → ℕ → SA → Option (ℤ × ℕ)
  | 0, _, s => some (s.I, s.J)
  | f + 1, n, s => match stepA n s with
    | none => none
    | some s' => walkA f (n + 1) s'

/-! ### `Ã`, `G̃` step by step -/

theorem Atil_zero (d : ℕ) : Atil 0 d = 0 := by simp [Atil]

theorem Atil_succ (n d : ℕ) : Atil (n + 1) d = Atil n d + if d ∣ n + 1 then Fq (n + 1) else 0 := by
  unfold Atil
  rw [show Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) by
    ext x; simp only [mem_insert, mem_Icc]; omega, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [add_zero]

theorem Atil_of_lt {n d : ℕ} (h : n < d) : Atil n d = 0 := by
  unfold Atil
  refine sum_eq_zero fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := mem_filter.1 hr
  have := Nat.le_of_dvd (by have := (mem_Icc.1 hr1).1; omega) hr2
  have := (mem_Icc.1 hr1).2
  omega

/-- `G̃(n+1) − G̃(n) = ∑_{d ∣ n+1} μ(d) F(n+1) (2 Ã_d(n) + F(n+1))`. -/
theorem Gtil_succ (n : ℕ) : Gtil (n + 1) = Gtil n +
    ∑ d ∈ (n + 1).divisors, μ d * (Fq (n + 1) * (2 * Atil n d + Fq (n + 1))) := by
  unfold Gtil
  have hext : ∑ d ∈ Icc 1 n, μ d * Atil n d ^ 2 = ∑ d ∈ Icc 1 (n + 1), μ d * Atil n d ^ 2 := by
    rw [show Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) by
      ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp), Atil_of_lt (by omega)]
    simp
  have hdiv : (n + 1).divisors = (Icc 1 (n + 1)).filter (· ∣ n + 1) := by
    ext d; simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨h1, -⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos h1 (by omega), Nat.le_of_dvd (by omega) h1⟩, h1⟩
    · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
  rw [hext, hdiv, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [Atil_succ]
  split_ifs <;> ring

/-! ### `upd` and `stepG` -/

theorem upd_spec (F : ℤ) : ∀ (L : List (ℕ × Bool)) (t : Tr ℤ), (L.map (fun x => x.1 / 2)).Nodup →
    (∀ x ∈ L, 2 * (x.1 / 2) + 1 < 2 ^ 20) →
    (∀ j, (upd F t L).1.get 0 j = t.get 0 j + if j ∈ L.map (fun x => x.1 / 2) then F else 0) ∧
    (upd F t L).2 = (L.map (fun x => (if x.2 then 1 else -1) * (F * (2 * t.get 0 (x.1 / 2) + F)))).sum := by
  intro L
  induction L with
  | nil => intro t _ _; simp [upd]
  | cons x L ih =>
    intro t hnd hk
    obtain ⟨d, s⟩ := x
    rw [List.map_cons, List.nodup_cons] at hnd
    have hk1 : 2 * (d / 2) + 1 < 2 ^ 20 := hk (d, s) List.mem_cons_self
    obtain ⟨i1, i2⟩ := ih (Tr.set 0 20 t (d / 2) (t.get 0 (d / 2) + F)) hnd.2
      fun y hy => hk y (List.mem_cons_of_mem _ hy)
    simp only [upd]
    refine ⟨fun j => ?_, ?_⟩
    · rw [i1, Tr.get_set _ _ _ _ _ _ hk1]
      by_cases hj : j = d / 2
      · subst hj
        have : d / 2 ∉ L.map (fun x => x.1 / 2) := hnd.1
        simp [this]
      · have hm : j ∈ List.map (fun x => x.1 / 2) ((d, s) :: L) ↔ j ∈ List.map (fun x => x.1 / 2) L := by
          simp [hj]
        simp only [hj, ite_false]
        split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hm.2 h1) h2 | exact absurd (hm.1 h2) h1
    · rw [i2, List.map_cons, List.sum_cons, add_comm]
      congr 1
      · cases s <;> simp
      · refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
        have : y.1 / 2 ≠ d / 2 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hy)
        rw [Tr.get_set _ _ _ _ _ _ hk1]; simp [this]

theorem Fq_eq_zero_of_not {n : ℕ} (h : ¬ (n % 2 = 1 ∧ Squarefree n)) : Fq n = 0 := by
  unfold Fq
  split_ifs with h1
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h2 => h ⟨h1, h2⟩)]; simp
  · rfl

theorem odd_of_dvd_odd {d n : ℕ} (hn : n % 2 = 1) (hd : d ∣ n) : d % 2 = 1 := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso; have := (even_iff_two_dvd.1 he).trans hd; omega
  · exact Nat.odd_iff.1 ho

/-- One step of `stepG`. -/
theorem stepG_spec {n : ℕ} (hn1 : 1 ≤ n) (hn : n < 2 ^ 20) {t : Tr ℤ} {G : ℤ}
    (ht : ∀ m, t.get 0 m = Atil (n - 1) (2 * m + 1)) (hG : G = Gtil (n - 1)) :
    (∀ m, (stepG n (oddPrimes n) t G).1.get 0 m = Atil n (2 * m + 1)) ∧
      (stepG n (oddPrimes n) t G).2 = Gtil n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht hG
  have hzero : Fq (k + 1) = 0 → (∀ m, t.get 0 m = Atil (k + 1) (2 * m + 1)) ∧ G = Gtil (k + 1) := by
    intro hF
    refine ⟨fun m => by rw [ht, Atil_succ, hF]; simp, ?_⟩
    rw [Gtil_succ, hF, hG]; simp
  unfold stepG
  by_cases he : (k + 1) % 2 = 0
  · simp only [he, if_true]
    exact hzero (Fq_eq_zero_of_not (by omega))
  simp only [he, if_false]
  have ho : (k + 1) % 2 = 1 := by omega
  have hodd : Odd (k + 1) := Nat.odd_iff.2 ho
  set ps := oddPrimes (k + 1)
  have hnd : ps.Nodup := nodup_oddPrimes (by omega)
  have hpr : ∀ p ∈ ps, p.Prime := fun p hp => ((mem_oddPrimes (by omega)).1 hp).1
  by_cases hsq : ps.prod = k + 1
  · simp only [hsq, if_true]
    -- `F` is `Fq (k+1)`
    have hF : (if ps.length % 2 = 0 then (1 : ℤ) else -1) * ((D / (ps.map (· + 1)).prod : ℕ) : ℤ) =
        Fq (k + 1) := by
      unfold Fq
      rw [if_pos ho, ← hsq, moebius_prod_primes ps hnd hpr, sigma_prod_primes ps hnd hpr]
      congr 1
      rcases Nat.even_or_odd ps.length with h | h
      · rw [if_pos (Nat.even_iff.1 h), h.neg_one_pow]
      · rw [if_neg (by have := Nat.odd_iff.1 h; omega), h.neg_one_pow]
    rw [hF]
    obtain ⟨i1, i2, i3⟩ := dvs_spec ps hnd hpr
    have hdvd : ∀ x ∈ dvs ps, x.1 ∣ k + 1 := fun x hx =>
      hsq ▸ (i2 x.1).1 (List.mem_map_of_mem hx)
    have hxodd : ∀ x ∈ dvs ps, x.1 % 2 = 1 := fun x hx => odd_of_dvd_odd ho (hdvd x hx)
    have hkeys : ((dvs ps).map (fun x => x.1 / 2)).Nodup := by
      have : (fun x : ℕ × Bool => x.1 / 2) = (fun d => d / 2) ∘ Prod.fst := rfl
      rw [this, ← List.map_map]
      refine List.Nodup.map_on (fun a ha b hb hab => ?_) i1
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      have := hxodd x hx; have := hxodd y hy; omega
    have hfuel : ∀ x ∈ dvs ps, 2 * (x.1 / 2) + 1 < 2 ^ 20 := fun x hx => by
      have := Nat.le_of_dvd (by omega) (hdvd x hx); omega
    obtain ⟨u1, u2⟩ := upd_spec (Fq (k + 1)) (dvs ps) t hkeys hfuel
    refine ⟨fun m => ?_, ?_⟩
    · rw [u1, ht, Atil_succ]
      congr 1
      have hiff : m ∈ (dvs ps).map (fun x => x.1 / 2) ↔ 2 * m + 1 ∣ k + 1 := by
        constructor
        · intro h
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
          have := hxodd x hx
          rw [show 2 * (x.1 / 2) + 1 = x.1 by omega]; exact hdvd x hx
        · intro h
          obtain ⟨x, hx, hx1⟩ := List.mem_map.1 ((i2 (2 * m + 1)).2 (hsq ▸ h))
          exact List.mem_map.2 ⟨x, hx, by rw [hx1]; omega⟩
      by_cases h : 2 * m + 1 ∣ k + 1
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    · rw [u2, Gtil_succ, hG]
      congr 1
      have hs := sum_dvs (fun d => μ d * (Fq (k + 1) * (2 * Atil k d + Fq (k + 1)))) hnd hpr
      rw [hsq] at hs
      rw [← hs]
      refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
      rw [i3 x hx, ht]
      have := hxodd x hx
      rw [show 2 * (x.1 / 2) + 1 = x.1 by omega]
  · simp only [hsq, if_false]
    exact hzero (Fq_eq_zero_of_not fun ⟨_, h⟩ => hsq ((squarefree_iff_prod_oddPrimes hodd).1 h))

/-! ### The walk invariant -/

theorem sigD_eq (td : Tr ℤ) : ∀ L : List (ℕ × Bool),
    sigD td L = (L.map (fun x => (x.1 : ℤ) * td.get 0 x.1)).sum := by
  intro L
  induction L with
  | nil => rfl
  | cons x L ih => obtain ⟨t, b⟩ := x; simp only [sigD, ih, List.map_cons, List.sum_cons]; ring

theorem cdivI_ge (a : ℤ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ cdivI a b := by
  unfold cdivI
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h := Int.ediv_mul_le (-a) (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
  have h' : ((-a / (b : ℤ) : ℤ) : ℝ) * b ≤ -a := by exact_mod_cast h
  rw [div_le_iff₀ hb']
  push_cast
  linarith

/-- `J(n) = ∑_{1 ≤ m < n} |G̃(m)|`. -/
def Jsp (n : ℕ) : ℕ := ∑ m ∈ Ico 1 n, (Gtil m).natAbs

/-- `∑_{1 ≤ m < n} G̃(m) log(1 + 1/m)`. -/
noncomputable def Isp (n : ℕ) : ℝ := ∑ m ∈ Ico 1 n, (Gtil m : ℝ) * Real.log (1 + 1 / m)

/-- The state after `n`. -/
def Inv (n : ℕ) (s : SA) : Prop :=
  (∀ m, s.t.get 0 m = Atil n (2 * m + 1)) ∧ s.G = Gtil n ∧ Isp n ≤ s.I ∧ s.J = Jsp n ∧
  (∀ k, k ≤ min n (S0 - 1) → s.td.get 0 k = dG k ∧ s.ta.get 0 k = atil k ∧ s.tc.get 0 k = ctil k) ∧
  s.a = atil (min n (S0 - 1)) ∧ s.c = ctil (min n (S0 - 1))

/-- The `α`/`β` check at `n`. -/
def GoodAB (n : ℕ) : Prop := chkABv (atil n) (ctil n) (atil (n / 2)) (ctil (n / 2)) n = true

/-- The `I`/`J` check at `n`. -/
def GoodIJ (n : ℕ) : Prop :=
  ∃ I I' : ℤ, Isp n ≤ I ∧ Isp (n + 1) ≤ I' ∧ chkIJ n I I' (Jsp n) (Jsp (n + 1)) = true

theorem Inv_zero : Inv 0 ⟨.nil, 0, 0, 0, .nil, .nil, .nil, 0, 0⟩ := by
  refine ⟨fun m => by simp [Tr.get_nil, Atil_zero], by simp [Gtil], by simp [Isp], by simp [Jsp],
    fun k hk => ?_, by simp [atil], by simp [ctil]⟩
  have : k = 0 := by simpa using hk
  subst this
  simp [Tr.get_nil, dG, atil, ctil]

theorem Isp_succ {n : ℕ} (hn : 1 ≤ n) : Isp (n + 1) = Isp n + (Gtil n : ℝ) * Real.log (1 + 1 / n) := by
  unfold Isp; rw [sum_Ico_succ_top hn]

theorem Jsp_succ (n : ℕ) (h : n = 0 → Gtil n = 0) : Jsp (n + 1) = Jsp n + (Gtil n).natAbs := by
  unfold Jsp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h rfl]
  · rw [sum_Ico_succ_top hn]

theorem Gtil_zero : Gtil 0 = 0 := by simp [Gtil]

theorem atil_succ (k : ℕ) : atil (k + 1) = atil k + if (k + 1) % 2 = 1 then sigS (k + 1) / ((k + 1 : ℕ) : ℤ) else 0 := by
  unfold atil; rw [sum_Icc_succ_top (by omega)]

theorem ctil_succ (k : ℕ) : ctil (k + 1) = ctil k - if (k + 1) % 2 = 1 then sigS (k + 1) else 0 := by
  unfold ctil; rw [sum_Icc_succ_top (by omega)]; ring

/-- One step of the walk. -/
theorem stepA_spec {n : ℕ} {s s' : SA} (hn : n + 1 ≤ XX) (h : Inv n s) (hs : stepA n s = some s') :
    Inv (n + 1) s' ∧ (16 ≤ n → n < S0 → GoodAB n) ∧ (S0 ≤ n → GoodIJ n) := by
  obtain ⟨ht, hG, hI, hJ, htr, ha, hc⟩ := h
  have hXX : XX = 10000 := rfl
  have hS0 : S0 = 700 := rfl
  unfold stepA at hs
  by_cases hab : 16 ≤ n ∧ n < S0 ∧ chkAB s.a s.c s.ta s.tc n = false
  · rw [if_pos hab] at hs; exact absurd hs (by simp)
  rw [if_neg hab] at hs
  have gAB : 16 ≤ n → n < S0 → GoodAB n := by
    intro h1 h2
    have hmin : min n (S0 - 1) = n := by omega
    have e1 := (htr (n / 2) (by omega)).2.1
    have e2 := (htr (n / 2) (by omega)).2.2
    rw [hmin] at ha hc
    have : chkAB s.a s.c s.ta s.tc n = true := by
      by_contra hf; exact hab ⟨h1, h2, by simpa using hf⟩
    unfold chkAB at this
    rw [e1, e2, ha, hc] at this
    exact this
  -- the `G̃` step
  obtain ⟨u1, u2⟩ := stepG_spec (n := n + 1) (by omega) (by rw [hXX] at hn; omega)
    (t := s.t) (G := s.G) (by simpa using ht) (by simpa using hG)
  set u := stepG (n + 1) (oddPrimes (n + 1)) s.t s.G
  -- `I`, `J`
  set dI : ℤ := if n = 0 then 0 else if 0 ≤ s.G then cdivI (s.G * lhiN n) (lhiD n)
    else cdivI (s.G * lloN n) (lloD n) with hdI
  have hI' : Isp (n + 1) ≤ ((s.I + dI : ℤ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have e1 : Isp (0 + 1) = 0 := by simp [Isp]
      rw [e1, hdI, if_pos rfl, add_zero]
      have e0 : Isp 0 = 0 := by simp [Isp]
      rw [e0] at hI; exact hI
    rw [Isp_succ hn0]
    push_cast
    refine add_le_add hI ?_
    rw [hdI, if_neg (by omega)]
    obtain ⟨l1, l2⟩ := log_bounds hn0
    have hD1 : 0 < lhiD n := by unfold lhiD; positivity
    have hD0 : 0 < lloD n := by unfold lloD; positivity
    split_ifs with hg
    · refine le_trans ?_ (cdivI_ge _ hD1)
      push_cast
      rw [← hG, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left l2 (by exact_mod_cast hg)
    · refine le_trans ?_ (cdivI_ge _ hD0)
      push_cast
      rw [← hG, mul_div_assoc]
      exact mul_le_mul_of_nonpos_left l1 (by exact_mod_cast (not_le.1 hg).le)
  have hJ' : s.J + s.G.natAbs = Jsp (n + 1) := by
    rw [Jsp_succ n (fun h => by subst h; exact Gtil_zero), hJ, hG]
  by_cases hij : S0 ≤ n ∧ chkIJ n s.I (s.I + dI) s.J (s.J + s.G.natAbs) = false
  · rw [if_pos hij] at hs; exact absurd hs (by simp)
  rw [if_neg hij] at hs
  have gIJ : S0 ≤ n → GoodIJ n := by
    intro h1
    refine ⟨s.I, s.I + dI, hI, hI', ?_⟩
    rw [← hJ, ← hJ']
    by_contra hf; exact hij ⟨h1, by simpa using hf⟩
  refine ⟨?_, gAB, gIJ⟩
  by_cases hm : n + 1 < S0
  · rw [if_pos hm] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hmin : min (n + 1) (S0 - 1) = n + 1 := by omega
    have hmin' : min n (S0 - 1) = n := by omega
    rw [hmin'] at htr ha hc
    -- the new `ΔG̃` trie
    set td := Tr.set 0 12 s.td (n + 1) (u.2 - s.G) with htd
    have hfuel : 2 * (n + 1) + 1 < 2 ^ 12 := by rw [hS0] at hm; norm_num; omega
    have htd' : ∀ k, k ≤ n + 1 → td.get 0 k = dG k := by
      intro k hk
      rw [htd, Tr.get_set _ _ _ _ _ _ hfuel]
      split_ifs with he
      · subst he; rw [u2, hG]; rfl
      · exact (htr k (by omega)).1
    -- `sigD`
    have hsig : (if (n + 1) % 2 = 1 then sigD td (dvs (oddPrimes (n + 1))) else 0) =
        if (n + 1) % 2 = 1 then sigS (n + 1) else 0 := by
      split_ifs with ho
      · have hodd : Odd (n + 1) := Nat.odd_iff.2 ho
        have hnd := nodup_oddPrimes (show 0 < n + 1 by omega)
        have hpr : ∀ p ∈ oddPrimes (n + 1), p.Prime := fun p hp =>
          ((mem_oddPrimes (by omega)).1 hp).1
        rw [sigD_eq, sigS, ← prod_oddPrimes hodd]
        rw [← sum_dvs (fun t => (t : ℤ) * dG t) hnd hpr]
        refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
        have hxd : x.1 ∣ (oddPrimes (n + 1)).prod :=
          ((dvs_spec _ hnd hpr).2.1 x.1).1 (List.mem_map_of_mem hx)
        rw [prod_oddPrimes hodd] at hxd
        have := Nat.le_of_dvd (by omega) (hxd.trans (Nat.prod_primeFactors_dvd (n + 1)))
        rw [htd' x.1 this]
      · rfl
    refine ⟨u1, u2, hI', hJ', fun k hk => ?_, ?_, ?_⟩
    · rw [hmin] at hk
      refine ⟨htd' k hk, ?_, ?_⟩
      · show (Tr.set 0 12 s.ta (n + 1) _).get 0 k = _
        rw [Tr.get_set _ _ _ _ _ _ hfuel]
        by_cases he : k = n + 1
        · rw [if_pos he, he, hsig, atil_succ, ← ha]
          split_ifs <;> simp
        · rw [if_neg he]; exact (htr k (by omega)).2.1
      · show (Tr.set 0 12 s.tc (n + 1) _).get 0 k = _
        rw [Tr.get_set _ _ _ _ _ _ hfuel]
        by_cases he : k = n + 1
        · rw [if_pos he, he, hsig, ctil_succ, ← hc]
        · rw [if_neg he]; exact (htr k (by omega)).2.2
    · show _ + _ = _
      rw [hmin, hsig, atil_succ, ← ha]
      split_ifs <;> simp
    · show _ - _ = _
      rw [hmin, hsig, ctil_succ, ← hc]
  · rw [if_neg hm] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hmin : min (n + 1) (S0 - 1) = min n (S0 - 1) := by omega
    exact ⟨u1, u2, hI', hJ', by rw [hmin]; exact htr, by rw [hmin]; exact ha,
      by rw [hmin]; exact hc⟩

theorem walkA_spec : ∀ (len n : ℕ) (s : SA) (r : ℤ × ℕ), Inv n s → n + len ≤ XX →
    walkA len n s = some r →
    (∃ s', Inv (n + len) s' ∧ r = (s'.I, s'.J)) ∧
      ∀ k, n ≤ k → k < n + len → (16 ≤ k → k < S0 → GoodAB k) ∧ (S0 ≤ k → GoodIJ k) := by
  intro len
  induction len with
  | zero =>
    intro n s r h _ hw
    simp only [walkA, Option.some.injEq] at hw
    exact ⟨⟨s, by simpa using h, hw.symm⟩, fun k h1 h2 => by omega⟩
  | succ len ih =>
    intro n s r h hn hw
    simp only [walkA] at hw
    rcases hst : stepA n s with _ | s'
    · rw [hst] at hw; exact absurd hw (by simp)
    rw [hst] at hw
    obtain ⟨h1, g1, g2⟩ := stepA_spec (by omega) h hst
    obtain ⟨⟨s'', i1, i2⟩, i3⟩ := ih (n + 1) s' r h1 (by omega) hw
    refine ⟨⟨s'', by rw [show n + (len + 1) = n + 1 + len by omega]; exact i1, i2⟩, fun k hk1 hk2 => ?_⟩
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
    · exact ⟨g1, g2⟩
    · exact i3 k (by omega) (by omega)

/-! ### The computation -/

def Ifin : ℤ := 1442305043071741356929337106029717587029646414197648482569251
def Jfin : ℕ := 9218553783470309560072038260070108962893361103201224033363762

set_option maxHeartbeats 0 in
theorem walk_ok : walkA XX 0 ⟨.nil, 0, 0, 0, .nil, .nil, .nil, 0, 0⟩ = some (Ifin, Jfin) := by
  decide +kernel

/-- **The kernel computation**: `∑_{m < 10⁴} G̃(m) log(1 + 1/m) ≤ Ifin`, `∑_{m < 10⁴} |G̃(m)| = Jfin`,
and the checks at every `16 ≤ n < 10⁴`. -/
theorem walk_spec :
    Isp XX ≤ Ifin ∧ Jsp XX = Jfin ∧ ∀ k, 16 ≤ k → k < XX → (k < S0 → GoodAB k) ∧ (S0 ≤ k → GoodIJ k) := by
  obtain ⟨⟨s', hi, hr⟩, hk⟩ := walkA_spec XX 0 _ _ Inv_zero (by simp) walk_ok
  simp only [zero_add] at hi
  obtain ⟨-, -, hI, hJ, -⟩ := hi
  simp only [Prod.mk.injEq] at hr
  refine ⟨hr.1 ▸ hI, hr.2 ▸ hJ.symm, fun k h1 h2 => ?_⟩
  obtain ⟨a, b⟩ := hk k (by omega) (by simpa using h2)
  exact ⟨a h1, b⟩

end TernaryGoldbach.MinorArcs.SmallG2
