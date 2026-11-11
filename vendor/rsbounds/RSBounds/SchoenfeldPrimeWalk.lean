import TernaryGoldbach.Prelim.SmallMertensProd
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# A kernel-checked walk for `θ(n)` and `ψ(n)`

The finite parts of Schoenfeld (1976), (5.5a*), (5.5b*), (5.6a*) and (5.6*), below the range where
`|ψ(x) − x| ≤ (4/5)√x` (PsiCert) is strong enough, are checked by computing `θ(n)` and `ψ(n)` for
every integer `n` up to about `1.35·10⁶`.

The state holds integer enclosures of `D θ(n)` and `D ψ(n)`, with `D = 10³⁰`. A step from `n − 1`
to `n` adds

* `log n` to both, if `n` is prime (`isPr`: trial division below `1163`, coprimality with the
  product of the primes below `1163` above, valid below `1163²`);
* `log p` to `ψ` only, if `n = p^k` with `k ≥ 2` (`p = gcd(n, primeProd)`, and `n` a power of
  `p`);
* nothing otherwise.

`log m` is enclosed by `log m = k log 2 + log(1 + b/a)`, `a = 2^k ≤ m − 1 < 2a`, `b = m − a`, with
the twelve-term artanh bounds `MertProd.q_bounds` of the upstream finite Mertens certificate.

At every `n` the walk also checks four inequalities against thresholds `Req` (scaled by `D`); they
give, for every real `x ∈ [n, n+1)`, `θ(x) − x < thUp/D`, `x − θ(x) < thLo/D`,
`ψ(x) − x < psUp/D` and `x − ψ(x) < psLo/D` (`walk_spec`). Nothing here assumes RH, a zero-free
region or any analytic estimate.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk

open TernaryGoldbach.Prelim.MertProd (isP isP_iff qLo qHi q_bounds)

/-- The fixed-point scale. -/
def D : ℕ := 10 ^ 30

/-! ## Logarithms -/

/-- `(k, 2^k)` with `2^k ≤ m − 1 < 2^(k+1)`, found by doubling (fuel-bounded). -/
def lgAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, k, a => (k, a)
  | fuel + 1, k, a => if 2 * a ≤ m - 1 then lgAux m fuel (k + 1) (2 * a) else (k, a)

def lg (m : ℕ) : ℕ × ℕ := lgAux m 64 0 1

theorem lgAux_spec (m : ℕ) : ∀ fuel k a, a = 2 ^ k → a ≤ m - 1 → m - 1 < 2 ^ (k + fuel) →
    (lgAux m fuel k a).2 = 2 ^ (lgAux m fuel k a).1 ∧ (lgAux m fuel k a).2 ≤ m - 1 ∧
      m - 1 < 2 * (lgAux m fuel k a).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k a ha hle hlt
    simp only [lgAux, add_zero] at hlt ⊢
    subst ha
    exact ⟨rfl, hle, by omega⟩
  | succ f ih =>
    intro k a ha hle hlt
    unfold lgAux
    split_ifs with h
    · exact ih (k + 1) (2 * a) (by rw [ha, pow_succ]; ring) h
        (by rw [show k + 1 + f = k + (f + 1) by ring]; exact hlt)
    · exact ⟨ha, hle, by omega⟩

theorem lg_spec {m : ℕ} (hm : 2 ≤ m) (hm64 : m < 2 ^ 64) :
    (lg m).2 = 2 ^ (lg m).1 ∧ (lg m).2 ≤ m - 1 ∧ m - 1 < 2 * (lg m).2 :=
  lgAux_spec m 64 0 1 (by simp) (by omega) (by simpa using (show m - 1 < 2 ^ 64 by omega))

/-- Lower enclosure of `D log m`. -/
def logLo (m : ℕ) : ℕ :=
  (lg m).1 * qLo 1 1 + qLo (lg m).2 (m - (lg m).2)

/-- Upper enclosure of `D log m`. -/
def logHi (m : ℕ) : ℕ :=
  (lg m).1 * qHi 1 1 + qHi (lg m).2 (m - (lg m).2)

theorem log_bounds {m : ℕ} (hm : 2 ≤ m) (hm64 : m < 2 ^ 64) :
    (logLo m : ℝ) ≤ (D : ℝ) * Real.log m ∧ (D : ℝ) * Real.log m ≤ (logHi m : ℝ) := by
  obtain ⟨ha, hle, hlt⟩ := lg_spec hm hm64
  set k := (lg m).1
  set a := (lg m).2
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < m - a := by omega
  have hba : m - a ≤ a := by omega
  have q1 := q_bounds ha0 hb0 hba
  have q2 := q_bounds (a := 1) (b := 1) (by norm_num) (by norm_num) le_rfl
  norm_num only [Nat.cast_one, div_one] at q2
  have hlog : Real.log m = k * Real.log 2 + Real.log (1 + ((m - a : ℕ) : ℝ) / a) := by
    have haR : (a : ℝ) = 2 ^ k := by rw [ha]; push_cast; ring
    have hm' : (m : ℝ) = 2 ^ k * (1 + ((m - a : ℕ) : ℝ) / a) := by
      rw [← haR]
      have : ((m - a : ℕ) : ℝ) = (m : ℝ) - a := by
        rw [Nat.cast_sub (by omega)]
      rw [this]
      field_simp
      ring
    rw [hm', Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hD : (D : ℝ) = 10 ^ 30 := by norm_num [D]
  unfold logLo logHi
  rw [hlog, hD]
  push_cast
  constructor
  · have := mul_le_mul_of_nonneg_left q2.1 hk
    nlinarith [q1.1]
  · have := mul_le_mul_of_nonneg_left q2.2 hk
    nlinarith [q1.2]

/-! ## Primes below `1163²`

Trial division costs the kernel about `√m` steps per prime `m`. Instead, below `1163²` a number
`m ≥ 1163` is prime iff it is coprime to the product of the primes below `1163`, a single
(GMP-accelerated) `gcd`. -/

/-- The primes below `1163`. -/
def smallPrimes : List ℕ := (List.range 1163).filter isP

set_option linter.style.longLine false in
/-- The product of the primes below `1163`, as a literal (`primeProd_eq`). -/
def primeProd : ℕ := 100170827783160516020927195602424238112707840245321201229994351438692207686493522184814569042682353315165372535425978052770006659336962837513908655230015615187851590374165921682662817413811024967900208589177781798882097306526208167134590426258581098103446716578895678704470876663423671526120467228690264303701683905754282528133598356001098742582509404821835698126231016091198518108222584410545865663528510926918463760431563328701700414587369967698290059957060208183805480959513058109390

theorem primeProd_eq : primeProd = smallPrimes.prod := by decide +kernel

theorem primeProd_sq : ∀ p < 1163, isP p = true → primeProd % (p * p) ≠ 0 := by decide +kernel

theorem mem_smallPrimes {q : ℕ} : q ∈ smallPrimes ↔ q < 1163 ∧ q.Prime := by
  simp [smallPrimes, List.mem_filter, List.mem_range, isP_iff]

theorem dvd_primeProd {q : ℕ} (hq : q.Prime) (h : q < 1163) : q ∣ primeProd := by
  rw [primeProd_eq]; exact List.dvd_prod (mem_smallPrimes.mpr ⟨h, hq⟩)

theorem lt_of_dvd_primeProd {q : ℕ} (hq : q.Prime) (h : q ∣ primeProd) : q < 1163 := by
  rw [primeProd_eq] at h
  obtain ⟨a, ha, hqa⟩ := (Nat.Prime.prime hq).dvd_prod_iff.mp h
  obtain ⟨ha1, ha2⟩ := mem_smallPrimes.mp ha
  have := (Nat.prime_dvd_prime_iff_eq hq ha2).mp hqa
  omega

theorem sq_not_dvd_primeProd {q : ℕ} (hq : q.Prime) : ¬ q * q ∣ primeProd := by
  intro h
  have hlt := lt_of_dvd_primeProd hq ((dvd_mul_right q q).trans h)
  exact primeProd_sq q hlt ((isP_iff q).mpr hq) (Nat.mod_eq_zero_of_dvd h)

/-- Primality below `1163²`: trial division below `1163`, coprimality with `primeProd` above. -/
def isPr (m : ℕ) : Bool := if m < 1163 then isP m else Nat.gcd m primeProd == 1

theorem isPr_iff {m : ℕ} (hm : m < 1163 * 1163) : isPr m = true ↔ m.Prime := by
  unfold isPr
  split_ifs with h
  · exact isP_iff m
  · rw [beq_iff_eq]
    constructor
    · intro hg
      by_contra hnp
      have hm1 : m ≠ 1 := by omega
      have hq := Nat.minFac_prime hm1
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hlt : m.minFac < 1163 := by
        by_contra hc
        push_neg at hc
        nlinarith
      have h1 : m.minFac ∣ Nat.gcd m primeProd :=
        Nat.dvd_gcd (Nat.minFac_dvd m) (dvd_primeProd hq hlt)
      rw [hg] at h1
      exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
    · intro hp
      rcases Nat.coprime_or_dvd_of_prime hp primeProd with hc | hd
      · exact hc
      · have := lt_of_dvd_primeProd hp hd
        omega

/-- The candidate base of a non-prime `m`: if `m = p^k` with `k ≥ 2` and `m < 1163²`, then
`p < 1163` and `gcd(m, primeProd) = p`. -/
def ppBase (m : ℕ) : ℕ := Nat.gcd m primeProd

/-- Whether `m` is a power of `p` (fuel-bounded repeated division). -/
def isPowOf (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, m => if m = 1 then true else if m % p = 0 then isPowOf p fuel (m / p) else false

theorem isPowOf_sound {p : ℕ} (hp : 2 ≤ p) : ∀ fuel m, isPowOf p fuel m = true → ∃ j, m = p ^ j := by
  intro fuel
  induction fuel with
  | zero => intro m h; simp [isPowOf] at h
  | succ f ih =>
    intro m h
    unfold isPowOf at h
    split_ifs at h with h1 h2
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨j, hj⟩ := ih (m / p) h
      refine ⟨j + 1, ?_⟩
      rw [pow_succ, ← hj]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)).symm

theorem isPowOf_complete {p : ℕ} (hp : 2 ≤ p) : ∀ j fuel, j < fuel → isPowOf p fuel (p ^ j) = true := by
  intro j
  induction j with
  | zero => intro fuel hf; obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩; simp [isPowOf]
  | succ j ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    unfold isPowOf
    have hne : p ^ (j + 1) ≠ 1 := by
      have : 1 < p ^ (j + 1) := Nat.one_lt_pow (by omega) (by omega)
      omega
    have hmod : p ^ (j + 1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
    rw [if_neg hne, if_pos hmod, pow_succ, Nat.mul_div_cancel _ (by omega)]
    exact ih f (by omega)

/-- `Λ m` below `1163²`. -/
theorem vonMangoldt_eq {m : ℕ} (hm : 2 ≤ m) (hmB : m < 1163 * 1163) :
    Λ m = if isPr m then Real.log m
      else if isPowOf (ppBase m) 64 m && isP (ppBase m) then Real.log (ppBase m) else 0 := by
  have hm64 : m < 2 ^ 64 := by norm_num at hmB ⊢; omega
  by_cases hp : isPr m = true
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime ((isPr_iff hmB).mp hp)]
  rw [if_neg hp]
  have hnp : ¬ m.Prime := fun h => hp ((isPr_iff hmB).mpr h)
  by_cases hc : (isPowOf (ppBase m) 64 m && isP (ppBase m)) = true
  · rw [if_pos hc]
    rw [Bool.and_eq_true] at hc
    have hg := (isP_iff _).mp hc.2
    obtain ⟨j, hj⟩ := isPowOf_sound hg.two_le 64 m hc.1
    have hj0 : j ≠ 0 := by rintro rfl; simp at hj; omega
    conv_lhs => rw [hj]
    rw [ArithmeticFunction.vonMangoldt_apply_pow hj0,
      ArithmeticFunction.vonMangoldt_apply_prime hg]
  · rw [if_neg hc]
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    rintro ⟨q, j, hqp, hj, hqj⟩
    have hq : q.Prime := hqp.nat_prime
    have hj2 : 2 ≤ j := by
      by_contra h2
      have : j = 1 := by omega
      subst this
      exact hnp (by rw [← hqj, pow_one]; exact hq)
    have hqq : q * q ≤ m := by
      rw [← hqj, ← sq]
      exact Nat.pow_le_pow_right hq.pos hj2
    have hq1163 : q < 1163 := by
      by_contra hc'
      push_neg at hc'
      nlinarith
    have hqm : q ∣ m := by rw [← hqj]; exact dvd_pow_self q (by omega)
    have hqg : q ∣ ppBase m := Nat.dvd_gcd hqm (dvd_primeProd hq hq1163)
    have hgm : ppBase m ∣ q ^ j := by rw [hqj]; exact Nat.gcd_dvd_left m primeProd
    obtain ⟨i, -, hgi⟩ := (Nat.dvd_prime_pow hq).mp hgm
    have hi1 : i = 1 := by
      rcases Nat.lt_or_ge i 2 with h | h
      · interval_cases i
        · rw [hgi, pow_zero] at hqg
          exact absurd (Nat.dvd_one.mp hqg) hq.one_lt.ne'
        · rfl
      · exfalso
        apply sq_not_dvd_primeProd hq
        have h3 : q * q ∣ ppBase m := by rw [hgi, ← sq]; exact pow_dvd_pow q h
        exact h3.trans (Nat.gcd_dvd_right m primeProd)
    rw [hi1, pow_one] at hgi
    apply hc
    rw [hgi, Bool.and_eq_true]
    refine ⟨?_, (isP_iff q).mpr hq⟩
    rw [← hqj]
    apply isPowOf_complete hq.two_le j 64
    by_contra hge
    have h2j : 2 ^ j ≤ q ^ j := Nat.pow_le_pow_left hq.two_le j
    have h64 : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hqj] at h2j
    exact absurd hm64 (not_lt.mpr (h64.trans h2j))

/-! ## The walk -/

structure WS where
  Tlo : ℕ
  Thi : ℕ
  Plo : ℕ
  Phi : ℕ
deriving DecidableEq

/-- Thresholds, scaled by `D`: `θ(x) − x < thUp/D`, `x − θ(x) < thLo/D`, and the same for `ψ`. -/
structure Req where
  thUp : ℕ
  thLo : ℕ
  psUp : ℕ
  psLo : ℕ
deriving DecidableEq

/-- Add the term for `m`. -/
def step (m : ℕ) (s : WS) : WS :=
  if isPr m then ⟨s.Tlo + logLo m, s.Thi + logHi m, s.Plo + logLo m, s.Phi + logHi m⟩
  else if isPowOf (ppBase m) 64 m && isP (ppBase m) then
    ⟨s.Tlo, s.Thi, s.Plo + logLo (ppBase m), s.Phi + logHi (ppBase m)⟩
  else s

/-- The four checks at `n`. -/
def chk (n : ℕ) (r : Req) (s : WS) : Bool :=
  decide (s.Thi < D * n + r.thUp) && decide (D * (n + 1) ≤ s.Tlo + r.thLo) &&
    decide (s.Phi < D * n + r.psUp) && decide (D * (n + 1) ≤ s.Plo + r.psLo)

/-- Check at `n, …, n + len − 1`, stepping after each check. -/
def walk : ℕ → ℕ → Req → WS → Option WS
  | _, 0, _, s => some s
  | n, len + 1, r, s => if chk n r s then walk (n + 1) len r (step (n + 1) s) else none

/-- The enclosures at `n`. -/
def Inv (n : ℕ) (s : WS) : Prop :=
  (s.Tlo : ℝ) ≤ D * Chebyshev.theta n ∧ (D : ℝ) * Chebyshev.theta n ≤ s.Thi ∧
    (s.Plo : ℝ) ≤ D * Chebyshev.psi n ∧ (D : ℝ) * Chebyshev.psi n ≤ s.Phi

/-- What the checks give at `n`, for every real `x ∈ [n, n+1)`. -/
def Holds (n : ℕ) (r : Req) : Prop :=
  ∀ x : ℝ, (n : ℝ) ≤ x → x < n + 1 →
    Chebyshev.theta x - x < r.thUp / D ∧ x - Chebyshev.theta x < r.thLo / D ∧
      Chebyshev.psi x - x < r.psUp / D ∧ x - Chebyshev.psi x < r.psLo / D

theorem theta_succ (n : ℕ) :
    Chebyshev.theta ((n + 1 : ℕ) : ℝ) =
      Chebyshev.theta (n : ℝ) + if (n + 1).Prime then Real.log (n + 1 : ℕ) else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
    Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]

theorem psi_succ (n : ℕ) :
    Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi (n : ℝ) + Λ (n + 1) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast,
    Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega)]

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) (hnB : n + 1 < 1163 * 1163) {s : WS} (h : Inv n s) :
    Inv (n + 1) (step (n + 1) s) := by
  obtain ⟨t1, t2, p1, p2⟩ := h
  have hm : 2 ≤ n + 1 := by omega
  have hm64 : n + 1 < 2 ^ 64 := by norm_num at hnB ⊢; omega
  have hth := theta_succ n
  have hps := psi_succ n
  have hΛ := vonMangoldt_eq hm hnB
  unfold step
  by_cases hp : isPr (n + 1) = true
  · have hp' : (n + 1).Prime := (isPr_iff hnB).mp hp
    obtain ⟨l1, l2⟩ := log_bounds hm hm64
    rw [if_pos hp] at hΛ ⊢
    rw [if_pos hp'] at hth
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hth, mul_add]; push_cast at l1 l2 ⊢; linarith
    · rw [hth, mul_add]; push_cast at l1 l2 ⊢; linarith
    · rw [hps, hΛ, mul_add]; push_cast at l1 l2 ⊢; linarith
    · rw [hps, hΛ, mul_add]; push_cast at l1 l2 ⊢; linarith
  · have hp' : ¬ (n + 1).Prime := fun h => hp ((isPr_iff hnB).mpr h)
    rw [if_neg hp] at hΛ ⊢
    rw [if_neg hp', add_zero] at hth
    by_cases hq : (isPowOf (ppBase (n + 1)) 64 (n + 1) && isP (ppBase (n + 1))) = true
    · have hg : (ppBase (n + 1)).Prime := by
        rw [Bool.and_eq_true] at hq
        exact (isP_iff _).mp hq.2
      have hg64 : ppBase (n + 1) < 2 ^ 64 :=
        lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hm64
      obtain ⟨l1, l2⟩ := log_bounds hg.two_le hg64
      simp only [if_pos hq] at hΛ ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hth]; exact t1
      · rw [hth]; exact t2
      · rw [hps, hΛ, mul_add]; push_cast at l1 l2 ⊢; linarith
      · rw [hps, hΛ, mul_add]; push_cast at l1 l2 ⊢; linarith
    · simp only [if_neg hq] at hΛ ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hth]; exact t1
      · rw [hth]; exact t2
      · rw [hps, hΛ, add_zero]; exact p1
      · rw [hps, hΛ, add_zero]; exact p2

theorem holds_of_chk {n : ℕ} {r : Req} {s : WS} (h : Inv n s) (hc : chk n r s = true) :
    Holds n r := by
  obtain ⟨t1, t2, p1, p2⟩ := h
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have c1' : (s.Thi : ℝ) < (D : ℝ) * n + r.thUp := by exact_mod_cast c1
  have c2' : (D : ℝ) * (n + 1) ≤ s.Tlo + r.thLo := by exact_mod_cast c2
  have c3' : (s.Phi : ℝ) < (D : ℝ) * n + r.psUp := by exact_mod_cast c3
  have c4' : (D : ℝ) * (n + 1) ≤ s.Plo + r.psLo := by exact_mod_cast c4
  have hD : (0 : ℝ) < D := by norm_num [D]
  intro x hx1 hx2
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg n) hx1
  have hfl : ⌊x⌋₊ = n := by
    apply Nat.floor_eq_iff hx0 |>.mpr
    exact ⟨hx1, hx2⟩
  have hthx : Chebyshev.theta x = Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfl]
  have hpsx : Chebyshev.psi x = Chebyshev.psi n := by
    rw [Chebyshev.psi_eq_psi_coe_floor, hfl]
  rw [hthx, hpsx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [lt_div_iff₀ hD]; nlinarith

theorem walk_spec : ∀ (len n : ℕ) (r : Req) (s s' : WS), 1 ≤ n → n + len < 1163 * 1163 → Inv n s →
    walk n len r s = some s' → Inv (n + len) s' ∧ ∀ m, n ≤ m → m < n + len → Holds m r := by
  intro len
  induction len with
  | zero =>
    intro n r s s' _ _ h hw
    simp only [walk, Option.some.injEq] at hw
    subst hw
    exact ⟨by simpa using h, fun m h1 h2 => by omega⟩
  | succ len ih =>
    intro n r s s' hn hn64 h hw
    rw [walk] at hw
    split_ifs at hw with hc
    have h1 := Inv_step hn (by omega) h
    obtain ⟨hinv, hhold⟩ := ih (n + 1) r _ s' (by omega) (by omega) h1 hw
    refine ⟨by rw [show n + (len + 1) = n + 1 + len by ring]; exact hinv, ?_⟩
    intro m hm1 hm2
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have : m = n := by omega
      subst this
      exact holds_of_chk h hc
    · exact hhold m hge (by omega)

theorem Inv_one : Inv 1 ⟨0, 0, 0, 0⟩ := by
  have ht : Chebyshev.theta (1 : ℕ) = 0 := by simpa using Chebyshev.theta_one
  have hp : Chebyshev.psi (1 : ℕ) = 0 := by simpa using Chebyshev.psi_one
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ht, hp]

/-! ## What the walk certifies -/

/-- The target inequalities for `x ∈ [n, n+1)`. -/
def Good (n : ℕ) : Prop :=
  ∀ x : ℝ, (n : ℝ) ≤ x → x < n + 1 →
    (n < 250000 → Chebyshev.theta x < x) ∧
    (n < 100000 → Chebyshev.psi x - x < 0.04 * x) ∧
    (89909 ≤ n → n < 200000 → x - Chebyshev.psi x < 0.0220646 * x / Real.log x) ∧
    (161971 ≤ n → n < 200000 → Chebyshev.psi x - x < 0.0220646 * x / Real.log x) ∧
    (758711 ≤ n → n < 1350000 → |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x)

/-- `x / log x` is increasing on `[3, ∞)`. -/
theorem div_log_le {A x : ℝ} (hA : 3 ≤ A) (hx : A ≤ x) : A / Real.log A ≤ x / Real.log x := by
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h := Real.log_div_self_antitoneOn (show A ∈ Set.Ici (Real.exp 1) from he.trans hA)
    (show x ∈ Set.Ici (Real.exp 1) from (he.trans hA).trans hx) hx
  simp only at h
  have hA0 : 0 < A := by linarith
  have hlA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [div_le_div_iff₀ hlA hlx]
  rw [div_le_div_iff₀ (by linarith) hA0] at h
  nlinarith

/-- `t / D ≤ (a / b) · A / log A`, checked through the upper enclosure of `D log A`. -/
def logOk (a b A t : ℕ) : Bool :=
  decide (3 ≤ A) && decide (A < 1163 * 1163) && decide (t * logHi A * b ≤ a * A * D * D)

theorem logOk_spec {a b A t : ℕ} {c : ℝ} (hb : 0 < b) (hc : (a : ℝ) / b = c)
    (h : logOk a b A t = true) {x : ℝ} (hx : (A : ℝ) ≤ x) :
    (t : ℝ) / D ≤ c * x / Real.log x := by
  simp only [logOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h3, hlt⟩, hle⟩ := h
  have hA3 : (3 : ℝ) ≤ A := by exact_mod_cast h3
  have hm64 : A < 2 ^ 64 := by norm_num at hlt ⊢; omega
  obtain ⟨-, hhi⟩ := log_bounds (by omega) hm64
  have hle' : (t : ℝ) * logHi A * b ≤ a * A * D * D := by exact_mod_cast hle
  have hD : (0 : ℝ) < D := by norm_num [D]
  have hlA : 0 < Real.log A := Real.log_pos (by linarith)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h2 : (t : ℝ) * (D * Real.log A) * b ≤ a * A * D * D := by
    calc (t : ℝ) * (D * Real.log A) * b ≤ t * logHi A * b := by gcongr
      _ ≤ _ := hle'
  have key : (t : ℝ) * b * Real.log A ≤ a * A * D := by
    have : D * ((t : ℝ) * b * Real.log A) ≤ D * (a * A * D) := by nlinarith
    exact le_of_mul_le_mul_left this hD
  have hc0 : 0 ≤ c := by rw [← hc]; positivity
  have h1 : (t : ℝ) / D ≤ c * A / Real.log A := by
    rw [← hc, div_le_iff₀ hD]
    rw [show (a : ℝ) / b * A / Real.log A * D = a * A * D / (b * Real.log A) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc (t : ℝ) / D ≤ c * A / Real.log A := h1
    _ = c * (A / Real.log A) := by ring
    _ ≤ c * (x / Real.log x) := mul_le_mul_of_nonneg_left (div_log_le hA3 hx) hc0
    _ = c * x / Real.log x := by ring

/-- The thresholds of a stretch `[A, B)` give the target inequalities on it. -/
def reqOk (A B : ℕ) (r : Req) : Bool :=
  (decide (250000 ≤ A) || decide (r.thUp = 0)) &&
  (decide (100000 ≤ A) || decide (r.psUp * 100 ≤ 4 * D * A)) &&
  (decide (200000 ≤ A) || decide (B ≤ 89909) || logOk 220646 10000000 A r.psLo) &&
  (decide (200000 ≤ A) || decide (B ≤ 161971) || logOk 220646 10000000 A r.psUp) &&
  (decide (1350000 ≤ A) || decide (B ≤ 758711) ||
    (logOk 239922 10000000 A r.thUp && logOk 239922 10000000 A r.thLo))

theorem good_of_holds {A B n : ℕ} {r : Req} (hr : reqOk A B r = true) (hAn : A ≤ n)
    (hnB : n < B) (h : Holds n r) : Good n := by
  simp only [reqOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩ := hr
  intro x hx1 hx2
  obtain ⟨h1, h2, h3, h4⟩ := h x hx1 hx2
  have hD : (0 : ℝ) < D := by norm_num [D]
  have hAx : (A : ℝ) ≤ x := le_trans (by exact_mod_cast hAn) hx1
  have c55 : ((220646 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) = 0.0220646 := by norm_num
  have c56 : ((239922 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) = 0.0239922 := by norm_num
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn1 hn2 => ?_, fun hn1 hn2 => ?_, fun hn1 hn2 => ?_⟩
  · rcases r1 with r1 | r1
    · omega
    · rw [r1, Nat.cast_zero, zero_div] at h1
      linarith
  · rcases r2 with r2 | r2
    · omega
    · have hc : (r.psUp : ℝ) * 100 ≤ 4 * D * A := by exact_mod_cast r2
      have : (r.psUp : ℝ) / D ≤ 0.04 * x := by
        rw [div_le_iff₀ hD]
        nlinarith
      linarith
  · rcases r3 with (r3 | r3) | r3
    · omega
    · omega
    · linarith [logOk_spec (by norm_num) c55 r3 hAx]
  · rcases r4 with (r4 | r4) | r4
    · omega
    · omega
    · linarith [logOk_spec (by norm_num) c55 r4 hAx]
  · rcases r5 with (r5 | r5) | ⟨r5, r6⟩
    · omega
    · omega
    · rw [abs_lt]
      constructor
      · linarith [logOk_spec (by norm_num) c56 r6 hAx]
      · linarith [logOk_spec (by norm_num) c56 r5 hAx]

/-- A certified stretch `[A, B)` of the walk. -/
def Seg (A B : ℕ) (sA sB : WS) : Prop :=
  Inv A sA → Inv B sB ∧ ∀ n, A ≤ n → n < B → Good n

theorem Seg.trans {A B C : ℕ} {sA sB sC : WS} (h1 : Seg A B sA sB) (h2 : Seg B C sB sC) :
    Seg A C sA sC := by
  intro h
  obtain ⟨hB, g1⟩ := h1 h
  obtain ⟨hC, g2⟩ := h2 hB
  refine ⟨hC, fun n hn1 hn2 => ?_⟩
  rcases Nat.lt_or_ge n B with hn | hn
  · exact g1 n hn1 hn
  · exact g2 n hn hn2

theorem seg_of {A L : ℕ} (r : Req) {sA sB : WS} (hA : 1 ≤ A) (hB : A + L < 1163 * 1163)
    (h : walk A L r sA = some sB ∧ reqOk A (A + L) r = true) : Seg A (A + L) sA sB := by
  intro hinv
  obtain ⟨hw, hr⟩ := h
  obtain ⟨h1, h2⟩ := walk_spec L A r sA sB hA hB hinv hw
  exact ⟨h1, fun n hn1 hn2 => good_of_holds hr hn1 hn2 (h2 n hn1 hn2)⟩

end TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk
