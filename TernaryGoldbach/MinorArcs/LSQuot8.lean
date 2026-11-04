import TernaryGoldbach.MinorArcs.LSQuotRed
import TernaryGoldbach.Prelim.SmallMuPhi

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# [H, Prop 12.2.4] with `c₊ = 2`, part 3: the divisors of `30030`

For every `A ∣ 30030` and every `n ≥ 4`, `Φ(A, n, log A) ≤ 0`:
* `n ≥ 2600` by Ramaré's estimate (12.12) (`Phi2_tail`);
* `4 ≤ n < 2600` by a kernel walk over `r ≤ 2599`: trial division gives squarefreeness and `φ(r)`
  (`phiAll`), the walk accumulates `U = ∑ ⌈10¹²/φ(r)⌉ ≥ 10¹² G_A(n)` and checks, on blocks
  `[a, b]`, `K_A U(b)/10¹² + 0.1768 K_A F_A/v ≤ j·0.693147/6 + 1.9999999 + W_A`, with
  `2^j ≤ a⁶` (so `j log 2/6 ≤ log a`) and `v³ ≤ a` (so `a^{−1/3} ≤ 1/v`).

`K_A = A/φ(A)`, `F_A ≥ f₁(A)` and `W_A ≤ 0.6586 S_A + 0.3414 log A` are products and sums over
the primes of `A` of rational per-prime bounds (`fupQ`, `wlQ`, `rlQ`).
-/

open Real Finset
open TernaryGoldbach.Prelim.SmallMuPhi (phiTD phiTD_spec)

namespace TernaryGoldbach.MinorArcs

/-! ### Per-prime bounds -/

/-- Rational lower bounds for `log p`, `p ≤ 13`. -/
def lpQ (p : ℕ) : ℚ :=
  if p = 2 then 0.693146 else if p = 3 then 1.098612 else if p = 5 then 1.609437 else
  if p = 7 then 1.945909 else if p = 11 then 2.397895 else if p = 13 then 2.564949 else 0

/-- Rational upper bounds for `f₁(p)`, `p ≤ 13`. -/
def fupQ (p : ℕ) : ℚ :=
  if p = 2 then 0.67254 else if p = 3 then 0.93306 else if p = 5 then 1.0896 else
  if p = 7 then 1.12415 else if p = 11 then 1.12864 else if p = 13 then 1.1241 else 0

/-- `0.6586 log p/p + 0.3414 log p ≥ wlQ p`. -/
def wlQ (p : ℕ) : ℚ := (0.6586 / p + 0.3414) * lpQ p

/-- `0.3414 (log p − log p/p) ≥ rlQ p`. -/
def rlQ (p : ℕ) : ℚ := 0.3414 * (1 - 1 / p) * lpQ p

theorem mem_PR {p : ℕ} {A : ℕ} (hA : A ∣ 30030) (hp : p ∈ A.primeFactors) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have h1 : p ∈ (30030 : ℕ).primeFactors := Nat.primeFactors_mono hA (by norm_num) hp
  have h2 : (30030 : ℕ).primeFactors = {2, 3, 5, 7, 11, 13} := by decide +kernel
  rw [h2] at h1
  simpa using h1

theorem lpQ_le {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13) :
    (lpQ p : ℝ) ≤ Real.log p := by
  have u := fun (z : ℝ) (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : 2.7182818286 ^ n * (taylor6 f + f ^ 7 / 4410) ≤ z) => le_log_num (z := z) n f h0 h1 h
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (lpQ 2 : ℝ) = 0.693146 by norm_num [lpQ]]
    have := u 2 0 0.693146 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith
  · rw [show (lpQ 3 : ℝ) = 1.098612 by norm_num [lpQ]]
    have := u 3 1 0.098612 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith
  · rw [show (lpQ 5 : ℝ) = 1.609437 by norm_num [lpQ]]
    have := u 5 1 0.609437 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith
  · rw [show (lpQ 7 : ℝ) = 1.945909 by norm_num [lpQ]]
    have := u 7 1 0.945909 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith
  · rw [show (lpQ 11 : ℝ) = 2.397895 by norm_num [lpQ]]
    have := u 11 2 0.397895 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith
  · rw [show (lpQ 13 : ℝ) = 2.564949 by norm_num [lpQ]]
    have := u 13 2 0.564949 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    push_cast at this; linarith

theorem f1p_le_fupQ {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13) :
    f1p p ≤ (fupQ p : ℝ) := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · refine (f1p_le_of (by norm_num) (u := 1.2599) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num
  · refine (f1p_le_of (by norm_num) (u := 1.4422) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num
  · refine (f1p_le_of (by norm_num) (u := 1.7099) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num
  · refine (f1p_le_of (by norm_num) (u := 1.9129) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num
  · refine (f1p_le_of (by norm_num) (u := 2.2239) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num
  · refine (f1p_le_of (by norm_num) (u := 2.3513) (by norm_num) (by norm_num)).trans ?_
    simp only [fupQ]; norm_num

/-! ### The constants of `A` -/

def KQ (A : ℕ) : ℚ := ∏ p ∈ A.primeFactors, (p : ℚ) / (p - 1)
def FupA (A : ℕ) : ℚ := ∏ p ∈ A.primeFactors, fupQ p
def WQ (A : ℕ) : ℚ := ∑ p ∈ A.primeFactors, wlQ p
def RQ (A : ℕ) : ℚ := ∑ p ∈ A.primeFactors, rlQ p

theorem KQ_eq {A : ℕ} (hA : 1 ≤ A) : (A : ℝ) / Nat.totient A = (KQ A : ℝ) := by
  rw [TernaryGoldbach.Prelim.div_totient_eq_prod hA, KQ]; push_cast; rfl

theorem f1q_le_FQ {A : ℕ} (hA : A ∣ 30030) : f1q A ≤ (FupA A : ℝ) := by
  unfold f1q FupA; push_cast
  exact prod_le_prod₀ (fun p _ => (f1p_pos p).le) (fun p hp => f1p_le_fupQ (mem_PR hA hp))

theorem log_eq_sum {A : ℕ} (hA : A ∣ 30030) : Real.log A = ∑ p ∈ A.primeFactors, Real.log p := by
  have hsq : Squarefree A := Squarefree.squarefree_of_dvd hA (by decide +kernel)
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  push_cast
  exact Real.log_prod fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).pos; positivity

theorem WQ_le {A : ℕ} (hA : A ∣ 30030) : (WQ A : ℝ) ≤ 0.6586 * Sq A + 0.3414 * Real.log A := by
  rw [log_eq_sum hA, Sq, mul_sum, mul_sum, ← sum_add_distrib, WQ]; push_cast
  refine sum_le_sum fun p hp => ?_
  have hp' := mem_PR hA hp
  have hl := lpQ_le hp'
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  unfold wlQ; push_cast
  have : (0.6586 / (p : ℝ) + 0.3414) * lpQ p ≤ (0.6586 / (p : ℝ) + 0.3414) * Real.log p :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have e : (0.6586 / (p : ℝ) + 0.3414) * Real.log p = 0.6586 * (Real.log p / p) + 0.3414 * Real.log p := by
    ring
  linarith

theorem RQ_le {A : ℕ} (hA : A ∣ 30030) : (RQ A : ℝ) ≤ 0.3414 * (Real.log A - Sq A) := by
  rw [log_eq_sum hA, Sq, ← sum_sub_distrib, mul_sum, RQ]; push_cast
  refine sum_le_sum fun p hp => ?_
  have hl := lpQ_le (mem_PR hA hp)
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  unfold rlQ; push_cast
  have h1 : 0 ≤ 1 - 1 / (p : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have : 0.3414 * (1 - 1 / (p : ℝ)) * lpQ p ≤ 0.3414 * (1 - 1 / (p : ℝ)) * Real.log p :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have e : 0.3414 * (1 - 1 / (p : ℝ)) * Real.log p = 0.3414 * (Real.log p - Real.log p / p) := by ring
  linarith

/-! ### `n ≥ 2600`: Ramaré -/

/-- `Φ(q, n, L) ≤ 7.4608 K f₁ n^{−1/3} + 10⁻⁷ − (0.3414 (L − S) + 0.6674177)`. -/
theorem Phi2_ramare {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (L : ℝ) :
    Phi2 q n L ≤ 7.4608 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) + 1e-7 -
      (0.3414 * (L - Sq q) + 0.6674177) := by
  obtain ⟨c, hc1, hc2, hram⟩ := ramare_Gq
  have h := (abs_le.1 (hram q hq n (by exact_mod_cast hn))).2
  have hK := qphi_pos hq
  have hKk : (q : ℝ) / Nat.totient q * (Nat.totient q / q) = 1 := by
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have : (0 : ℝ) < q := by exact_mod_cast hq
    field_simp
  have hn3 : 0 < (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hneg : (n : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg (by positivity), inv_eq_one_div]
  rw [hneg] at h
  have h2 := mul_le_mul_of_nonneg_left h hK.le
  have e : (q : ℝ) / Nat.totient q * (Gq q n - Nat.totient q / q * (Real.log n + c + Sq q)) =
      (q : ℝ) / Nat.totient q * Gq q n - (Real.log n + c + Sq q) := by
    rw [mul_sub, ← mul_assoc, hKk, one_mul]
  rw [e] at h2
  unfold Phi2
  have e2 : (q : ℝ) / Nat.totient q * (7.284 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) * f1q q) =
      7.284 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) := by ring
  have e3 : 0.1768 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) =
      0.1768 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) := by ring
  rw [e2] at h2
  rw [e3]
  have e4 : 7.4608 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) =
      7.284 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) +
        0.1768 * ((q : ℝ) / Nat.totient q * f1q q) / (n : ℝ) ^ (1 / 3 : ℝ) := by ring
  rw [e4]
  linarith

/-- The tail check, over the divisors of `30030`. -/
def tailOK (A : ℕ) : Bool := decide (7.4608 * KQ A * FupA A ≤ 13.75 * (RQ A + 0.6674176))

theorem tailOK_all : ∀ A ∈ (30030 : ℕ).divisors, tailOK A = true := by decide +kernel

theorem Phi2_tail {A n : ℕ} (hA : A ∣ 30030) (hn : 2600 ≤ n) : Phi2 A n (Real.log A) ≤ 0 := by
  have hA1 : 1 ≤ A := Nat.pos_of_dvd_of_pos hA (by norm_num)
  have h := Phi2_ramare hA1 (by omega) (Real.log A) (q := A) (n := n)
  have ht := tailOK_all A (Nat.mem_divisors.2 ⟨hA, by norm_num⟩)
  simp only [tailOK, decide_eq_true_eq] at ht
  have ht' : (7.4608 : ℝ) * KQ A * FupA A ≤ 13.75 * (RQ A + 0.6674176) := by
    have := (Rat.cast_le (K := ℝ)).2 ht
    push_cast at this; linarith
  have hK := KQ_eq hA1
  have hF := f1q_le_FQ hA
  have hR := RQ_le hA
  have hK0 := qphi_pos hA1
  have hf0 := f1q_pos A
  have hn3 : (13.75 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    calc (13.75 : ℝ) = ((13.75 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num)
          (by have : (2600 : ℝ) ≤ n := by exact_mod_cast hn
              norm_num; linarith) (by norm_num)
  have hKF : (A : ℝ) / Nat.totient A * f1q A ≤ (KQ A : ℝ) * FupA A := by
    rw [hK]; exact mul_le_mul_of_nonneg_left hF (by rw [← hK]; exact hK0.le)
  have hKF0 : 0 ≤ (KQ A : ℝ) * FupA A := le_trans (mul_pos hK0 hf0).le hKF
  have h1 : 7.4608 * ((A : ℝ) / Nat.totient A * f1q A) / (n : ℝ) ^ (1 / 3 : ℝ) ≤
      7.4608 * ((KQ A : ℝ) * FupA A) / 13.75 := by
    apply div_le_div₀ (by positivity) (by linarith) (by norm_num) hn3
  have h2 : 7.4608 * ((KQ A : ℝ) * FupA A) / 13.75 ≤ RQ A + 0.6674176 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  linarith

/-! ### Squarefreeness and `φ` by trial division -/

/-- `some none` if `r` is not squarefree, `some (some φ(r))` if it is. -/
def phiAll (r : ℕ) : Option (Option ℕ) :=
  if r % 2 = 0 then (if r % 4 = 0 then some none else phiTD r (r / 2) 3) else phiTD (r + 2) r 3

theorem phiAll_spec {r : ℕ} (hr : 1 ≤ r) {o : Option ℕ} (h : phiAll r = some o) :
    (o = none → ¬ Squarefree r) ∧ (∀ t, o = some t → Squarefree r ∧ r.totient = t) := by
  unfold phiAll at h
  split_ifs at h with h2 h4
  · cases h
    refine ⟨fun _ hs => ?_, fun t ht => by simp at ht⟩
    have : 2 * 2 ∣ r := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.isUnit_iff.1 (hs 2 this); omega
  · -- `r = 2m`, `m` odd
    have hm : r = 2 * (r / 2) := by omega
    have hmodd : (r / 2) % 2 = 1 := by omega
    have hm1 : 1 ≤ r / 2 := by omega
    have hspec := phiTD_spec _ _ _ _ le_rfl rfl hm1 (fun p hp hpd => by
      have h2le := hp.two_le
      by_contra hlt; have : p = 2 := by omega
      subst this; omega) h
    have hcop : Nat.Coprime 2 (r / 2) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    refine ⟨fun ho hs => hspec.1 ho (hs.squarefree_of_dvd ⟨2, by omega⟩), fun t ht => ?_⟩
    obtain ⟨hs, ht'⟩ := hspec.2 t ht
    rw [hm, Nat.squarefree_mul hcop, Nat.totient_mul hcop, Nat.totient_two, one_mul]
    exact ⟨⟨Nat.prime_two.squarefree, hs⟩, ht'⟩
  · have hodd : r % 2 = 1 := by omega
    exact phiTD_spec _ _ _ _ le_rfl rfl hr (fun p hp hpd => by
      have h2le := hp.two_le
      by_contra hlt; have : p = 2 := by omega
      subst this; omega) h

/-! ### The accumulator -/

/-- `U_A(n) = ∑_{r ≤ n, (r, A) = 1, r squarefree} ⌈10¹²/φ(r)⌉`. -/
noncomputable def UA (A n : ℕ) : ℕ :=
  ∑ r ∈ Icc 1 n, if Nat.Coprime r A ∧ Squarefree r then
    (1000000000000 + r.totient - 1) / r.totient else 0

theorem UA_succ (A n : ℕ) : UA A (n + 1) = UA A n +
    if Nat.Coprime (n + 1) A ∧ Squarefree (n + 1) then
      (1000000000000 + (n + 1).totient - 1) / (n + 1).totient else 0 := by
  rw [UA, UA, sum_Icc_succ_top (by omega)]

theorem Gq_le_UA (A n : ℕ) : 1000000000000 * Gq A n ≤ (UA A n : ℝ) := by
  rw [Gq_eq, Nat.floor_natCast, UA, mul_sum, sum_filter]
  push_cast
  refine sum_le_sum fun r hr => ?_
  have hr1 : 1 ≤ r := (mem_Icc.1 hr).1
  by_cases hc : Nat.Coprime r A
  · rw [if_pos hc]
    by_cases hs : Squarefree r
    · rw [if_pos ⟨hc, hs⟩, gf_eq_gQ]
      simp only [gQ, if_pos hs]
      have ht : 0 < r.totient := Nat.totient_pos.2 (by omega)
      set t := r.totient
      have h1 : (1000000000000 : ℝ) / t ≤ (((1000000000000 + t - 1) / t : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast ht)]
        have h2 : 1000000000000 ≤ (1000000000000 + t - 1) / t * t := by
          have := Nat.div_add_mod (1000000000000 + t - 1) t
          have := Nat.mod_lt (1000000000000 + t - 1) ht
          rw [mul_comm]; omega
        exact_mod_cast h2
      push_cast; rw [← div_eq_mul_one_div]; exact h1
    · rw [if_neg (fun h => hs h.2), gf_eq_gQ]; simp [gQ, hs]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]

theorem Gq_mono_nat (A : ℕ) {m n : ℕ} (h : m ≤ n) : Gq A m ≤ Gq A n := by
  rw [Gq_eq, Gq_eq, Nat.floor_natCast, Nat.floor_natCast]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Icc_subset_Icc le_rfl h))
    (fun r _ _ => gf_nonneg r)

/-! ### The walk -/

/-- The contribution of `r`. -/
def stepAdd (A r : ℕ) : Option ℕ :=
  if Nat.gcd r A = 1 then
    match phiAll r with
    | none => none
    | some none => some 0
    | some (some t) => some ((1000000000000 + t - 1) / t)
  else some 0

theorem stepAdd_spec {A r : ℕ} (hr : 1 ≤ r) {d : ℕ} (h : stepAdd A r = some d) :
    d = if Nat.Coprime r A ∧ Squarefree r then (1000000000000 + r.totient - 1) / r.totient
      else 0 := by
  unfold stepAdd at h
  split_ifs at h with hg
  · rcases hp : phiAll r with _ | _ | t
    · rw [hp] at h; simp at h
    · rw [hp] at h; simp only [Option.some.injEq] at h
      have := (phiAll_spec hr hp).1 rfl
      rw [if_neg (fun hc => this hc.2)]; exact h.symm
    · rw [hp] at h; simp only [Option.some.injEq] at h
      obtain ⟨hs, ht⟩ := (phiAll_spec hr hp).2 t rfl
      rw [if_pos ⟨hg, hs⟩, ht]; exact h.symm
  · simp only [Option.some.injEq] at h
    rw [if_neg (fun hc => hg hc.1)]; exact h.symm

/-- Advances from `r` to `b`, returning `U_A(b)`. -/
def advance (A : ℕ) : ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, r, b, acc => if r = b then some acc else none
  | f + 1, r, b, acc =>
    if r = b then some acc else
    match stepAdd A (r + 1) with
    | none => none
    | some d => advance A f (r + 1) b (acc + d)

theorem advance_spec (A : ℕ) : ∀ (f r b acc acc' : ℕ), acc = UA A r →
    advance A f r b acc = some acc' → acc' = UA A b ∧ r ≤ b := by
  intro f
  induction f with
  | zero =>
    intro r b acc acc' hacc h
    simp only [advance] at h
    split_ifs at h with hrb
    · simp only [Option.some.injEq] at h; subst hrb; exact ⟨h ▸ hacc, le_rfl⟩
  | succ f ih =>
    intro r b acc acc' hacc h
    simp only [advance] at h
    split_ifs at h with hrb
    · simp only [Option.some.injEq] at h; subst hrb; exact ⟨h ▸ hacc, le_rfl⟩
    · rcases hs : stepAdd A (r + 1) with _ | d
      · rw [hs] at h; simp at h
      · rw [hs] at h
        simp only at h
        have hd := stepAdd_spec (by omega) hs
        have := ih (r + 1) b (acc + d) acc' (by rw [hacc, hd, UA_succ]) h
        exact ⟨this.1, by omega⟩

/-- The block check at `[a, b]` with `U = U_A(b)`. -/
def blockOK (K c W : ℚ) (U a b j : ℕ) (v : ℚ) : Bool :=
  decide (1 ≤ a) && decide (a ≤ b) && decide (2 ^ j ≤ a ^ 6) && decide (0 < v) &&
    decide (v ^ 3 ≤ a) &&
    decide (K * U / 1000000000000 + c / v ≤ j * 0.693146 / 6 + 1.9999999 + W)

/-- The walk over the blocks. -/
def walkB (A : ℕ) (K c W : ℚ) : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℚ) → Bool
  | _, _, [] => true
  | r, acc, (a, b, j, v) :: rest =>
    match advance A (b - r) r b acc with
    | none => false
    | some acc' => blockOK K c W acc' a b j v && walkB A K c W b acc' rest

theorem walkB_spec (A : ℕ) (K c W : ℚ) : ∀ (L : List (ℕ × ℕ × ℕ × ℚ)) (r : ℕ),
    walkB A K c W r (UA A r) L = true →
    ∀ x ∈ L, blockOK K c W (UA A x.2.1) x.1 x.2.1 x.2.2.1 x.2.2.2 = true := by
  intro L
  induction L with
  | nil => intro r _ x hx; simp at hx
  | cons hd tl ih =>
    intro r h x hx
    obtain ⟨a, b, j, v⟩ := hd
    simp only [walkB] at h
    rcases hadv : advance A (b - r) r b (UA A r) with _ | acc'
    · rw [hadv] at h; simp at h
    · rw [hadv] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hb, hrest⟩ := h
      have hsp := advance_spec A _ r b _ acc' rfl hadv
      rw [hsp.1] at hb hrest
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hb
      · exact ih b hrest x hx

/-- A passed block gives `Φ(A, n, log A) ≤ 0` on `[a, b]`. -/
theorem Phi2_of_block {A a b j n : ℕ} {v : ℚ} (hA : A ∣ 30030)
    (h : blockOK (KQ A) (0.1768 * KQ A * FupA A) (WQ A) (UA A b) a b j v = true)
    (hna : a ≤ n) (hnb : n ≤ b) : Phi2 A n (Real.log A) ≤ 0 := by
  simp only [blockOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha1, -⟩, hj⟩, hv0⟩, hv3⟩, hmain⟩ := h
  have hA1 : 1 ≤ A := Nat.pos_of_dvd_of_pos hA (by norm_num)
  have hn1 : 1 ≤ n := le_trans ha1 hna
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  -- the pieces in `ℝ`
  have hmain' : (KQ A : ℝ) * (UA A b : ℝ) / 1000000000000 + (0.1768 * KQ A * FupA A : ℚ) / (v : ℝ) ≤
      j * 0.693146 / 6 + 1.9999999 + (WQ A : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hmain
    push_cast at this ⊢; linarith
  have hK := KQ_eq hA1
  have hK0 := qphi_pos hA1
  have hF := f1q_le_FQ hA
  have hf0 := f1q_pos A
  have hW := WQ_le hA
  have hv0' : (0 : ℝ) < v := by exact_mod_cast hv0
  -- `K G_A(n) ≤ K U_A(b)/10¹²`
  have hG : (A : ℝ) / Nat.totient A * Gq A n ≤ (KQ A : ℝ) * (UA A b : ℝ) / 1000000000000 := by
    have h1 := Gq_mono_nat A hnb
    have h2 := Gq_le_UA A b
    rw [hK] at hK0 ⊢
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hK0.le
    rw [le_div_iff₀ (by norm_num)]; linarith
  -- `log n ≥ j log 2/6 ≥ j·0.693146/6`
  have hlog : (j : ℝ) * 0.693146 / 6 ≤ Real.log n := by
    have h1 : (2 : ℝ) ^ j ≤ (a : ℝ) ^ 6 := by exact_mod_cast hj
    have h2 : (j : ℝ) * Real.log 2 ≤ 6 * Real.log a := by
      have := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow, Real.log_pow] at this
    have h3 : (0.693146 : ℝ) ≤ Real.log 2 := by
      have := lpQ_le (p := 2) (Or.inl rfl)
      have e : (lpQ 2 : ℝ) = 0.693146 := by norm_num [lpQ]
      push_cast at this; linarith
    have h4 : Real.log a ≤ Real.log n := Real.log_le_log ha0 (by exact_mod_cast hna)
    have : (j : ℝ) * 0.693146 ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  -- `n^{1/3} ≥ v`
  have hn3 : (v : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h1 : ((v : ℝ) ^ 3) ^ (1 / 3 : ℝ) = v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv0'.le]; norm_num
    have h2 : (v : ℝ) ^ 3 ≤ n := by
      have : ((v ^ 3 : ℚ) : ℝ) ≤ ((a : ℚ) : ℝ) := by exact_mod_cast hv3
      push_cast at this
      have : (a : ℝ) ≤ n := by exact_mod_cast hna
      linarith
    calc (v : ℝ) = ((v : ℝ) ^ 3) ^ (1 / 3 : ℝ) := h1.symm
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  have hc : 0.1768 * ((A : ℝ) / Nat.totient A) * f1q A / (n : ℝ) ^ (1 / 3 : ℝ) ≤
      ((0.1768 * KQ A * FupA A : ℚ) : ℝ) / (v : ℝ) := by
    push_cast
    rw [← hK]
    apply div_le_div₀ _ _ hv0' hn3
    · have : (0 : ℝ) ≤ (A : ℝ) / Nat.totient A * FupA A :=
        mul_nonneg hK0.le (le_trans hf0.le hF)
      nlinarith
    · have := mul_le_mul_of_nonneg_left hF hK0.le
      nlinarith
  unfold Phi2
  linarith

end TernaryGoldbach.MinorArcs
