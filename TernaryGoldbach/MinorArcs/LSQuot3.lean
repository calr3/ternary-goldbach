import TernaryGoldbach.MinorArcs.LSQuot2

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# [H, Prop 12.2.4], part 3: small `R` ([H, Lemmas 12.2.1–12.2.3])

`regionS`: if `log q + 1.039 R ≤ c' (qR)^{2/9}` and `e^γ log c' + 2.50637/log log q ≤ 0.86`, then
`G_q(R) ≤ (log Q₀ + 1.36)/(log Q + c_E) · G_q(tR)`.
-/

open Real Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `G(t) ≥ log t + 1.064` for `t ≥ 20000`, from (12.12). -/
theorem G_ge_log {t : ℝ} (ht : 20000 ≤ t) : Real.log t + 1.064 ≤ Gq 1 t := by
  obtain ⟨c, hc1, -, hram⟩ := ramare_Gq
  have h := (abs_le.1 (hram 1 le_rfl t (by linarith))).1
  have hS : Sq 1 = 0 := by simp [Sq]
  have hf : f1q 1 = 1 := by simp [f1q]
  rw [hS, hf] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul, mul_one, add_zero] at h
  have := rpow_neg_third_le ht
  nlinarith

/-- The primes `≤ R` together with those dividing `q`. -/
noncomputable def primeSetRq (R : ℝ) (q : ℕ) : Finset ℕ := (Icc 1 ⌊R⌋₊).filter Nat.Prime ∪ q.primeFactors

theorem primeSetRq_prime {R : ℝ} {q : ℕ} : ∀ p ∈ primeSetRq R q, p.Prime := by
  intro p hp
  rcases mem_union.1 hp with h | h
  · exact (mem_filter.1 h).2
  · exact Nat.prime_of_mem_primeFactors h

/-- `log P ≤ log q + 1.039 R` for `P = ∏_{p ≤ R or p ∣ q} p`. -/
theorem log_prod_primeSetRq_le {R : ℝ} (hR : 0 ≤ R) {q : ℕ} (hq : 1 ≤ q) :
    Real.log (∏ p ∈ primeSetRq R q, p : ℕ) ≤ Real.log q + 1.039 * R := by
  have hpos : ∀ p ∈ primeSetRq R q, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (primeSetRq_prime p hp).pos
  rw [Nat.cast_prod, Real.log_prod (fun p hp => (hpos p hp).ne')]
  have hnn : ∀ p ∈ primeSetRq R q, 0 ≤ Real.log (p : ℝ) := fun p _ => Real.log_natCast_nonneg p
  have h1 : ∑ p ∈ primeSetRq R q, Real.log (p : ℝ) ≤
      ∑ p ∈ (Icc 1 ⌊R⌋₊).filter Nat.Prime, Real.log (p : ℝ) +
        ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    unfold primeSetRq
    rw [← sum_union_inter]
    exact le_add_of_nonneg_right (sum_nonneg fun p _ => Real.log_natCast_nonneg p)
  have h2 : ∑ p ∈ (Icc 1 ⌊R⌋₊).filter Nat.Prime, Real.log (p : ℝ) ≤ 1.039 * R := by
    have h := (TernaryGoldbach.Prelim.thetaN_le_psiN ⌊R⌋₊).trans
      (TernaryGoldbach.Prelim.psiN_le ⌊R⌋₊)
    unfold TernaryGoldbach.Prelim.thetaN at h
    have hf : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR
    nlinarith
  have h3 : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log q := by
    rw [← Real.log_prod (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)]
    apply Real.log_le_log (prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    have : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
    have h2 : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    simpa [Nat.cast_prod] using h2
  linarith

/-- `X (L + 1.33258) ≤ (l + 1.36)(L − l + 1.064)` for `X ≤ 0.4 l + 0.86`, `l ≥ 11.5`, `l ≤ 0.6 L`. -/
theorem poly_regionS {X l L : ℝ} (hX : X ≤ 0.4 * l + 0.86) (hX0 : 0 ≤ X) (hl : 11.5 ≤ l)
    (hρ : l ≤ 0.6 * L) : X * (L + 1.33258) ≤ (l + 1.36) * (L - l + 1.064) := by
  have hLc : 0 ≤ L + 1.33258 := by linarith
  have h06 : 0 ≤ 0.6 * l + 0.5 := by linarith
  have hLl : 0 ≤ 0.6 * L - l := by linarith
  nlinarith [mul_nonneg h06 hLl, mul_le_mul_of_nonneg_right hX hLc]

/-- **Small `R`** ([H, Lemmas 12.2.1–12.2.3], with `log Q + c_E` in the denominator). -/
theorem regionS {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    (hR : 1 ≤ Q₀ / (s * q)) {c' : ℝ} (hc' : 0 < c') (hlq : 3 ≤ Real.log q)
    (hcc : Real.exp Real.eulerMascheroniConstant * Real.log c' +
      2.50637 / Real.log (Real.log q) ≤ 0.86)
    (hh : Real.log q + 1.039 * (Q₀ / (s * q)) ≤ c' * ((q : ℝ) * (Q₀ / (s * q))) ^ ((2 : ℝ) / 9)) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hQ₀0 : 0 < Q₀ := by linarith
  set R := Q₀ / (s * q) with hRdef
  have hR0 : 0 < R := by linarith
  set t := Q / Q₀ with htdef
  have ht : 20000 ≤ t := by rw [htdef, le_div_iff₀ hQ₀0]; linarith
  have htR : Q / (s * q) = t * R := by rw [htdef, hRdef]; field_simp
  rw [htR]
  -- `P`
  set T := primeSetRq R q
  set P := ∏ p ∈ T, p
  have hTp := primeSetRq_prime (R := R) (q := q)
  have hP0 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => (hTp p hp).ne_zero)
  have hPsq : Squarefree P := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
      fun p hp => (hTp p hp).squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hTp a ha) (hTp b hb)).mpr hab
  have hPR : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → p ∣ P := fun p hp hpR =>
    dvd_prod_of_mem _ (mem_union_left _ (mem_filter.2
      ⟨mem_Icc.2 ⟨hp.one_le, Nat.le_floor hpR⟩, hp⟩))
  have hPq : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ P := fun p hp hpq =>
    dvd_prod_of_mem _ (mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, hpq, by omega⟩))
  have h1 := Gq_mul_le (q := q) (P := P) (R := R) (t := t) hR0.le (by linarith) hPR hPq
  have h2 := G_le_mul_Gq hPsq (t := t)
  have h3 := G_ge_log ht
  -- `X = P/φ(P) ≤ 0.86 + 0.4 log(qR)`
  set X := (P : ℝ) / Nat.totient P
  set V := Real.log q + 1.039 * R with hVdef
  have hVq : Real.log q ≤ V := by rw [hVdef]; linarith
  have hV3 : 3 ≤ V := by linarith
  have hPV : (P : ℝ) ≤ Real.exp V := by
    have hl := log_prod_primeSetRq_le hR0.le hq
    have hPpos : (0 : ℝ) < P := by exact_mod_cast hP0
    calc (P : ℝ) = Real.exp (Real.log P) := (Real.exp_log hPpos).symm
      _ ≤ Real.exp V := Real.exp_le_exp.2 hl
  have hexpV : (3 : ℝ) ≤ Real.exp V := by
    have := Real.add_one_le_exp V; linarith
  have hX := TernaryGoldbach.Prelim.div_totient_lt hP0 hexpV hPV
  rw [Real.log_exp] at hX
  have hllq : 1 ≤ Real.log (Real.log q) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlV1 : Real.log (Real.log q) ≤ Real.log V := Real.log_le_log (by linarith) hVq
  have hqR : 0 < (q : ℝ) * R := by positivity
  have hlogV : Real.log V ≤ Real.log c' + (2 / 9) * Real.log ((q : ℝ) * R) := by
    have := Real.log_le_log (by linarith) hh
    rwa [Real.log_mul hc'.ne' (by positivity), Real.log_rpow hqR] at this
  have hγ := TernaryGoldbach.MinorArcs.exp_gamma_le_sharp
  have hγ0 : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlqR : 0 ≤ Real.log ((q : ℝ) * R) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 hR)
  have hX' : X ≤ 0.86 + 0.4 * Real.log ((q : ℝ) * R) := by
    have e1 : 2.50637 / Real.log V ≤ 2.50637 / Real.log (Real.log q) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hlV1
    have e2 : Real.exp Real.eulerMascheroniConstant * Real.log V ≤
        Real.exp Real.eulerMascheroniConstant * Real.log c' +
          Real.exp Real.eulerMascheroniConstant * ((2 / 9) * Real.log ((q : ℝ) * R)) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hlogV hγ0.le
    have e3 : Real.exp Real.eulerMascheroniConstant * ((2 / 9) * Real.log ((q : ℝ) * R)) ≤
        0.4 * Real.log ((q : ℝ) * R) := by nlinarith
    linarith
  -- `log(qR) ≤ log Q₀`
  have hqRQ : Real.log ((q : ℝ) * R) ≤ Real.log Q₀ := by
    apply Real.log_le_log hqR
    have e : (q : ℝ) * R = Q₀ / s := by rw [hRdef]; field_simp
    rw [e]; exact div_le_self hQ₀0.le hs
  -- combine
  have hX0 : 0 < X := by
    have : (0 : ℝ) < Nat.totient P := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have : (0 : ℝ) < P := by exact_mod_cast hP0
    positivity
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hGP : (Real.log t + 1.064) / X ≤ Gq P t := by
    rw [div_le_iff₀ hX0]; nlinarith
  have hGqR := Gq_nonneg_q q R
  have hmain : Gq q R * (Real.log t + 1.064) ≤ Gq q (t * R) * X := by
    have := mul_le_mul_of_nonneg_left hGP hGqR
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hX0] at this
    calc Gq q R * (Real.log t + 1.064) ≤ Gq q R * Gq P t * X := this
      _ ≤ Gq q (t * R) * X := mul_le_mul_of_nonneg_right h1 hX0.le
  -- the polynomial inequality
  set l := Real.log Q₀
  set L := Real.log Q
  have hl5 : 11.5 ≤ l := le_trans log_1e5_ge (Real.log_le_log (by norm_num) hQ₀)
  have hlogt : Real.log t = L - l := by
    rw [htdef, Real.log_div (by linarith) hQ₀0.ne']
  have hD : X * (L + cE) ≤ (l + 1.36) * (Real.log t + 1.064) := by
    rw [hlogt]; unfold cE
    exact poly_regionS (by linarith) hX0.le hl5 hρ
  have hden : 0 < Real.log t + 1.064 := by linarith
  have hLcE : 0 < L + cE := by unfold cE; linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hLcE]
  have hG2 := Gq_nonneg_q q (t * R)
  calc Gq q R * (L + cE) ≤ Gq q R * ((l + 1.36) * (Real.log t + 1.064) / X) := by
        apply mul_le_mul_of_nonneg_left _ hGqR
        rw [le_div_iff₀ hX0]; linarith
    _ = Gq q R * (Real.log t + 1.064) * (l + 1.36) / X := by ring
    _ ≤ Gq q (t * R) * X * (l + 1.36) / X := by
        apply div_le_div_of_nonneg_right _ hX0.le
        exact mul_le_mul_of_nonneg_right hmain (by linarith)
    _ = (l + 1.36) * Gq q (t * R) := by field_simp

end TernaryGoldbach.MinorArcs
