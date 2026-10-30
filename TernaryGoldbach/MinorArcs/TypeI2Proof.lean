import TernaryGoldbach.MinorArcs.TypeILogProof
import TernaryGoldbach.Prelim.LambdaMu

/-!
# Proof of [B, Lemma 4.2.4] (the Type I sum with `Λ(v) μ(u)`; `η = η₂`)
-/

open Real Finset
open ArithmeticFunction (moebius vonMangoldt)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- `c(a) = ∑_{v | a, v ≤ V, a/v ≤ U} Λ(v) μ(a/v)` [B, (4.53)]. -/
noncomputable def coefI2 (U V : ℝ) (a : ℕ) : ℝ :=
  ∑ v ∈ a.divisors, if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then (Λ v : ℝ) * (μ (a / v) : ℝ) else 0

/-- `|c(a)| ≤ log a` [B, p. 73]. -/
theorem abs_coefI2_le (U V : ℝ) (a : ℕ) : |coefI2 U V a| ≤ Real.log a := by
  rw [coefI2, ← ArithmeticFunction.vonMangoldt_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  split_ifs
  · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have : |(μ (a / v) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := v), abs_nonneg ((μ (a / v) : ℝ))]
  · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg

/-- `typeI2` grouped by `a = uv`: `∑_{a ≤ ⌊U⌋⌊V⌋, a odd} c(a) T_{a,∘}(α)`. -/
theorem typeI2_eq {α x : ℝ} (hx : 0 < x) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    typeI2 α x U V = ∑ a ∈ Icc 1 (⌊V⌋₊ * ⌊U⌋₊),
      if Odd a then (coefI2 U V a : ℂ) * Todd α x a else 0 := by
  set NU := ⌊U⌋₊
  set NV := ⌊V⌋₊
  -- Step 1: the inner sums are `T_{vu,∘}`.
  have h1 : typeI2 α x U V = ∑ p ∈ Icc 1 NV ×ˢ Icc 1 NU,
      if Odd p.1 ∧ Odd p.2 then ((Λ p.1 : ℝ) * (μ p.2 : ℝ) : ℂ) * Todd α x (p.1 * p.2) else 0 := by
    rw [typeI2, sum_product]
    refine sum_congr rfl fun v hv => ?_
    by_cases hvo : Odd v
    · rw [if_pos hvo, mul_sum]
      refine sum_congr rfl fun u hu => ?_
      by_cases huo : Odd u
      · rw [if_pos huo, if_pos ⟨hvo, huo⟩]
        have hvu : 1 ≤ v * u := Nat.one_le_iff_ne_zero.2
          (Nat.mul_ne_zero (by have := (mem_Icc.1 hv).1; omega) (by have := (mem_Icc.1 hu).1; omega))
        rw [← inner_eq_Todd hx hvu]
        push_cast
        simp only [mul_assoc]
      · rw [if_neg huo, if_neg (fun h => huo h.2), mul_zero]
    · rw [if_neg hvo]
      exact (sum_eq_zero fun u _ => by rw [if_neg (fun h => hvo h.1)]).symm
  rw [h1]
  -- Step 2: group by `a = vu`.
  rw [← sum_fiberwise_of_maps_to (t := Icc 1 (NV * NU)) (g := fun p : ℕ × ℕ => p.1 * p.2)
    (fun p hp => by
      simp only [mem_product, mem_Icc] at hp ⊢
      exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul hp.1.2 hp.2.2⟩)]
  refine sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
  -- The fibre over `a`, matched with the divisors `v` of `a` with `v ≤ V`, `a/v ≤ U`.
  have hfib : ∑ p ∈ (Icc 1 NV ×ˢ Icc 1 NU).filter (fun p : ℕ × ℕ => p.1 * p.2 = a),
      (if Odd p.1 ∧ Odd p.2 then ((Λ p.1 : ℝ) * (μ p.2 : ℝ) : ℂ) * Todd α x (p.1 * p.2) else 0) =
      ∑ v ∈ a.divisors.filter (fun v : ℕ => (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U),
        (if Odd a then ((Λ v : ℝ) * (μ (a / v) : ℝ) : ℂ) * Todd α x a else 0) := by
    refine sum_nbij' (fun p => p.1) (fun v => (v, a / v)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      simp only [mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨p.2, h5.symm⟩, by omega⟩, (Nat.le_floor_iff hV).1 h2, ?_⟩
      rw [hdiv]; exact (Nat.le_floor_iff hU).1 h4
    · intro v hv
      simp only [mem_filter, Nat.mem_divisors] at hv
      obtain ⟨⟨hva, ha0⟩, h1, h2⟩ := hv
      have hv1 : 1 ≤ v := Nat.pos_of_dvd_of_pos hva (by omega)
      have hav : v * (a / v) = a := Nat.mul_div_cancel' hva
      simp only [mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨hv1, Nat.le_floor h1⟩, ?_, Nat.le_floor h2⟩, hav⟩
      rcases Nat.eq_zero_or_pos (a / v) with h | h
      · rw [h, mul_zero] at hav; omega
      · exact h
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      ext <;> simp [hdiv]
    · intro v _; rfl
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
      have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
      have hodd : Odd p.1 ∧ Odd p.2 ↔ Odd a := by rw [← h5, Nat.odd_mul]
      simp only [hdiv, h5]
      by_cases ho : Odd a
      · rw [if_pos (hodd.2 ho), if_pos ho]
      · rw [if_neg (fun h => ho (hodd.1 h)), if_neg ho]
  rw [hfib, coefI2, sum_filter]
  by_cases ho : Odd a
  · rw [if_pos ho, Complex.ofReal_sum, sum_mul]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  · rw [if_neg ho]
    exact sum_eq_zero fun v _ => by split_ifs <;> rfl


/-- `∑_{u ≤ R, u odd, q' | u} f(u) = ∑_{w ≤ R/q', q'w odd} f(q'w)`. -/
theorem sum_dvd_reindex {q' : ℕ} (hq' : 1 ≤ q') (R : ℝ) (hR : 0 ≤ R) (f : ℕ → ℝ) :
    ∑ u ∈ Icc 1 ⌊R⌋₊, (if Odd u ∧ q' ∣ u then f u else 0) =
      ∑ w ∈ Icc 1 ⌊R / q'⌋₊, (if Odd (q' * w) then f (q' * w) else 0) := by
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq'
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (fun u => u / q') (fun w => q' * w) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_Icc] at hu ⊢
    obtain ⟨⟨h1, h2⟩, hodd, ⟨t, rfl⟩⟩ := hu
    rw [Nat.mul_div_cancel_left t (by omega)]
    refine ⟨⟨?_, ?_⟩, hodd⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at h1
      · exact h
    · apply Nat.le_floor
      rw [le_div_iff₀ hq0]
      have : ((q' * t : ℕ) : ℝ) ≤ R := (Nat.le_floor_iff hR).1 h2
      push_cast at this; linarith
  · intro w hw
    simp only [mem_filter, mem_Icc] at hw ⊢
    obtain ⟨⟨h1, h2⟩, hodd⟩ := hw
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, hodd,
      ⟨w, rfl⟩⟩
    apply Nat.le_floor
    have := (Nat.le_floor_iff (by positivity)).1 h2
    rw [le_div_iff₀ hq0] at this
    push_cast; linarith
  · intro u hu
    simp only [mem_filter] at hu
    exact Nat.mul_div_cancel' hu.2.2
  · intro w _; exact Nat.mul_div_cancel_left w (by omega)
  · intro u hu
    simp only [mem_filter] at hu
    rw [Nat.mul_div_cancel' hu.2.2]

/-- [B, p. 72]: for `q'` odd, `|∑_{u ≤ R, u odd, q' | u} μ(u)/u| ≤ 1/q'` (by (2.20)). -/
theorem abs_sum_moebius_odd_dvd_le {q' : ℕ} (hq' : Odd q') (R : ℝ) (hR : 0 ≤ R) :
    |∑ u ∈ Icc 1 ⌊R⌋₊, (if Odd u ∧ q' ∣ u then (μ u : ℝ) / u else 0)| ≤ 1 / q' := by
  have hq1 : 1 ≤ q' := hq'.pos
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  rw [sum_dvd_reindex hq1 R hR]
  have hodd : ∀ w, Odd (q' * w) ↔ Odd w := fun w => by
    rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hq', h⟩⟩
  have hterm : ∀ w ∈ Icc 1 ⌊R / q'⌋₊, (if Odd (q' * w) then (μ (q' * w) : ℝ) / ((q' * w : ℕ) : ℝ) else 0) =
      (1 / q') * ((μ q' : ℝ) * (if Nat.Coprime w (2 * q') then (μ w : ℝ) / w * 1 else 0)) := by
    intro w hw
    have hw1 : (0 : ℝ) < w := by exact_mod_cast (mem_Icc.1 hw).1
    rw [← moebius_odd_term hq' w]
    by_cases ho : Odd w
    · rw [if_pos ((hodd w).2 ho), if_pos ho]; push_cast; field_simp
    · rw [if_neg (fun h => ho ((hodd w).1 h)), if_neg ho, mul_zero]
  rw [sum_congr rfl hterm, ← mul_sum, ← mul_sum, abs_mul, abs_mul, abs_of_pos (by positivity)]
  have h1 : |(μ q' : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 := Prelim.abs_sum_moebius_div_coprime_le_one (R / q') (q := 2 * q') (by omega)
  simp only [mul_one] at h2 ⊢
  calc 1 / (q' : ℝ) * (|(μ q' : ℝ)| * |∑ w ∈ Icc 1 ⌊R / q'⌋₊,
        (if Nat.Coprime w (2 * q') then (μ w : ℝ) / w else 0)|) ≤ 1 / q' * (1 * 1) := by gcongr
    _ = 1 / q' := by ring

/-- `gcd(q, p^k) = p^{min(v_p(q), k)}`. -/
theorem gcd_prime_pow {p k q : ℕ} (hp : p.Prime) (hq : q ≠ 0) :
    Nat.gcd q (p ^ k) = p ^ min (q.factorization p) k := by
  obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right q (p ^ k))
  rw [hi]
  congr 1
  have h1 : i ≤ q.factorization p :=
    (hp.pow_dvd_iff_le_factorization hq).1 (hi ▸ Nat.gcd_dvd_left q (p ^ k))
  have h2 : p ^ min (q.factorization p) k ∣ Nat.gcd q (p ^ k) :=
    Nat.dvd_gcd ((pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd q p))
      (pow_dvd_pow p (min_le_right _ _))
  rw [hi] at h2
  have h3 : min (q.factorization p) k ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  exact le_antisymm (le_min h1 hik) h3

/-- For a prime power `v = p^k` not dividing `q`: `v/gcd(q,v) = p^{k - v_p(q)}` with `k > v_p(q)`. -/
theorem div_gcd_of_prime_pow {p k q : ℕ} (hp : p.Prime) (hq : q ≠ 0) (hndvd : ¬ p ^ k ∣ q) :
    q.factorization p < k ∧ p ^ k / Nat.gcd q (p ^ k) = p ^ (k - q.factorization p) := by
  have hlt : q.factorization p < k := by
    by_contra h; push Not at h
    exact hndvd ((hp.pow_dvd_iff_le_factorization hq).2 h)
  refine ⟨hlt, ?_⟩
  rw [gcd_prime_pow hp hq, min_eq_left hlt.le, Nat.pow_div hlt.le hp.pos]

/-- `Λ(v) gcd(q,v)/v ≤ [v | q] Λ(v) + [v ∤ q] Λ(v/gcd(q,v))/(v/gcd(q,v))`, with equality. -/
theorem vonMangoldt_gcd_term (q v : ℕ) (hq : q ≠ 0) (hv : v ≠ 0) :
    (Λ v : ℝ) * Nat.gcd q v / v =
      (if v ∣ q then (Λ v : ℝ) else 0) +
        (if ¬ v ∣ q ∧ IsPrimePow v then
          (Λ (v / Nat.gcd q v) : ℝ) / ((v / Nat.gcd q v : ℕ) : ℝ) else 0) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast Nat.pos_of_ne_zero hv
  by_cases hd : v ∣ q
  · rw [if_pos hd, if_neg (fun h => h.1 hd), add_zero, Nat.gcd_eq_right hd]
    field_simp
  · rw [if_neg hd, zero_add]
    by_cases hpp : IsPrimePow v
    · rw [if_pos ⟨hd, hpp⟩]
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff v).1 hpp
      obtain ⟨hlt, hdiv⟩ := div_gcd_of_prime_pow hp hq hd
      rw [hdiv, gcd_prime_pow hp hq, min_eq_left hlt.le,
        ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
      push_cast
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [show k = (k - q.factorization p) + q.factorization p by omega, pow_add]
      simp only [Nat.add_sub_cancel]
      field_simp
    · rw [if_neg (fun h => hpp h.2), (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hpp]
      simp

/-- `v ↦ v/gcd(q,v)` is injective on prime powers not dividing `q`. -/
theorem injOn_div_gcd (q : ℕ) (hq : q ≠ 0) (S : Finset ℕ) :
    Set.InjOn (fun v => v / Nat.gcd q v) ↑(S.filter (fun v => ¬ v ∣ q ∧ IsPrimePow v)) := by
  intro v hv v' hv' heq
  simp only [coe_filter, Set.mem_setOf_eq] at hv hv'
  obtain ⟨_, hd, hpp⟩ := hv
  obtain ⟨_, hd', hpp'⟩ := hv'
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff v).1 hpp
  obtain ⟨p', k', hp', hk', rfl⟩ := (isPrimePow_nat_iff v').1 hpp'
  obtain ⟨hlt, hdiv⟩ := div_gcd_of_prime_pow hp hq hd
  obtain ⟨hlt', hdiv'⟩ := div_gcd_of_prime_pow hp' hq hd'
  simp only at heq
  rw [hdiv, hdiv'] at heq
  have hpp' : p = p' := by
    have : p ∣ p' ^ (k' - q.factorization p') := by
      rw [← heq]; exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow this)
  subst hpp'
  have : k - q.factorization p = k' - q.factorization p :=
    Nat.pow_right_injective hp.two_le heq
  congr 1; omega

/-- [B, p. 72]: `∑_{v ≤ V} Λ(v) gcd(q,v)/v ≤ log q + log V` (with (2.12)). -/
theorem sum_vonMangoldt_gcd_le {q : ℕ} (hq : 1 ≤ q) {V : ℝ} (hV : 1 ≤ V) :
    ∑ v ∈ Icc 1 ⌊V⌋₊, (Λ v : ℝ) * Nat.gcd q v / v ≤ Real.log q + Real.log V := by
  have hq0 : q ≠ 0 := by omega
  set S := Icc 1 ⌊V⌋₊
  rw [sum_congr rfl fun v hv => vonMangoldt_gcd_term q v hq0 (by have := (mem_Icc.1 hv).1; omega),
    sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- `∑_{v | q} Λ(v) ≤ log q`.
    rw [← sum_filter, ← ArithmeticFunction.vonMangoldt_sum]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    intro v hv
    simp only [mem_filter] at hv
    exact Nat.mem_divisors.2 ⟨hv.2, hq0⟩
  · rw [← sum_filter, ← sum_image (f := fun w => (Λ w : ℝ) / w) (injOn_div_gcd q hq0 S)]
    refine le_trans ?_ (Prelim.sum_vonMangoldt_div_le_log hV)
    refine sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    intro w hw
    simp only [mem_image, mem_filter, S, mem_Icc] at hw
    obtain ⟨v, ⟨⟨hv1, hvV⟩, hd, hpp⟩, rfl⟩ := hw
    simp only [mem_Icc]
    have hg : 0 < Nat.gcd q v := Nat.gcd_pos_of_pos_left v (by omega)
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right q v)) hg
    · exact (Nat.div_le_self v _).trans hvV


/-- Sums over pairs `(v, u)`, `v ≤ V`, `u ≤ U`, regrouped by `a = vu`. -/
theorem sum_pairs_eq_sum_divisors {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ Icc 1 ⌊V⌋₊ ×ˢ Icc 1 ⌊U⌋₊, g p.1 p.2 = ∑ a ∈ Icc 1 (⌊V⌋₊ * ⌊U⌋₊),
      ∑ v ∈ a.divisors, (if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then g v (a / v) else 0) := by
  set NU := ⌊U⌋₊
  set NV := ⌊V⌋₊
  rw [← sum_fiberwise_of_maps_to (t := Icc 1 (NV * NU)) (g := fun p : ℕ × ℕ => p.1 * p.2)
    (fun p hp => by
      simp only [mem_product, mem_Icc] at hp ⊢
      exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul hp.1.2 hp.2.2⟩)]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_filter]
  refine sum_nbij' (fun p => p.1) (fun v => (v, a / v)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
    have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨p.2, h5.symm⟩, by
      intro ha; rw [ha] at h5; rcases Nat.mul_eq_zero.1 h5 with h | h <;> omega⟩,
      (Nat.le_floor_iff hV).1 h2, ?_⟩
    rw [hdiv]; exact (Nat.le_floor_iff hU).1 h4
  · intro v hv
    simp only [mem_filter, Nat.mem_divisors] at hv
    obtain ⟨⟨hva, ha0⟩, h1, h2⟩ := hv
    have hv1 : 1 ≤ v := Nat.pos_of_dvd_of_pos hva (Nat.pos_of_ne_zero ha0)
    have hav : v * (a / v) = a := Nat.mul_div_cancel' hva
    simp only [mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨hv1, Nat.le_floor h1⟩, ?_, Nat.le_floor h2⟩, hav⟩
    rcases Nat.eq_zero_or_pos (a / v) with h | h
    · rw [h, mul_zero] at hav; omega
    · exact h
  · intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
    have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
    ext <;> simp [hdiv]
  · intro v _; rfl
  · intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, _⟩, _⟩, h5⟩ := hp
    have hdiv : a / p.1 = p.2 := by rw [← h5]; exact Nat.mul_div_cancel_left _ (by omega)
    simp only [hdiv]

/-- `c(a) = 0` for `a > ⌊V⌋⌊U⌋`. -/
theorem coefI2_eq_zero_of_gt {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {a : ℕ}
    (ha : ⌊V⌋₊ * ⌊U⌋₊ < a) : coefI2 U V a = 0 := by
  refine sum_eq_zero fun v hv => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have hva : v ∣ a := (Nat.mem_divisors.1 hv).1
  have : v * (a / v) ≤ ⌊V⌋₊ * ⌊U⌋₊ := Nat.mul_le_mul (Nat.le_floor h1) (Nat.le_floor h2)
  rw [Nat.mul_div_cancel' hva] at this; omega

/-- `∑_{a ≤ N} [P a] c(a) f(a) = ∑_{v ≤ V, u ≤ U} [P(vu)] Λ(v) μ(u) f(vu)` for `N ≥ ⌊V⌋⌊U⌋`. -/
theorem sum_coefI2_eq {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → ℝ) {N : ℕ} (hN : ⌊V⌋₊ * ⌊U⌋₊ ≤ N) :
    ∑ a ∈ Icc 1 N, (if P a then coefI2 U V a * f a else 0) =
      ∑ p ∈ Icc 1 ⌊V⌋₊ ×ˢ Icc 1 ⌊U⌋₊,
        (if P (p.1 * p.2) then (Λ p.1 : ℝ) * (μ p.2 : ℝ) * f (p.1 * p.2) else 0) := by
  rw [sum_pairs_eq_sum_divisors hU hV (fun v u =>
    if P (v * u) then (Λ v : ℝ) * (μ u : ℝ) * f (v * u) else 0)]
  have hsub : Icc 1 (⌊V⌋₊ * ⌊U⌋₊) ⊆ Icc 1 N := Icc_subset_Icc le_rfl hN
  rw [← sum_subset hsub (fun a ha hna => by
    rw [coefI2_eq_zero_of_gt hU hV (by simp only [mem_Icc] at ha hna; omega)]; simp)]
  refine sum_congr rfl fun a _ => ?_
  rw [coefI2]
  split_ifs with hP
  · rw [sum_mul]
    refine sum_congr rfl fun v hv => ?_
    have hva : v * (a / v) = a := Nat.mul_div_cancel' (Nat.mem_divisors.1 hv).1
    rw [hva, if_pos hP]
    split_ifs <;> ring
  · refine (sum_eq_zero fun v hv => ?_).symm
    have hva : v * (a / v) = a := Nat.mul_div_cancel' (Nat.mem_divisors.1 hv).1
    rw [hva, if_neg hP]; split_ifs <;> rfl

end TernaryGoldbach.MinorArcs
