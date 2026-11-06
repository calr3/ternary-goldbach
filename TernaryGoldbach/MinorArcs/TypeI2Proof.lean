import TernaryGoldbach.MinorArcs.TypeILogProof
import TernaryGoldbach.Prelim.LambdaMu

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# Proof of [H, Lemma 4.2.4] (the Type I sum with `Λ(v) μ(u)`; `η = η₂`)
-/

open Real Finset
open ArithmeticFunction (moebius vonMangoldt)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- `c(a) = ∑_{v | a, v ≤ V, a/v ≤ U} Λ(v) μ(a/v)` [H, (4.53)]. -/
noncomputable def coefI2 (U V : ℝ) (a : ℕ) : ℝ :=
  ∑ v ∈ a.divisors, if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then (Λ v : ℝ) * (μ (a / v) : ℝ) else 0

/-- `|c(a)| ≤ log a` [H, p. 73]. -/
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

/-- [H, p. 72]: for `q'` odd, `|∑_{u ≤ R, u odd, q' | u} μ(u)/u| ≤ 1/q'` (by (2.20)). -/
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

/-- [H, p. 72]: `∑_{v ≤ V} Λ(v) gcd(q,v)/v ≤ log q + log V` (with (2.12)). -/
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


/-- `q | vu ⟺ q/gcd(q,v) | u`. -/
theorem dvd_mul_iff_div_gcd {q v u : ℕ} (hq : 0 < q) :
    q ∣ v * u ↔ q / Nat.gcd q v ∣ u := by
  have hg : 0 < Nat.gcd q v := Nat.gcd_pos_of_pos_left v hq
  set g := Nat.gcd q v with hgdef
  obtain ⟨q₁, hq₁⟩ := Nat.gcd_dvd_left q v
  obtain ⟨v₁, hv₁⟩ := Nat.gcd_dvd_right q v
  have hq1eq : q / g = q₁ := by
    have : q / g = g * q₁ / g := congrArg (· / g) hq₁
    rw [this, Nat.mul_div_cancel_left _ hg]
  have hv1eq : v / g = v₁ := by
    have : v / g = g * v₁ / g := congrArg (· / g) hv₁
    rw [this, Nat.mul_div_cancel_left _ hg]
  have hcop : Nat.Coprime q₁ v₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := q) (n := v) hg
    rwa [← hgdef, hq1eq, hv1eq] at this
  rw [hq1eq]
  have e : (q ∣ v * u) = (g * q₁ ∣ g * (v₁ * u)) := by
    rw [← mul_assoc, ← hq₁, ← hv₁]
  rw [e]
  constructor
  · intro h
    exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg h)
  · intro h
    exact Nat.mul_dvd_mul_left _ (Dvd.dvd.mul_left h _)

/-- **[H, p. 72]**: `|∑_{a ≤ M, a odd, q | a} c(a)/a| ≤ (log q + log V)/q` for `q` odd. -/
theorem abs_sum_coefI2_div_le {U V M : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : 0 ≤ M) {q : ℕ}
    (hq : Odd q) :
    |∑ a ∈ Icc 1 ⌊M⌋₊, (if Odd a ∧ q ∣ a then coefI2 U V a * (1 / a) else 0)| ≤
      (Real.log q + Real.log V) / q := by
  have hq1 : 1 ≤ q := hq.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set NV := ⌊V⌋₊
  set NU := ⌊U⌋₊
  set NM := ⌊M⌋₊
  set N := max NM (NV * NU)
  -- Extend the range to `N ≥ ⌊V⌋⌊U⌋`.
  have hext : ∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then coefI2 U V a * (1 / a) else 0) =
      ∑ a ∈ Icc 1 N, (if (Odd a ∧ q ∣ a) ∧ a ≤ NM then coefI2 U V a * (1 / a) else 0) := by
    rw [← sum_subset (Icc_subset_Icc le_rfl (le_max_left _ _) : Icc 1 NM ⊆ Icc 1 N)
      (fun a ha hna => by
        simp only [mem_Icc] at ha hna
        rw [if_neg (fun h => by omega)])]
    refine sum_congr rfl fun a ha => ?_
    have : a ≤ NM := (mem_Icc.1 ha).2
    by_cases h : Odd a ∧ q ∣ a
    · rw [if_pos h, if_pos ⟨h, this⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [hext, sum_coefI2_eq (by linarith) (by linarith) _ _ (le_max_right _ _), sum_product]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  -- Each `v`.
  have hv : ∀ v ∈ Icc 1 NV, |∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then
      (Λ v : ℝ) * (μ u : ℝ) * (1 / ((v * u : ℕ) : ℝ)) else 0)| ≤
      (Λ v : ℝ) * Nat.gcd q v / v * (1 / q) := by
    intro v hv
    have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
    have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := v)
    have hgpos : (0 : ℝ) < Nat.gcd q v := by exact_mod_cast Nat.gcd_pos_of_pos_left v (by omega)
    have hRHS : 0 ≤ (Λ v : ℝ) * Nat.gcd q v / v * (1 / q) := by positivity
    rcases Nat.even_or_odd v with hve | hvo
    · rw [sum_eq_zero fun u _ => by
        rw [if_neg]; rintro ⟨⟨ho, _⟩, _⟩
        exact (Nat.not_odd_iff_even.2 (hve.mul_right u)) ho]
      simpa using hRHS
    set q' := q / Nat.gcd q v
    have hq'odd : Odd q' := Odd.of_dvd_nat hq (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q v))
    have hq'eq : (q' : ℝ) = q / Nat.gcd q v := by
      simp only [q']; rw [Nat.cast_div (Nat.gcd_dvd_left q v) hgpos.ne']
    -- Rewrite the `u`-sum.
    have hrw : ∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then
        (Λ v : ℝ) * (μ u : ℝ) * (1 / ((v * u : ℕ) : ℝ)) else 0) =
        (Λ v : ℝ) / v * ∑ u ∈ Icc 1 (min NU (NM / v)),
          (if Odd u ∧ q' ∣ u then (μ u : ℝ) / u else 0) := by
      rw [mul_sum]
      rw [← sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _) : Icc 1 (min NU (NM / v)) ⊆ Icc 1 NU)
        (fun u hu hnu => by
          rw [if_neg]
          rintro ⟨_, hle⟩
          simp only [mem_Icc] at hu hnu
          have : u ≤ NM / v := (Nat.le_div_iff_mul_le hv1).2 (by rw [mul_comm]; exact hle)
          omega)]
      refine sum_congr rfl fun u hu => ?_
      have hule : u ≤ NM / v := (mem_Icc.1 hu).2.trans (min_le_right _ _)
      have hvu : v * u ≤ NM := by
        have := (Nat.le_div_iff_mul_le hv1).1 hule; rw [mul_comm]; exact this
      have hodd : Odd (v * u) ↔ Odd u := by
        rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hvo, h⟩⟩
      have hdvd := dvd_mul_iff_div_gcd (q := q) (v := v) (u := u) (by omega)
      by_cases h : Odd u ∧ q' ∣ u
      · rw [if_pos ⟨⟨hodd.2 h.1, hdvd.2 h.2⟩, hvu⟩, if_pos h]
        have hu0 : (0 : ℝ) < u := by exact_mod_cast (mem_Icc.1 hu).1
        push_cast; field_simp
      · rw [if_neg (fun h' => h ⟨hodd.1 h'.1.1, hdvd.1 h'.1.2⟩), if_neg h, mul_zero]
    rw [hrw, abs_mul, abs_of_nonneg (by positivity)]
    have hA := abs_sum_moebius_odd_dvd_le hq'odd ((min NU (NM / v) : ℕ) : ℝ) (Nat.cast_nonneg _)
    rw [Nat.floor_natCast] at hA
    calc (Λ v : ℝ) / v * |∑ u ∈ Icc 1 (min NU (NM / v)), (if Odd u ∧ q' ∣ u then (μ u : ℝ) / u else 0)|
        ≤ (Λ v : ℝ) / v * (1 / q') := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = _ := by rw [hq'eq]; field_simp
  refine (sum_le_sum hv).trans ?_
  rw [← sum_mul]
  have hC := sum_vonMangoldt_gcd_le hq1 hV
  calc (∑ v ∈ Icc 1 NV, (Λ v : ℝ) * Nat.gcd q v / v) * (1 / q)
      ≤ (Real.log q + Real.log V) * (1 / q) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

theorem geom_sum_le_three_halves {p : ℕ} (hp : 3 ≤ p) (L : ℕ) :
    ∑ α ∈ Icc 1 L, ((p : ℝ) ^ α) ≤ 3 / 2 * (p : ℝ) ^ L := by
  induction L with
  | zero => simp; norm_num
  | succ L ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have : (0 : ℝ) ≤ (p : ℝ) ^ L := by positivity
    rw [pow_succ]; nlinarith [ih]

/-- **Lemma D** (cf. [H, (4.55)]): `∑_{v ≤ V, (v, q) > 1} Λ(v) v ≤ (3/2) V log q` for `q` odd. -/
theorem sum_vonMangoldt_mul_not_coprime_le {q : ℕ} (hq : Odd q) {V : ℝ} (hV : 1 ≤ V) :
    ∑ v ∈ Icc 1 ⌊V⌋₊, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v else 0) ≤
      3 / 2 * V * Real.log q := by
  have hq0 : q ≠ 0 := by have := hq.pos; omega
  set NV := ⌊V⌋₊
  have hNV : (NV : ℝ) ≤ V := Nat.floor_le (by linarith)
  have hNV0 : NV ≠ 0 := by
    have : 1 ≤ NV := Nat.le_floor (by simpa using hV); omega
  -- Only prime powers contribute.
  have h1 : ∑ v ∈ Icc 1 NV, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v else 0) =
      ∑ v ∈ (Icc 1 NV).filter (fun v => ¬ Nat.Coprime q v ∧ IsPrimePow v), (Λ v : ℝ) * v := by
    rw [sum_filter]
    refine sum_congr rfl fun v _ => ?_
    by_cases hc : Nat.Coprime q v
    · rw [if_neg (fun h => h hc), if_neg (fun h => h.1 hc)]
    · rw [if_pos hc]
      by_cases hpp : IsPrimePow v
      · rw [if_pos ⟨hc, hpp⟩]
      · rw [if_neg (fun h => hpp h.2), (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hpp]; simp
  rw [h1]
  set S := (Icc 1 NV).filter (fun v => ¬ Nat.Coprime q v ∧ IsPrimePow v)
  -- Group by the prime `p = minFac v`, which divides `q`.
  have hmaps : ∀ v ∈ S, v.minFac ∈ q.primeFactors := by
    intro v hv
    simp only [S, mem_filter] at hv
    obtain ⟨_, hc, hpp⟩ := hv
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff v).1 hpp
    rw [hp.pow_minFac hk.ne']
    obtain ⟨r, hr, hrq, hrv⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    have : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrv)
    subst this
    exact Nat.mem_primeFactors.2 ⟨hr, hrq, hq0⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ p ∈ q.primeFactors, ∑ v ∈ S with v.minFac = p, (Λ v : ℝ) * v ≤
      3 / 2 * NV * Real.log p := by
    intro p hp
    obtain ⟨hpp, hpq, _⟩ := Nat.mem_primeFactors.1 hp
    have hp3 : 3 ≤ p := by
      rcases hpp.eq_two_or_odd' with h | h
      · exfalso; subst h; exact (Nat.not_even_iff_odd.2 hq) (even_iff_two_dvd.2 hpq)
      · have := hpp.two_le; rcases h with ⟨j, hj⟩; omega
    set L := Nat.log p NV
    have hsub : S.filter (fun v => v.minFac = p) ⊆ (Icc 1 L).image (fun α => p ^ α) := by
      intro v hv
      simp only [S, mem_filter, mem_Icc] at hv
      obtain ⟨⟨⟨hv1, hvN⟩, _, hppv⟩, hmin⟩ := hv
      obtain ⟨p', k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).1 hppv
      rw [hp'.pow_minFac hk.ne'] at hmin
      subst hmin
      simp only [mem_image, mem_Icc]
      exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hpp.one_lt hvN⟩, rfl⟩
    calc ∑ v ∈ S with v.minFac = p, (Λ v : ℝ) * v
        ≤ ∑ v ∈ (Icc 1 L).image (fun α => p ^ α), (Λ v : ℝ) * v :=
          sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
      _ = ∑ α ∈ Icc 1 L, Real.log p * (p : ℝ) ^ α := by
          rw [sum_image (fun a _ b _ h => Nat.pow_right_injective hpp.two_le h)]
          refine sum_congr rfl fun α hα => ?_
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := (mem_Icc.1 hα).1; omega),
            ArithmeticFunction.vonMangoldt_apply_prime hpp]
          push_cast; ring
      _ = Real.log p * ∑ α ∈ Icc 1 L, (p : ℝ) ^ α := by rw [mul_sum]
      _ ≤ Real.log p * (3 / 2 * (p : ℝ) ^ L) :=
          mul_le_mul_of_nonneg_left (geom_sum_le_three_halves hp3 L)
            (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
      _ ≤ Real.log p * (3 / 2 * NV) := by
          have h1 : ((p ^ L : ℕ) : ℝ) ≤ NV := by exact_mod_cast Nat.pow_log_le_self p hNV0
          push_cast at h1
          have h2 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
          gcongr
      _ = _ := by ring
  refine (sum_le_sum hfib).trans ?_
  rw [← mul_sum]
  have hlog : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
    rw [← Real.log_prod (fun p hp => by
      have := (Nat.mem_primeFactors.1 hp).1.pos; positivity)]
    apply Real.log_le_log (by
      apply prod_pos; intro p hp; have := (Nat.mem_primeFactors.1 hp).1.pos; positivity)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
    have h : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    push_cast at h; exact h
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.pos)
  calc 3 / 2 * (NV : ℝ) * ∑ p ∈ q.primeFactors, Real.log p ≤ 3 / 2 * (NV : ℝ) * Real.log q := by
        gcongr
    _ ≤ 3 / 2 * V * Real.log q := by gcongr


/-- [H, p. 73]: `∑_{u ≤ K, u odd, q | u} u ≤ K²/4q + 3K/4` for `q` odd. -/
theorem sum_odd_dvd_le {q : ℕ} (hq : Odd q) (K : ℕ) :
    ∑ u ∈ Icc 1 K, (if Odd u ∧ q ∣ u then (u : ℝ) else 0) ≤ (K : ℝ) ^ 2 / (4 * q) + 3 * K / 4 := by
  have hq1 : 1 ≤ q := hq.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h := sum_dvd_reindex hq1 (K : ℝ) (Nat.cast_nonneg _) (fun u => (u : ℝ))
  rw [Nat.floor_natCast] at h
  rw [h]
  set N := ⌊(K : ℝ) / q⌋₊
  have hN : (N : ℝ) ≤ K / q := Nat.floor_le (by positivity)
  have hodd : ∀ w, Odd (q * w) ↔ Odd w := fun w => by
    rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  have e : ∑ w ∈ Icc 1 N, (if Odd (q * w) then ((q * w : ℕ) : ℝ) else 0) =
      q * ∑ w ∈ Icc 1 N, (if Odd w then (w : ℝ) else 0) := by
    rw [mul_sum]; refine sum_congr rfl fun w _ => ?_
    by_cases ho : Odd w
    · rw [if_pos ((hodd w).2 ho), if_pos ho]; push_cast; ring
    · rw [if_neg (fun h => ho ((hodd w).1 h)), if_neg ho, mul_zero]
  rw [e]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0]; simp; positivity
  have hqK : (q : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    rw [le_div_iff₀ hq0] at hN; nlinarith
  calc (q : ℝ) * ∑ w ∈ Icc 1 N, (if Odd w then (w : ℝ) else 0)
      ≤ q * (((N : ℝ) + 1) ^ 2 / 4) := mul_le_mul_of_nonneg_left (sum_odd_le N) hq0.le
    _ ≤ q * ((K / q + 1) ^ 2 / 4) := by gcongr
    _ = (K : ℝ) ^ 2 / (4 * q) + K / 2 + q / 4 := by field_simp; ring
    _ ≤ _ := by linarith

/-- **[H, (4.54)–(4.55)]** (with `3/2` in the last term, see `sum_vonMangoldt_mul_not_coprime_le`):
`∑_{a ≤ M, a odd, q | a} |c(a)| a ≤ M² log V/4q + (3c₄/4) MV + (3/2)(U+1)² V log q/4`. -/
theorem sum_abs_coefI2_mul_le {U V M : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : 0 ≤ M) {q : ℕ}
    (hq : Odd q) :
    ∑ a ∈ Icc 1 ⌊M⌋₊, (if Odd a ∧ q ∣ a then |coefI2 U V a| * a else 0) ≤
      M ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * M * V +
        3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4 := by
  have hq1 : 1 ≤ q := hq.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set NV := ⌊V⌋₊
  set NU := ⌊U⌋₊
  set NM := ⌊M⌋₊
  set N := max NM (NV * NU)
  have hNM : (NM : ℝ) ≤ M := Nat.floor_le hM
  have hNU : (NU : ℝ) ≤ U := Nat.floor_le (by linarith)
  -- Step 1: `|c(a)| ≤ ∑_{v | a, …} Λ(v)`, extend the range, and regroup.
  set c0 : ℕ → ℝ := fun a => ∑ v ∈ a.divisors,
    (if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then (Λ v : ℝ) else 0)
  have hc0 : ∀ a, |coefI2 U V a| ≤ c0 a := by
    intro a
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
    split_ifs
    · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have : |(μ (a / v) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := v), abs_nonneg ((μ (a / v) : ℝ))]
    · simp
  have hz : ∀ a, NV * NU < a → c0 a = 0 := by
    intro a ha
    refine sum_eq_zero fun v hv => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hva : v ∣ a := (Nat.mem_divisors.1 hv).1
    have : v * (a / v) ≤ NV * NU := Nat.mul_le_mul (Nat.le_floor h1) (Nat.le_floor h2)
    rw [Nat.mul_div_cancel' hva] at this; omega
  have h1 : ∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then |coefI2 U V a| * a else 0) ≤
      ∑ p ∈ Icc 1 NV ×ˢ Icc 1 NU, (if (Odd (p.1 * p.2) ∧ q ∣ p.1 * p.2) ∧ p.1 * p.2 ≤ NM then
        (Λ p.1 : ℝ) * ((p.1 * p.2 : ℕ) : ℝ) else 0) := by
    calc ∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then |coefI2 U V a| * a else 0)
        ≤ ∑ a ∈ Icc 1 NM, (if (Odd a ∧ q ∣ a) ∧ a ≤ NM then c0 a * a else 0) :=
          sum_le_sum fun a ha => by
            have : a ≤ NM := (mem_Icc.1 ha).2
            by_cases h : Odd a ∧ q ∣ a
            · rw [if_pos h, if_pos ⟨h, this⟩]
              exact mul_le_mul_of_nonneg_right (hc0 a) (Nat.cast_nonneg _)
            · rw [if_neg h, if_neg (fun h' => h h'.1)]
      _ = ∑ a ∈ Icc 1 N, (if (Odd a ∧ q ∣ a) ∧ a ≤ NM then c0 a * a else 0) :=
          sum_subset (Icc_subset_Icc le_rfl (le_max_left _ _)) (fun a ha hna => by
            simp only [mem_Icc] at ha hna; rw [if_neg (fun h => by omega)])
      _ = ∑ a ∈ Icc 1 (NV * NU), (if (Odd a ∧ q ∣ a) ∧ a ≤ NM then c0 a * a else 0) :=
          (sum_subset (Icc_subset_Icc le_rfl (le_max_right _ _)) (fun a ha hna => by
            simp only [mem_Icc] at ha hna
            split_ifs
            · rw [hz a (by omega), zero_mul]
            · rfl)).symm
      _ = ∑ a ∈ Icc 1 (NV * NU), ∑ v ∈ a.divisors,
            (if (v : ℝ) ≤ V ∧ ((a / v : ℕ) : ℝ) ≤ U then
              (if (Odd (v * (a / v)) ∧ q ∣ v * (a / v)) ∧ v * (a / v) ≤ NM then
                (Λ v : ℝ) * ((v * (a / v) : ℕ) : ℝ) else 0) else 0) := by
          refine sum_congr rfl fun a _ => ?_
          simp only [c0]
          split_ifs with h
          · rw [sum_mul]
            refine sum_congr rfl fun v hv => ?_
            have hva : v * (a / v) = a := Nat.mul_div_cancel' (Nat.mem_divisors.1 hv).1
            rw [hva, if_pos h]
            split_ifs <;> simp
          · refine (sum_eq_zero fun v hv => ?_).symm
            have hva : v * (a / v) = a := Nat.mul_div_cancel' (Nat.mem_divisors.1 hv).1
            rw [hva, if_neg h]; split_ifs <;> rfl
      _ = _ := (sum_pairs_eq_sum_divisors (by linarith) (by linarith) (fun v u =>
            if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then
              (Λ v : ℝ) * ((v * u : ℕ) : ℝ) else 0)).symm
  refine h1.trans ?_
  rw [sum_product]
  -- Per `v`.
  have hv : ∀ v ∈ Icc 1 NV, ∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then
      (Λ v : ℝ) * ((v * u : ℕ) : ℝ) else 0) ≤
      (if Nat.Coprime q v then (Λ v : ℝ) / v * (M ^ 2 / (4 * q)) + (Λ v : ℝ) * (3 * M / 4) else 0) +
      (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v * ((U + 1) ^ 2 / 4) else 0) := by
    intro v hv
    have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
    have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := v)
    have hRHS : 0 ≤ (if Nat.Coprime q v then (Λ v : ℝ) / v * (M ^ 2 / (4 * q)) +
        (Λ v : ℝ) * (3 * M / 4) else 0) +
        (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v * ((U + 1) ^ 2 / 4) else 0) := by
      have : 0 ≤ (U + 1) ^ 2 / 4 := by positivity
      split_ifs <;> positivity
    rcases Nat.even_or_odd v with hve | hvo
    · rw [sum_eq_zero fun u _ => by
        rw [if_neg]; rintro ⟨⟨ho, _⟩, _⟩
        exact (Nat.not_odd_iff_even.2 (hve.mul_right u)) ho]
      exact hRHS
    have hfac : ∀ u, (Λ v : ℝ) * ((v * u : ℕ) : ℝ) = (Λ v : ℝ) * v * u := fun u => by
      push_cast; ring
    simp_rw [hfac]
    have hfac2 : ∀ u, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then (Λ v : ℝ) * v * u else 0) =
        (Λ v : ℝ) * v * (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then (u : ℝ) else 0) :=
      fun u => by split_ifs <;> simp
    rw [sum_congr rfl fun u _ => hfac2 u, ← mul_sum]
    by_cases hc : Nat.Coprime q v
    · rw [if_pos hc, if_neg (fun h => h hc), add_zero]
      have hrw : ∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then (u : ℝ) else 0) =
          ∑ u ∈ Icc 1 (min NU (NM / v)), (if Odd u ∧ q ∣ u then (u : ℝ) else 0) := by
        rw [← sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _) :
            Icc 1 (min NU (NM / v)) ⊆ Icc 1 NU)
          (fun u hu hnu => by
            rw [if_neg]
            rintro ⟨_, hle⟩
            simp only [mem_Icc] at hu hnu
            have : u ≤ NM / v := (Nat.le_div_iff_mul_le hv1).2 (by rw [mul_comm]; exact hle)
            omega)]
        refine sum_congr rfl fun u hu => ?_
        have hule : u ≤ NM / v := (mem_Icc.1 hu).2.trans (min_le_right _ _)
        have hvu : v * u ≤ NM := by
          have := (Nat.le_div_iff_mul_le hv1).1 hule; rw [mul_comm]; exact this
        have hodd : Odd (v * u) ↔ Odd u := by
          rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hvo, h⟩⟩
        have hdvd : q ∣ v * u ↔ q ∣ u := hc.dvd_mul_left
        by_cases h : Odd u ∧ q ∣ u
        · rw [if_pos ⟨⟨hodd.2 h.1, hdvd.2 h.2⟩, hvu⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨hodd.1 h'.1.1, hdvd.1 h'.1.2⟩), if_neg h]
      rw [hrw]
      have hE := sum_odd_dvd_le hq (min NU (NM / v))
      have hK : ((min NU (NM / v) : ℕ) : ℝ) ≤ M / v := by
        have : ((NM / v : ℕ) : ℝ) ≤ (NM : ℝ) / v := Nat.cast_div_le
        have h2 : ((min NU (NM / v) : ℕ) : ℝ) ≤ ((NM / v : ℕ) : ℝ) := by
          exact_mod_cast min_le_right _ _
        calc ((min NU (NM / v) : ℕ) : ℝ) ≤ (NM : ℝ) / v := h2.trans this
          _ ≤ M / v := div_le_div_of_nonneg_right hNM hv0.le
      have hK0 : (0 : ℝ) ≤ ((min NU (NM / v) : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (Λ v : ℝ) * v * ∑ u ∈ Icc 1 (min NU (NM / v)), (if Odd u ∧ q ∣ u then (u : ℝ) else 0)
          ≤ (Λ v : ℝ) * v * (((min NU (NM / v) : ℕ) : ℝ) ^ 2 / (4 * q) +
              3 * ((min NU (NM / v) : ℕ) : ℝ) / 4) := by gcongr
        _ ≤ (Λ v : ℝ) * v * ((M / v) ^ 2 / (4 * q) + 3 * (M / v) / 4) := by gcongr
        _ = _ := by field_simp
    · rw [if_neg hc, if_pos hc, zero_add]
      have hle : ∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then (u : ℝ) else 0) ≤
          ∑ u ∈ Icc 1 NU, (if Odd u then (u : ℝ) else 0) := sum_le_sum fun u _ => by
        have hodd : Odd (v * u) ↔ Odd u := by
          rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hvo, h⟩⟩
        split_ifs with h1 h2 <;> first | exact le_rfl | exact absurd (hodd.1 h1.1.1) h2 |
          exact Nat.cast_nonneg _
      have h2 := sum_odd_le NU
      calc (Λ v : ℝ) * v * ∑ u ∈ Icc 1 NU, (if (Odd (v * u) ∧ q ∣ v * u) ∧ v * u ≤ NM then (u : ℝ) else 0)
          ≤ (Λ v : ℝ) * v * (((NU : ℝ) + 1) ^ 2 / 4) := by gcongr; exact hle.trans h2
        _ ≤ _ := by gcongr
  refine (sum_le_sum hv).trans ?_
  rw [sum_add_distrib]
  -- The coprime part.
  have hA : ∑ v ∈ Icc 1 NV, (if Nat.Coprime q v then (Λ v : ℝ) / v * (M ^ 2 / (4 * q)) +
      (Λ v : ℝ) * (3 * M / 4) else 0) ≤ M ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * M * V := by
    have h2 : ∑ v ∈ Icc 1 NV, (if Nat.Coprime q v then (Λ v : ℝ) / v * (M ^ 2 / (4 * q)) +
        (Λ v : ℝ) * (3 * M / 4) else 0) ≤
        (∑ v ∈ Icc 1 NV, (Λ v : ℝ) / v) * (M ^ 2 / (4 * q)) +
          (∑ v ∈ Icc 1 NV, (Λ v : ℝ)) * (3 * M / 4) := by
      rw [sum_mul, sum_mul, ← sum_add_distrib]
      refine sum_le_sum fun v _ => ?_
      split_ifs
      · exact le_rfl
      · have := ArithmeticFunction.vonMangoldt_nonneg (n := v)
        positivity
    refine h2.trans ?_
    have h12 := Prelim.sum_vonMangoldt_div_le_log hV
    have h15 := Prelim.sum_vonMangoldt_lt (show 0 < V by linarith)
    have hc4 : (1.03883 : ℝ) ≤ c₄ := by unfold c₄; norm_num
    have : (∑ v ∈ Icc 1 NV, (Λ v : ℝ)) * (3 * M / 4) ≤ 3 * c₄ / 4 * M * V := by
      have : (∑ v ∈ Icc 1 NV, (Λ v : ℝ)) ≤ c₄ * V := by
        have : 1.03883 * V ≤ c₄ * V := mul_le_mul_of_nonneg_right hc4 (by linarith)
        linarith
      calc (∑ v ∈ Icc 1 NV, (Λ v : ℝ)) * (3 * M / 4) ≤ (c₄ * V) * (3 * M / 4) := by gcongr
        _ = _ := by ring
    have h3 : (∑ v ∈ Icc 1 NV, (Λ v : ℝ) / v) * (M ^ 2 / (4 * q)) ≤
        Real.log V * (M ^ 2 / (4 * q)) := by gcongr
    have : Real.log V * (M ^ 2 / (4 * q)) = M ^ 2 * Real.log V / (4 * q) := by ring
    linarith
  -- The non-coprime part.
  have hB : ∑ v ∈ Icc 1 NV, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v * ((U + 1) ^ 2 / 4) else 0) ≤
      3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4 := by
    have hD := sum_vonMangoldt_mul_not_coprime_le hq hV
    have e : ∑ v ∈ Icc 1 NV, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v * ((U + 1) ^ 2 / 4) else 0) =
        (∑ v ∈ Icc 1 NV, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v else 0)) * ((U + 1) ^ 2 / 4) := by
      rw [sum_mul]; refine sum_congr rfl fun v _ => ?_; split_ifs <;> ring
    rw [e]
    calc (∑ v ∈ Icc 1 NV, (if ¬ Nat.Coprime q v then (Λ v : ℝ) * v else 0)) * ((U + 1) ^ 2 / 4)
        ≤ (3 / 2 * V * Real.log q) * ((U + 1) ^ 2 / 4) := by gcongr
      _ = _ := by ring
  linarith


/-- The main part of `typeI2`: `∑_{a ≤ M, a odd, q | a} c(a) T_{a,∘}(α)`. -/
noncomputable def mainPartI2 (α x M U V : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ Icc 1 ⌊M⌋₊, if Odd a ∧ q ∣ a then (coefI2 U V a : ℂ) * Todd α x a else 0

set_option maxHeartbeats 1000000 in
/-- **[H, (4.50)]** (with the factor `3/2`, see `bound_4_50`): the terms with `q | a ≤ M`. -/
theorem norm_mainPartI2_le {α x δ M U V : ℝ} {a₀ k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (h2α : 2 * α = a₀ / q + δ / x + k) (hU : 1 ≤ U) (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hMδ : |δ| * M ≤ x / 2) (hMD : M ≤ U * V) :
    ‖mainPartI2 α x M U V q‖ ≤ bound_4_50 x δ q U V := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c₀_pos
  have hpi4 : (0 : ℝ) ≤ 1 / 4 - 1 / π ^ 2 := by
    have := Real.pi_gt_three
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hc4 : (0 : ℝ) < c₄ := by unfold c₄; norm_num
  have hRHS : 0 ≤ bound_4_50 x δ q U V := by
    unfold bound_4_50; simp only []
    have := minInv_nonneg c₀ (π * δ) hc0.le
    have : 0 ≤ Real.log (V * q) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hV (by exact_mod_cast hq))
    positivity
  rcases Nat.even_or_odd q with hqe | hqo
  · have : mainPartI2 α x M U V q = 0 := by
      refine sum_eq_zero fun a _ => ?_
      rw [if_neg]; rintro ⟨ho, hd⟩
      exact (Nat.not_even_iff_odd.2 ho) ((even_iff_two_dvd.2 (even_iff_two_dvd.1 hqe)).trans_dvd hd |>
        fun h => h)
    rw [this, norm_zero]; exact hRHS
  set NM := ⌊M⌋₊
  have hNM : (NM : ℝ) ≤ M := Nat.floor_le hM0
  -- Per-term data from `Todd_main`.
  have hT : ∀ a : ℕ, ∃ E : ℂ, Odd a → q ∣ a → 1 ≤ a → a ≤ NM →
      Todd α x a = e ((a₀ + k * q) / 2) * ((x / (2 * a) : ℝ) * eta2hat (-(δ / 2)) + E) ∧
      ‖E‖ ≤ a / x * (c₀ / (2 * π ^ 2)) * (π ^ 2 - 4) := by
    intro a
    by_cases h : Odd a ∧ q ∣ a ∧ 1 ≤ a ∧ a ≤ NM
    · obtain ⟨ho, ⟨m', rfl⟩, h1, hle⟩ := h
      have hm'o : Odd m' := (Nat.odd_mul.1 ho).2
      have hr : |δ * (q * m' : ℕ) / x| ≤ 1 / 2 := by
        have hqm : ((q * m' : ℕ) : ℝ) ≤ M := (by exact_mod_cast hle : ((q * m' : ℕ) : ℝ) ≤ NM).trans hNM
        rw [abs_div, abs_mul, abs_of_pos hx, Nat.abs_cast, div_le_iff₀ hx]
        nlinarith [abs_nonneg δ]
      obtain ⟨E, hE1, hE2⟩ := Todd_main hx hq hm'o h2α hr
      exact ⟨E, fun _ _ _ _ => ⟨hE1, hE2⟩⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose E hE using hT
  set κ := e ((a₀ + k * q) / 2)
  set η0 := eta2hat (-(δ / 2))
  have hsplit : mainPartI2 α x M U V q = κ * (((x / 2 : ℝ) : ℂ) * η0 *
        ((∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then coefI2 U V a * (1 / a) else 0) : ℝ) : ℂ) +
      ∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then (coefI2 U V a : ℂ) * E a else 0)) := by
    rw [mainPartI2, Complex.ofReal_sum, mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
    have haN : a ≤ NM := (mem_Icc.1 ha).2
    by_cases h : Odd a ∧ q ∣ a
    · rw [if_pos h, if_pos h, if_pos h, (hE a h.1 h.2 ha1 haN).1]
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
      push_cast; field_simp
    · rw [if_neg h, if_neg h, if_neg h]; simp
  rw [hsplit, norm_mul, norm_e, one_mul]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖((x / 2 : ℝ) : ℂ) * η0 *
      ((∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then coefI2 U V a * (1 / a) else 0) : ℝ) : ℂ)‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) * Real.log (V * q) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hS := abs_sum_coefI2_div_le hU hV hM0 hqo
    have hη := norm_eta2hat_le_minInv δ
    have := minInv_nonneg c₀ (π * δ) hc0.le
    rw [Real.log_mul (by linarith) hq0.ne']
    calc x / 2 * ‖η0‖ * |∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then coefI2 U V a * (1 / a) else 0)|
        ≤ x / 2 * minInv c₀ (π * δ) * ((Real.log q + Real.log V) / q) := by gcongr
      _ = _ := by field_simp; ring
  have h2 : ‖∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then (coefI2 U V a : ℂ) * E a else 0)‖ ≤
      c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) *
        (M ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * M * V + 3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ a ∈ Icc 1 NM, ‖(if Odd a ∧ q ∣ a then (coefI2 U V a : ℂ) * E a else 0)‖ ≤
        c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) * (if Odd a ∧ q ∣ a then |coefI2 U V a| * a else 0) := by
      intro a ha
      by_cases h : Odd a ∧ q ∣ a
      · rw [if_pos h, if_pos h, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hE2 := (hE a h.1 h.2 (mem_Icc.1 ha).1 (mem_Icc.1 ha).2).2
        calc |coefI2 U V a| * ‖E a‖ ≤ |coefI2 U V a| * (a / x * (c₀ / (2 * π ^ 2)) * (π ^ 2 - 4)) :=
              mul_le_mul_of_nonneg_left hE2 (abs_nonneg _)
          _ = _ := by field_simp
      · rw [if_neg h, if_neg h, norm_zero, mul_zero]
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hpi2 : (0 : ℝ) ≤ π ^ 2 - 4 := by have := Real.pi_gt_three; nlinarith
    exact mul_le_mul_of_nonneg_left (sum_abs_coefI2_mul_le hU hV hM0 hqo) (by positivity)
  refine (add_le_add h1 h2).trans ?_
  unfold bound_4_50; simp only []
  have hD : M ^ 2 ≤ (U * V) ^ 2 := by gcongr
  have hMV : M * V ≤ U * V * V := by gcongr
  have e : c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) = 2 * (1 / 4 - 1 / π ^ 2) * c₀ / x := by
    field_simp; ring
  rw [e]
  have hk : 0 ≤ 2 * (1 / 4 - 1 / π ^ 2) * c₀ / x := by positivity
  have hstep : 2 * (1 / 4 - 1 / π ^ 2) * c₀ / x *
      (M ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * M * V + 3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4) ≤
      2 * (1 / 4 - 1 / π ^ 2) * c₀ / x *
      ((U * V) ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * (U * V * V) + 3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have h3 : 3 * c₄ / 4 * M * V ≤ 3 * c₄ / 4 * (U * V * V) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hMV (by positivity)
    have h4 : M ^ 2 * Real.log V / (4 * q) ≤ (U * V) ^ 2 * Real.log V / (4 * q) := by gcongr
    linarith
  have e2 : 2 * (1 / 4 - 1 / π ^ 2) * c₀ / x *
      ((U * V) ^ 2 * Real.log V / (4 * q) + 3 * c₄ / 4 * (U * V * V) + 3 / 2 * (U + 1) ^ 2 * V * Real.log q / 4) =
      (1 / 4 - 1 / π ^ 2) * c₀ * ((U * V) ^ 2 * Real.log V / (2 * q * x) + 3 * c₄ / 2 * (U * V ^ 2 / x) +
        3 / 2 * ((U + 1) ^ 2 * V / (2 * x) * Real.log q)) := by
    field_simp; ring
  linarith


/-- The terms of `typeI2` not in `mainPartI2`. -/
noncomputable def restPartI2 (α x M U V : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ Icc 1 (⌊V⌋₊ * ⌊U⌋₊), if Odd a ∧ ¬ (q ∣ a ∧ (a : ℝ) ≤ M) then
    (coefI2 U V a : ℂ) * Todd α x a else 0

theorem typeI2_eq_main_add_rest {α x M U V : ℝ} {q : ℕ} (hx : 0 < x) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hM0 : 0 ≤ M) : typeI2 α x U V = mainPartI2 α x M U V q + restPartI2 α x M U V q := by
  set NV := ⌊V⌋₊
  set NU := ⌊U⌋₊
  set NM := ⌊M⌋₊
  have hz : ∀ a, NV * NU < a → coefI2 U V a = 0 := fun a ha => coefI2_eq_zero_of_gt hU hV ha
  rw [typeI2_eq hx hU hV, restPartI2, mainPartI2]
  have hsplit : ∀ a ∈ Icc 1 (NV * NU), (if Odd a then (coefI2 U V a : ℂ) * Todd α x a else 0) =
      (if Odd a ∧ (q ∣ a ∧ (a : ℝ) ≤ M) then (coefI2 U V a : ℂ) * Todd α x a else 0) +
      (if Odd a ∧ ¬ (q ∣ a ∧ (a : ℝ) ≤ M) then (coefI2 U V a : ℂ) * Todd α x a else 0) := by
    intro a _
    by_cases h1 : Odd a <;> by_cases h2 : (q ∣ a ∧ (a : ℝ) ≤ M) <;> simp [h1, h2]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  congr 1
  -- Both main sums equal the sum over `a ≤ max(NM, NV NU)`.
  set N := max NM (NV * NU)
  have hA : ∑ a ∈ Icc 1 (NV * NU), (if Odd a ∧ (q ∣ a ∧ (a : ℝ) ≤ M) then
      (coefI2 U V a : ℂ) * Todd α x a else 0) =
      ∑ a ∈ Icc 1 N, (if Odd a ∧ (q ∣ a ∧ (a : ℝ) ≤ M) then (coefI2 U V a : ℂ) * Todd α x a else 0) :=
    sum_subset (Icc_subset_Icc le_rfl (le_max_right _ _)) (fun a ha hna => by
      simp only [mem_Icc] at ha hna
      split_ifs
      · rw [hz a (by omega)]; simp
      · rfl)
  have hB : ∑ a ∈ Icc 1 NM, (if Odd a ∧ q ∣ a then (coefI2 U V a : ℂ) * Todd α x a else 0) =
      ∑ a ∈ Icc 1 N, (if Odd a ∧ (q ∣ a ∧ (a : ℝ) ≤ M) then (coefI2 U V a : ℂ) * Todd α x a else 0) := by
    rw [← sum_subset (Icc_subset_Icc le_rfl (le_max_left _ _) : Icc 1 NM ⊆ Icc 1 N) (fun a ha hna => by
      simp only [mem_Icc] at ha hna
      rw [if_neg]
      rintro ⟨_, _, hle⟩
      have : a ≤ NM := Nat.le_floor hle
      omega)]
    refine sum_congr rfl fun a ha => ?_
    have hle : (a : ℝ) ≤ M := (Nat.cast_le.2 (mem_Icc.1 ha).2).trans (Nat.floor_le hM0)
    by_cases h : Odd a ∧ q ∣ a
    · rw [if_pos h, if_pos ⟨h.1, h.2, hle⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
  rw [hA, hB]

end TernaryGoldbach.MinorArcs
