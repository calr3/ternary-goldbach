import TernaryGoldbach.Prelim.RamareBound

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# The main term of `G_d(R)`

* `∑_a |h_d(a)| a^{1/3} ≤ 11 f₁(d)` (summability), and `E(R) = ∑_a h_d(a) Fo(R/a)` has
  `|E(R)| ≤ 0.64 · 11 f₁(d) R^{−1/3}`;
* `G_d(R) = (½ log R + C_γ) ∑_a h_d(a) − ½ ∑_a h_d(a) log a + E(R)` (`GqP_decomp`);
* `∑_a h_d(a) = 2φ(d)/d` (`tsum_hD`, Euler product).
-/

open Finset Real ArithmeticFunction

namespace TernaryGoldbach.Prelim.RamPf

open TernaryGoldbach.Prelim (f1pP f1qP GqP SqP)

/-! ### Summability -/

theorem wD_zero (d : ℕ) : wD d 0 = 0 := by simp [wD]

theorem summable_wD {d : ℕ} (hd : 1 ≤ d) : Summable (wD d) := by
  refine summable_of_sum_range_le (wD_nonneg d) (c := 11 * f1qP d) fun n => ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp only [range_zero, sum_empty]
    have := sum_wD_le hd 0; simpa using this
  · have e : range n = insert 0 (Icc 1 (n - 1)) := by
      ext a; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [e, sum_insert (by simp), wD_zero, zero_add]
    exact sum_wD_le hd (n - 1)

theorem tsum_wD_le {d : ℕ} (hd : 1 ≤ d) : ∑' a, wD d a ≤ 11 * f1qP d := by
  refine Real.tsum_le_of_sum_range_le (wD_nonneg d) fun n => ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp only [range_zero, sum_empty]
    have := sum_wD_le hd 0; simpa using this
  · have e : range n = insert 0 (Icc 1 (n - 1)) := by
      ext a; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [e, sum_insert (by simp), wD_zero, zero_add]
    exact sum_wD_le hd (n - 1)

theorem hD_zero (d : ℕ) : hD d 0 = 0 := by simp

theorem abs_hD_le_wD (d a : ℕ) : |hD d a| ≤ wD d a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp [wD]
  · have : (1 : ℝ) ≤ (a : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by exact_mod_cast h) (by norm_num)
    unfold wD; nlinarith [abs_nonneg (hD d a)]

theorem log_le_three_rpow {a : ℕ} (ha : 1 ≤ a) : Real.log a ≤ 3 * (a : ℝ) ^ ((1 : ℝ) / 3) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hr : 0 < (a : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ha0 _
  have e : Real.log a = 3 * Real.log ((a : ℝ) ^ ((1 : ℝ) / 3)) := by
    rw [Real.log_rpow ha0]; ring
  have := Real.log_le_sub_one_of_pos hr
  rw [e]; linarith

theorem abs_hD_log_le (d a : ℕ) : |hD d a| * Real.log a ≤ 3 * wD d a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp [wD]
  · have := log_le_three_rpow h
    unfold wD
    nlinarith [abs_nonneg (hD d a)]

theorem summable_hD {d : ℕ} (hd : 1 ≤ d) : Summable (hD d) :=
  Summable.of_norm_bounded (summable_wD hd) fun a => by
    rw [Real.norm_eq_abs]; exact abs_hD_le_wD d a

theorem summable_abs_hD {d : ℕ} (hd : 1 ≤ d) : Summable fun a => |hD d a| :=
  Summable.of_nonneg_of_le (fun a => abs_nonneg _) (abs_hD_le_wD d) (summable_wD hd)

theorem summable_hD_log {d : ℕ} (hd : 1 ≤ d) : Summable fun a => hD d a * Real.log a :=
  Summable.of_norm_bounded ((summable_wD hd).mul_left 3) fun a => by
    rw [Real.norm_eq_abs, abs_mul]
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp [wD]
    · rw [abs_of_nonneg (Real.log_natCast_nonneg a)]; exact abs_hD_log_le d a

/-! ### The error series `E(R) = ∑_a h_d(a) Fo(R/a)` -/

theorem abs_hD_Fo_le {d a : ℕ} {R : ℝ} (hR : 0 < R) :
    |hD d a * Fo (R / a)| ≤ 0.64 * R ^ (-(1 / 3 : ℝ)) * wD d a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp [wD]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast h
  have hx : 0 < R / a := div_pos hR ha0
  have hF := Fo_bound hx
  have hr : 0 < (R / a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  have hFo : |Fo (R / a)| ≤ 0.64 / (R / a) ^ ((1 : ℝ) / 3) := by rw [le_div_iff₀ hr]; exact hF
  have e : 0.64 / (R / a) ^ ((1 : ℝ) / 3) = 0.64 * R ^ (-(1 / 3 : ℝ)) * (a : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow hR.le ha0.le, Real.rpow_neg hR.le]
    have : 0 < R ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hR _
    have : 0 < (a : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ha0 _
    field_simp
  rw [abs_mul, wD]
  calc |hD d a| * |Fo (R / a)| ≤ |hD d a| * (0.64 * R ^ (-(1 / 3 : ℝ)) * (a : ℝ) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (hFo.trans (le_of_eq e)) (abs_nonneg _)
    _ = _ := by ring

theorem summable_E {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    Summable fun a => hD d a * Fo (R / a) :=
  Summable.of_norm_bounded ((summable_wD hd).mul_left (0.64 * R ^ (-(1 / 3 : ℝ)))) fun a => by
    rw [Real.norm_eq_abs]; exact abs_hD_Fo_le hR

theorem abs_E_le {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    |∑' a, hD d a * Fo (R / a)| ≤ 7.04 * R ^ (-(1 / 3 : ℝ)) * f1qP d := by
  have h1 : |∑' a, hD d a * Fo (R / a)| ≤ ∑' a, 0.64 * R ^ (-(1 / 3 : ℝ)) * wD d a := by
    have hn := norm_tsum_le_tsum_norm (summable_E hd hR).norm
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (Summable.tsum_le_tsum (fun a => abs_hD_Fo_le hR) (summable_E hd hR).abs
        ((summable_wD hd).mul_left _))
  rw [tsum_mul_left] at h1
  have h2 := tsum_wD_le hd
  have h3 : 0 ≤ R ^ (-(1 / 3 : ℝ)) := by positivity
  nlinarith

/-! ### The decomposition of `G_d(R)` -/

theorem V_eq_zero {x : ℝ} (hx : x < 1) : V x = 0 := by
  rw [V, Nat.floor_eq_zero.2 hx]; simp

theorem summable_T {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    Summable fun a => hD d a * (Real.log (R / a) / 2 + Cg) := by
  have h1 := summable_hD hd
  have h2 := summable_hD_log hd
  have e : (fun a : ℕ => hD d a * (Real.log (R / a) / 2 + Cg)) =
      fun a => (Real.log R / 2 + Cg) * hD d a - (1 / 2) * (hD d a * Real.log a) := by
    funext a
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · have ha : (a : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      rw [Real.log_div hR.ne' ha]; ring
  rw [e]
  exact (h1.mul_left _).sub (h2.mul_left _)

theorem tsum_T {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∑' a, hD d a * (Real.log (R / a) / 2 + Cg) =
      (Real.log R / 2 + Cg) * ∑' a, hD d a - (1 / 2) * ∑' a, hD d a * Real.log a := by
  have e : (fun a : ℕ => hD d a * (Real.log (R / a) / 2 + Cg)) =
      fun a => (Real.log R / 2 + Cg) * hD d a - (1 / 2) * (hD d a * Real.log a) := by
    funext a
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · have ha : (a : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      rw [Real.log_div hR.ne' ha]; ring
  rw [e, Summable.tsum_sub ((summable_hD hd).mul_left _) ((summable_hD_log hd).mul_left _),
    tsum_mul_left, tsum_mul_left]

/-- **`G_d(R) = ∑_a h_d(a)(½ log(R/a) + C_γ) + E(R)`.** -/
theorem GqP_decomp {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    GqP d R = (Real.log R / 2 + Cg) * ∑' a, hD d a - (1 / 2) * ∑' a, hD d a * Real.log a +
      ∑' a, hD d a * Fo (R / a) := by
  rw [← tsum_T hd hR, ← Summable.tsum_add (summable_T hd hR) (summable_E hd hR), GqP_eq]
  have hV : ∀ a : ℕ, hD d a * (Real.log (R / a) / 2 + Cg) + hD d a * Fo (R / a) = hD d a * V (R / a) := by
    intro a; rw [Fo]; ring
  simp_rw [hV]
  symm
  refine tsum_eq_sum fun a ha => ?_
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp
  · have hlt : ⌊R⌋₊ < a := by
      by_contra hc; exact ha (mem_Icc.2 ⟨h, by omega⟩)
    have : R / a < 1 := by
      have ha0 : (0 : ℝ) < a := by exact_mod_cast h
      rw [div_lt_one ha0]
      have := Nat.lt_floor_add_one R
      have h2 : (⌊R⌋₊ : ℝ) + 1 ≤ a := by exact_mod_cast hlt
      linarith
    rw [V_eq_zero this, mul_zero]

/-! ### `∑_a h_d(a) = 2φ(d)/d` -/

theorem totient_div {d : ℕ} (hd : 1 ≤ d) :
    (Nat.totient d : ℝ) / d = ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors d
  have h' : (((Nat.totient d : ℕ) : ℚ) : ℝ) =
      (((d : ℚ) * ∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [h', mul_div_cancel_left₀ _ hd0]
  simp only [one_div]

theorem S0_split {d p : ℕ} (hp : p.Prime) :
    S0 d p = (if p ∣ d then 1 - 1 / (p : ℝ) else 1) * (if p = 2 then 2 else 1) := by
  rw [S0_eq hp]
  by_cases h2 : p = 2
  · subst h2; by_cases hd : 2 ∣ d <;> simp [hd] <;> norm_num
  · by_cases hd : p ∣ d <;> simp [h2, hd]

theorem prod_S0 {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : 2 * d < n) :
    ∏ p ∈ Nat.primesBelow n, S0 d p = 2 * ((Nat.totient d : ℝ) / d) := by
  have hsub : (2 * d).primeFactors ⊆ Nat.primesBelow n := by
    intro p hp
    have := Nat.le_of_mem_primeFactors hp
    exact Nat.mem_primesBelow.2 ⟨by omega, Nat.prime_of_mem_primeFactors hp⟩
  rw [← prod_subset hsub fun p hp hnot => ?_]
  · rw [prod_congr rfl fun p hp => S0_split (Nat.prime_of_mem_primeFactors hp), prod_mul_distrib]
    have h1 : ∏ p ∈ (2 * d).primeFactors, (if p ∣ d then 1 - 1 / (p : ℝ) else 1) =
        ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ)) := by
      rw [prod_ite, prod_const_one, mul_one]
      congr 1
      ext p; simp only [mem_filter, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨a, _, _⟩, b⟩; exact ⟨a, b, by omega⟩
      · rintro ⟨a, b, _⟩; exact ⟨⟨a, b.trans (dvd_mul_left d 2), by omega⟩, b⟩
    have h2 : ∏ p ∈ (2 * d).primeFactors, (if p = 2 then (2 : ℝ) else 1) = 2 := by
      rw [prod_ite_eq' (2 * d).primeFactors 2 (fun _ => (2 : ℝ))]
      rw [if_pos (Nat.mem_primeFactors.2 ⟨Nat.prime_two, dvd_mul_right 2 d, by omega⟩)]
    rw [h1, h2, totient_div hd]; ring
  · have hpp := (Nat.mem_primesBelow.1 hp).2
    have hnd : ¬ p ∣ 2 * d := fun h => hnot (Nat.mem_primeFactors.2 ⟨hpp, h, by omega⟩)
    have h2 : p ≠ 2 := by rintro rfl; exact hnd (dvd_mul_right 2 d)
    have hdd : ¬ p ∣ d := fun h => hnd (h.trans (dvd_mul_left d 2))
    rw [S0_split hpp, if_neg hdd, if_neg h2, mul_one]

theorem tsum_local_S0 {d p : ℕ} (hp : p.Prime) : ∑' e, hD d (p ^ e) = S0 d p := by
  have := hasSum_local (d := d) hp (fun _ => 1)
  simp only [one_mul] at this
  rw [this.tsum_eq, S0]

theorem tsum_hD {d : ℕ} (hd : 1 ≤ d) : ∑' a, hD d a = 2 * ((Nat.totient d : ℝ) / d) := by
  have hE := EulerProduct.eulerProduct (f := hD d) (isMult_hD d).map_one
    (fun h => (isMult_hD d).map_mul_of_coprime h)
    (by simpa [Real.norm_eq_abs] using summable_abs_hD hd) (hD_zero d)
  refine tendsto_nhds_unique hE (tendsto_const_nhds.congr' ?_)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨2 * d + 1, fun n hn => ?_⟩
  rw [prod_congr rfl fun p hp => tsum_local_S0 (Nat.mem_primesBelow.1 hp).2, prod_S0 hd (by omega)]

end TernaryGoldbach.Prelim.RamPf
