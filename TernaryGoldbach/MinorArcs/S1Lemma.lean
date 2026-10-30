import TernaryGoldbach.Prelim.SqfreeCount

/-!
# Lemma 5.1.1 [B] (case `v = 2`)

* `sum_odd_inv_sqrt_le`: `∑_{t ≤ Y odd} 1/√t ≤ √Y`;
* `sum_odd_rpow_le_zeta`: `∑_{d ≤ K odd} d^{-3/2} ≤ (1 - 2^{-3/2}) ζ(3/2)`;
* `sum_odd_divisors_le`: `∑_{r ≤ y odd} ∑_{d | r} 1/√(rd) ≤ (1 - 2^{-3/2}) ζ(3/2) √y`;
* `lemma_5_1_1`: [B, (5.9)–(5.11)] for `v = 2`.
-/

open Real Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs
open TernaryGoldbach.Prelim

/-! ### Sums over odd integers -/

theorem sum_odd_Icc (K : ℕ) (g : ℕ → ℝ) :
    ∑ t ∈ (Icc 1 K).filter Odd, g t = ∑ i ∈ range ((K + 1) / 2), g (2 * i + 1) := by
  symm
  refine sum_nbij' (fun i => 2 * i + 1) (fun t => t / 2) (fun i hi => ?_) (fun t ht => ?_)
    (fun i _ => ?_) (fun t ht => ?_) (fun _ _ => rfl)
  · simp only [mem_range] at hi
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
  · simp only [mem_filter, mem_Icc] at ht
    obtain ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩ := ht
    simp only [mem_range]; omega
  · omega
  · simp only [mem_filter, mem_Icc] at ht
    obtain ⟨_, ⟨k, rfl⟩⟩ := ht
    omega

theorem sum_range_inv_sqrt_odd (j : ℕ) :
    ∑ i ∈ range j, 1 / √(2 * i + 1 : ℝ) ≤ √(2 * j - 1 : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h1 : 0 < √(2 * j + 1 : ℝ) := sqrt_pos.2 (by linarith)
    have h2 : √(2 * (j : ℝ) - 1) ≤ 2 * j / √(2 * j + 1) := by
      rw [le_div_iff₀ h1, ← sqrt_mul (by linarith), sqrt_le_iff]
      constructor
      · positivity
      · nlinarith
    have h3 : 2 * (j : ℝ) / √(2 * j + 1) + 1 / √(2 * j + 1) = √(2 * j + 1) := by
      rw [← add_div, div_eq_iff h1.ne', mul_self_sqrt (by linarith)]
    push_cast
    calc ∑ i ∈ range j, 1 / √(2 * (i : ℝ) + 1) + 1 / √(2 * j + 1)
        ≤ √(2 * (j : ℝ) - 1) + 1 / √(2 * j + 1) := by gcongr
      _ ≤ √(2 * (j : ℝ) + 1) := by linarith
      _ = √(2 * ((j : ℝ) + 1) - 1) := by ring_nf

/-- `∑_{t ≤ K odd} 1/√t ≤ √K`. -/
theorem sum_odd_inv_sqrt_le (K : ℕ) :
    ∑ t ∈ (Icc 1 K).filter Odd, 1 / √(t : ℝ) ≤ √(K : ℝ) := by
  rw [sum_odd_Icc]
  push_cast
  refine (sum_range_inv_sqrt_odd _).trans (sqrt_le_sqrt ?_)
  have : 2 * ((K + 1) / 2) ≤ K + 1 := Nat.mul_div_le _ _
  have : (2 * ((K + 1) / 2 : ℕ) : ℝ) ≤ K + 1 := by exact_mod_cast this
  linarith

theorem zeta_three_halves_eq :
    (riemannZeta (3 / 2)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num)]
  have : ∑' n : ℕ, 1 / (n : ℂ) ^ (3 / 2 : ℂ) = ((∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 3, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [this, Complex.ofReal_re]

/-- `∑_{d ≤ K odd} d^{-3/2} ≤ (1 - 2^{-3/2}) ζ(3/2)`. -/
theorem sum_odd_rpow_le_zeta (K : ℕ) :
    ∑ d ∈ (Icc 1 K).filter Odd, 1 / (d : ℝ) ^ (3 / 2 : ℝ) ≤
      (1 - 2 ^ (-(3 / 2) : ℝ)) * (riemannZeta (3 / 2)).re := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ (3 / 2 : ℝ)
  have hf : Summable f := Real.summable_one_div_nat_rpow.2 (by norm_num)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [f]; positivity
  have heven : ∀ k : ℕ, f (2 * k) = 2 ^ (-(3 / 2) : ℝ) * f k := fun k => by
    simp only [f]; push_cast
    rw [mul_rpow (by norm_num) (Nat.cast_nonneg _), rpow_neg (by norm_num)]
    field_simp
  have hse : Summable fun k => f (2 * k) := by
    simp_rw [heven]; exact hf.mul_left _
  have hso : Summable fun k => f (2 * k + 1) :=
    hf.comp_injective (fun a b h => by omega)
  have hsplit := tsum_even_add_odd hse hso
  simp_rw [heven] at hsplit
  rw [tsum_mul_left] at hsplit
  have hodd : ∑' k, f (2 * k + 1) = (1 - 2 ^ (-(3 / 2) : ℝ)) * ∑' n, f n := by linarith
  rw [zeta_three_halves_eq, ← show ∑' n, f n = ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) from rfl,
    ← hodd, sum_odd_Icc]
  exact hso.sum_le_tsum _ (fun i _ => hf0 _)

theorem one_sub_two_rpow_pos : (0 : ℝ) < 1 - 2 ^ (-(3 / 2) : ℝ) := by
  have : (2 : ℝ) ^ (-(3 / 2) : ℝ) < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith

theorem zeta_three_halves_nonneg : 0 ≤ (riemannZeta (3 / 2)).re := by
  rw [zeta_three_halves_eq]; exact tsum_nonneg fun n => by positivity

theorem rpow_three_halves (d : ℝ) (hd : 0 ≤ d) : d ^ (3 / 2 : ℝ) = d * √d := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, sqrt_eq_rpow]
  rcases hd.eq_or_lt with rfl | hd
  · rw [zero_rpow (by norm_num)]; simp
  rw [rpow_add hd, rpow_one]

/-- `∑_{r ≤ y odd} ∑_{d | r} 1/√(rd) ≤ (1 - 2^{-3/2}) ζ(3/2) √y`. -/
theorem sum_odd_divisors_le {y : ℝ} (hy : 0 ≤ y) :
    ∑ r ∈ (Icc 1 ⌊y⌋₊).filter Odd, ∑ d ∈ r.divisors, 1 / √((r : ℝ) * d) ≤
      (1 - 2 ^ (-(3 / 2) : ℝ)) * (riemannZeta (3 / 2)).re * √y := by
  set K := ⌊y⌋₊
  set F := (Icc 1 K).filter Odd
  rw [sum_comm' (t' := F) (s' := fun d => F.filter (d ∣ ·))]
  swap
  · intro r d
    simp only [F, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ho⟩, hd, hr0⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨⟨⟨h1, h2⟩, ho⟩, hd⟩, ⟨hd0, (Nat.le_of_dvd (by omega) hd).trans h2⟩,
        Odd.of_dvd_nat ho hd⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, ho⟩, hd⟩, _⟩
      exact ⟨⟨⟨h1, h2⟩, ho⟩, hd, by omega⟩
  rw [mul_comm _ (√y)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_odd_rpow_le_zeta K) (sqrt_nonneg y))
  rw [mul_sum]
  refine sum_le_sum fun d hd => ?_
  simp only [F, mem_filter, mem_Icc] at hd
  obtain ⟨⟨hd1, hdK⟩, hdo⟩ := hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  -- Inner sum over multiples `r = d t`.
  have himg : F.filter (d ∣ ·) = ((Icc 1 (K / d)).filter Odd).image (d * ·) := by
    ext r
    simp only [F, mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ho⟩, ⟨t, rfl⟩⟩
      refine ⟨t, ⟨⟨?_, ?_⟩, (Nat.odd_mul.1 ho).2⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp at h1
        · exact ht
      · exact (Nat.le_div_iff_mul_le hd1).2 (by rw [mul_comm]; exact h2)
    · rintro ⟨t, ⟨⟨h1, h2⟩, ho⟩, rfl⟩
      refine ⟨⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩, Nat.odd_mul.2 ⟨hdo, ho⟩⟩,
        dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hd1).1 h2
      rw [mul_comm]; exact this
  rw [himg, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd1 h)]
  have hterm : ∀ t ∈ (Icc 1 (K / d)).filter Odd,
      1 / √(((d * t : ℕ) : ℝ) * d) = 1 / d * (1 / √(t : ℝ)) := by
    intro t _
    push_cast
    rw [show (d : ℝ) * t * d = d ^ 2 * t by ring, sqrt_mul (by positivity), sqrt_sq hd0.le]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  have h1 := sum_odd_inv_sqrt_le (K / d)
  have h2 : ((K / d : ℕ) : ℝ) ≤ y / d := by
    refine (Nat.cast_div_le).trans ?_
    gcongr; exact Nat.floor_le hy
  calc 1 / (d : ℝ) * ∑ t ∈ (Icc 1 (K / d)).filter Odd, 1 / √(t : ℝ)
      ≤ 1 / d * √(y / d) := by
        gcongr; exact h1.trans (sqrt_le_sqrt h2)
    _ = √y * (1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [rpow_three_halves _ hd0.le, sqrt_div' _ hd0.le]
        have : 0 < √(d : ℝ) := sqrt_pos.2 hd0
        field_simp

/-! ### Lemma 5.1.1 -/

theorem sum_divisors_mul_le (m n : ℕ) (g : ℕ → ℝ) (hg : ∀ e, 0 ≤ g e) :
    ∑ e ∈ (m * n).divisors, g e ≤ ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, g (a * b) := by
  rw [Nat.divisors_mul, Finset.mul_def, ← sum_product' (f := fun a b => g (a * b))]
  rw [sum_comp (f := g) (g := fun p : ℕ × ℕ => p.1 * p.2)]
  refine sum_le_sum fun e he => ?_
  obtain ⟨p, hp, rfl⟩ := mem_image.1 he
  have : 1 ≤ #{q ∈ m.divisors ×ˢ n.divisors | q.1 * q.2 = p.1 * p.2} :=
    card_pos.2 ⟨p, mem_filter.2 ⟨hp, rfl⟩⟩
  rw [nsmul_eq_mul]
  exact le_mul_of_one_le_left (hg _) (by exact_mod_cast this)

theorem sigma_one_two : σ 1 2 = 3 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors Nat.prime_two]

theorem sum_divisors_two_inv_sqrt : ∑ d ∈ (2 : ℕ).divisors, 1 / √(d : ℝ) = 1 + 1 / √2 := by
  rw [Nat.Prime.divisors Nat.prime_two, sum_pair (by norm_num)]; simp

/-- Lower end of the `l`-range in [B, (5.9)]: `max(z/(y r₁), z/(y r₂), z/(2 r₁ r₂))`. -/
noncomputable def aL (y z : ℝ) (r₁ r₂ : ℕ) : ℝ :=
  max (max (z / (y * r₁)) (z / (y * r₂))) (z / (2 * r₁ * r₂))

/-- Upper end of the `l`-range in [B, (5.9)]: `z/(r₁ r₂)`. -/
noncomputable def bL (z : ℝ) (r₁ r₂ : ℕ) : ℝ := z / (r₁ * r₂)

/-- The weight `1 - max(1/2, r₁/y, r₂/y)` in [B, (5.10)]. -/
noncomputable def wM (y : ℝ) (r₁ r₂ : ℕ) : ℝ := 1 - max (1 / 2) (max (r₁ / y) (r₂ / y))

/-- `A(r) = ∑_{d | r} 1/√(rd)`. -/
noncomputable def divA (r : ℕ) : ℝ := ∑ d ∈ r.divisors, 1 / √((r : ℝ) * d)

theorem divA_nonneg (r : ℕ) : 0 ≤ divA r := sum_nonneg fun _ _ => by positivity

/-- The error for one pair `(r₁, r₂)` in Lemma 5.1.1. -/
theorem lemma_5_1_1_term {y z : ℝ} (hy : 0 < y) (hz : 0 < z) {r₁ r₂ : ℕ}
    (hr₁ : r₁ ∈ Icc 1 ⌊y⌋₊) (hr₂ : r₂ ∈ Icc 1 ⌊y⌋₊) :
    |if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
        (μ r₁ : ℝ) * μ r₂ * (cntSq (2 * (r₁ * r₂)) (aL y z r₁ r₂) (bL z r₁ r₂) -
          4 * z / π ^ 2 / ((σ 1 r₁ : ℝ) * σ 1 r₂) * wM y r₁ r₂) else 0| ≤
      1.27 * √z * (1 + 1 / √2) * ((if Odd r₁ then divA r₁ else 0) *
        (if Odd r₂ then divA r₂ else 0)) := by
  have hE0 : 0 ≤ 1.27 * √z * (1 + 1 / √2) * ((if Odd r₁ then divA r₁ else 0) *
      (if Odd r₂ then divA r₂ else 0)) := by
    have := divA_nonneg r₁; have := divA_nonneg r₂
    split_ifs <;> positivity
  by_cases hg : Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂)
  swap
  · rw [if_neg hg, abs_zero]; exact hE0
  rw [if_pos hg]
  obtain ⟨hcop, hodd⟩ := hg
  rw [if_pos (Nat.odd_mul.1 hodd).1, if_pos (Nat.odd_mul.1 hodd).2]
  simp only [mem_Icc] at hr₁ hr₂
  have hr₁y : (r₁ : ℝ) ≤ y := (Nat.cast_le.2 hr₁.2).trans (Nat.floor_le hy.le)
  have hr₂y : (r₂ : ℝ) ≤ y := (Nat.cast_le.2 hr₂.2).trans (Nat.floor_le hy.le)
  have hr₁0 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁.1
  have hr₂0 : (0 : ℝ) < r₂ := by exact_mod_cast hr₂.1
  by_cases hμ : (μ r₁ : ℝ) * μ r₂ = 0
  · rw [hμ, zero_mul, abs_zero]
    have := divA_nonneg r₁; have := divA_nonneg r₂; positivity
  have hsq₁ : Squarefree r₁ := by
    by_contra h; apply hμ; simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  have hsq₂ : Squarefree r₂ := by
    by_contra h; apply hμ; simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  have hcop2 : Nat.Coprime 2 (r₁ * r₂) := Nat.coprime_two_left.2 hodd
  have hP : Squarefree (2 * (r₁ * r₂)) :=
    Nat.squarefree_mul_iff.2 ⟨hcop2, Nat.prime_two.squarefree,
      Nat.squarefree_mul_iff.2 ⟨hcop, hsq₁, hsq₂⟩⟩
  -- The interval.
  set c := z / ((r₁ : ℝ) * r₂) with hc
  have hc0 : 0 < c := by positivity
  have haL : aL y z r₁ r₂ = c * max (1 / 2) (max (r₁ / y) (r₂ / y)) := by
    have e1 : z / (y * r₁) = c * (r₂ / y) := by rw [hc]; field_simp
    have e2 : z / (y * r₂) = c * (r₁ / y) := by rw [hc]; field_simp
    have e3 : z / (2 * r₁ * r₂) = c * (1 / 2) := by rw [hc]; field_simp
    rw [aL, e1, e2, e3, ← mul_max_of_nonneg _ _ hc0.le, ← mul_max_of_nonneg _ _ hc0.le,
      max_comm, max_comm ((r₂ : ℝ) / y)]
  have hbL : bL z r₁ r₂ = c := rfl
  have hM1 : max (1 / 2) (max ((r₁ : ℝ) / y) (r₂ / y)) ≤ 1 :=
    max_le (by norm_num) (max_le ((div_le_one hy).2 hr₁y) ((div_le_one hy).2 hr₂y))
  have ha0 : 0 ≤ aL y z r₁ r₂ := by rw [haL]; positivity
  have hab : aL y z r₁ r₂ ≤ bL z r₁ r₂ := by
    rw [haL, hbL]; exact mul_le_of_le_one_right hc0.le hM1
  have hb2 : bL z r₁ r₂ ≤ 2 * aL y z r₁ r₂ := by
    rw [haL, hbL]
    have : (1 / 2 : ℝ) ≤ max (1 / 2) (max ((r₁ : ℝ) / y) (r₂ / y)) := le_max_left _ _
    nlinarith
  have hcnt := cntSq_approx hP ha0 hab hb2
  -- The main term.
  have hσ : (σ 1 (2 * (r₁ * r₂)) : ℝ) = 3 * ((σ 1 r₁ : ℝ) * σ 1 r₂) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two]
    push_cast; ring
  have hσ0 : (0 : ℝ) < (σ 1 r₁ : ℝ) * σ 1 r₂ := by
    have h1 : 0 < σ 1 r₁ := ArithmeticFunction.sigma_pos _ _ (by omega)
    have h2 : 0 < σ 1 r₂ := ArithmeticFunction.sigma_pos _ _ (by omega)
    positivity
  have hmain : (bL z r₁ r₂ - aL y z r₁ r₂) *
      (6 / π ^ 2 * (((2 * (r₁ * r₂) : ℕ) : ℝ) / σ 1 (2 * (r₁ * r₂)))) =
      4 * z / π ^ 2 / ((σ 1 r₁ : ℝ) * σ 1 r₂) * wM y r₁ r₂ := by
    rw [haL, hbL, hσ, wM, hc]
    push_cast
    field_simp
    ring
  rw [hmain] at hcnt
  rw [abs_mul]
  have hμ1 : |(μ r₁ : ℝ) * μ r₂| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_moebius_le_one_real _) (abs_nonneg _) (abs_moebius_le_one_real _)
  refine (mul_le_of_le_one_left (abs_nonneg _) hμ1).trans (hcnt.trans ?_)
  -- The error sum.
  set g : ℕ → ℝ := fun e => √(bL z r₁ r₂ / e)
  have hg0 : ∀ e, 0 ≤ g e := fun e => sqrt_nonneg _
  calc ∑ e ∈ (2 * (r₁ * r₂)).divisors, fsq √(bL z r₁ r₂ / e)
      ≤ ∑ e ∈ (2 * (r₁ * r₂)).divisors, 1.27 * g e :=
        sum_le_sum fun e _ => fsq_le (sqrt_nonneg _)
    _ = 1.27 * ∑ e ∈ (2 * (r₁ * r₂)).divisors, g e := by rw [mul_sum]
    _ ≤ 1.27 * ∑ d₃ ∈ (2 : ℕ).divisors, ∑ d₁ ∈ r₁.divisors, ∑ d₂ ∈ r₂.divisors,
          g (d₃ * (d₁ * d₂)) := by
        gcongr
        refine (sum_divisors_mul_le 2 (r₁ * r₂) g hg0).trans (sum_le_sum fun d₃ _ => ?_)
        exact sum_divisors_mul_le r₁ r₂ (fun e => g (d₃ * e)) (fun e => hg0 _)
    _ = 1.27 * √z * (1 + 1 / √2) * (divA r₁ * divA r₂) := by
        have key : ∀ d₃ ∈ (2 : ℕ).divisors, ∀ d₁ ∈ r₁.divisors, ∀ d₂ ∈ r₂.divisors,
            g (d₃ * (d₁ * d₂)) = √z * (1 / √(d₃ : ℝ)) *
              ((1 / √((r₁ : ℝ) * d₁)) * (1 / √((r₂ : ℝ) * d₂))) := by
          intro d₃ hd₃ d₁ hd₁ d₂ hd₂
          have h3 : (0 : ℝ) < d₃ := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
          have h1 : (0 : ℝ) < d₁ := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
          have h2 : (0 : ℝ) < d₂ := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
          simp only [g, bL]
          push_cast
          rw [show z / (r₁ * r₂) / (d₃ * (d₁ * d₂)) = z / (d₃ * ((r₁ * d₁) * (r₂ * d₂))) by
            field_simp]
          rw [sqrt_div' _ (by positivity), sqrt_mul (by positivity), sqrt_mul (by positivity)]
          have : 0 < √(d₃ : ℝ) := sqrt_pos.2 h3
          have : 0 < √((r₁ : ℝ) * d₁) := sqrt_pos.2 (by positivity)
          have : 0 < √((r₂ : ℝ) * d₂) := sqrt_pos.2 (by positivity)
          field_simp
        rw [sum_congr rfl fun d₃ hd₃ => sum_congr rfl fun d₁ hd₁ =>
          sum_congr rfl fun d₂ hd₂ => key d₃ hd₃ d₁ hd₁ d₂ hd₂]
        rw [← sum_divisors_two_inv_sqrt, divA, divA]
        simp_rw [← mul_sum, ← sum_mul]
        rw [← mul_sum]
        ring

/-- **Lemma 5.1.1** [B, (5.9)–(5.11)], `v = 2`: for `y, z > 0`,
`∑_{r₁, r₂ ≤ y, (r₁,r₂)=1, r₁r₂ odd} μ(r₁)μ(r₂) #{l ∈ (a, b] : l sq-free, (l, 2r₁r₂) = 1}`
`= (4z/π²) ∑ μ(r₁)μ(r₂)/(σ(r₁)σ(r₂)) (1 - max(1/2, r₁/y, r₂/y))`
`+ O*(1.27 (1 + 1/√2) ((1 - 2^{-3/2}) ζ(3/2))² y √z)`, where
`(a, b] = (max(z/(y r₁), z/(y r₂), z/(2 r₁ r₂)), z/(r₁ r₂)]`. -/
theorem lemma_5_1_1 {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    |∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
      (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
        (μ r₁ : ℝ) * μ r₂ * (cntSq (2 * (r₁ * r₂)) (aL y z r₁ r₂) (bL z r₁ r₂) -
          4 * z / π ^ 2 / ((σ 1 r₁ : ℝ) * σ 1 r₂) * wM y r₁ r₂) else 0)| ≤
      1.27 * (1 + 1 / √2) * ((1 - 2 ^ (-(3 / 2) : ℝ)) * (riemannZeta (3 / 2)).re) ^ 2 *
        y * √z := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun r₁ hr₁ => (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun r₂ hr₂ => lemma_5_1_1_term hy hz hr₁ hr₂)).trans ?_
  simp_rw [← mul_sum, ← sum_mul]
  rw [← sq, ← sum_filter]
  have hA := sum_odd_divisors_le hy.le
  have hA0 : 0 ≤ ∑ r ∈ (Icc 1 ⌊y⌋₊).filter Odd, divA r := sum_nonneg fun r _ => divA_nonneg r
  have hsq : (∑ r ∈ (Icc 1 ⌊y⌋₊).filter Odd, divA r) ^ 2 ≤
      ((1 - 2 ^ (-(3 / 2) : ℝ)) * (riemannZeta (3 / 2)).re * √y) ^ 2 :=
    pow_le_pow_left₀ hA0 hA 2
  rw [mul_pow, sq_sqrt hy.le] at hsq
  have : 0 ≤ 1.27 * √z * (1 + 1 / √2) := by positivity
  calc 1.27 * √z * (1 + 1 / √2) * (∑ r ∈ (Icc 1 ⌊y⌋₊).filter Odd, divA r) ^ 2
      ≤ 1.27 * √z * (1 + 1 / √2) *
          (((1 - 2 ^ (-(3 / 2) : ℝ)) * (riemannZeta (3 / 2)).re) ^ 2 * y) := by gcongr
    _ = _ := by ring

end TernaryGoldbach.MinorArcs
