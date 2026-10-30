import TernaryGoldbach.MinorArcs.TypeI2Proof

/-!
# [B, Lemma 4.2.4]: the terms other than the main term (weights `log m`)

Since `|c(a)| ≤ log a`, the terms of `typeI2` outside the main term are bounded by
`∑ log m · |T_{m,∘}|` over the ranges of [B, Lemma 4.2.2]. Here we bound these weighted range
sums, using on each block of length `q` the weight `log` of the block's upper end, and the
block bounds `block_R2`, `block_R3` of Lemma 4.2.2.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-- Weighted block decomposition: if `log t ≤ W j` on the `j`-th block and the `j`-th block of
`∑ G` is at most `B j`, then `∑ log n · G n ≤ ∑_j W j · B j`. -/
theorem sum_log_mul_le_blocks {G : ℤ → ℝ} (hG : ∀ n, 0 ≤ G n) {q : ℕ} (hq : 1 ≤ q) (J : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ a + J * q) (W B : ℕ → ℝ) (hW0 : ∀ j < J, 0 ≤ W j)
    (hW : ∀ j < J, ∀ t : ℝ, 1 ≤ t → t ≤ min (a + (j + 1) * q) b → Real.log t ≤ W j)
    (hB : ∀ j < J, ∑ n ∈ Ioc ⌊a + j * q⌋ ⌊min (a + (j + 1) * q) b⌋, G n ≤ B j) :
    ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, Real.log n * G n ≤ ∑ j ∈ range J, W j * B j := by
  have hlog : ∀ n : ℤ, 0 ≤ Real.log (n : ℝ) := fun n => Real.log_intCast_nonneg n
  refine (sum_Ioc_le_blocks (G := fun n => Real.log n * G n)
    (fun n => mul_nonneg (hlog n) (hG n)) hq J a b hab).trans ?_
  refine sum_le_sum fun j hj => ?_
  have hj' := mem_range.1 hj
  calc ∑ n ∈ Ioc ⌊a + j * q⌋ ⌊min (a + (j + 1) * q) b⌋, Real.log n * G n
      ≤ ∑ n ∈ Ioc ⌊a + j * q⌋ ⌊min (a + (j + 1) * q) b⌋, W j * G n := by
        refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (hG n)
        rw [mem_Ioc] at hn
        have h0 : (0 : ℤ) ≤ ⌊a + j * q⌋ := Int.floor_nonneg.2 (by positivity)
        have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
        exact hW j hj' n h1 ((Int.cast_le.2 hn.2).trans (Int.floor_le _))
    _ = W j * ∑ n ∈ Ioc ⌊a + j * q⌋ ⌊min (a + (j + 1) * q) b⌋, G n := (mul_sum _ _ _).symm
    _ ≤ W j * B j := mul_le_mul_of_nonneg_left (hB j hj') (hW0 j hj')

/-! ### Elementary real inequalities -/

/-- `t (log t - c)` is increasing on `[s, ∞)` if `c ≤ 1 + log s`. -/
theorem mul_log_sub_mono {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (hc : c ≤ 1 + Real.log s) :
    s * (Real.log s - c) ≤ t * (Real.log t - c) := by
  have ht : 0 < t := hs.trans_le hst
  -- `t (log t - log s) ≥ t - s`.
  have h1 : t - s ≤ t * (Real.log t - Real.log s) := by
    have := Real.log_le_sub_one_of_pos (div_pos hs ht)
    rw [Real.log_div hs.ne' ht.ne'] at this
    have e : t * (s / t - 1) = s - t := by field_simp
    nlinarith
  nlinarith

/-- `d/dt [(t²/2)(log t - 1/2)] = t log t`. -/
theorem hasDerivAt_F₄ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ 2 / 2 * (Real.log t - 1 / 2)) (t * Real.log t) t := by
  have h := ((hasDerivAt_pow 2 t).div_const 2).mul ((Real.hasDerivAt_log ht.ne').sub_const (1 / 2))
  convert h using 1; simp; field_simp; ring

/-- `d/dt [t (log t - 1)] = log t`. -/
theorem hasDerivAt_F₅ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t * (Real.log t - 1)) (Real.log t) t := by
  have h := (hasDerivAt_id' t).mul ((Real.hasDerivAt_log ht.ne').sub_const 1)
  convert h using 1; simp; field_simp; ring

theorem F₄_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    s ^ 2 / 2 * (Real.log s - 1 / 2) ≤ t ^ 2 / 2 * (Real.log t - 1 / 2) := by
  have := monotoneOn_of_deriv_nonneg (f := fun t => t ^ 2 / 2 * (Real.log t - 1 / 2))
    (convex_Ici 1)
    (fun u hu => (hasDerivAt_F₄ (show (0 : ℝ) < u by linarith [Set.mem_Ici.1 hu])).continuousAt.continuousWithinAt)
    (fun u hu => by
      rw [interior_Ici] at hu
      exact (hasDerivAt_F₄ (show (0 : ℝ) < u by linarith [Set.mem_Ioi.1 hu])).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Ici] at hu
      have hu1 : (1 : ℝ) < u := hu
      rw [(hasDerivAt_F₄ (show (0 : ℝ) < u by linarith)).deriv]
      exact mul_nonneg (by linarith) (Real.log_nonneg hu1.le))
  exact this (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hst)) hst

theorem F₄_ge {t : ℝ} (ht : 0 < t) : -(1 / 4) ≤ t ^ 2 / 2 * (Real.log t - 1 / 2) := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  rw [Real.log_inv] at h
  have h' : 1 - 1 / t ≤ Real.log t := by rw [one_div]; linarith
  have e : t ^ 2 * (1 - 1 / t) = t ^ 2 - t := by field_simp
  nlinarith [sq_nonneg (t - 1), mul_le_mul_of_nonneg_left h' (sq_nonneg t)]

/-- `log(3R)/R ≤ (log(3R₀) + 1)/R₀` for `R ≥ R₀ ≥ 1/3`. -/
theorem log_three_mul_div_le {R R₀ : ℝ} (hR₀ : 1 / 3 ≤ R₀) (hR : R₀ ≤ R) :
    Real.log (3 * R) / R ≤ (Real.log (3 * R₀) + 1) / R₀ := by
  have hR₀0 : 0 < R₀ := by linarith
  have hR0 : 0 < R := hR₀0.trans_le hR
  have hl0 : 0 ≤ Real.log (3 * R₀) := Real.log_nonneg (by linarith)
  have hsplit : Real.log (3 * R) = Real.log (3 * R₀) + Real.log (R / R₀) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hl : Real.log (R / R₀) ≤ R / R₀ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [div_le_div_iff₀ hR0 hR₀0, hsplit]
  have e : (R / R₀ - 1) * R₀ = R - R₀ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hl hR₀0.le]

/-! ### The weighted ranges -/

/-- Weighted range (R1): `∑_{m ≤ q/2} log m |T_{m,∘}| ≤ log⁺(q/2) · (R1 bound)`. -/
theorem sum_R1W {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) :
    ∑ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Real.log n * Tn α x n ≤
      logPlus ((q : ℝ) / 2) *
        (2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)))) := by
  have hpt : ∀ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Real.log n * Tn α x n ≤ logPlus ((q : ℝ) / 2) * Tn α x n := by
    intro n hn
    refine mul_le_mul_of_nonneg_right ?_ (Tn_nonneg α x n)
    rw [mem_Ioc] at hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    exact log_le_logPlus (by linarith) ((Int.cast_le.2 hn.2).trans (Int.floor_le _))
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_R1 hx hq hcop h2α hqQ hδ) (logPlus_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Weighted range (R2) (cf. [B, (4.59)]): for `q/2 < D' ≤ Q/2`,
`∑_{q/2 < m ≤ D', q ∤ m} log m |T_{m,∘}| ≤ (10c₀q/3π²x)(F(D' + 2q) + 1/4)`,
`F(t) = (t²/2)(log t - 1/2)`. -/
theorem sum_R2W {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {D' : ℝ} (hD'q : (q : ℝ) / 2 < D') (hD'Q : D' ≤ Q / 2) :
    ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      10 * c₀ * q / (3 * π ^ 2 * x) *
        ((D' + 2 * q) ^ 2 / 2 * (Real.log (D' + 2 * q) - 1 / 2) + 1 / 4) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 := c₀_pos
  set J := ⌈(D' - q / 2) / q⌉₊
  set K := 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x)
  have hK : 0 ≤ K := by positivity
  have hmain := sum_log_mul_le_blocks (G := fun n => if (q : ℤ) ∣ n then 0 else Tn α x n)
    (fun n => by split_ifs; exacts [le_rfl, Tn_nonneg _ _ _]) hq J (a := q / 2) (b := D')
    (by positivity) (nblocks_spec hq0)
    (fun j => Real.log ((j + 3 / 2) * q)) (fun j => K * ((j : ℝ) + 3 / 2))
    (fun j _ => Real.log_nonneg (by nlinarith))
    (fun j _ t ht1 ht => Real.log_le_log (by linarith) (by
      have := min_le_left ((q : ℝ) / 2 + (j + 1) * q) D'; linarith))
    (fun j _ => block_R2 hx hq hcop h2α hqQ hδ hD'Q j)
  refine hmain.trans ?_
  -- `∑_j (j + 3/2) log((j + 3/2) q) = (1/q²) ∑_j f(3q/2 + jq)`, `f(t) = t log t`.
  have hrw : ∀ j ∈ range J, Real.log (((j : ℝ) + 3 / 2) * q) * (K * ((j : ℝ) + 3 / 2)) =
      K / q * ((3 * q / 2 + j * q) * Real.log (3 * q / 2 + j * q)) := by
    intro j _
    rw [show 3 * (q : ℝ) / 2 + j * q = ((j : ℝ) + 3 / 2) * q by ring]
    field_simp
  rw [sum_congr rfl hrw, ← mul_sum]
  have hsum := sum_le_of_monotone (F := fun t => t ^ 2 / 2 * (Real.log t - 1 / 2))
    (f := fun t => t * Real.log t) (a := 3 * q / 2) (h := q) hq0 J
    (fun t ht => hasDerivAt_F₄ (by linarith [ht.1]))
    (fun s hs t ht hst => by
      have := mul_log_sub_mono (c := 0) (by linarith [hs.1]) hst
        (by have := Real.log_nonneg (show (1 : ℝ) ≤ s by linarith [hs.1]); linarith)
      simpa using this)
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (by
    simp only [J, ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hq0)
  have hJD : (q : ℝ) / 2 + ((J : ℝ) - 1) * q < D' := by
    have := lt_of_lt_nblocks hq0 (a := q / 2) (b := D') (j := J - 1) (by omega)
    rw [Nat.cast_sub hJ1] at this; push_cast at this; linarith
  have hmono := F₄_mono (s := 3 * q / 2 + J * q) (t := D' + 2 * q) (by nlinarith) (by linarith)
  have hge := F₄_ge (t := 3 * q / 2) (by positivity)
  have hS : ∑ j ∈ range J, (3 * (q : ℝ) / 2 + j * q) * Real.log (3 * q / 2 + j * q) ≤
      ((D' + 2 * q) ^ 2 / 2 * (Real.log (D' + 2 * q) - 1 / 2) + 1 / 4) / q := by
    rw [le_div_iff₀ hq0, mul_comm]
    linarith
  calc K / q * ∑ j ∈ range J, (3 * (q : ℝ) / 2 + j * q) * Real.log (3 * q / 2 + j * q)
      ≤ K / q * (((D' + 2 * q) ^ 2 / 2 * (Real.log (D' + 2 * q) - 1 / 2) + 1 / 4) / q) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by simp only [K]; field_simp

set_option maxHeartbeats 1000000 in
/-- Weighted range (R3) (cf. [B, (4.61)–(4.62)]): for `1 ≤ R`, `q/2 ≤ R < D`, with
`c₁ = 1 + |η'|₁/(x/D)`,
`∑_{R < m ≤ D} log m |T_{m,∘}| ≤ (3c₁/2) x (log(3R)/R + (log D/q) log(D/R)) +
(2√(c₀c₁)/π)(√3 q log(3R) + D(log D - 1) - R(log R - 1) + 2q log(D/R) + (q/2) log D log(D/R))`. -/
theorem sum_R3W {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {R D : ℝ} (hR1 : 1 ≤ R) (hRq : (q : ℝ) / 2 ≤ R) (hRD : R < D) :
    ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Real.log n * Tn α x n ≤
      3 * (1 + eta2'L1 / (x / D)) / 2 * x *
          (Real.log (3 * R) / R + Real.log D / q * Real.log (D / R)) +
        2 * √(c₀ * (1 + eta2'L1 / (x / D))) / π *
          (q * √3 * Real.log (3 * R) + (D * (Real.log D - 1) - R * (Real.log R - 1)) +
            2 * q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  set J := ⌈(D - R) / q⌉₊
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (by
    simp only [J, ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hq0)
  have hlt : ∀ j < J, R + j * q < D := fun j hj => lt_of_lt_nblocks hq0 hj
  have hmain := sum_log_mul_le_blocks (G := Tn α x) (Tn_nonneg α x) hq J (a := R) (b := D)
    hR0.le (nblocks_spec hq0)
    (fun j => Real.log (min (R + (j + 1) * q) D))
    (fun j => 3 * c₁ / 2 * x * (1 / (R + j * q)) +
      2 * q * √(c₀ * c₁) / π * √(1 + q / (R + j * q)))
    (fun j _ => Real.log_nonneg (le_min (by
      have : (0 : ℝ) ≤ (j + 1) * q := by positivity
      linarith) hD1))
    (fun j _ t ht1 ht => Real.log_le_log (by linarith) ht)
    (fun j hj => block_R3 hx hq hcop h2α hqQ hδ hR0 j (hlt j hj))
  refine hmain.trans ?_
  obtain ⟨K, hK⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hKD : R + K * q < D := by
    have := hlt K (by omega); exact this
  rw [hK, sum_range_succ']
  set Bc := 2 * √(c₀ * c₁) / π
  have hBc : 0 ≤ Bc := by positivity
  set P1 := 3 * c₁ / 2 * x
  have hP1 : 0 ≤ P1 := by positivity
  -- The term `j = 0`.
  have h0 : Real.log (min (R + (((0 : ℕ) : ℝ) + 1) * q) D) *
      (P1 * (1 / (R + ((0 : ℕ) : ℝ) * q)) + 2 * q * √(c₀ * c₁) / π * √(1 + q / (R + ((0 : ℕ) : ℝ) * q))) ≤
      P1 * (Real.log (3 * R) / R) + Bc * (q * √3 * Real.log (3 * R)) := by
    simp only [Nat.cast_zero, zero_add, one_mul, zero_mul, add_zero]
    have hW0 : 0 ≤ Real.log (min (R + q) D) := Real.log_nonneg (le_min (by linarith) hD1)
    have hW : Real.log (min (R + q) D) ≤ Real.log (3 * R) :=
      Real.log_le_log (lt_min (by linarith) hD0) ((min_le_left _ _).trans (by linarith))
    have hs : √(1 + q / R) ≤ √3 := Real.sqrt_le_sqrt (by
      have : q / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
      linarith)
    have e : 2 * q * √(c₀ * c₁) / π = Bc * q := by simp only [Bc]; ring
    rw [e]
    calc Real.log (min (R + q) D) * (P1 * (1 / R) + Bc * q * √(1 + q / R))
        = P1 * (1 / R) * Real.log (min (R + q) D) + Bc * q * (Real.log (min (R + q) D) * √(1 + q / R)) := by
          ring
      _ ≤ P1 * (1 / R) * Real.log (3 * R) + Bc * q * (Real.log (3 * R) * √3) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * R by linarith)
          gcongr
      _ = _ := by ring
  -- The terms `j = i + 1`.
  set y : ℕ → ℝ := fun i => R + ((i + 1 : ℕ) : ℝ) * q with hy
  have hy0 : ∀ i, 0 < y i := fun i => by simp only [y]; positivity
  have hterm : ∀ i ∈ range K, Real.log (min (R + (((i + 1 : ℕ) : ℝ) + 1) * q) D) *
      (P1 * (1 / (R + ((i + 1 : ℕ) : ℝ) * q)) +
        2 * q * √(c₀ * c₁) / π * √(1 + q / (R + ((i + 1 : ℕ) : ℝ) * q))) ≤
      (P1 * Real.log D + Bc * q * q + Bc * q * (q / 2) * Real.log D) * (1 / y i) +
        Bc * q * Real.log (y i) := by
    intro i _
    have hyi := hy0 i
    have hyR : R ≤ y i := by simp only [y]; have : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) * q := by positivity
                             linarith
    have hyq : R + (((i + 1 : ℕ) : ℝ) + 1) * q = y i + q := by simp only [y]; ring
    rw [hyq]
    change Real.log (min (y i + q) D) * (P1 * (1 / y i) + 2 * q * √(c₀ * c₁) / π * √(1 + q / y i)) ≤ _
    set W := Real.log (min (y i + q) D)
    have hW0 : 0 ≤ W := Real.log_nonneg (le_min (by linarith) hD1)
    have hWD : W ≤ Real.log D := Real.log_le_log (lt_min (by linarith) hD0) (min_le_right _ _)
    have hWy : W ≤ Real.log (y i) + q * (1 / y i) := by
      have h1 : W ≤ Real.log (y i + q) :=
        Real.log_le_log (lt_min (by linarith) hD0) (min_le_left _ _)
      have h2 : Real.log ((y i + q) / y i) ≤ (y i + q) / y i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) hyi.ne'] at h2
      have e : (y i + q) / y i - 1 = q * (1 / y i) := by field_simp; ring
      linarith
    have hs : √(1 + q / y i) ≤ 1 + q / y i / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [sq_nonneg (q / y i)]
    have e2 : W * √(1 + q / y i) ≤ Real.log (y i) + q * (1 / y i) + q / 2 * Real.log D * (1 / y i) := by
      calc W * √(1 + q / y i) ≤ W * (1 + q / y i / 2) := mul_le_mul_of_nonneg_left hs hW0
        _ = W + W * (q / 2 * (1 / y i)) := by ring
        _ ≤ (Real.log (y i) + q * (1 / y i)) + Real.log D * (q / 2 * (1 / y i)) :=
            add_le_add hWy (mul_le_mul_of_nonneg_right hWD (by positivity))
        _ = _ := by ring
    have e : 2 * q * √(c₀ * c₁) / π = Bc * q := by simp only [Bc]; ring
    rw [e]
    calc W * (P1 * (1 / y i) + Bc * q * √(1 + q / y i))
        = P1 * (1 / y i) * W + Bc * q * (W * √(1 + q / y i)) := by ring
      _ ≤ P1 * (1 / y i) * Real.log D +
          Bc * q * (Real.log (y i) + q * (1 / y i) + q / 2 * Real.log D * (1 / y i)) :=
          add_le_add (mul_le_mul_of_nonneg_left hWD (by have := hy0 i; positivity))
            (mul_le_mul_of_nonneg_left e2 (by positivity))
      _ = _ := by ring
  refine (add_le_add (sum_le_sum hterm) h0).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  -- `S₁ = ∑ 1/y_i ≤ (1/q) log(D/R)`.
  have hS1 : ∑ i ∈ range K, 1 / y i ≤ 1 / q * Real.log (D / R) := by
    have h := sum_inv_le hR0 hq0 hJ1 (D := D) (by
      rw [hK]; push_cast; simp only [add_sub_cancel_right]; linarith)
    rw [hK, sum_range_succ'] at h
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    have : ∑ i ∈ range K, 1 / y i = ∑ i ∈ range K, 1 / (R + ((i + 1 : ℕ) : ℝ) * q) := rfl
    linarith
  -- `S₂ = ∑ log y_i ≤ (1/q)(G(D) - G(R)) + log(D/R)`, `G(t) = t(log t - 1)`.
  have hS2 : ∑ i ∈ range K, Real.log (y i) ≤
      1 / q * (D * (Real.log D - 1) - R * (Real.log R - 1)) + Real.log (D / R) := by
    have tel := sum_range_sub (fun i : ℕ => Real.log (R + i * q)) K
    simp only [Nat.cast_zero, zero_mul, add_zero] at tel
    have hsplit : ∑ i ∈ range K, Real.log (y i) =
        ∑ i ∈ range K, Real.log (R + i * q) + (Real.log (R + K * q) - Real.log R) := by
      rw [← tel, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [y]; ring
    have hsum := sum_le_of_monotone (F := fun t => t * (Real.log t - 1)) (f := Real.log)
      (a := R) (h := q) hq0 K (fun t ht => hasDerivAt_F₅ (by linarith [ht.1]))
      (fun s hs t _ hst => Real.log_le_log (by linarith [hs.1]) hst)
    have hG := mul_log_sub_mono (c := 1) (s := R + K * q) (t := D) (by positivity) hKD.le
      (by have := Real.log_nonneg (show (1 : ℝ) ≤ R + K * q by
            have : (0 : ℝ) ≤ K * q := by positivity
            linarith)
          linarith)
    have hl : Real.log (R + K * q) - Real.log R ≤ Real.log (D / R) := by
      rw [Real.log_div hD0.ne' hR0.ne']
      have := Real.log_le_log (by positivity) hKD.le; linarith
    have hS : ∑ i ∈ range K, Real.log (R + i * q) ≤
        1 / q * (D * (Real.log D - 1) - R * (Real.log R - 1)) := by
      beta_reduce at hsum
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hq0]
      linarith
    linarith
  have hlogDR : 0 ≤ Real.log (D / R) := Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hcoef : 0 ≤ P1 * Real.log D + Bc * q * q + Bc * q * (q / 2) * Real.log D := by positivity
  have h1 := mul_le_mul_of_nonneg_left hS1 hcoef
  have h2 := mul_le_mul_of_nonneg_left hS2 (show 0 ≤ Bc * q by positivity)
  have e1 : (P1 * Real.log D + Bc * q * q + Bc * q * (q / 2) * Real.log D) *
      (1 / q * Real.log (D / R)) = P1 * (Real.log D / q * Real.log (D / R)) +
        Bc * (q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) := by
    field_simp; ring
  have e2 : Bc * q * (1 / q * (D * (Real.log D - 1) - R * (Real.log R - 1)) + Real.log (D / R)) =
      Bc * ((D * (Real.log D - 1) - R * (Real.log R - 1)) + q * Real.log (D / R)) := by
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  have e3 : P1 * (Real.log (3 * R) / R + Real.log D / q * Real.log (D / R)) +
      Bc * (q * √3 * Real.log (3 * R) + (D * (Real.log D - 1) - R * (Real.log R - 1)) +
        2 * q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) =
      (P1 * (Real.log (3 * R) / R) + Bc * (q * √3 * Real.log (3 * R))) +
      P1 * (Real.log D / q * Real.log (D / R)) +
        Bc * (q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) +
      Bc * ((D * (Real.log D - 1) - R * (Real.log R - 1)) + q * Real.log (D / R)) := by ring
  rw [e3]
  linarith

end TernaryGoldbach.MinorArcs
