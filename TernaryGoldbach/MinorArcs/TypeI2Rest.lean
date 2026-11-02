import TernaryGoldbach.MinorArcs.TypeI2Proof

/-!
# [H, Lemma 4.2.4]: the terms other than the main term (weights `log m`)

Since `|c(a)| ≤ log a`, the terms of `typeI2` outside the main term are bounded by
`∑ log m · |T_{m,∘}|` over the ranges of [H, Lemma 4.2.2]. Here we bound these weighted range
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
/-- Weighted range (R2) (cf. [H, (4.59)]): for `q/2 < D' ≤ Q/2`,
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
/-- Weighted range (R3) (cf. [H, (4.61)–(4.62)]), general form: for `1 ≤ R < D`, with
`c₁ = 1 + |η'|₁/(x/D)`,
`∑_{R < m ≤ D} log m |T_{m,∘}| ≤ (3c₁/2) x (log(R+q)/R + (log D/q) log(D/R)) +
(2√(c₀c₁)/π)(√(1+q/R) q log(R+q) + D(log D - 1) - R(log R - 1) + 2q log(D/R) + (q/2) log D log(D/R))`. -/
theorem sum_R3W' {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {R D : ℝ} (hR1 : 1 ≤ R) (hRD : R < D) :
    ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Real.log n * Tn α x n ≤
      3 * (1 + eta2'L1 / (x / D)) / 2 * x *
          (Real.log (R + q) / R + Real.log D / q * Real.log (D / R)) +
        2 * √(c₀ * (1 + eta2'L1 / (x / D))) / π *
          (q * √(1 + q / R) * Real.log (R + q) + (D * (Real.log D - 1) - R * (Real.log R - 1)) +
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
      P1 * (Real.log (R + q) / R) + Bc * (q * √(1 + q / R) * Real.log (R + q)) := by
    simp only [Nat.cast_zero, zero_add, one_mul, zero_mul, add_zero]
    have hW0 : 0 ≤ Real.log (min (R + q) D) := Real.log_nonneg (le_min (by linarith) hD1)
    have hW : Real.log (min (R + q) D) ≤ Real.log (R + q) :=
      Real.log_le_log (lt_min (by linarith) hD0) (min_le_left _ _)
    have e : 2 * q * √(c₀ * c₁) / π = Bc * q := by simp only [Bc]; ring
    rw [e]
    calc Real.log (min (R + q) D) * (P1 * (1 / R) + Bc * q * √(1 + q / R))
        = P1 * (1 / R) * Real.log (min (R + q) D) + Bc * q * (Real.log (min (R + q) D) * √(1 + q / R)) := by
          ring
      _ ≤ P1 * (1 / R) * Real.log (R + q) + Bc * q * (Real.log (R + q) * √(1 + q / R)) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ R + q by linarith)
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
  have e3 : P1 * (Real.log (R + q) / R + Real.log D / q * Real.log (D / R)) +
      Bc * (q * √(1 + q / R) * Real.log (R + q) + (D * (Real.log D - 1) - R * (Real.log R - 1)) +
        2 * q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) =
      (P1 * (Real.log (R + q) / R) + Bc * (q * √(1 + q / R) * Real.log (R + q))) +
      P1 * (Real.log D / q * Real.log (D / R)) +
        Bc * (q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R)) +
      Bc * ((D * (Real.log D - 1) - R * (Real.log R - 1)) + q * Real.log (D / R)) := by ring
  rw [e3]
  linarith


/-- Weighted range (R3) for `q/2 ≤ R` (cf. [H, (4.61)–(4.62)]). -/
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
  have hl : Real.log (R + q) ≤ Real.log (3 * R) := Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log (R + q) := Real.log_nonneg (by linarith)
  have hs : √(1 + q / R) ≤ √3 := Real.sqrt_le_sqrt (by
    have : q / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
    linarith)
  refine (sum_R3W' hx hq hcop h2α hqQ hδ hR1 hRD).trans ?_
  have hc0 := c₀_pos
  have hV := eta2'L1_pos
  have hD0 : 0 < D := by linarith
  have h1 : Real.log (R + q) / R ≤ Real.log (3 * R) / R := div_le_div_of_nonneg_right hl hR0.le
  have h2 : q * √(1 + q / R) * Real.log (R + q) ≤ q * √3 * Real.log (3 * R) := by
    gcongr
  gcongr

/-! ### Case (b): assembling (4.51) -/

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)

/-- `log t ≥ 1/2` for `t ≥ √3`. -/
theorem half_le_log {t : ℝ} (ht : √3 ≤ t) : 1 / 2 ≤ Real.log t := by
  have h3 : 0 < √3 := by positivity
  have := Real.log_le_log h3 ht
  rw [Real.log_sqrt (by norm_num)] at this
  linarith [one_le_log_three]

set_option maxHeartbeats 1000000 in
/-- Simplification of `sum_R2W` in case (b): for `q/2 < D' ≤ c₂x/q`, `1 ≤ D' ≤ D`, `2 ≤ x`. -/
theorem R2W_simp {x D D' : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 2 ≤ x) (hD'q : (q : ℝ) / 2 < D')
    (hD'1 : 1 ≤ D') (hD'c : D' ≤ c₂ * x / q) (hD'D : D' ≤ D) :
    10 * c₀ * q / (3 * π ^ 2 * x) * ((D' + 2 * q) ^ 2 / 2 * (Real.log (D' + 2 * q) - 1 / 2) + 1 / 4) ≤
      2 * √c₀ / π * (D' * (Real.log D' - 1 / 2)) +
        (2 * √c₀ / π * √(2 * c₂ * x) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have hc21 := c₂_lt_one
  have hD'0 : 0 < D' := by linarith
  set P := D' + 2 * q with hPdef
  have hP0 : 0 < P := by positivity
  have hP5 : P ≤ 5 * D := by simp only [P]; linarith
  have hL0 : 0 ≤ Real.log P - 1 / 2 := by
    have := Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ P by simp only [P]; linarith)
    linarith [one_le_log_three]
  have hqD' : (q : ℝ) * D' ≤ c₂ * x := by rw [le_div_iff₀ hq0] at hD'c; linarith
  have hq2 : (q : ℝ) ^ 2 ≤ 2 * c₂ * x := by
    have : (q : ℝ) / 2 * q < c₂ * x := by
      have := mul_lt_mul_of_pos_right (hD'q.trans_le hD'c) hq0
      rwa [div_mul_cancel₀ _ hq0.ne'] at this
    nlinarith
  have hqx : (q : ℝ) ≤ x := by nlinarith
  have hqP : (q : ℝ) * P ^ 2 ≤ c₂ * x * (D' + 12 * q) := by
    have e : (q : ℝ) * P ^ 2 = (q * D') * D' + 4 * q * (q * D') + 4 * q * q ^ 2 := by
      simp only [P]; ring
    rw [e]
    have h1 : (q * D') * D' ≤ (c₂ * x) * D' := mul_le_mul_of_nonneg_right hqD' hD'0.le
    have h2 : 4 * q * (q * D') ≤ 4 * q * (c₂ * x) := mul_le_mul_of_nonneg_left hqD' (by positivity)
    have h3 : 4 * q * q ^ 2 ≤ 4 * q * (2 * c₂ * x) := mul_le_mul_of_nonneg_left hq2 (by positivity)
    nlinarith
  -- `(D' + 12q) L ≤ D'(log D' - 1/2) + 2q + 12q log(5D)`.
  have hLD' : D' * (Real.log P - 1 / 2) ≤ D' * (Real.log D' - 1 / 2) + 2 * q := by
    have h := Real.log_le_sub_one_of_pos (div_pos hP0 hD'0)
    rw [Real.log_div hP0.ne' hD'0.ne'] at h
    have e : D' * (P / D' - 1) = 2 * q := by simp only [P]; field_simp; ring
    nlinarith
  have hLq : Real.log P - 1 / 2 ≤ Real.log (5 * D) := by
    have := Real.log_le_log hP0 hP5; linarith
  have hlog5 : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by linarith)
  have hk : 0 ≤ 2 * √c₀ / π := by positivity
  have hqs : (q : ℝ) ≤ √(2 * c₂ * x) := Real.le_sqrt_of_sq_le hq2
  have hmain : 10 * c₀ * q / (3 * π ^ 2 * x) * (P ^ 2 / 2 * (Real.log P - 1 / 2)) ≤
      2 * √c₀ / π * ((D' + 12 * q) * (Real.log P - 1 / 2)) := by
    rw [← c₂_identity]
    have e : 10 * c₀ * q / (3 * π ^ 2 * x) * (P ^ 2 / 2 * (Real.log P - 1 / 2)) =
        5 * c₀ / (3 * π ^ 2) * (q * P ^ 2 / x) * (Real.log P - 1 / 2) := by field_simp; ring
    rw [e]
    have h : (q : ℝ) * P ^ 2 / x ≤ c₂ * (D' + 12 * q) := by
      rw [div_le_iff₀ hx0]; linarith
    calc 5 * c₀ / (3 * π ^ 2) * (q * P ^ 2 / x) * (Real.log P - 1 / 2)
        ≤ 5 * c₀ / (3 * π ^ 2) * (c₂ * (D' + 12 * q)) * (Real.log P - 1 / 2) := by gcongr
      _ = _ := by ring
  have hquarter : 10 * c₀ * q / (3 * π ^ 2 * x) * (1 / 4) ≤ 5 * c₀ / (6 * π ^ 2) := by
    rw [show 10 * c₀ * q / (3 * π ^ 2 * x) * (1 / 4) = 5 * c₀ / (6 * π ^ 2) * (q / x) by
      field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hx0).2 hqx)
  have hsplit : (D' + 12 * q) * (Real.log P - 1 / 2) ≤
      D' * (Real.log D' - 1 / 2) + q * (2 + 12 * Real.log (5 * D)) := by
    have := mul_le_mul_of_nonneg_left hLq (show (0 : ℝ) ≤ 12 * q by positivity)
    nlinarith
  have hq' : (q : ℝ) * (2 + 12 * Real.log (5 * D)) ≤ √(2 * c₂ * x) * (2 + 12 * Real.log (5 * D)) :=
    mul_le_mul_of_nonneg_right hqs (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hsplit hk
  have h2 := mul_le_mul_of_nonneg_left hq' hk
  calc 10 * c₀ * q / (3 * π ^ 2 * x) * (P ^ 2 / 2 * (Real.log P - 1 / 2) + 1 / 4)
      = 10 * c₀ * q / (3 * π ^ 2 * x) * (P ^ 2 / 2 * (Real.log P - 1 / 2)) +
        10 * c₀ * q / (3 * π ^ 2 * x) * (1 / 4) := by ring
    _ ≤ _ := by nlinarith

set_option maxHeartbeats 4000000 in
/-- **[H, Lemma 4.2.4], case (b), terms other than the main term**: if
`D' = min(c₂x/q, D) ≤ Q/2` and `D' ≤ M` (`D = UV`), the terms of `typeI2` with
`¬(q ∣ a ∧ a ≤ M)` contribute at most `bound_4_51` (our form of (4.51)). -/
theorem norm_restPartI2_le_caseB {α x δ Q M U V : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) (hU : 0 ≤ U) (hV : 0 ≤ V) (hD2 : 2 ≤ U * V)
    (hcx : 6 ≤ c₂ * x) (hD'Q : min (c₂ * x / q) (U * V) ≤ Q / 2)
    (hMD' : min (c₂ * x / q) (U * V) ≤ M) :
    ‖restPartI2 α x M U V q‖ ≤ bound_4_51 x q U V := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hη := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have hc21 := c₂_lt_one
  set D := U * V with hDdef
  have hD0 : 0 < D := by linarith
  have hx6 : 6 ≤ x := by nlinarith
  set D' := min (c₂ * x / q) D with hD'def
  have hD'0 : 0 ≤ D' := le_min (by positivity) hD0.le
  have hD'D : D' ≤ D := min_le_right _ _
  have hD'c : D' ≤ c₂ * x / q := min_le_left _ _
  set R := max D' ((q : ℝ) / 2) with hRdef
  have hD'R : D' ≤ R := le_max_left _ _
  have hqR : (q : ℝ) / 2 ≤ R := le_max_right _ _
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  have hsq : √c₀ ≤ √(c₀ * c₁) := Real.sqrt_le_sqrt (by nlinarith)
  have hlog : ∀ n : ℤ, 0 ≤ Real.log (n : ℝ) := fun n => Real.log_intCast_nonneg n
  -- Step 1: `|c(a)| ≤ log a`; drop the parity; integer indices.
  set g : ℤ → ℝ := fun n => if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then Tn α x n else 0
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [g]; split_ifs <;> first | exact Tn_nonneg _ _ _ | exact le_rfl
  have h1 : ‖restPartI2 α x M U V q‖ ≤ ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, Real.log n * g n := by
    rw [restPartI2]
    refine (norm_sum_le _ _).trans ?_
    have hfl : ((⌊D⌋₊ : ℕ) : ℤ) = ⌊D⌋ := Int.natCast_floor_eq_floor hD0.le
    rw [← hfl, ← sum_Icc_eq_Ioc_int]
    have hsub : Icc 1 (⌊V⌋₊ * ⌊U⌋₊) ⊆ Icc 1 ⌊D⌋₊ := Icc_subset_Icc le_rfl (Nat.le_floor (by
      push_cast
      calc (⌊V⌋₊ : ℝ) * ⌊U⌋₊ ≤ V * U :=
            mul_le_mul (Nat.floor_le hV) (Nat.floor_le hU) (by positivity) hV
        _ = D := by rw [hDdef]; ring))
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg (hlog n) (hg0 n))
    refine sum_le_sum fun m _ => ?_
    by_cases h : Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M)
    · rw [if_pos h, norm_mul]
      have hg : g (m : ℤ) = ‖Todd α x m‖ := by
        simp only [g]
        rw [if_pos (by
          intro ⟨hd, hle⟩; exact h.2 ⟨by exact_mod_cast hd, by exact_mod_cast hle⟩)]
        simp [Tn]
      rw [hg]
      have hc : ‖(coefI2 U V m : ℂ)‖ ≤ Real.log ((m : ℤ) : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, Int.cast_natCast]; exact abs_coefI2_le U V m
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    · rw [if_neg h, norm_zero]; exact mul_nonneg (hlog _) (hg0 _)
  -- Step 2: split the range.
  have h2 : ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, Real.log n * g n ≤
      ∑ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Real.log n * Tn α x n +
      ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) +
      ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Real.log n * Tn α x n := by
    have hpt : ∀ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n ≤
        (if n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋ then Tn α x n else 0) +
        (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then (if (q : ℤ) ∣ n then 0 else Tn α x n) else 0) +
        (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then Tn α x n else 0) := by
      intro n hn
      have hT := Tn_nonneg α x n
      have hgT : g n ≤ Tn α x n := by simp only [g]; split_ifs <;> linarith
      rw [mem_Ioc] at hn
      by_cases hA : n ≤ ⌊(q : ℝ) / 2⌋
      · rw [if_pos (mem_Ioc.2 ⟨hn.1, hA⟩)]
        have : 0 ≤ (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then (if (q : ℤ) ∣ n then 0 else Tn α x n) else 0) := by
          split_ifs <;> linarith
        have : 0 ≤ (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then Tn α x n else 0) := by split_ifs <;> linarith
        linarith
      push Not at hA
      by_cases hB : n ≤ ⌊D'⌋
      · rw [if_pos (mem_Ioc.2 ⟨hA, hB⟩), if_neg (by rw [mem_Ioc]; omega)]
        have : 0 ≤ (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then Tn α x n else 0) := by split_ifs <;> linarith
        by_cases hd : (q : ℤ) ∣ n
        · rw [if_pos hd]
          have hnD' : (n : ℝ) ≤ D' := (Int.cast_le.2 hB).trans (Int.floor_le _)
          have : g n = 0 := by
            simp only [g]; rw [if_neg (not_not.2 ⟨hd, hnD'.trans hMD'⟩)]
          linarith
        · rw [if_neg hd]; linarith
      push Not at hB
      have hnR : ⌊R⌋ < n := by
        have h1 : D' < n := by
          have := Int.lt_floor_add_one D'
          have : ((⌊D'⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hB
          linarith
        have h2 : (q : ℝ) / 2 < n := by
          have := Int.lt_floor_add_one ((q : ℝ) / 2)
          have : ((⌊(q : ℝ) / 2⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hA
          linarith
        have : R < n := max_lt h1 h2
        exact Int.floor_lt.2 this
      rw [if_neg (by rw [mem_Ioc]; omega), if_neg (by rw [mem_Ioc]; omega),
        if_pos (mem_Ioc.2 ⟨hnR, hn.2⟩)]
      linarith
    have hpt' : ∀ n ∈ Ioc (0 : ℤ) ⌊D⌋, Real.log n * g n ≤
        (if n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋ then Real.log n * Tn α x n else 0) +
        (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then
          Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) else 0) +
        (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then Real.log n * Tn α x n else 0) := by
      intro n hn
      calc Real.log n * g n ≤ Real.log n * ((if n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋ then Tn α x n else 0) +
          (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then (if (q : ℤ) ∣ n then 0 else Tn α x n) else 0) +
          (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then Tn α x n else 0)) := mul_le_mul_of_nonneg_left (hpt n hn) (hlog n)
        _ = _ := by split_ifs <;> ring
    have hnn : ∀ n : ℤ, 0 ≤ Real.log n * Tn α x n := fun n => mul_nonneg (hlog n) (Tn_nonneg _ _ _)
    refine (sum_le_sum hpt').trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_ite_mem, sum_ite_mem, sum_ite_mem]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => hnn n
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => by
        split_ifs
        · simp
        · exact hnn n
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => hnn n
  -- Step 3: the three weighted ranges.
  have hW1 := sum_R1W hx hq hcop h2α hqQ hδ (α := α)
  set E2 := 2 * √c₀ / π * √(2 * c₂ * x) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2)
    with hE2def
  have hE2 : 0 ≤ E2 := by
    have : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by linarith)
    positivity
  set T2 := if (q : ℝ) / 2 < D' ∧ 1 ≤ D' then D' * (Real.log D' - 1 / 2) else 0 with hT2def
  have hW2 : ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      2 * √c₀ / π * T2 + E2 := by
    by_cases hP : (q : ℝ) / 2 < D' ∧ 1 ≤ D'
    · rw [hT2def, if_pos hP]
      exact (sum_R2W hx hq hcop h2α hqQ hδ hP.1 hD'Q).trans
        (R2W_simp hq (by linarith) hP.1 hP.2 hD'c hD'D)
    · rw [hT2def, if_neg hP, mul_zero, zero_add]
      have hempty : ⌊D'⌋ ≤ ⌊(q : ℝ) / 2⌋ := by
        rcases not_and_or.1 hP with h | h
        · exact Int.floor_mono (not_lt.1 h)
        · push Not at h
          have : ⌊D'⌋ ≤ 0 := Int.floor_le_iff.2 (by push_cast; linarith)
          have : 0 ≤ ⌊(q : ℝ) / 2⌋ := Int.floor_nonneg.2 (by positivity)
          omega
      rw [Ioc_eq_empty (not_lt.2 hempty), sum_empty]; exact hE2
  set Bc := 2 * √(c₀ * c₁) / π with hBcdef
  have hBc : 0 ≤ Bc := by positivity
  have hBc' : 2 * √c₀ / π ≤ Bc := by
    have := Real.pi_pos
    simp only [Bc]; gcongr
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hlP1 := logPlus_nonneg (D / (c₂ * x / q))
  have hlP2 := logPlus_nonneg (D / (q / 2))
  set R₀ := √(c₂ * x / 2) with hR₀def
  have hR₀3 : √3 ≤ R₀ := Real.sqrt_le_sqrt (by linarith)
  have hR₀1 : 1 ≤ R₀ := le_trans (by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)) hR₀3
  have hlogR₀ : 0 ≤ Real.log (3 * R₀) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * R₀ by linarith); linarith
  have hsx : √(2 * x / c₂) = x / R₀ := by
    have hR₀0 : 0 < R₀ := by linarith
    rw [eq_div_iff hR₀0.ne', hR₀def, ← Real.sqrt_mul (by positivity)]
    rw [show 2 * x / c₂ * (c₂ * x / 2) = x ^ 2 by field_simp]
    exact Real.sqrt_sq hx.le
  -- Upper bound for range (R3) in its simplified form (`0` if empty).
  set G := fun t : ℝ => t * (Real.log t - 1)
  set T3 := if R < D then D * (Real.log D - 1) - R * (Real.log R - 1) else 0 with hT3def
  have hW3 : ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Real.log n * Tn α x n ≤
      3 * c₁ / 2 * (√(2 * x / c₂) * (Real.log (3 * R₀) + 1) +
        x / q * Real.log D * logPlus (D / (c₂ * x / q))) +
      Bc * (q * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2))) + T3) := by
    by_cases hRD : R < D
    · rw [hT3def, if_pos hRD]
      have hD'eq : D' = c₂ * x / q := by
        rcases min_choice (c₂ * x / q) D with h | h
        · exact h
        · exfalso; have : D' = D := h; linarith
      have hRc : c₂ * x / q ≤ R := hD'eq ▸ hD'R
      have hR0 : 0 < R := by
        have : 0 < c₂ * x / q := by positivity
        linarith
      have hRR₀ : R₀ ≤ R := by
        rw [hR₀def, ← Real.sqrt_sq hR0.le]
        refine Real.sqrt_le_sqrt ?_
        have : c₂ * x / 2 = (c₂ * x / q) * (q / 2) := by field_simp
        rw [this, sq]
        exact mul_le_mul hRc hqR (by positivity) hR0.le
      have hR1 : 1 ≤ R := hR₀1.trans hRR₀
      have h := sum_R3W hx hq hcop h2α hqQ hδ hR1 hqR hRD (α := α)
      rw [← hc₁def] at h
      refine h.trans ?_
      have hlDR : 0 ≤ Real.log (D / R) := Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith)
      have hl1 : Real.log (D / R) ≤ logPlus (D / (c₂ * x / q)) :=
        log_le_logPlus (by positivity) (div_le_div_of_nonneg_left hD0.le (by positivity) hRc)
      have hl2 : Real.log (D / R) ≤ logPlus (D / (q / 2)) :=
        log_le_logPlus (by positivity) (div_le_div_of_nonneg_left hD0.le (by positivity) hqR)
      have hx3 : x * (Real.log (3 * R) / R) ≤ √(2 * x / c₂) * (Real.log (3 * R₀) + 1) := by
        rw [hsx]
        have := log_three_mul_div_le (by linarith) hRR₀
        calc x * (Real.log (3 * R) / R) ≤ x * ((Real.log (3 * R₀) + 1) / R₀) :=
              mul_le_mul_of_nonneg_left this hx.le
          _ = _ := by ring
      have hl3 : Real.log (3 * R) ≤ Real.log (3 * D) := Real.log_le_log (by positivity) (by linarith)
      have hA : 3 * c₁ / 2 * x * (Real.log (3 * R) / R + Real.log D / q * Real.log (D / R)) ≤
          3 * c₁ / 2 * (√(2 * x / c₂) * (Real.log (3 * R₀) + 1) +
            x / q * Real.log D * logPlus (D / (c₂ * x / q))) := by
        have e : 3 * c₁ / 2 * x * (Real.log (3 * R) / R + Real.log D / q * Real.log (D / R)) =
            3 * c₁ / 2 * (x * (Real.log (3 * R) / R) + x / q * Real.log D * Real.log (D / R)) := by
          ring
        rw [e]
        have : x / q * Real.log D * Real.log (D / R) ≤ x / q * Real.log D * logPlus (D / (c₂ * x / q)) :=
          mul_le_mul_of_nonneg_left hl1 (by positivity)
        gcongr
      have hB : q * √3 * Real.log (3 * R) + (D * (Real.log D - 1) - R * (Real.log R - 1)) +
            2 * q * Real.log (D / R) + q / 2 * Real.log D * Real.log (D / R) ≤
          q * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2))) +
            (D * (Real.log D - 1) - R * (Real.log R - 1)) := by
        have h1 : q * √3 * Real.log (3 * R) ≤ q * √3 * Real.log (3 * D) :=
          mul_le_mul_of_nonneg_left hl3 (by positivity)
        have h2 : 2 * q * Real.log (D / R) ≤ 2 * q * logPlus (D / (q / 2)) :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
        have h3 : q / 2 * Real.log D * Real.log (D / R) ≤ q / 2 * Real.log D * logPlus (D / (q / 2)) :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
        nlinarith
      have hB' := mul_le_mul_of_nonneg_left hB hBc
      have e2 : 2 * √(c₀ * c₁) / π = Bc := rfl
      rw [e2]
      linarith
    · rw [hT3def, if_neg hRD, Ioc_eq_empty (not_lt.2 (Int.floor_mono (not_lt.1 hRD))), sum_empty,
        add_zero]
      have : 0 ≤ √(2 * x / c₂) * (Real.log (3 * R₀) + 1) := by positivity
      have : 0 ≤ q * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2))) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * D by linarith)
        positivity
      positivity
  -- Step 4: the `D log D` terms: `(2√c₀/π) T2 + Bc T3 ≤ Bc D (log D - 1/2)`.
  have hDD : 0 ≤ D * (Real.log D - 1 / 2) := by
    have : 1 / 2 ≤ Real.log D := by
      have h4 : (1 : ℝ) ≤ Real.log 4 := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (by norm_num) hD2
      linarith
    nlinarith
  have hT : 2 * √c₀ / π * T2 + Bc * T3 ≤ Bc * (D * (Real.log D - 1 / 2)) := by
    by_cases hRD : R < D
    · rw [hT3def, if_pos hRD]
      have hD'eq : D' = c₂ * x / q := by
        rcases min_choice (c₂ * x / q) D with h | h
        · exact h
        · exfalso; have : D' = D := h; linarith
      have hRc : c₂ * x / q ≤ R := hD'eq ▸ hD'R
      have hR0 : 0 < R := by
        have : 0 < c₂ * x / q := by positivity
        linarith
      have hRR₀ : R₀ ≤ R := by
        rw [hR₀def, ← Real.sqrt_sq hR0.le]
        refine Real.sqrt_le_sqrt ?_
        have : c₂ * x / 2 = (c₂ * x / q) * (q / 2) := by field_simp
        rw [this, sq]
        exact mul_le_mul hRc hqR (by positivity) hR0.le
      have hlR : 1 / 2 ≤ Real.log R := half_le_log (hR₀3.trans hRR₀)
      by_cases hP : (q : ℝ) / 2 < D' ∧ 1 ≤ D'
      · rw [hT2def, if_pos hP]
        have hRD' : R = D' := max_eq_left hP.1.le
        rw [hRD']
        rw [hRD'] at hlR
        have hT2 : 0 ≤ D' * (Real.log D' - 1 / 2) := by nlinarith
        have := mul_le_mul_of_nonneg_right hBc' hT2
        have e : Bc * (D' * (Real.log D' - 1 / 2)) + Bc * (D * (Real.log D - 1) - D' * (Real.log D' - 1)) =
            Bc * (D * (Real.log D - 1 / 2)) - Bc * ((D - D') / 2) := by ring
        have : 0 ≤ Bc * ((D - D') / 2) := mul_nonneg hBc (by linarith)
        linarith
      · rw [hT2def, if_neg hP, mul_zero, zero_add]
        have : R * (Real.log R - 1) ≥ -(R / 2) := by nlinarith
        have : D * (Real.log D - 1) - R * (Real.log R - 1) ≤ D * (Real.log D - 1 / 2) := by
          nlinarith
        exact mul_le_mul_of_nonneg_left this hBc
    · rw [hT3def, if_neg hRD, mul_zero, add_zero]
      by_cases hP : (q : ℝ) / 2 < D' ∧ 1 ≤ D'
      · rw [hT2def, if_pos hP]
        have hm := mul_log_sub_mono (c := 1 / 2) (by linarith [hP.2]) hD'D
          (by have := Real.log_nonneg hP.2; linarith)
        rcases le_total 0 (D' * (Real.log D' - 1 / 2)) with h0 | h0
        · calc 2 * √c₀ / π * (D' * (Real.log D' - 1 / 2))
              ≤ Bc * (D' * (Real.log D' - 1 / 2)) := mul_le_mul_of_nonneg_right hBc' h0
            _ ≤ Bc * (D * (Real.log D - 1 / 2)) := mul_le_mul_of_nonneg_left hm hBc
        · have : 2 * √c₀ / π * (D' * (Real.log D' - 1 / 2)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
          have := mul_nonneg hBc hDD
          linarith
      · rw [hT2def, if_neg hP, mul_zero]
        exact mul_nonneg hBc hDD
  -- Step 5: combine.
  refine h1.trans (h2.trans ?_)
  unfold bound_4_51
  simp only []
  rw [← hc₁def, ← hBcdef]
  have hlogsq : Real.log (D / √(rexp 1)) = Real.log D - 1 / 2 := by
    rw [Real.log_div hD0.ne' (by positivity), Real.log_sqrt (by positivity), Real.log_exp]
  rw [hlogsq, ← hR₀def, ← hE2def]
  have hW1' : logPlus ((q : ℝ) / 2) *
      (2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)))) =
      2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
        logPlus ((q : ℝ) / 2) := by ring
  rw [hW1'] at hW1
  linarith

theorem three_fifths_le_c₂ : 3 / 5 ≤ c₂ := by
  unfold c₂
  have hc0 : √c₀ ≤ 6 := by
    rw [Real.sqrt_le_left (by norm_num)]; unfold c₀; norm_num
  have hpi := Real.pi_gt_three
  have : 0 < √c₀ := Real.sqrt_pos.2 c₀_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **[H, Lemma 4.2.4], case (b)** (`|δ| ≤ 1/2c₂` or `UV ≤ Q₀/2`), for `η = η₂`: (4.50) + (4.51),
in our corrected form (`bound_4_50`, `bound_4_51`), with `M = Mof x δ q (UV)`. Hypotheses: [H]'s
`x ≥ e²c₂/2` is replaced by `x ≥ 10`, and we need `UV ≥ 2`. -/
theorem lemma_4_2_4_caseB {α x δ Q₀ U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hx : 10 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hD2 : 2 ≤ U * V)
    (hcase : |δ| ≤ 1 / (2 * c₂) ∨ U * V ≤ Q₀ / 2) :
    ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_51 x q U V := by
  obtain ⟨hq, hcop, ⟨k, h2α⟩, hδQ₀, hqQ₀⟩ := h
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc2 := c₂_pos
  have hQ₀0 : 0 < Q₀ := lt_of_lt_of_le hq0 hqQ₀
  set D := U * V with hDdef
  have hD : 1 ≤ D := by linarith
  -- The approximation parameter `Q` and `M = min(Q/2, D)`, as in Lemma 4.2.2.
  obtain ⟨Q, hqQ, hδ, hD'Q, hMQ⟩ : ∃ Q : ℝ, (q : ℝ) ≤ Q ∧ |δ / x| * (q * Q) ≤ 1 ∧
      min (c₂ * x / q) D ≤ Q / 2 ∧ Mof x δ q D = min (Q / 2) D := by
    by_cases hδ0 : δ = 0
    · refine ⟨max Q₀ (2 * D), hqQ₀.trans (le_max_left _ _), by simp [hδ0], ?_, ?_⟩
      · have := le_max_right Q₀ (2 * D)
        exact (min_le_right _ _).trans (by linarith)
      · rw [Mof, if_pos hδ0, min_eq_right]
        have := le_max_right Q₀ (2 * D); linarith
    · have hδpos : 0 < |δ| := abs_pos.2 hδ0
      have hQ₀le : Q₀ ≤ x / (|δ| * q) := by
        rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by positivity)] at hδQ₀
        rw [le_div_iff₀ (by positivity)]; nlinarith
      refine ⟨x / (|δ| * q), hqQ₀.trans hQ₀le, ?_, ?_, by rw [Mof, if_neg hδ0]⟩
      · rw [abs_div, abs_of_pos hx0]; field_simp; rfl
      · rcases hcase with hc | hc
        · refine (min_le_left _ _).trans ?_
          have h1 : 2 * c₂ * |δ| ≤ 1 := by
            rw [le_div_iff₀ (by positivity)] at hc; linarith
          have e : c₂ * x / q = (2 * c₂ * |δ|) * (x / (|δ| * q) / 2) := by field_simp
          rw [e]; exact mul_le_of_le_one_left (by positivity) h1
        · exact (min_le_right _ _).trans (hc.trans (by linarith))
  set M := Mof x δ q D
  have hMD : M ≤ D := by rw [hMQ]; exact min_le_right _ _
  have hM0 : 0 ≤ M := by
    rw [hMQ]; exact le_min (by linarith) (by linarith)
  have hMD' : min (c₂ * x / q) D ≤ M := by rw [hMQ]; exact le_min hD'Q (min_le_right _ _)
  have hMδ : |δ| * M ≤ x / 2 := by
    have h1 : |δ| * M ≤ |δ| * (Q / 2) := by
      rw [hMQ]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
    have h2 : |δ| * (q * Q) ≤ x := by
      have e : |δ / x| * (q * Q) = |δ| * (q * Q) / x := by rw [abs_div, abs_of_pos hx0]; ring
      rw [e, div_le_one hx0] at hδ; exact hδ
    have h3 : |δ| * Q ≤ x := by
      have : |δ| * Q ≤ |δ| * (q * Q) := by
        have hQ0 : 0 ≤ Q := by linarith
        have : Q ≤ q * Q := by
          nlinarith [mul_nonneg (sub_nonneg.2 (show (1 : ℝ) ≤ q by exact_mod_cast hq)) hQ0]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      linarith
    linarith
  have hcx : 6 ≤ c₂ * x := by nlinarith [three_fifths_le_c₂]
  rw [typeI2_eq_main_add_rest hx0 (by linarith) (by linarith) hM0]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_mainPartI2_le hx0 hq h2α hU hV hM0 hMδ hMD
  · exact norm_restPartI2_le_caseB hx0 hq hcop h2α hqQ hδ (by linarith) (by linarith) hD2 hcx
      hD'Q hMD'

/-! ### Case (a): (4.52) -/

/-- `‖restPartI2‖ ≤ ∑_{0 < n ≤ UV, ¬(q ∣ n ∧ n ≤ M)} log n |T_{n,∘}|` (since `|c(a)| ≤ log a`). -/
theorem norm_restPartI2_le_sum {α x M U V : ℝ} {q : ℕ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ‖restPartI2 α x M U V q‖ ≤ ∑ n ∈ Ioc (0 : ℤ) ⌊U * V⌋,
      Real.log n * (if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then Tn α x n else 0) := by
  have hlog : ∀ n : ℤ, 0 ≤ Real.log (n : ℝ) := fun n => Real.log_intCast_nonneg n
  set g : ℤ → ℝ := fun n => if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then Tn α x n else 0
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [g]; split_ifs <;> first | exact Tn_nonneg _ _ _ | exact le_rfl
  rw [restPartI2]
  refine (norm_sum_le _ _).trans ?_
  have hfl : ((⌊U * V⌋₊ : ℕ) : ℤ) = ⌊U * V⌋ := Int.natCast_floor_eq_floor (by positivity)
  rw [← hfl, ← sum_Icc_eq_Ioc_int]
  have hsub : Icc 1 (⌊V⌋₊ * ⌊U⌋₊) ⊆ Icc 1 ⌊U * V⌋₊ := Icc_subset_Icc le_rfl (Nat.le_floor (by
    push_cast
    calc (⌊V⌋₊ : ℝ) * ⌊U⌋₊ ≤ V * U :=
          mul_le_mul (Nat.floor_le hV) (Nat.floor_le hU) (by positivity) hV
      _ = U * V := by ring))
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    mul_nonneg (hlog n) (hg0 n))
  refine sum_le_sum fun m _ => ?_
  by_cases h : Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M)
  · rw [if_pos h, norm_mul]
    have hg : g (m : ℤ) = ‖Todd α x m‖ := by
      simp only [g]
      rw [if_pos (by
        intro ⟨hd, hle⟩; exact h.2 ⟨by exact_mod_cast hd, by exact_mod_cast hle⟩)]
      simp [Tn]
    change _ ≤ Real.log ((m : ℤ) : ℝ) * g (m : ℤ)
    rw [hg]
    have hc : ‖(coefI2 U V m : ℂ)‖ ≤ Real.log ((m : ℤ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, Int.cast_natCast]; exact abs_coefI2_le U V m
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  · rw [if_neg h, norm_zero]; exact mul_nonneg (hlog _) (hg0 _)

set_option maxHeartbeats 4000000 in
/-- **[H, Lemma 4.2.4], case (a), terms other than the main term**: for `|δ| ≥ 1/2c₂`, the terms
of `typeI2` with `¬(q ∣ a ∧ a ≤ M)`, `M = Mof x δ q (UV)`, contribute at most `bound_4_52`. -/
theorem norm_restPartI2_le_caseA {α x δ Q₀ U V ε : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k)
    (hδQ₀ : |δ / x| ≤ 1 / (q * Q₀)) (hqQ₀ : (q : ℝ) ≤ Q₀) (hQ₀2 : 2 ≤ Q₀)
    (hδ : 1 / (2 * c₂) ≤ |δ|) (hU : 0 ≤ U) (hV : 0 ≤ V) (hD1 : 1 ≤ U * V)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖restPartI2 α x (Mof x δ q (U * V)) U V q‖ ≤ bound_4_52 x δ q U V Q₀ ε := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hη := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have hlog : ∀ n : ℤ, 0 ≤ Real.log (n : ℝ) := fun n => Real.log_intCast_nonneg n
  set D := U * V with hDdef
  have hD0 : 0 < D := by linarith
  have hδpos : 0 < |δ| := lt_of_lt_of_le (by positivity) hδ
  have hδ0 : δ ≠ 0 := abs_pos.1 hδpos
  set Qr := x / (|δ| * q) with hQrdef
  have hQrpos : 0 < Qr := by positivity
  have hQ₀0 : 0 < Q₀ := by linarith
  have hQ₀Qr : Q₀ ≤ Qr := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ₀
    rw [hQrdef, le_div_iff₀ (by positivity)]; nlinarith
  have hqQr : (q : ℝ) ≤ Qr := hqQ₀.trans hQ₀Qr
  set M := Mof x δ q D
  have hMdef : M = min (Qr / 2) D := by simp only [M, Mof, if_neg hδ0]; rfl
  have hM1 : 1 ≤ M := by rw [hMdef]; exact le_min (by linarith) hD1
  have hM0 : 0 < M := by linarith
  have hMQ : M ≤ Qr / 2 := by rw [hMdef]; exact min_le_left _ _
  have hMD : M ≤ D := by rw [hMdef]; exact min_le_right _ _
  have hexact : |δ / x| * (q * Qr) = 1 := by
    rw [abs_div, abs_of_pos hx, hQrdef]; field_simp
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  set Bc := 2 * √(c₀ * c₁) / π with hBcdef
  have hBc : 0 ≤ Bc := by positivity
  have hBc' : 2 * √c₀ / π ≤ Bc := by
    have := Real.pi_pos
    have : √c₀ ≤ √(c₀ * c₁) := Real.sqrt_le_sqrt (by nlinarith)
    simp only [Bc]; gcongr
  set Y := min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) with hYdef
  have hfl1 : Qr ≤ (⌊Qr⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one Qr).le
  have hYM : 2 * M ≤ Y := le_min (by linarith) (by linarith)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hlog5 : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by linarith)
  have hlP := logPlus_nonneg (2 * D / Qr)
  -- `qM/x ≤ c₂` and `q² ≤ 2c₂x`.
  have hqM : q * M / x ≤ c₂ := by
    have h1 : q * M / x ≤ q * (Qr / 2) / x := by gcongr
    have h2 : (q : ℝ) * (Qr / 2) / x = 1 / (2 * |δ|) := by rw [hQrdef]; field_simp
    have h3 : 1 / (2 * |δ|) ≤ c₂ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hδ; linarith
    linarith
  have hq2 : (q : ℝ) ^ 2 ≤ 2 * c₂ * x := by
    have h1 : (q : ℝ) * Q₀ ≤ 2 * c₂ * x := by
      rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ₀
      rw [div_le_iff₀ (by positivity)] at hδ
      nlinarith
    nlinarith
  -- Step 1 and the split at `M`.
  set g : ℤ → ℝ := fun n => if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then Tn α x n else 0
  have hsplit : ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, Real.log n * g n ≤
      ∑ n ∈ Ioc 0 ⌊M⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) +
        ∑ n ∈ Ioc ⌊M⌋ ⌊D⌋, Real.log n * Tn α x n := by
    have hsub : Ioc (0 : ℤ) ⌊D⌋ = Ioc 0 ⌊M⌋ ∪ Ioc ⌊M⌋ ⌊D⌋ := by
      have h1 : 0 ≤ ⌊M⌋ := Int.floor_nonneg.2 hM0.le
      have h2 : ⌊M⌋ ≤ ⌊D⌋ := Int.floor_mono hMD
      ext n; simp only [mem_Ioc, mem_union]; omega
    rw [hsub, sum_union (disjoint_left.2 fun n h1 h2 => by simp only [mem_Ioc] at h1 h2; omega)]
    refine add_le_add (sum_le_sum fun n hn => ?_) (sum_le_sum fun n _ => ?_)
    · rw [mem_Ioc] at hn
      have hnM : (n : ℝ) ≤ M := (Int.cast_le.2 hn.2).trans (Int.floor_le _)
      by_cases hd : (q : ℤ) ∣ n
      · simp only [g]; rw [if_neg (not_not.2 ⟨hd, hnM⟩), if_pos hd]
      · simp only [g]; rw [if_pos (fun h => hd h.1), if_neg hd]
    · have := Tn_nonneg α x n
      have := hlog n
      simp only [g]
      split_ifs <;> nlinarith
  -- Range (A1), weight `log M`.
  have hA1 := sum_A1 hx hq hcop h2α hqQr hexact.le hM0.le hMQ (α := α)
  have hA1' : ∑ n ∈ Ioc ⌊(0 : ℝ)⌋ ⌊M⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      2 * √c₀ / π * M + 35 * c₀ * c₂ / (3 * π ^ 2) * q := by
    refine hA1.trans ?_
    have e1 : (q : ℝ) * M ^ 2 / x ≤ c₂ * M := by
      have : (q : ℝ) * M ^ 2 / x = (q * M / x) * M := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hqM hM0.le
    have e2 : 3 * (q : ℝ) ^ 2 * M / x ≤ 3 * c₂ * q := by
      have : 3 * (q : ℝ) ^ 2 * M / x = 3 * q * (q * M / x) := by ring
      rw [this]; nlinarith
    have e3 : 2 * (q : ℝ) ^ 3 / x ≤ 4 * c₂ * q := by
      rw [div_le_iff₀ hx]; nlinarith
    calc 5 * c₀ / (3 * π ^ 2) * (q * M ^ 2 / x + 3 * q ^ 2 * M / x + 2 * q ^ 3 / x)
        ≤ 5 * c₀ / (3 * π ^ 2) * (c₂ * M + 3 * c₂ * q + 4 * c₂ * q) := by gcongr
      _ = 5 * c₀ * c₂ / (3 * π ^ 2) * M + 35 * c₀ * c₂ / (3 * π ^ 2) * q := by ring
      _ = _ := by rw [c₂_identity]
  rw [Int.floor_zero] at hA1'
  have hW1 : ∑ n ∈ Ioc 0 ⌊M⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      Real.log M * (2 * √c₀ / π * M + 35 * c₀ * c₂ / (3 * π ^ 2) * q) := by
    have hpt : ∀ n ∈ Ioc 0 ⌊M⌋, Real.log n * (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
        Real.log M * (if (q : ℤ) ∣ n then 0 else Tn α x n) := by
      intro n hn
      refine mul_le_mul_of_nonneg_right ?_ (by split_ifs; exacts [le_rfl, Tn_nonneg _ _ _])
      rw [mem_Ioc] at hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      exact Real.log_le_log (by linarith) ((Int.cast_le.2 hn.2).trans (Int.floor_le _))
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hA1' (Real.log_nonneg hM1)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogMD : Real.log M ≤ Real.log D := Real.log_le_log hM0 hMD
  -- Range (A2): above `M`, with the second approximation (`0` if empty).
  set T3 := if M < D then D * (Real.log D - 1) - M * (Real.log M - 1) else 0 with hT3def
  have hW2 : ∑ n ∈ Ioc ⌊M⌋ ⌊D⌋, Real.log n * Tn α x n ≤
      3 * c₁ / 2 * (2 * Real.log (5 * D) + (1 + ε) / ε * Real.log D * logPlus (2 * D / Qr)) *
          (x / Q₀) +
        Bc * ((1 + ε) * Y * (√(3 + 2 * ε) * Real.log (5 * D) +
          (2 + Real.log D / 2) * logPlus (2 * D / Qr)) + T3) := by
    by_cases hDM : M < D
    · rw [hT3def, if_pos hDM]
      have hMeq : M = Qr / 2 := by
        rcases min_choice (Qr / 2) D with h | h
        · rw [hMdef, h]
        · exfalso; rw [hMdef, h] at hDM; linarith
      set ξ := (a : ℝ) / q + δ / x
      have hξ : |ξ - a / q| = 1 / (q * Qr) := by
        simp only [ξ, add_sub_cancel_left]
        rw [eq_div_iff (by positivity)]; linarith [hexact]
      obtain ⟨a', q', hq'1, hcop', hq'Q', happ', hq'low⟩ := second_approx hq hcop hqQr hε hξ
      have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'1
      set δ' := x * (ξ - a' / q')
      have hδ'x : δ' / x = ξ - a' / q' := by simp only [δ']; field_simp
      have h2α' : 2 * α = a' / q' + δ' / x + k := by rw [hδ'x, h2α]; ring
      have hδ' : |δ' / x| * (q' * ((1 + ε) * Qr)) ≤ 1 := by
        rw [hδ'x]
        have := happ'
        rw [le_div_iff₀ (by positivity)] at this; linarith
      have hA2 := sum_R3W' hx hq'1 hcop' h2α' hq'Q' hδ' hM1 hDM (α := α)
      rw [← hc₁def, ← hBcdef] at hA2
      refine hA2.trans ?_
      have hDMlog : 0 ≤ Real.log (D / M) := Real.log_nonneg (by rw [le_div_iff₀ hM0]; linarith)
      have hlogeq : Real.log (D / M) ≤ logPlus (2 * D / Qr) := by
        rw [hMeq, show D / (Qr / 2) = 2 * D / Qr by field_simp]; exact le_max_left _ _
      have hxM : x / M ≤ 2 * (x / Q₀) := by
        rw [hMeq, show x / (Qr / 2) = 2 * (x / Qr) by field_simp]
        gcongr
      have hxq' : x / q' ≤ (1 + ε) / ε * (x / Q₀) := by
        have h1 : x / q' ≤ x / (ε * Qr / (1 + ε)) :=
          div_le_div_of_nonneg_left hx.le (by positivity) hq'low
        have h2 : x / (ε * Qr / (1 + ε)) = (1 + ε) / ε * (x / Qr) := by field_simp
        have h3 : x / Qr ≤ x / Q₀ := div_le_div_of_nonneg_left hx.le hQ₀0 hQ₀Qr
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      have hsqrt : √(1 + q' / M) ≤ √(3 + 2 * ε) := by
        apply Real.sqrt_le_sqrt
        rw [hMeq, div_div_eq_mul_div]
        have : (q' : ℝ) * 2 / Qr ≤ 2 * (1 + ε) := by
          rw [div_le_iff₀ hQrpos]; nlinarith
        linarith
      have hq'min : (q' : ℝ) ≤ (1 + ε) * Y := by
        refine hq'Q'.trans (mul_le_mul_of_nonneg_left (le_min hfl1 ?_) (by linarith))
        rw [hMeq] at hDM; linarith
      have hMq' : Real.log (M + q') ≤ Real.log (5 * D) := by
        refine Real.log_le_log (by positivity) ?_
        have : (q' : ℝ) ≤ 4 * D := by
          have : (q' : ℝ) ≤ (1 + ε) * Qr := hq'Q'
          rw [hMeq] at hDM; nlinarith
        linarith
      have hlMq : 0 ≤ Real.log (M + q') := Real.log_nonneg (by linarith)
      have hP1 : x * (Real.log (M + q') / M + Real.log D / q' * Real.log (D / M)) ≤
          (2 * Real.log (5 * D) + (1 + ε) / ε * Real.log D * logPlus (2 * D / Qr)) * (x / Q₀) := by
        have e : x * (Real.log (M + q') / M + Real.log D / q' * Real.log (D / M)) =
            (x / M) * Real.log (M + q') + (x / q') * (Real.log D * Real.log (D / M)) := by
          field_simp
        rw [e]
        have h1 : (x / M) * Real.log (M + q') ≤ (2 * (x / Q₀)) * Real.log (5 * D) :=
          mul_le_mul hxM hMq' hlMq (by positivity)
        have h2 : (x / q') * (Real.log D * Real.log (D / M)) ≤
            ((1 + ε) / ε * (x / Q₀)) * (Real.log D * logPlus (2 * D / Qr)) :=
          mul_le_mul hxq' (mul_le_mul_of_nonneg_left hlogeq hlogD) (by positivity) (by positivity)
        linarith
      have hP2 : q' * √(1 + q' / M) * Real.log (M + q') + 2 * q' * Real.log (D / M) +
            q' / 2 * Real.log D * Real.log (D / M) ≤
          (1 + ε) * Y * (√(3 + 2 * ε) * Real.log (5 * D) +
            (2 + Real.log D / 2) * logPlus (2 * D / Qr)) := by
        have h1 : √(1 + q' / M) * Real.log (M + q') ≤ √(3 + 2 * ε) * Real.log (5 * D) :=
          mul_le_mul hsqrt hMq' hlMq (by positivity)
        have h2 : 2 * Real.log (D / M) + Real.log D / 2 * Real.log (D / M) ≤
            (2 + Real.log D / 2) * logPlus (2 * D / Qr) := by
          have := mul_le_mul_of_nonneg_left hlogeq (show 0 ≤ 2 + Real.log D / 2 by positivity)
          linarith
        have hX : 0 ≤ √(3 + 2 * ε) * Real.log (5 * D) + (2 + Real.log D / 2) * logPlus (2 * D / Qr) := by
          positivity
        calc q' * √(1 + q' / M) * Real.log (M + q') + 2 * q' * Real.log (D / M) +
              q' / 2 * Real.log D * Real.log (D / M)
            = q' * (√(1 + q' / M) * Real.log (M + q') +
                (2 * Real.log (D / M) + Real.log D / 2 * Real.log (D / M))) := by ring
          _ ≤ q' * (√(3 + 2 * ε) * Real.log (5 * D) + (2 + Real.log D / 2) * logPlus (2 * D / Qr)) :=
              mul_le_mul_of_nonneg_left (add_le_add h1 h2) hq'0.le
          _ ≤ _ := mul_le_mul_of_nonneg_right hq'min hX
      have hk1 : 0 ≤ 3 * c₁ / 2 := by positivity
      have hP1' := mul_le_mul_of_nonneg_left hP1 hk1
      have hP2' := mul_le_mul_of_nonneg_left hP2 hBc
      linarith
    · rw [hT3def, if_neg hDM, Ioc_eq_empty (not_lt.2 (Int.floor_mono (not_lt.1 hDM))), sum_empty,
        add_zero]
      have : 0 ≤ 2 * Real.log (5 * D) + (1 + ε) / ε * Real.log D * logPlus (2 * D / Qr) := by
        positivity
      have : 0 ≤ (1 + ε) * Y * (√(3 + 2 * ε) * Real.log (5 * D) +
          (2 + Real.log D / 2) * logPlus (2 * D / Qr)) := by
        have : 0 ≤ Y := by linarith
        positivity
      positivity
  -- The `D log D` terms: `log M (2√c₀/π) M + Bc T3 ≤ Bc (D (log D - 1) + M)`.
  have hT : Real.log M * (2 * √c₀ / π * M) + Bc * T3 ≤ Bc * (D * (Real.log D - 1) + M) := by
    have h1 : Real.log M * (2 * √c₀ / π * M) ≤ Bc * (M * Real.log M) := by
      have := mul_le_mul_of_nonneg_right hBc' (mul_nonneg hM0.le hlogM)
      linarith
    by_cases hDM : M < D
    · rw [hT3def, if_pos hDM]
      have e : Bc * (M * Real.log M) + Bc * (D * (Real.log D - 1) - M * (Real.log M - 1)) =
          Bc * (D * (Real.log D - 1) + M) := by ring
      linarith
    · rw [hT3def, if_neg hDM, mul_zero, add_zero]
      have hMDe : M = D := le_antisymm hMD (not_lt.1 hDM)
      have e : Bc * (M * Real.log M) = Bc * (D * (Real.log D - 1) + M) := by rw [hMDe]; ring
      linarith
  -- Combine.
  refine (norm_restPartI2_le_sum hU hV).trans ?_
  rw [← hDdef]
  refine hsplit.trans ?_
  unfold bound_4_52
  simp only []
  rw [← hc₁def, ← hBcdef, ← hQrdef, ← hYdef]
  have hlogDe : Real.log (D / rexp 1) = Real.log D - 1 := by
    rw [Real.log_div hD0.ne' (by positivity), Real.log_exp]
  rw [hlogDe]
  have hMY : Bc * M ≤ Bc * ((1 + ε) * Y * (1 / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hBc
    nlinarith
  have hq : Real.log M * (35 * c₀ * c₂ / (3 * π ^ 2) * q) ≤ 35 * c₀ * c₂ / (3 * π ^ 2) * q * Real.log D := by
    have := mul_le_mul_of_nonneg_right hlogMD (show 0 ≤ 35 * c₀ * c₂ / (3 * π ^ 2) * q by positivity)
    linarith
  linarith

/-- **[H, Lemma 4.2.4], case (a)** (`|δ| ≥ 1/2c₂`), for `η = η₂`: (4.50) + (4.52), in our form
(`bound_4_50`, `bound_4_52`), with `M = Mof x δ q (UV)`. -/
theorem lemma_4_2_4_caseA {α x δ Q₀ U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀2 : 2 ≤ Q₀) (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hδ : 1 / (2 * c₂) ≤ |δ|) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_52 x δ q U V Q₀ ε := by
  obtain ⟨hq, hcop, ⟨k, h2α⟩, hδQ₀, hqQ₀⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hδpos : 0 < |δ| := lt_of_lt_of_le (by have := c₂_pos; positivity) hδ
  have hδ0 : δ ≠ 0 := abs_pos.1 hδpos
  have hD1 : 1 ≤ U * V := by nlinarith
  set M := Mof x δ q (U * V)
  have hMdef : M = min (x / (|δ| * q) / 2) (U * V) := by simp only [M, Mof, if_neg hδ0]
  have hMD : M ≤ U * V := by rw [hMdef]; exact min_le_right _ _
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_min (by positivity) (by linarith)
  have hMδ : |δ| * M ≤ x / 2 := by
    have h1 : |δ| * M ≤ |δ| * (x / (|δ| * q) / 2) := by
      rw [hMdef]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
    have h2 : |δ| * (x / (|δ| * q) / 2) = x / (2 * q) := by field_simp
    have h3 : x / (2 * q) ≤ x / 2 := div_le_div_of_nonneg_left hx.le (by norm_num)
      (by have : (1 : ℝ) ≤ q := by exact_mod_cast hq
          linarith)
    linarith
  rw [typeI2_eq_main_add_rest hx (by linarith) (by linarith) hM0]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_mainPartI2_le hx hq h2α hU hV hM0 hMδ hMD
  · exact norm_restPartI2_le_caseA hx hq hcop h2α hδQ₀ hqQ₀ hQ₀2 hδ (by linarith) (by linarith)
      hD1 hε hε1

/-- **[H, Lemma 4.2.4]** for `η = η₂`, in our form: the main term `bound_4_50` (factor `3/2`
added) and the error terms `bound_4_51`, `bound_4_52` (corrected `c₁`, cruder lower-order terms;
see their docstrings). Hypotheses: [H]'s `x ≥ e²c₂/2` is replaced by `x ≥ 10`; we need `UV ≥ 2`;
[H]'s `UV + (19/18)Q₀ ≤ x/5.6` and `Q₀ ≥ 2√x` are not needed (the latter only to turn `x/Q₀`
into `√x/2`). Depends only on the trusted `eta2_fourier_bound'` and the literature bounds
(2.12), (2.15), (2.20). -/
theorem lemma_4_2_4 {α x δ Q₀ U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀ : 2 * rexp 1 ≤ Q₀) (hx : 10 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hD2 : 2 ≤ U * V) :
    ((|δ| ≤ 1 / (2 * c₂) ∨ U * V ≤ Q₀ / 2) →
      ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_51 x q U V) ∧
    (1 / (2 * c₂) ≤ |δ| → ∀ ε, 0 < ε → ε ≤ 1 →
      ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_52 x δ q U V Q₀ ε) := by
  have hQ₀2 : 2 ≤ Q₀ := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  exact ⟨lemma_4_2_4_caseB h hx hU hV hD2,
    fun hδ ε hε hε1 => lemma_4_2_4_caseA h hQ₀2 (by linarith) hU hV hδ hε hε1⟩

end TernaryGoldbach.MinorArcs
