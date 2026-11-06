import TernaryGoldbach.MinorArcs.LSQuot1
import TernaryGoldbach.MinorArcs.SecondNumerics

/-!
# [H, Prop 12.2.4], part 2: the reduction

Notation: `R = Q₀/(sq)`, `t = Q/Q₀ ≥ 20000`, `l = log Q₀`, `L = log Q ≥ l/0.6`, `k = φ(q)/q`,
`e₁ = G_q(R) − k(log R + c + S_q)`, `e₂ = G_q(tR) − k(log tR + c + S_q)` with Ramaré's `c`.

* `star_suffices` ([H, (12.25)–(12.26)]): the conclusion of Prop 12.2.4 follows from
  `(q/φ(q)) (e₁ + 0.6274 max(0, −e₂)) ≤ 0.3726 (log sq − S_q) + 0.0274177`
  (since `θ = (l + 1.36)/(L + c) ≤ 0.6274`);
* `regionL`: this holds for `R ≥ λ(q)` by (12.12) ([H, (12.33)]);
* `checkC_suffices`: it holds if the finite check `checkC q ⌊R⌋` does;
* `regionS` ([H, Lemmas 12.2.1–12.2.3]): Prop 12.2.4 holds if `log q + 1.039 R ≤ c' (qR)^{2/9}` and
  `e^γ log c' + 2.50637/log log q ≤ 0.86`. Proof: `G_q(R) G_P(t) ≤ G_q(tR)` with
  `P = ∏_{p ≤ R or p ∣ q} p`, `G(t) ≤ (P/φ(P)) G_P(t)`, `G(t) ≥ log t + 1.064`, and
  `P/φ(P) < e^γ log log P + 2.50637/log log P` with `log P ≤ log q + 1.039 R`.

Note: [H]'s Lemma 12.2.3 bounds the quotient by `(log Q₀ + σ)/(log Q + 1.312)`, while (12.23) has
`log Q + c_E` in the denominator; with `σ = c₊ = 1.36` the former does not imply the latter. Our
`regionS` proves the bound with `c_E` directly.
-/

open Real Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `κ(q) = 0.3726 (log q − S_q) + 0.0274177` ([H, (12.31)] with `ω = 0.6274`, `c_Δ = 1.36 − c_E`). -/
noncomputable def kapQ (q : ℕ) : ℝ := 0.3726 * (Real.log q - Sq q) + 0.0274177

/-- `λ(q) = ((q/φ(q)) · 7.4527 f₁(q)/κ(q))³` ([H, (12.33)]). -/
noncomputable def lamQ (q : ℕ) : ℝ := ((q : ℝ) / Nat.totient q * 7.4527 * f1q q / kapQ q) ^ 3

/-- The finite check at `R ∈ [n, n+1)` ([H, (12.31)], strengthened by `log sq ≥ log(10⁵/(n+1))`). -/
def checkC (q n : ℕ) : Prop :=
  (q : ℝ) / Nat.totient q * Gq q n - Real.log n - 1.3325822 - Sq q +
      0.1687 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) ≤
    0.3726 * (max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1))) - Sq q) + 0.0274177

/-! ### Elementary facts -/

theorem f1p_pos (p : ℕ) : 0 < f1p p := by
  unfold f1p
  rcases Nat.lt_or_ge p 2 with h | h
  · interval_cases p <;> simp
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
    apply div_pos (by positivity)
    have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    positivity

theorem f1q_pos (q : ℕ) : 0 < f1q q := prod_pos fun p _ => f1p_pos p

theorem qphi_pos {q : ℕ} (hq : 1 ≤ q) : 0 < (q : ℝ) / Nat.totient q := by
  have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have : (0 : ℝ) < q := by exact_mod_cast hq
  positivity

theorem kapQ_pos {q : ℕ} (hq : 1 ≤ q) : 0.0274177 ≤ kapQ q := by
  unfold kapQ; have := Sq_le_log hq; nlinarith

theorem log_1e5_ge : 11.5 ≤ Real.log 1e5 := by
  have := le_log_num (z := 1e5) 11 0.5 (by norm_num) (by norm_num)
    (by unfold taylor6; norm_num)
  push_cast at this; linarith

/-- `t^{−1/3} ≤ 0.03685` for `t ≥ 20000`. -/
theorem rpow_neg_third_le {t : ℝ} (ht : 20000 ≤ t) : t ^ (-(1 / 3 : ℝ)) ≤ 0.03685 := by
  have h1 : (27.14 : ℝ) ≤ t ^ (1 / 3 : ℝ) := by
    calc (27.14 : ℝ) = ((27.14 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ t ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  rw [Real.rpow_neg (by linarith), ← one_div]
  calc 1 / t ^ (1 / 3 : ℝ) ≤ 1 / 27.14 := one_div_le_one_div_of_le (by norm_num) h1
    _ ≤ 0.03685 := by norm_num

/-! ### The reduction ([H, (12.25)–(12.26)]) -/

/-- The algebra of the reduction: with `θ = (l + 1.36)/(L + c) ≤ 0.6274`. -/
theorem star_core {k K l L a S c e1 e2 : ℝ} (hk : 0 < k) (hkK : k * K = 1) (hl : 11.5 ≤ l)
    (hρ : l ≤ 0.6 * L) (hc1 : 1.3325822 ≤ c) (hc2 : c ≤ 1.3325823) (haS : S ≤ a)
    (hst : K * (e1 + 0.6274 * max 0 (-e2)) ≤ 0.3726 * (a - S) + 0.0274177)
    (hG2 : 0 ≤ k * (L - a + c + S) + e2) :
    k * (l - a + c + S) + e1 ≤ (l + 1.36) / (L + 1.33258) * (k * (L - a + c + S) + e2) := by
  have hLc : 0 < L + c := by linarith
  set θ := (l + 1.36) / (L + c) with hθ
  have hθ1 : θ ≤ 0.6274 := by rw [hθ, div_le_iff₀ hLc]; nlinarith
  have hθL : θ * (L + c) = l + 1.36 := by rw [hθ]; field_simp
  have hst' : e1 + 0.6274 * max 0 (-e2) ≤ k * (0.3726 * (a - S) + 0.0274177) := by
    have := mul_le_mul_of_nonneg_left hst hk.le
    rwa [← mul_assoc, hkK, one_mul] at this
  have hmax : -e2 ≤ max 0 (-e2) := le_max_right _ _
  have hmax0 : 0 ≤ max 0 (-e2) := le_max_left _ _
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hLc.le
  have h1 : e1 - θ * e2 ≤ e1 + 0.6274 * max 0 (-e2) := by nlinarith
  have h2 : k * (0.3726 * (a - S) + 0.0274177) ≤ k * ((1.36 - c) + (1 - θ) * (a - S)) := by
    apply mul_le_mul_of_nonneg_left _ hk.le; nlinarith
  have key : k * (l - a + c + S) + e1 ≤ θ * (k * (L - a + c + S) + e2) := by nlinarith
  have hθ' : θ ≤ (l + 1.36) / (L + 1.33258) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  exact key.trans (mul_le_mul_of_nonneg_right hθ' hG2)

/-- **The reduction.** -/
theorem star_suffices {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    {c : ℝ} (hc1 : 1.3325822 ≤ c) (hc2 : c ≤ 1.3325823)
    (hstar : (q : ℝ) / Nat.totient q *
        ((Gq q (Q₀ / (s * q)) - (Nat.totient q / q) * (Real.log (Q₀ / (s * q)) + c + Sq q)) +
          0.6274 * max 0 (-(Gq q (Q / (s * q)) -
            (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q)))) ≤
      0.3726 * (Real.log (s * q) - Sq q) + 0.0274177) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hQ₀0 : 0 < Q₀ := by linarith
  have hQ0 : 0 < Q := by linarith
  have hsq : 0 < s * q := by positivity
  have hkK : (Nat.totient q : ℝ) / q * ((q : ℝ) / Nat.totient q) = 1 := by field_simp
  have hl5 : 11.5 ≤ Real.log Q₀ := le_trans log_1e5_ge (Real.log_le_log (by norm_num) hQ₀)
  have haS : Sq q ≤ Real.log (s * q) :=
    (Sq_le_log hq).trans (Real.log_le_log hq0 (by nlinarith))
  have hlog1 : Real.log (Q₀ / (s * q)) = Real.log Q₀ - Real.log (s * q) :=
    Real.log_div hQ₀0.ne' hsq.ne'
  have hlog2 : Real.log (Q / (s * q)) = Real.log Q - Real.log (s * q) :=
    Real.log_div hQ0.ne' hsq.ne'
  have h := star_core (k := (Nat.totient q : ℝ) / q) (K := (q : ℝ) / Nat.totient q)
    (l := Real.log Q₀) (L := Real.log Q) (a := Real.log (s * q)) (S := Sq q) (c := c)
    (e1 := Gq q (Q₀ / (s * q)) - (Nat.totient q / q) * (Real.log (Q₀ / (s * q)) + c + Sq q))
    (e2 := Gq q (Q / (s * q)) - (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))
    (by positivity) hkK hl5 hρ hc1 hc2 haS hstar (by rw [hlog2]; linarith [Gq_nonneg_q q (Q / (s * q))])
  rw [hlog1, hlog2] at h
  unfold cE
  convert h using 2 <;> ring

/-! ### Ramaré's estimate at `R` and `tR` -/

theorem Q_div_ge {Q Q₀ s : ℝ} {q : ℕ} (hQ : 20000 * Q₀ ≤ Q) (hsq : 0 < s * q) :
    20000 * (Q₀ / (s * q)) ≤ Q / (s * q) := by
  rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hQ hsq.le

/-- `max(0, −e₂) ≤ 7.284 · 0.03685 · R^{−1/3} f₁(q)`. -/
theorem e2_bound {Q Q₀ s c : ℝ} {q : ℕ} (hq : 1 ≤ q) (hQ : 20000 * Q₀ ≤ Q) (hs : 1 ≤ s)
    (hR : 1 ≤ Q₀ / (s * q))
    (hram : ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 1 ≤ R →
      |Gq d R - (Nat.totient d / d) * (Real.log R + c + Sq d)| ≤ 7.284 * R ^ (-(1 / 3 : ℝ)) * f1q d) :
    max 0 (-(Gq q (Q / (s * q)) - (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))) ≤
      7.284 * 0.03685 * (Q₀ / (s * q)) ^ (-(1 / 3 : ℝ)) * f1q q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  set R := Q₀ / (s * q)
  have htR := Q_div_ge (q := q) hQ hsq
  have hTR : 1 ≤ Q / (s * q) := by linarith
  have h := hram q hq _ hTR
  have hf := f1q_pos q
  have hR0 : 0 < R := by linarith
  -- `(Q/(sq))^{−1/3} = (t)^{−1/3} R^{−1/3}` with `t ≥ 20000`
  have ht : 20000 ≤ (Q / (s * q)) / R := by rw [le_div_iff₀ hR0]; linarith
  have e : Q / (s * q) = (Q / (s * q)) / R * R := by field_simp
  have hpow : (Q / (s * q)) ^ (-(1 / 3 : ℝ)) ≤ 0.03685 * R ^ (-(1 / 3 : ℝ)) := by
    rw [e, Real.mul_rpow (by linarith) hR0.le]
    exact mul_le_mul_of_nonneg_right (rpow_neg_third_le ht) (by positivity)
  refine max_le (by positivity) ?_
  have h2 := (abs_le.1 h).1
  calc _ ≤ 7.284 * (Q / (s * q)) ^ (-(1 / 3 : ℝ)) * f1q q := by linarith
    _ ≤ 7.284 * (0.03685 * R ^ (-(1 / 3 : ℝ))) * f1q q := by gcongr
    _ = _ := by ring

/-! ### Large `R`: Ramaré's estimate suffices ([H, (12.33)]) -/

theorem regionL {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    (hR : 1 ≤ Q₀ / (s * q)) (hlam : lamQ q ≤ Q₀ / (s * q)) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  obtain ⟨c, hc1, hc2, hram⟩ := ramare_Gq
  refine star_suffices hQ hQ₀ hρ hq hs hc1 hc2 ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  set R := Q₀ / (s * q)
  have hR0 : 0 < R := by linarith
  set K := (q : ℝ) / Nat.totient q
  have hK := qphi_pos hq
  have hf := f1q_pos q
  have hκ := kapQ_pos hq
  have he1 := (abs_le.1 (hram q hq R hR)).2
  have he2 := e2_bound hq hQ hs hR hram
  -- `K · 7.4527 f₁ R^{−1/3} ≤ κ(q)`
  set X := K * 7.4527 * f1q q / kapQ q
  have hX0 : 0 < X := by positivity
  have hXR : X ≤ R ^ (1 / 3 : ℝ) := by
    have h1 : (X ^ 3) ^ (1 / 3 : ℝ) ≤ R ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlam (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
      Real.rpow_one] at h1
  have hR3 : 0 < R ^ (1 / 3 : ℝ) := by positivity
  have hRneg : R ^ (-(1 / 3 : ℝ)) = 1 / R ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg hR0.le, inv_eq_one_div]
  have hmain : K * 7.4527 * f1q q * R ^ (-(1 / 3 : ℝ)) ≤ kapQ q := by
    rw [hRneg, mul_one_div, div_le_iff₀ hR3]
    have : K * 7.4527 * f1q q = X * kapQ q := by simp only [X]; field_simp
    rw [this]; nlinarith
  have hloga : Real.log q ≤ Real.log (s * q) := Real.log_le_log hq0 (by nlinarith)
  have hRp : 0 ≤ R ^ (-(1 / 3 : ℝ)) := by positivity
  calc K * ((Gq q R - (Nat.totient q / q) * (Real.log R + c + Sq q)) +
        0.6274 * max 0 (-(Gq q (Q / (s * q)) -
          (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))))
      ≤ K * (7.284 * R ^ (-(1 / 3 : ℝ)) * f1q q +
          0.6274 * (7.284 * 0.03685 * R ^ (-(1 / 3 : ℝ)) * f1q q)) := by gcongr
    _ ≤ K * 7.4527 * f1q q * R ^ (-(1 / 3 : ℝ)) := by
        have : 0 ≤ K * f1q q * R ^ (-(1 / 3 : ℝ)) := by positivity
        nlinarith
    _ ≤ kapQ q := hmain
    _ ≤ _ := by unfold kapQ; nlinarith

/-! ### The finite check suffices -/

theorem checkC_suffices {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    (hR : 1 ≤ Q₀ / (s * q)) (hC : checkC q ⌊Q₀ / (s * q)⌋₊) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  obtain ⟨c, hc1, hc2, hram⟩ := ramare_Gq
  refine star_suffices hQ hQ₀ hρ hq hs hc1 hc2 ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  set R := Q₀ / (s * q)
  set n := ⌊R⌋₊
  have hR0 : 0 < R := by linarith
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hR)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR : (n : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRn : R < (n : ℝ) + 1 := Nat.lt_floor_add_one R
  set K := (q : ℝ) / Nat.totient q
  have hK := qphi_pos hq
  have hKk : K * (Nat.totient q / q) = 1 := by
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    simp only [K]; field_simp
  have hf := f1q_pos q
  have he2 := e2_bound hq hQ hs hR hram
  have hGn : Gq q R = Gq q n := by unfold Gq; rw [Nat.floor_natCast]
  -- `R^{−1/3} ≤ n^{−1/3}`
  have hRn3 : R ^ (-(1 / 3 : ℝ)) ≤ 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg hR0.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow hn0.le hnR (by norm_num))
  -- the right sides: `log sq ≥ max(log q, log(10⁵/(n+1)))`
  have hsqR : s * q = Q₀ / R := by simp only [R]; field_simp
  have hmax : max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1))) ≤ Real.log (s * q) := by
    refine max_le (Real.log_le_log hq0 (by nlinarith)) ?_
    rw [hsqR]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) hR0]; nlinarith
  have hlogR : Real.log n ≤ Real.log R := Real.log_le_log hn0 hnR
  unfold checkC at hC
  have hmx0 : 0 ≤ max 0 (-(Gq q (Q / (s * q)) -
      (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))) := le_max_left _ _
  calc K * ((Gq q R - (Nat.totient q / q) * (Real.log R + c + Sq q)) +
        0.6274 * max 0 (-(Gq q (Q / (s * q)) -
          (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))))
      = K * Gq q n - (Real.log R + c + Sq q) + K * (0.6274 * max 0 (-(Gq q (Q / (s * q)) -
          (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q)))) := by
        rw [hGn, mul_add, mul_sub, ← mul_assoc, hKk, one_mul]
    _ ≤ K * Gq q n - (Real.log n + 1.3325822 + Sq q) +
          K * (0.6274 * (7.284 * 0.03685 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) * f1q q)) := by
        gcongr
        exact he2.trans (by gcongr)
    _ ≤ K * Gq q n - Real.log n - 1.3325822 - Sq q +
          0.1687 * K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) := by
        have : 0 ≤ K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
        rw [mul_one_div]
        have e : K * (0.6274 * (7.284 * 0.03685 / (n : ℝ) ^ (1 / 3 : ℝ) * f1q q)) =
            0.6274 * 7.284 * 0.03685 * (K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
        have e2 : 0.1687 * K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) =
            0.1687 * (K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
        rw [e, e2]; nlinarith
    _ ≤ 0.3726 * (max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1))) - Sq q) + 0.0274177 := hC
    _ ≤ 0.3726 * (Real.log (s * q) - Sq q) + 0.0274177 := by gcongr

end TernaryGoldbach.MinorArcs
