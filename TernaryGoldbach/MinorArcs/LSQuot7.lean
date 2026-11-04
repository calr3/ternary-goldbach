import TernaryGoldbach.MinorArcs.LSQuot5

/-!
# [H, Prop 12.2.4] with `c₊ = 2`, part 1: the reduction to `Φ(q, n) ≤ 0`

With `c₊ = 2` in place of [H]'s `1.36`, the reduction [H, (12.25)–(12.26)] goes through with
`θ = (l + 2)/(L + c) ≤ ω = 0.6586`, and Prop 12.2.4 at `R ∈ [n, n+1)` follows from
`Φ(q, n, L) ≤ 0` for any `L ≤ log sq` (`checkC2_suffices`), where
`Φ(q, n, L) = (q/φ(q)) G_q(n) − log n − 1.3325822 − S_q + 0.1768 (q/φ(q)) f₁(q) n^{−1/3}
  − (0.3414 (L − S_q) + 0.6674177)`.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-- `Φ(q, n, L)`. -/
noncomputable def Phi2 (q n : ℕ) (L : ℝ) : ℝ :=
  (q : ℝ) / Nat.totient q * Gq q n - Real.log n - 1.3325822 - Sq q +
    0.1768 * ((q : ℝ) / Nat.totient q) * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) -
    (0.3414 * (L - Sq q) + 0.6674177)

theorem Phi2_anti (q n : ℕ) {L L' : ℝ} (h : L ≤ L') : Phi2 q n L' ≤ Phi2 q n L := by
  unfold Phi2; linarith

/-- The algebra of the reduction with `c₊ = 2`: `θ = (l + 2)/(L + c) ≤ 0.6586`. -/
theorem star_core2 {k K l L a S c e1 e2 : ℝ} (hk : 0 < k) (hkK : k * K = 1) (hl : 11.5 ≤ l)
    (hρ : l ≤ 0.6 * L) (hc1 : 1.3325822 ≤ c) (hc2 : c ≤ 1.3325823) (haS : S ≤ a)
    (hst : K * (e1 + 0.6586 * max 0 (-e2)) ≤ 0.3414 * (a - S) + 0.6674177)
    (hG2 : 0 ≤ k * (L - a + c + S) + e2) :
    k * (l - a + c + S) + e1 ≤ (l + 2) / (L + 1.33258) * (k * (L - a + c + S) + e2) := by
  have hLc : 0 < L + c := by linarith
  set θ := (l + 2) / (L + c) with hθ
  have hθ1 : θ ≤ 0.6586 := by rw [hθ, div_le_iff₀ hLc]; nlinarith
  have hθL : θ * (L + c) = l + 2 := by rw [hθ]; field_simp
  have hst' : e1 + 0.6586 * max 0 (-e2) ≤ k * (0.3414 * (a - S) + 0.6674177) := by
    have := mul_le_mul_of_nonneg_left hst hk.le
    rwa [← mul_assoc, hkK, one_mul] at this
  have hmax : -e2 ≤ max 0 (-e2) := le_max_right _ _
  have hmax0 : 0 ≤ max 0 (-e2) := le_max_left _ _
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hLc.le
  have h1 : e1 - θ * e2 ≤ e1 + 0.6586 * max 0 (-e2) := by nlinarith
  have h2 : k * (0.3414 * (a - S) + 0.6674177) ≤ k * ((2 - c) + (1 - θ) * (a - S)) := by
    apply mul_le_mul_of_nonneg_left _ hk.le; nlinarith
  have key : k * (l - a + c + S) + e1 ≤ θ * (k * (L - a + c + S) + e2) := by nlinarith
  have hθ' : θ ≤ (l + 2) / (L + 1.33258) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  exact key.trans (mul_le_mul_of_nonneg_right hθ' hG2)

theorem star_suffices2 {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    {c : ℝ} (hc1 : 1.3325822 ≤ c) (hc2 : c ≤ 1.3325823)
    (hstar : (q : ℝ) / Nat.totient q *
        ((Gq q (Q₀ / (s * q)) - (Nat.totient q / q) * (Real.log (Q₀ / (s * q)) + c + Sq q)) +
          0.6586 * max 0 (-(Gq q (Q / (s * q)) -
            (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q)))) ≤
      0.3414 * (Real.log (s * q) - Sq q) + 0.6674177) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 2) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ₀0 : 0 < Q₀ := by linarith
  have hQ0 : 0 < Q := by linarith
  have hsq : 0 < s * q := by positivity
  have hkK : (Nat.totient q : ℝ) / q * ((q : ℝ) / Nat.totient q) = 1 := by
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    field_simp
  have hl5 : 11.5 ≤ Real.log Q₀ := le_trans log_1e5_ge (Real.log_le_log (by norm_num) hQ₀)
  have haS : Sq q ≤ Real.log (s * q) :=
    (Sq_le_log hq).trans (Real.log_le_log hq0 (by nlinarith))
  have hlog1 : Real.log (Q₀ / (s * q)) = Real.log Q₀ - Real.log (s * q) :=
    Real.log_div hQ₀0.ne' hsq.ne'
  have hlog2 : Real.log (Q / (s * q)) = Real.log Q - Real.log (s * q) :=
    Real.log_div hQ0.ne' hsq.ne'
  have h := star_core2 (k := (Nat.totient q : ℝ) / q) (K := (q : ℝ) / Nat.totient q)
    (l := Real.log Q₀) (L := Real.log Q) (a := Real.log (s * q)) (S := Sq q) (c := c)
    (e1 := Gq q (Q₀ / (s * q)) - (Nat.totient q / q) * (Real.log (Q₀ / (s * q)) + c + Sq q))
    (e2 := Gq q (Q / (s * q)) - (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))
    (by positivity) hkK hl5 hρ hc1 hc2 haS hstar
    (by rw [hlog2]; linarith [Gq_nonneg_q q (Q / (s * q))])
  rw [hlog1, hlog2] at h
  unfold cE
  convert h using 2 <;> ring

/-- **The reduction to `Φ`**: Prop 12.2.4 with `c₊ = 2` holds at `R = Q₀/sq` if
`Φ(q, ⌊R⌋, max(log q, log(10⁵/(⌊R⌋ + 1)))) ≤ 0`. -/
theorem checkC2_suffices {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s)
    (hR : 1 ≤ Q₀ / (s * q))
    (hC : Phi2 q ⌊Q₀ / (s * q)⌋₊
      (max (Real.log q) (Real.log (1e5 / ((⌊Q₀ / (s * q)⌋₊ : ℝ) + 1)))) ≤ 0) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 2) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  obtain ⟨c, hc1, hc2, hram⟩ := ramare_Gq
  refine star_suffices2 hQ hQ₀ hρ hq hs hc1 hc2 ?_
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
  have hRn3 : R ^ (-(1 / 3 : ℝ)) ≤ 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg hR0.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow hn0.le hnR (by norm_num))
  have hsqR : s * q = Q₀ / R := by simp only [R]; field_simp
  have hmax : max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1))) ≤ Real.log (s * q) := by
    refine max_le (Real.log_le_log hq0 (by nlinarith)) ?_
    rw [hsqR]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) hR0]; nlinarith
  have hlogR : Real.log n ≤ Real.log R := Real.log_le_log hn0 hnR
  unfold Phi2 at hC
  have hmx0 : 0 ≤ max 0 (-(Gq q (Q / (s * q)) -
      (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))) := le_max_left _ _
  calc K * ((Gq q R - (Nat.totient q / q) * (Real.log R + c + Sq q)) +
        0.6586 * max 0 (-(Gq q (Q / (s * q)) -
          (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q))))
      = K * Gq q n - (Real.log R + c + Sq q) + K * (0.6586 * max 0 (-(Gq q (Q / (s * q)) -
          (Nat.totient q / q) * (Real.log (Q / (s * q)) + c + Sq q)))) := by
        rw [hGn, mul_add, mul_sub, ← mul_assoc, hKk, one_mul]
    _ ≤ K * Gq q n - (Real.log n + 1.3325822 + Sq q) +
          K * (0.6586 * (7.284 * 0.03685 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) * f1q q)) := by
        gcongr
        exact he2.trans (by gcongr)
    _ ≤ K * Gq q n - Real.log n - 1.3325822 - Sq q +
          0.1768 * K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) := by
        have : 0 ≤ K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
        rw [mul_one_div]
        have e : K * (0.6586 * (7.284 * 0.03685 / (n : ℝ) ^ (1 / 3 : ℝ) * f1q q)) =
            0.6586 * 7.284 * 0.03685 * (K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
        have e2 : 0.1768 * K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ) =
            0.1768 * (K * f1q q / (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
        rw [e, e2]; nlinarith
    _ ≤ 0.3414 * (max (Real.log q) (Real.log (1e5 / ((n : ℝ) + 1))) - Sq q) + 0.6674177 := by
        linarith
    _ ≤ 0.3414 * (Real.log (s * q) - Sq q) + 0.6674177 := by gcongr

end TernaryGoldbach.MinorArcs
