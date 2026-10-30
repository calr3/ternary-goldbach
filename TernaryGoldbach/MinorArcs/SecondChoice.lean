import TernaryGoldbach.MinorArcs.TypeI

/-!
# The second choice of parameters [B, §6.3.2]: re-approximation and case split

For `q > y = x^{1/3}/6`, [B] re-approximates `2α` with a smaller `Q₀` (we take `Q₀ ≥ 3.5x/U`, see
`NOTES.md`). With `a'/q'` the new approximation, either
* (a) `q' > y`, or
* (b) `q' ≤ y`, `|δ'| > 8` and `|δ'|q' > 8y`, or
* (c) `q' ≤ y` and `|δ'| ≤ 8y/q'` (the case [B] overlooks): then `a'/q'` is also an approximation
  for `Q = (3/4)x^{2/3}`, and the coexistence with `a/q` (`q > y`) forces `δ₀'q' ≥ 2y(1 - y/Q)`.

* `exists_approx2`: Dirichlet's approximation theorem in the form `Approx2`;
* `approx_gap`: two approximations with different denominators are `1/qq'` apart;
* **`second_case_split`**.
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- Dirichlet: for `Q ≥ 1` there is an approximation `2α = a/q + δ/x (mod 1)` with `q ≤ Q`,
`|δ/x| ≤ 1/qQ`. -/
theorem exists_approx2 (α : ℝ) {x : ℝ} (hx : 0 < x) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ (δ : ℝ) (a : ℤ) (q : ℕ), Approx2 α x δ a q Q := by
  set n := ⌊Q⌋₊
  have hn : 0 < n := Nat.floor_pos.2 hQ
  obtain ⟨r, hr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (2 * α) hn
  have hq1 : 1 ≤ r.den := r.den_pos
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast hq1
  have hcast : (r : ℝ) = r.num / r.den := Rat.cast_def r
  refine ⟨x * (2 * α - r.num / r.den), r.num, r.den, hq1, ?_, ⟨0, ?_⟩, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]; exact r.reduced
  · field_simp; push_cast; ring
  · rw [mul_div_cancel_left₀ _ hx.ne', ← hcast]
    refine hr.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    rw [mul_comm (r.den : ℝ)]
    exact mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one Q).le hq0.le
  · exact le_trans (by exact_mod_cast hrden) (Nat.floor_le (by linarith))

/-- Two approximations of `2α` with different denominators: `1/qq' ≤ |δ/x - δ'/x|`. -/
theorem approx_gap {α x δ δ' Q Q' : ℝ} {a a' : ℤ} {q q' : ℕ} (h : Approx2 α x δ a q Q)
    (h' : Approx2 α x δ' a' q' Q') (hne : q ≠ q') :
    1 / ((q : ℝ) * q') ≤ |δ / x - δ' / x| := by
  obtain ⟨hq, hcop, ⟨k, hk⟩, -, -⟩ := h
  obtain ⟨hq', hcop', ⟨k', hk'⟩, -, -⟩ := h'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  set N : ℤ := a' * q - a * q' + (k' - k) * q * q'
  have hN : N ≠ 0 := by
    intro hN0
    have h1 : (q : ℤ) ∣ q' := by
      have : (q : ℤ) ∣ a * q' := ⟨a' + (k' - k) * q', by
        have : a' * q - a * q' + (k' - k) * q * q' = 0 := hN0
        linear_combination -this⟩
      exact hcop.symm.dvd_of_dvd_mul_left this
    have h2 : (q' : ℤ) ∣ q := by
      have : (q' : ℤ) ∣ a' * q := ⟨a + (k - k') * q, by
        have : a' * q - a * q' + (k' - k) * q * q' = 0 := hN0
        linear_combination this⟩
      exact hcop'.symm.dvd_of_dvd_mul_left this
    exact hne (by exact_mod_cast Int.dvd_antisymm (by positivity) (by positivity) h1 h2)
  have e : δ / x - δ' / x = (N : ℝ) / (q * q') := by
    simp only [N]; push_cast
    field_simp
    have := congrArg (· * ((q : ℝ) * q')) (hk.symm.trans hk')
    field_simp at this
    linear_combination this
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Int.one_le_abs hN

/-- **The case split of [B, §6.3.2]**, corrected. Here `x = T³`, `y = T/6`, `Q = (3/4)T²`; `a/q`
is the given approximation (`q > y`) and `a'/q'` the new one (any `Q₀`). -/
theorem second_case_split {α T δ δ' Q₀ : ℝ} {a a' : ℤ} {q q' : ℕ} (hT : 1 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (3 / 4 * T ^ 2)) (hq : T / 6 < q)
    (h' : Approx2 α (T ^ 3) δ' a' q' Q₀) :
    T / 6 < q' ∨ ((q' : ℝ) ≤ T / 6 ∧ 8 < |δ'| ∧ 8 * (T / 6) < |δ'| * q') ∨
      ((q' : ℝ) ≤ T / 6 ∧ Approx2 α (T ^ 3) δ' a' q' (3 / 4 * T ^ 2) ∧
        2 * (T / 6) * (1 - (T / 6) / (3 / 4 * T ^ 2)) ≤ |δ'| * q' / 4) := by
  rcases lt_or_ge (T / 6) (q' : ℝ) with h1 | h1
  · exact Or.inl h1
  right
  have hT0 : 0 < T := by linarith
  have hx : 0 < T ^ 3 := by positivity
  obtain ⟨hq'1, hcop', hk', hδQ₀, hqQ₀⟩ := h'
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'1
  rcases lt_or_ge (8 * (T / 6)) (|δ'| * q') with h2 | h2
  · left
    refine ⟨h1, ?_, h2⟩
    by_contra h3; push Not at h3
    have : |δ'| * q' ≤ 8 * (T / 6) := mul_le_mul h3 h1 hq'0.le (by norm_num)
    linarith
  right
  have happ : Approx2 α (T ^ 3) δ' a' q' (3 / 4 * T ^ 2) := by
    refine ⟨hq'1, hcop', hk', ?_, by nlinarith⟩
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)]
    have : |δ'| * q' * (3 / 4 * T ^ 2) ≤ 8 * (T / 6) * (3 / 4 * T ^ 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have e : 8 * (T / 6) * (3 / 4 * T ^ 2) = 1 * T ^ 3 := by ring
    linarith [show |δ'| * (q' * (3 / 4 * T ^ 2)) = |δ'| * q' * (3 / 4 * T ^ 2) by ring]
  refine ⟨h1, happ, ?_⟩
  -- The gap between the two approximations.
  have hne : q ≠ q' := by
    intro he; rw [he] at hq; linarith
  have hgap := approx_gap h happ hne
  obtain ⟨hq1, -, -, hδQ, hqQ⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set Q := 3 / 4 * T ^ 2
  have hQ0 : 0 < Q := by positivity
  have htri : |δ / T ^ 3 - δ' / T ^ 3| ≤ 1 / (q * Q) + |δ'| / T ^ 3 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_div (δ') _, abs_of_pos hx]; linarith
  -- `1/(q q') - 1/(q Q) ≤ |δ'|/T³`, then multiply by `q' Q`... and use `q ≤ Q`.
  have key : 1 / ((q : ℝ) * q') - 1 / (q * Q) ≤ |δ'| / T ^ 3 := by linarith
  have e1 : 1 / ((q : ℝ) * q') - 1 / (q * Q) = (Q - q') / (q * q' * Q) := by
    field_simp
  rw [e1] at key
  have hQq' : (q' : ℝ) ≤ Q := by simp only [Q]; nlinarith
  have k2 : (Q - q') / (Q * q' * Q) ≤ (Q - q') / (q * q' * Q) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqQ hq'0.le) hQ0.le
  have k3 : (Q - q') / (Q * q' * Q) ≤ |δ'| / T ^ 3 := k2.trans key
  rw [div_le_div_iff₀ (by positivity) hx] at k3
  -- `(Q - q') T³ ≤ |δ'| q' Q²`, and `T³ = (8T/6) Q`.
  have hT3 : T ^ 3 = 8 * (T / 6) * Q := by simp only [Q]; ring
  rw [hT3] at k3
  have k4 : 8 * (T / 6) * (Q - q') ≤ |δ'| * q' * Q := by
    have : (Q - q') * (8 * (T / 6) * Q) = 8 * (T / 6) * (Q - q') * Q := by ring
    rw [this] at k3
    have : |δ'| * (Q * q' * Q) = |δ'| * q' * Q * Q := by ring
    rw [this] at k3
    exact le_of_mul_le_mul_right k3 hQ0
  have k5 : 8 * (T / 6) * (Q - T / 6) ≤ 8 * (T / 6) * (Q - q') :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have : 2 * (T / 6) * (1 - T / 6 / Q) = 8 * (T / 6) * (Q - T / 6) / Q / 4 := by
    field_simp; ring
  rw [this, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

end TernaryGoldbach.MinorArcs
