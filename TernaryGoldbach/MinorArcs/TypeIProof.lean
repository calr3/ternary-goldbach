import TernaryGoldbach.MinorArcs.TypeI
import TernaryGoldbach.MinorArcs.BlockSums

/-!
# Proof of [B, Lemma 4.2.2] (Type I sums with odd `m`, `n`; `η = η₂`)

Building blocks, following [B, proofs of Lemmas 4.2.1–4.2.2]:
* `approx_of`, `sin_sq_two_pi_mul`, `sin_ne_zero_of_approx`: the approximation `2α ≈ a/q`
  in the form taken by Lemmas 4.1.1–4.1.3.
* `norm_Todd_le_minA`, `norm_Todd_le_min_sin`: [B, (4.36)] in the shapes Lemmas 4.1.1–4.1.3 use.
* `sum_R1`, `sum_R2`, `sum_R3`: the three ranges of case (b), [B, (4.23)–(4.27)], adapted to
  odd `n` as described in [B, proof of Lemma 4.2.2].
* `norm_mainPart_le`: the terms with `q ∣ m ≤ M`, [B, (4.30)].
-/

open Real Finset
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- From `2α = a/q + δ/x + k`, `|δ/x| ≤ 1/(qQ)`: `a/q + δ/x` is an `Approx` with parameter `Q`. -/
theorem approx_of {x δ Q : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hqQ : (q : ℝ) ≤ Q) (hδ : |δ / x| * (q * Q) ≤ 1) : Approx (a / q + δ / x) a q Q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : 0 < Q := by linarith
  refine ⟨hq, hcop, δ / x * (q * Q), ?_, ?_, hqQ⟩
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q * Q)]; exact hδ
  · field_simp

theorem sin_sq_two_pi_mul {α x δ : ℝ} {a k : ℤ} {q : ℕ} (h2α : 2 * α = a / q + δ / x + k) (m : ℝ)
    (hm : ∃ j : ℤ, m = j) :
    Real.sin (2 * π * m * α) ^ 2 = Real.sin (π * (a / q + δ / x) * m) ^ 2 := by
  obtain ⟨j, rfl⟩ := hm
  have : 2 * π * (j : ℝ) * α = π * (a / q + δ / x) * j + ((j * k : ℤ) : ℝ) * π := by
    have : α = (a / q + δ / x + k) / 2 := by linarith
    rw [this]; push_cast; ring
  rw [this, sin_sq_add_int_mul_pi]

/-- For `q ∤ n` and `|n| ≤ Q/2`, `sin(π(a/q + β/(qQ))n) ≠ 0`. -/
theorem sin_ne_zero_of_approx {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {n : ℤ}
    (hn : ¬ (q : ℤ) ∣ n) (hnQ : |(n : ℝ)| ≤ Q / 2) : Real.sin (π * α * n) ≠ 0 := by
  obtain ⟨hq1, hcop, β, hβ, hα, hqQ⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := by linarith
  intro h0
  rw [Real.sin_eq_zero_iff] at h0
  obtain ⟨N, hN⟩ := h0
  -- `a n - N q = -β n / Q`, an integer of absolute value `≤ 1/2`.
  have key : ((a * n - N * q : ℤ) : ℝ) = -(β * n / Q) := by
    have : (N : ℝ) * π = π * (a / q + β / (q * Q)) * n := by rw [← hα]; exact hN
    have hpi := Real.pi_pos
    push_cast
    field_simp at this ⊢
    nlinarith [this]
  have hsmall : |((a * n - N * q : ℤ) : ℝ)| < 1 := by
    rw [key, abs_neg, abs_div, abs_mul, abs_of_pos hQ0, div_lt_one hQ0]
    calc |β| * |(n : ℝ)| ≤ 1 * (Q / 2) := mul_le_mul hβ hnQ (abs_nonneg _) zero_le_one
      _ < Q := by linarith
  have hz : a * n - N * q = 0 := by
    have : |a * n - N * q| < 1 := by exact_mod_cast hsmall
    exact Int.abs_lt_one_iff.1 this
  apply hn
  have : (q : ℤ) ∣ a * n := ⟨N, by linarith⟩
  exact hcop.symm.dvd_of_dvd_mul_left this

/-- [B, (4.36)] in the form used with Lemma 4.1.1: `|T_{m,∘}| ≤ minA(x/2m + |η'|₁/2, (m/x)(c₀/2), sin²)`. -/
theorem norm_Todd_le_minA {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m) {A C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖Todd α x m‖ ≤ minA A C (Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  obtain ⟨h1, h2⟩ := norm_Todd_le hx hm α
  push_cast at hs ⊢
  unfold minA
  split_ifs with h0
  · exact h1.trans hA
  · have hne : Real.sin (2 * π * m * α) ≠ 0 := by
      intro h; apply h0; rw [← hs, h]; ring
    refine le_min (h1.trans hA) ?_
    refine (h2 hne).2.trans ?_
    rw [hs]
    exact div_le_div_of_nonneg_right hC (sq_nonneg _)

/-- [B, (4.36)], second and third bounds, as used with Lemmas 4.1.2–4.1.3. -/
theorem norm_Todd_le_min_sin {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m)
    (hne : Real.sin (π * (a / q + δ / x) * (m : ℤ)) ≠ 0) {A B C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hB : eta2'L1 / 2 ≤ B) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖Todd α x m‖ ≤ min A (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) ∧
    ‖Todd α x m‖ ≤ min (B / |Real.sin (π * (a / q + δ / x) * (m : ℤ))|)
      (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  push_cast at hs hne ⊢
  have habs : |Real.sin (2 * π * m * α)| = |Real.sin (π * (a / q + δ / x) * m)| := by
    rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs, hs]
  have hne' : Real.sin (2 * π * m * α) ≠ 0 := by
    intro h; apply hne; rw [← abs_eq_zero, ← habs, h, abs_zero]
  obtain ⟨h1, h2⟩ := norm_Todd_le hx hm α
  obtain ⟨h2a, h2b⟩ := h2 hne'
  have hC' : ‖Todd α x m‖ ≤ C / Real.sin (π * (a / q + δ / x) * m) ^ 2 := by
    refine h2b.trans ?_; rw [hs]; exact div_le_div_of_nonneg_right hC (sq_nonneg _)
  refine ⟨le_min (h1.trans hA) hC', le_min ?_ hC'⟩
  refine h2a.trans ?_; rw [habs]; exact div_le_div_of_nonneg_right hB (abs_nonneg _)


/-- `‖T_{m,∘}(α)‖` indexed by integers. -/
noncomputable def Tn (α x : ℝ) (n : ℤ) : ℝ := ‖Todd α x n.toNat‖

theorem Tn_nonneg (α x : ℝ) (n : ℤ) : 0 ≤ Tn α x n := norm_nonneg _

theorem max_log_two_mul_le {X : ℝ} (hX : 0 < X) :
    max 2 (Real.log (2 * X)) ≤ 2 * max 1 (Real.log X) := by
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [Real.log_mul (by norm_num) hX.ne']
  rcases le_or_gt 1 (Real.log X) with h | h
  · rw [max_eq_right h]; apply max_le <;> linarith
  · rw [max_eq_left h.le]; apply max_le <;> linarith

/-- **Range (R1)** of [B, Lemma 4.2.2, case (b)], i.e. [B, (4.23)] doubled:
`∑_{m ≤ q/2} |T_{m,∘}| ≤ (2|η'|₁/π) q max(1, log(c₀e³q²/(4π|η'|₁x)))`. -/
theorem sum_R1 {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) :
    ∑ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Tn α x n ≤
      2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) := by
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  set B := eta2'L1 / 2
  set C := c₀ * q / (4 * x)
  have h13 := (lemma_4_1_3 happ (y₁ := 0) (y₂ := q / 2) le_rfl (by positivity) (by linarith)
    (by linarith) (B := B) (C := C) (by positivity) (by positivity)).1
  rw [Int.floor_zero] at h13
  have hterm : ∀ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Tn α x n ≤ (if (q : ℤ) ∣ n then 0 else
      min (B / |Real.sin (π * (a / q + δ / x) * n)|) (C / Real.sin (π * (a / q + δ / x) * n) ^ 2)) := by
    intro n hn
    rw [mem_Ioc] at hn
    have hnq : (n : ℝ) ≤ q / 2 := (Int.cast_le.2 hn.2).trans (Int.floor_le _)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hndvd : ¬ (q : ℤ) ∣ n := by
      intro ⟨t, ht⟩
      have : (n : ℝ) = q * t := by exact_mod_cast ht
      have ht1 : (1 : ℤ) ≤ t := by
        by_contra h; push Not at h
        have : (t : ℝ) ≤ 0 := by exact_mod_cast (by omega : t ≤ 0)
        nlinarith
      have : (q : ℝ) ≤ n := by rw [this]; nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast ht1]
      linarith
    rw [ite_eq_right hndvd]
    have hm : 1 ≤ n.toNat := by omega
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have hne : Real.sin (π * (a / q + δ / x) * ((n.toNat : ℕ) : ℤ)) ≠ 0 := by
      rw [hcast]
      exact sin_ne_zero_of_approx happ hndvd (by rw [abs_of_pos (by linarith)]; linarith)
    have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
    have := (norm_Todd_le_min_sin hx h2α hm hne (A := x / (2 * n.toNat) + eta2'L1 / 2)
      (B := B) (C := C) le_rfl le_rfl (by
        rw [hmR]; simp only [C]
        rw [show c₀ * q / (4 * x) = q / 2 / x * (c₀ / 2) by ring]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnq hx.le) (by positivity))).2
    rw [hcast] at this
    exact this
  refine (sum_le_sum hterm).trans (h13.trans ?_)
  have hX : 0 < c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x) := by positivity
  have harg : C * rexp 3 * q / (B * π) = 2 * (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)) := by
    simp only [B, C]; field_simp
  rw [harg]
  calc 2 * B * q / π * max 2 (Real.log (2 * (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))))
      ≤ 2 * B * q / π * (2 * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)))) :=
        mul_le_mul_of_nonneg_left (max_log_two_mul_le hX) (by positivity)
    _ = _ := by simp only [B]; ring


theorem sum_range_add_three_halves (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 3 / 2) = J * (J + 2) / 2 := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `⌈(b - a)/q⌉₊` blocks of length `q` starting at `a` cover `(a, b]`. -/
theorem nblocks_spec {a b q : ℝ} (hq : 0 < q) :
    b ≤ a + (⌈(b - a) / q⌉₊ : ℕ) * q := by
  have := Nat.le_ceil ((b - a) / q)
  rw [div_le_iff₀ hq] at this; linarith

theorem nblocks_le {a b q : ℝ} (hq : 0 < q) (hab : a ≤ b) :
    ((⌈(b - a) / q⌉₊ : ℕ) : ℝ) < (b - a) / q + 1 :=
  Nat.ceil_lt_add_one (div_nonneg (by linarith) hq.le)

theorem lt_of_lt_nblocks {a b q : ℝ} (hq : 0 < q) {j : ℕ} (hj : j < ⌈(b - a) / q⌉₊) :
    a + j * q < b := by
  have h1 : (j : ℝ) < (b - a) / q := by
    have := Nat.lt_ceil.1 hj; exact this
  rw [lt_div_iff₀ hq] at h1; linarith

/-- **Range (R2)** of [B, Lemma 4.2.2, case (b)], i.e. [B, (4.24)] doubled, before simplifying:
`∑_{q/2 < m ≤ D', q ∤ m} |T_{m,∘}| ≤ (5c₀/3π²)(qD'²/x + 3q²D'/x + 5q³/4x)` for `D' ≤ Q/2`. -/
theorem sum_R2 {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {D' : ℝ} (hD'0 : 0 ≤ D') (hD'Q : D' ≤ Q / 2) :
    ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      5 * c₀ / (3 * π ^ 2) * (q * D' ^ 2 / x + 3 * q ^ 2 * D' / x + 5 * q ^ 3 / (4 * x)) := by
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  set J := ⌈(D' - q / 2) / q⌉₊
  have hblocks := sum_Ioc_le_blocks (G := fun n => if (q : ℤ) ∣ n then 0 else Tn α x n)
    (fun n => by split_ifs; exacts [le_rfl, Tn_nonneg _ _ _]) hq J (q / 2) D' (nblocks_spec hq0)
  refine hblocks.trans ?_
  set A := x / 2 + eta2'L1 / 2
  -- Each block.
  have hblock : ∀ j ∈ range J,
      ∑ n ∈ Ioc ⌊(q : ℝ) / 2 + j * q⌋ ⌊min ((q : ℝ) / 2 + (j + 1) * q) D'⌋,
          (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
        10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * ((j : ℝ) + 3 / 2) := by
    intro j _
    set y₁ := (q : ℝ) / 2 + j * q
    set y₂ := min ((q : ℝ) / 2 + (j + 1) * q) D'
    set C := c₀ / 2 * ((q : ℝ) / 2 + (j + 1) * q) / x
    have hbound : 0 ≤ 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * ((j : ℝ) + 3 / 2) := by positivity
    rcases le_or_gt y₂ y₁ with h12 | h12
    · rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono h12))]; simpa using hbound
    have hy₂ : y₂ ≤ Q / 2 := (min_le_right _ _).trans hD'Q
    have h12' := (lemma_4_1_2 happ (y₁ := y₁) (y₂ := y₂) (by positivity) h12
      (by simp only [y₁, y₂]; have := min_le_left ((q : ℝ) / 2 + (j + 1) * q) D'; linarith)
      hy₂ (A := A) (C := C) (by positivity) (by positivity))
    have hterm : ∀ n ∈ Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
        (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * (a / q + δ / x) * n) ^ 2)) := by
      intro n hn
      split_ifs with hdvd
      · exact le_rfl
      rw [mem_Ioc] at hn
      have hy10 : (0 : ℝ) ≤ y₁ := by positivity
      have hn1 : (0 : ℤ) < n := lt_of_le_of_lt (Int.floor_nonneg.2 hy10) hn.1
      have hnR : (n : ℝ) ≤ y₂ := (Int.cast_le.2 hn.2).trans (Int.floor_le _)
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn1.le
      have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
      have hm : 1 ≤ n.toNat := by omega
      have hne : Real.sin (π * (a / q + δ / x) * ((n.toNat : ℕ) : ℤ)) ≠ 0 := by
        rw [hcast]
        exact sin_ne_zero_of_approx happ hdvd (by
          rw [abs_of_pos (by exact_mod_cast hn1)]; linarith)
      have := (norm_Todd_le_min_sin hx h2α hm hne (A := A) (B := eta2'L1 / 2) (C := C)
        (by
          rw [hmR]; simp only [A]
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have : x / (2 * n) ≤ x / 2 := div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
          linarith) le_rfl
        (by
          rw [hmR]; simp only [C]
          have : (n : ℝ) ≤ (q : ℝ) / 2 + (j + 1) * q := hnR.trans (min_le_left _ _)
          rw [show c₀ / 2 * ((q : ℝ) / 2 + (j + 1) * q) / x = ((q : ℝ) / 2 + (j + 1) * q) / x * (c₀ / 2)
            by ring]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this hx.le) (by positivity))).1
      rw [hcast] at this
      exact this
    refine (sum_le_sum hterm).trans (h12'.trans ((min_le_left _ _).trans (le_of_eq ?_)))
    simp only [C]; field_simp; ring
  refine (sum_le_sum hblock).trans ?_
  rw [← mul_sum, sum_range_add_three_halves]
  -- `J ≤ D'/q + 1/2`.
  have hJ : (J : ℝ) ≤ D' / q + 1 / 2 := by
    rcases le_or_gt (D' - q / 2) 0 with h | h
    · have : J = 0 := Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg h hq0.le)
      rw [this]; push_cast; positivity
    · have := nblocks_le hq0 (a := q / 2) (b := D') (by linarith)
      have e : (D' - q / 2) / q + 1 = D' / q + 1 / 2 := by field_simp; ring
      linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hJJ : (J : ℝ) * (J + 2) ≤ (D' / q + 1 / 2) * (D' / q + 5 / 2) := by
    apply mul_le_mul hJ (by linarith) (by positivity) (by positivity)
  calc 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (J * (J + 2) / 2)
      ≤ 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * ((D' / q + 1 / 2) * (D' / q + 5 / 2) / 2) := by
        gcongr
    _ = _ := by field_simp; ring


/-- **Range (R3)** of [B, Lemma 4.2.2, case (b)], i.e. [B, (4.25)–(4.27)] adapted: for
`q/2 ≤ R < D`, with `c₁ = 1 + |η'|₁/(x/D)`,
`∑_{R < m ≤ D} |T_{m,∘}| ≤ (3c₁/2)(x/R + (x/q) log(D/R)) +
(2√(c₀c₁)/π) q (√3 + (D - R)/q + (1/2) log(D/R))`. -/
theorem sum_R3 {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {R D : ℝ} (hR : (q : ℝ) / 2 ≤ R) (hRD : R < D) :
    ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Tn α x n ≤
      3 * (1 + eta2'L1 / (x / D)) / 2 * (x / R + x / q * Real.log (D / R)) +
        2 * √(c₀ * (1 + eta2'L1 / (x / D))) / π * q *
          (√3 + (D - R) / q + 1 / 2 * Real.log (D / R)) := by
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < D := by linarith
  have hV := eta2'L1_pos
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  set c₁ := 1 + eta2'L1 / (x / D)
  have hc₁ : 1 ≤ c₁ := by simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
                          linarith
  set J := ⌈(D - R) / q⌉₊
  have hblocks := sum_Ioc_le_blocks (G := Tn α x) (Tn_nonneg α x) hq J R D (nblocks_spec hq0)
  refine hblocks.trans ?_
  have hblock : ∀ j ∈ range J,
      ∑ n ∈ Ioc ⌊R + j * q⌋ ⌊min (R + (j + 1) * q) D⌋, Tn α x n ≤
        3 * c₁ / 2 * x * (1 / (R + j * q)) +
          2 * q * √(c₀ * c₁) / π * √(1 + q / (R + j * q)) := by
    intro j hj
    set y := R + j * q
    have hy0 : 0 < y := by positivity
    have hyD : y < D := lt_of_lt_nblocks hq0 (mem_range.1 hj)
    set A := c₁ * x / (2 * y)
    set C := c₀ / 2 * (y + q) / x
    have h11 := (lemma_4_1_1' happ y (A := A) (C := C) (by positivity) (by positivity))
    have hsub : Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋ ⊆ Ioc ⌊y⌋ ⌊y + q⌋ := by
      apply Ioc_subset_Ioc le_rfl (Int.floor_mono ?_)
      have := min_le_left (R + (j + 1) * q) D; simp only [y]; linarith
    have hterm : ∀ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋,
        Tn α x n ≤ minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) := by
      intro n hn
      rw [mem_Ioc] at hn
      have hyn : y < n := by
        have := Int.lt_floor_add_one y
        have : ((⌊y⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        linarith
      have hnR : (n : ℝ) ≤ y + q := by
        have := (Int.cast_le.2 hn.2).trans (Int.floor_le (min (R + (j + 1) * q) D))
        have := min_le_left (R + (j + 1) * q) D
        simp only [y] at *; push_cast at *; linarith
      have hn1 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn1.le
      have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
      have hm : 1 ≤ n.toNat := by omega
      have := norm_Todd_le_minA hx h2α hm (A := A) (C := C)
        (by
          rw [hmR]; simp only [A, c₁]
          have e : (1 + eta2'L1 / (x / D)) * x / (2 * y) = x / (2 * y) + eta2'L1 * D / (2 * y) := by
            field_simp
          rw [e]
          have h1 : x / (2 * n) ≤ x / (2 * y) := div_le_div_of_nonneg_left hx.le (by positivity)
            (by linarith)
          have h2 : eta2'L1 / 2 ≤ eta2'L1 * D / (2 * y) := by
            rw [le_div_iff₀ (by positivity)]; nlinarith
          linarith)
        (by
          rw [hmR]; simp only [C]
          rw [show c₀ / 2 * (y + q) / x = (y + q) / x * (c₀ / 2) by ring]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnR hx.le) (by positivity))
      rw [hcast] at this; exact this
    calc ∑ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋, Tn α x n
        ≤ ∑ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋, minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) :=
          sum_le_sum hterm
      _ ≤ ∑ n ∈ Ioc ⌊y⌋ ⌊y + q⌋, minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) :=
          sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
            minA_nonneg (by positivity) (by positivity) (sq_nonneg _)
      _ ≤ 3 * A + 4 * q / π * √(A * C) := h11.trans (min_le_right _ _)
      _ = _ := by
          have hAC : √(A * C) = √(c₀ * c₁) / 2 * √(1 + q / y) := by
            rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
            have e1 : √(c₀ * c₁) / 2 * √(1 + q / y) * (√(c₀ * c₁) / 2 * √(1 + q / y)) =
                (√(c₀ * c₁) * √(c₀ * c₁)) / 4 * (√(1 + q / y) * √(1 + q / y)) := by ring
            rw [e1, Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity)]
            simp only [A, C]; field_simp; norm_num
          rw [hAC]; simp only [A]; field_simp; ring
  refine (sum_le_sum hblock).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (by
    simp only [J, ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hq0)
  have hJD : R + ((J : ℝ) - 1) * q ≤ D := by
    have := lt_of_lt_nblocks hq0 (a := R) (b := D) (j := J - 1) (by omega)
    rw [Nat.cast_sub hJ1] at this; push_cast at this; linarith
  have h1 := sum_inv_le hR0 hq0 hJ1 hJD
  have h2 := sum_sqrt_le hR0 hq0 hJ1 hJD
  have h3 : √(1 + q / R) ≤ √3 := Real.sqrt_le_sqrt (by
    have : q / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
    linarith)
  have hk1 : 0 ≤ 3 * c₁ / 2 * x := by positivity
  have hk2 : 0 ≤ 2 * q * √(c₀ * c₁) / π := by positivity
  calc 3 * c₁ / 2 * x * ∑ j ∈ range J, 1 / (R + j * q) +
        2 * q * √(c₀ * c₁) / π * ∑ j ∈ range J, √(1 + q / (R + j * q))
      ≤ 3 * c₁ / 2 * x * (1 / R + 1 / q * Real.log (D / R)) +
          2 * q * √(c₀ * c₁) / π * (√3 + (D - R) / q + 1 / 2 * Real.log (D / R)) := by
        gcongr
        linarith
    _ = _ := by field_simp

theorem sum_odd_Icc (K : ℕ) :
    (∑ m ∈ Icc 1 (2 * K), (if Odd m then (m : ℝ) else 0)) = (K : ℝ) ^ 2 ∧
    (∑ m ∈ Icc 1 (2 * K + 1), (if Odd m then (m : ℝ) else 0)) = ((K : ℝ) + 1) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e1 : 2 * (K + 1) = (2 * K + 1) + 1 := by ring
    have h1 : (∑ m ∈ Icc 1 (2 * (K + 1)), (if Odd m then (m : ℝ) else 0)) = ((K : ℝ) + 1) ^ 2 := by
      rw [e1, sum_Icc_succ_top (by omega), ih.2]
      have : ¬ Odd (2 * K + 1 + 1) := by rw [Nat.not_odd_iff_even]; exact ⟨K + 1, by ring⟩
      simp [this]
    refine ⟨by push_cast; exact h1, ?_⟩
    rw [sum_Icc_succ_top (by omega), h1]
    have : Odd (2 * (K + 1) + 1) := ⟨K + 1, rfl⟩
    simp only [this, if_true]; push_cast; ring

/-- `∑_{m ≤ N, m odd} m ≤ ((N + 1)/2)²`. -/
theorem sum_odd_le (N : ℕ) :
    (∑ m ∈ Icc 1 N, (if Odd m then (m : ℝ) else 0)) ≤ ((N : ℝ) + 1) ^ 2 / 4 := by
  rcases Nat.even_or_odd' N with ⟨K, rfl | rfl⟩
  · rw [(sum_odd_Icc K).1]; push_cast
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  · rw [(sum_odd_Icc K).2]; push_cast; nlinarith

theorem minInv_nonneg (c δ : ℝ) (hc : 0 ≤ c) : 0 ≤ minInv c δ := by
  unfold minInv; split_ifs; exacts [zero_le_one, le_min zero_le_one (by positivity)]

theorem norm_eta2hat_le_minInv (δ : ℝ) : ‖eta2hat (-(δ / 2))‖ ≤ minInv c₀ (π * δ) := by
  unfold minInv
  split_ifs with h
  · exact norm_eta2hat_le_one _
  · have hδ : δ ≠ 0 := fun h' => h (by rw [h', mul_zero])
    refine le_min (norm_eta2hat_le_one _) ?_
    have := norm_eta2hat_le (-(δ / 2)) (by simpa using hδ)
    refine this.trans (le_of_eq ?_)
    congr 1; ring

/-- `[m odd] μ(qm)/m = μ(q) [(m, 2q) = 1] μ(m)/m` for `q` odd. -/
theorem moebius_odd_term {q : ℕ} (hq : Odd q) (m : ℕ) :
    (if Odd m then ((μ (q * m) : ℤ) : ℝ) / m else 0) =
      (μ q : ℝ) * (if Nat.Coprime m (2 * q) then (μ m : ℝ) / m * 1 else 0) := by
  by_cases hm : Odd m
  · rw [if_pos hm]
    by_cases hc : Nat.Coprime m q
    · have h2 : Nat.Coprime m (2 * q) := Nat.Coprime.mul_right
        (Nat.coprime_two_right.2 hm) hc
      rw [if_pos h2, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hc.symm]
      push_cast; ring
    · have h2 : ¬ Nat.Coprime m (2 * q) := fun h => hc (Nat.Coprime.coprime_mul_left_right h)
      rw [if_neg h2, ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun h => hc (Nat.squarefree_mul_iff.1 h).1.symm)]
      simp
  · rw [if_neg hm]
    have h2 : ¬ Nat.Coprime m (2 * q) := by
      intro h
      have := Nat.Coprime.coprime_mul_right_right h
      rw [Nat.coprime_two_right] at this; exact hm this
    rw [if_neg h2, mul_zero]

/-- The main part: `∑_{m ≤ M, m odd, q | m} μ(m) T_{m,∘}(α)`, indexed by `m = qm'`. -/
noncomputable def mainPart (α x M : ℝ) (q : ℕ) : ℂ :=
  ∑ m' ∈ Icc 1 ⌊M / q⌋₊, if Odd (q * m') then (μ (q * m') : ℂ) * Todd α x (q * m') else 0

/-- **[B, (4.30)]**: the terms with `q ∣ m`, `m ≤ M`. -/
theorem norm_mainPart_le {α x δ M D : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (h2α : 2 * α = a / q + δ / x + k) (hM0 : 0 ≤ M) (hMδ : |δ| * M ≤ x / 2) (hMD : M ≤ D) :
    ‖mainPart α x M q‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) * |muSum M q (2 * q) fun _ => 1| +
        c₀ * q / x * (1 / 8 - 1 / (2 * π ^ 2)) * (D / q + 1) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  have hpi4 : (0 : ℝ) ≤ 1 / 8 - 1 / (2 * π ^ 2) := by
    have := Real.pi_gt_three
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hRHS2 : 0 ≤ c₀ * q / x * (1 / 8 - 1 / (2 * π ^ 2)) * (D / q + 1) ^ 2 := by positivity
  have hRHS1 : 0 ≤ x / (2 * q) * minInv c₀ (π * δ) * |muSum M q (2 * q) fun _ => 1| :=
    mul_nonneg (mul_nonneg (by positivity) (minInv_nonneg _ _ hc0.le)) (abs_nonneg _)
  rcases Nat.even_or_odd q with hqe | hqo
  · -- `q` even: no odd multiples of `q`.
    have : mainPart α x M q = 0 := by
      refine sum_eq_zero fun m' _ => ?_
      rw [if_neg]; rw [Nat.not_odd_iff_even]; exact hqe.mul_right m'
    rw [this, norm_zero]; linarith
  -- `q` odd.
  set N := ⌊M / q⌋₊
  have hNM : (N : ℝ) ≤ M / q := Nat.floor_le (by positivity)
  have hT : ∀ m' : ℕ, ∃ E : ℂ, Odd m' → m' ≤ N →
      Todd α x (q * m') = e ((a + k * q) / 2) *
        ((x / (2 * (q * m' : ℕ)) : ℝ) * eta2hat (-(δ / 2)) + E) ∧
      ‖E‖ ≤ (q * m' : ℕ) / x * (c₀ / (2 * π ^ 2)) * (π ^ 2 - 4) := by
    intro m'
    by_cases h : Odd m' ∧ m' ≤ N
    · have hr : |δ * (q * m' : ℕ) / x| ≤ 1 / 2 := by
        have hm'N : (m' : ℝ) ≤ N := by exact_mod_cast h.2
        rw [abs_div, abs_mul, abs_of_pos hx, Nat.abs_cast, div_le_iff₀ hx]
        push_cast
        have : (q : ℝ) * m' ≤ M := by
          calc (q : ℝ) * m' ≤ q * (M / q) := by gcongr; linarith
            _ = M := by field_simp
        calc |δ| * (q * m') ≤ |δ| * M := mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ ≤ 1 / 2 * x := by linarith
      obtain ⟨E, hE1, hE2⟩ := Todd_main hx hq h.1 h2α hr
      exact ⟨E, fun _ _ => ⟨hE1, hE2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose E hE using hT
  set κ := e ((a + k * q) / 2)
  set η0 := eta2hat (-(δ / 2))
  have hsplit : mainPart α x M q = κ * (((x / (2 * q) : ℝ) : ℂ) * η0 *
        ((∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' else 0) : ℝ) : ℂ) +
      ∑ m' ∈ Icc 1 N, (if Odd m' then (μ (q * m') : ℂ) * E m' else 0)) := by
    rw [mainPart, Complex.ofReal_sum, mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m' hm' => ?_
    have hm'N : m' ≤ N := (mem_Icc.1 hm').2
    have hm'1 : 1 ≤ m' := (mem_Icc.1 hm').1
    have hodd : Odd (q * m') ↔ Odd m' := by
      rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hqo, h⟩⟩
    by_cases ho : Odd m'
    · rw [if_pos (hodd.2 ho), if_pos ho, if_pos ho, (hE m' ho hm'N).1]
      have hm'R : (0 : ℝ) < m' := by exact_mod_cast hm'1
      push_cast
      field_simp
    · rw [if_neg (fun h => ho (hodd.1 h)), if_neg ho, if_neg ho]; simp
  rw [hsplit, norm_mul, norm_e, one_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- The main term.
    have hmu : (∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' else 0)) =
        (μ q : ℝ) * muSum M q (2 * q) fun _ => 1 := by
      rw [muSum, mul_sum]
      exact sum_congr rfl fun m' _ => moebius_odd_term hqo m'
    rw [hmu, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_mul]
    have hmuq : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 := norm_eta2hat_le_minInv δ
    calc x / (2 * q) * ‖η0‖ * (|(μ q : ℝ)| * |muSum M q (2 * q) fun _ => 1|)
        ≤ x / (2 * q) * minInv c₀ (π * δ) * (1 * |muSum M q (2 * q) fun _ => 1|) := by
          have := minInv_nonneg c₀ (π * δ) hc0.le
          gcongr
      _ = _ := by ring
  · -- The error terms.
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ m' ∈ Icc 1 N, ‖(if Odd m' then (μ (q * m') : ℂ) * E m' else 0)‖ ≤
        q * c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) * (if Odd m' then (m' : ℝ) else 0) := by
      intro m' hm'
      by_cases ho : Odd m'
      · rw [if_pos ho, if_pos ho, norm_mul]
        have hmu : ‖(μ (q * m') : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hE2 := (hE m' ho (mem_Icc.1 hm').2).2
        calc ‖(μ (q * m') : ℂ)‖ * ‖E m'‖ ≤ 1 * ‖E m'‖ := by gcongr
          _ ≤ _ := by rw [one_mul]; refine hE2.trans (le_of_eq ?_); push_cast; field_simp
      · rw [if_neg ho, if_neg ho, norm_zero, mul_zero]
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hodd := sum_odd_le N
    have hpi2 : (0 : ℝ) ≤ π ^ 2 - 4 := by have := Real.pi_gt_three; nlinarith
    have hND : ((N : ℝ) + 1) ^ 2 ≤ (D / q + 1) ^ 2 := by
      have : (N : ℝ) ≤ D / q := hNM.trans (div_le_div_of_nonneg_right hMD hq0.le)
      gcongr
    calc q * c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) *
          ∑ m' ∈ Icc 1 N, (if Odd m' then (m' : ℝ) else 0)
        ≤ q * c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) * (((N : ℝ) + 1) ^ 2 / 4) := by gcongr
      _ ≤ q * c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) * ((D / q + 1) ^ 2 / 4) := by gcongr
      _ = _ := by field_simp; ring

open TernaryGoldbach.Helfgott (eta2)

/-- Odd `n ∈ [1, N]` are `2r + 1`, `r < (N + 1)/2`. -/
theorem sum_Icc_odd_eq (N : ℕ) (G : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, (if Odd n then G n else 0) = ∑ r ∈ range ((N + 1) / 2), G (2 * r + 1) := by
  rw [← sum_filter]
  refine (sum_nbij' (fun n => (n - 1) / 2) (fun r => 2 * r + 1) ?_ ?_ ?_ ?_ ?_).symm.symm
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩ := hn
    simp only [mem_range]; omega
  · intro r hr; simp only [mem_range] at hr; simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨_, ⟨j, rfl⟩⟩ := hn; omega
  · intro r _; omega
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨_, ⟨j, rfl⟩⟩ := hn
    congr 1; omega

/-- The inner sum of `typeI` is `T_{m,∘}(α)`. -/
theorem inner_eq_Todd {α x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (if Odd n then e (α * m * n) * (eta2 (m * n / x) : ℂ) else 0) =
      Todd α x m := by
  set N := ⌊x⌋₊
  set K := (N + 1) / 2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [sum_Icc_odd_eq N (fun n => e (α * m * n) * (eta2 (m * n / x) : ℂ)), Todd]
  rw [tsum_eq_sum (s := (range K).map Nat.castEmbedding)]
  · rw [sum_map]; refine sum_congr rfl fun r _ => ?_; simp
  · intro r hr
    simp only [mem_map, mem_range, Nat.castEmbedding_apply, not_exists, not_and] at hr
    rw [Helfgott.eta2_eq_zero, Complex.ofReal_zero, mul_zero]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    rcases lt_or_ge r 0 with h | h
    · left
      have : (2 * (r : ℝ) + 1) ≤ 0 := by
        have : r ≤ -1 := by omega
        have : (r : ℝ) ≤ -1 := by exact_mod_cast this
        linarith
      have : m * (2 * (r : ℝ) + 1) / x ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) this) hx.le
      linarith
    · right
      have hrK : K ≤ r.toNat := by
        by_contra hlt; push Not at hlt
        exact hr r.toNat hlt (Int.toNat_of_nonneg h)
      have h2K : N + 1 ≤ 2 * K + 1 := by omega
      have hr' : ((N : ℝ) + 1) ≤ 2 * r + 1 := by
        have : (N + 1 : ℤ) ≤ 2 * r + 1 := by
          have : (K : ℤ) ≤ r := by
            have := Int.toNat_of_nonneg h; omega
          omega
        exact_mod_cast this
      have hxN : x < N + 1 := Nat.lt_floor_add_one x
      rw [le_div_iff₀ hx]
      nlinarith

/-- `typeI` in terms of `T_{m,∘}`. -/
theorem typeI_eq_sum_Todd {α x : ℝ} (hx : 0 < x) (D : ℝ) :
    typeI α x D = ∑ m ∈ Icc 1 ⌊D⌋₊, if Odd m then (μ m : ℂ) * Todd α x m else 0 := by
  rw [typeI]
  refine sum_congr rfl fun m hm => ?_
  split_ifs
  · rw [inner_eq_Todd hx (mem_Icc.1 hm).1]
  · rfl

/-- The terms not in `mainPart`. -/
noncomputable def restPart (α x D M : ℝ) (q : ℕ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊D⌋₊, if Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * Todd α x m else 0

theorem typeI_eq_main_add_rest {α x M D : ℝ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q) (hM0 : 0 ≤ M)
    (hMD : M ≤ D) : typeI α x D = mainPart α x M q + restPart α x D M q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [typeI_eq_sum_Todd hx, restPart, mainPart]
  have hsplit : ∀ m ∈ Icc 1 ⌊D⌋₊, (if Odd m then (μ m : ℂ) * Todd α x m else 0) =
      (if Odd m ∧ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * Todd α x m else 0) +
      (if Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * Todd α x m else 0) := by
    intro m _
    by_cases h1 : Odd m <;> by_cases h2 : ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) <;> simp [h1, h2]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  congr 1
  rw [← sum_filter, ← sum_filter]
  refine (sum_nbij' (fun m => m / q) (fun m' => q * m') ?_ ?_ ?_ ?_ ?_)
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm
    obtain ⟨⟨h1, h2⟩, hodd, ⟨t, rfl⟩, hle⟩ := hm
    simp only [mem_filter, mem_Icc]
    have ht : q * t / q = t := Nat.mul_div_cancel_left t (by omega)
    rw [ht]
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at h1
      · exact h
    refine ⟨⟨ht1, ?_⟩, hodd⟩
    apply Nat.le_floor
    rw [le_div_iff₀ hq0]; push_cast at hle ⊢; linarith
  · intro m' hm'
    simp only [mem_filter, mem_Icc] at hm' ⊢
    obtain ⟨⟨h1, h2⟩, hodd⟩ := hm'
    have hle : ((q * m' : ℕ) : ℝ) ≤ M := by
      have := Nat.floor_le (show 0 ≤ M / q by positivity)
      have h2' : (m' : ℝ) ≤ M / q := le_trans (by exact_mod_cast h2) this
      push_cast; rw [le_div_iff₀ hq0] at h2'; linarith
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, hodd,
      ⟨m', rfl⟩, hle⟩
    exact Nat.le_floor (hle.trans hMD)
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨_, _, hdvd, _⟩ := hm
    exact Nat.mul_div_cancel' hdvd
  · intro m' _; exact Nat.mul_div_cancel_left m' (by omega)
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨_, hodd, hdvd, _⟩ := hm
    rw [Nat.mul_div_cancel' hdvd]


theorem c₀_pos : (0 : ℝ) < c₀ := by unfold c₀; norm_num

theorem c₂_pos : 0 < c₂ := by unfold c₂; have := c₀_pos; positivity

/-- [B, (4.37)]: `5c₀c₂/(3π²) = 2√c₀/π`. -/
theorem c₂_identity : 5 * c₀ * c₂ / (3 * π ^ 2) = 2 * √c₀ / π := by
  have h := c₀_pos
  have hs : √c₀ * √c₀ = c₀ := Real.mul_self_sqrt h.le
  have hs0 : 0 < √c₀ := Real.sqrt_pos.2 h
  unfold c₂
  field_simp
  rw [Real.sq_sqrt h.le]; ring

theorem c₂_identity' : 55 * c₀ * c₂ / (6 * π ^ 2) = 11 * √c₀ / π := by
  have := c₂_identity
  have e : 55 * c₀ * c₂ / (6 * π ^ 2) = 11 / 2 * (5 * c₀ * c₂ / (3 * π ^ 2)) := by ring
  rw [e, this]; ring

theorem sum_Icc_eq_Ioc_int (N : ℕ) (f : ℤ → ℝ) :
    ∑ m ∈ Icc 1 N, f m = ∑ n ∈ Ioc (0 : ℤ) N, f n := by
  refine sum_nbij' (fun m => (m : ℤ)) (fun n => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp only [mem_Icc] at hm; simp only [mem_Ioc]; omega
  · intro n hn; simp only [mem_Ioc] at hn; simp only [mem_Icc]; omega
  · intro m _; simp
  · intro n hn; simp only [mem_Ioc] at hn; simp; omega
  · intro m _; rfl


theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := le_max_right _ _

theorem log_le_logPlus {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : Real.log u ≤ logPlus v :=
  (Real.log_le_log hu huv).trans (le_max_left _ _)

set_option maxHeartbeats 1000000 in
/-- **[B, Lemma 4.2.2], case (b), terms other than the main term**: if
`D' = min(c₂x/q, D) ≤ Q/2` (`Q` an approximation parameter) and `D' ≤ M`, the terms of (4.29)
with `¬(q ∣ m ∧ m ≤ M)` contribute at most (4.31). -/
theorem norm_restPart_le_caseB {α x δ Q M D : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) (hD1 : 1 ≤ D) (hD'Q : min (c₂ * x / q) D ≤ Q / 2)
    (hMD' : min (c₂ * x / q) D ≤ M) :
    ‖restPart α x D M q‖ ≤ bound_4_31 x q D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  set D' := min (c₂ * x / q) D with hD'def
  have hD'0 : 0 ≤ D' := le_min (by positivity) (by linarith)
  have hD'D : D' ≤ D := min_le_right _ _
  set R := max D' ((q : ℝ) / 2)
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  have hsq : √c₀ ≤ √(c₀ * c₁) := Real.sqrt_le_sqrt (by nlinarith)
  -- Step 1: drop `μ` and the parity of `m`, and pass to integer indices.
  set g : ℤ → ℝ := fun n => if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then Tn α x n else 0
  have h1 : ‖restPart α x D M q‖ ≤ ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n := by
    rw [restPart]
    refine (norm_sum_le _ _).trans ?_
    have hfl : ((⌊D⌋₊ : ℕ) : ℤ) = ⌊D⌋ := Int.natCast_floor_eq_floor (by linarith)
    rw [← hfl, ← sum_Icc_eq_Ioc_int]
    refine sum_le_sum fun m hm => ?_
    simp only [g, Tn, Int.toNat_natCast]
    by_cases h : Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M)
    · rw [if_pos h, if_pos (by
        intro ⟨hd, hle⟩; exact h.2 ⟨by exact_mod_cast hd, by exact_mod_cast hle⟩), norm_mul]
      have : ‖(μ m : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖(μ m : ℂ)‖ * ‖Todd α x m‖ ≤ 1 * ‖Todd α x m‖ := by gcongr
        _ = _ := one_mul _
    · rw [if_neg h, norm_zero]; split_ifs <;> simp [norm_nonneg]
  -- Step 2: split the range.
  have h2 : ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n ≤
      ∑ n ∈ Ioc 0 ⌊(q : ℝ) / 2⌋, Tn α x n +
      ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) +
      ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Tn α x n := by
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
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_ite_mem, sum_ite_mem, sum_ite_mem]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => Tn_nonneg _ _ _
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => by
        split_ifs <;> first | exact le_rfl | exact Tn_nonneg _ _ _
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => Tn_nonneg _ _ _
  -- Step 3: the three bounds.
  have hR1 := sum_R1 hx hq hcop h2α hqQ hδ (α := α)
  have hB2 : ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      2 * √c₀ / π * (D' + 11 / 2 * q) := by
    rcases le_or_gt D' ((q : ℝ) / 2) with hle | hlt
    · rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hle)), sum_empty]; positivity
    have h := sum_R2 hx hq hcop h2α hqQ hδ hD'0 hD'Q (α := α)
    refine h.trans ?_
    have hD'c : D' ≤ c₂ * x / q := min_le_left _ _
    have hq2 : (q : ℝ) ^ 2 ≤ 2 * c₂ * x := by
      have : (q : ℝ) / 2 < c₂ * x / q := hlt.trans_le hD'c
      rw [lt_div_iff₀ hq0] at this; nlinarith
    have e1 : (q : ℝ) * D' ^ 2 / x ≤ c₂ * D' := by
      rw [div_le_iff₀ hx]
      have : (q : ℝ) * D' ≤ c₂ * x := by rw [le_div_iff₀ hq0] at hD'c; linarith
      nlinarith
    have e2 : 3 * (q : ℝ) ^ 2 * D' / x ≤ 3 * c₂ * q := by
      rw [div_le_iff₀ hx]
      have : (q : ℝ) * D' ≤ c₂ * x := by rw [le_div_iff₀ hq0] at hD'c; linarith
      nlinarith
    have e3 : 5 * (q : ℝ) ^ 3 / (4 * x) ≤ 5 / 2 * c₂ * q := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hk : 0 ≤ 5 * c₀ / (3 * π ^ 2) := by positivity
    calc 5 * c₀ / (3 * π ^ 2) * (q * D' ^ 2 / x + 3 * q ^ 2 * D' / x + 5 * q ^ 3 / (4 * x))
        ≤ 5 * c₀ / (3 * π ^ 2) * (c₂ * D' + 3 * c₂ * q + 5 / 2 * c₂ * q) := by gcongr
      _ = 5 * c₀ * c₂ / (3 * π ^ 2) * (D' + 11 / 2 * q) := by ring
      _ = _ := by rw [c₂_identity]
  have hB2pos : 0 ≤ 2 * √c₀ / π * (D' + 11 / 2 * q) := by positivity
  have hB1pos : 0 ≤ 2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) := by
    have := le_max_left 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)))
    have : (0 : ℝ) ≤ max 1 _ := le_trans zero_le_one this
    positivity
  have hlog1 := logPlus_nonneg (D / (c₂ * x / q))
  have hlog2 := logPlus_nonneg (D / (q / 2))
  have hsqrt3 : √(3 * c₀ * c₁) = √3 * √(c₀ * c₁) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  have hD'R : D' ≤ R := le_max_left _ _
  have hqR : (q : ℝ) / 2 ≤ R := le_max_right _ _
  -- Step 4: combine.
  refine h1.trans (h2.trans ?_)
  unfold bound_4_31
  simp only []
  rw [← hc₁def, c₂_identity', hsqrt3]
  have hB2' : ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else Tn α x n) ≤
      2 * √c₀ / π * D' + 11 * √c₀ / π * q := hB2.trans (le_of_eq (by ring))
  have hpos1 : 0 ≤ 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) := by positivity
  have hpos2 : 0 ≤ √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) := by positivity
  have hpos3 : 0 ≤ 2 * (√3 * √(c₀ * c₁)) / π * q := by positivity
  have hpos4 : 0 ≤ 3 * c₁ / (2 * c₂) * q := by positivity
  rcases lt_or_ge R D with hRD | hRD
  · -- Range (R3) is non-empty, so `D' = c₂x/q`.
    have hD'eq : D' = c₂ * x / q := by
      rcases min_choice (c₂ * x / q) D with h | h
      · exact h
      · exfalso; have : D' = D := h; linarith
    have hR0 : 0 < R := by linarith
    have hB3 := sum_R3 hx hq hcop h2α hqQ hδ hqR hRD (α := α)
    rw [← hc₁def] at hB3
    have hxR : x / R ≤ q / c₂ := by
      rw [div_le_div_iff₀ hR0 hc2]
      have : c₂ * x / q ≤ R := hD'eq ▸ hD'R
      rw [div_le_iff₀ hq0] at this; linarith
    have hl1 : Real.log (D / R) ≤ logPlus (D / (c₂ * x / q)) :=
      log_le_logPlus (by positivity) (div_le_div_of_nonneg_left (by linarith) (by positivity)
        (hD'eq ▸ hD'R))
    have hl2 : Real.log (D / R) ≤ logPlus (D / (q / 2)) :=
      log_le_logPlus (by positivity) (div_le_div_of_nonneg_left (by linarith) (by positivity) hqR)
    have hB3' : ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Tn α x n ≤
        3 * c₁ / 2 * (q / c₂ + x / q * logPlus (D / (c₂ * x / q))) +
          2 * √(c₀ * c₁) / π * q * (√3 + (D - R) / q + 1 / 2 * logPlus (D / (q / 2))) := by
      refine hB3.trans ?_
      gcongr
    have hB3'' : ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, Tn α x n ≤
        3 * c₁ / (2 * c₂) * q + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
          2 * (√3 * √(c₀ * c₁)) / π * q + 2 * √(c₀ * c₁) / π * (D - R) +
          √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) :=
      hB3'.trans (le_of_eq (by field_simp; ring))
    have hcancel : 2 * √c₀ / π * D' ≤ 2 * √(c₀ * c₁) / π * R := by
      have := Real.pi_pos
      gcongr
    calc _ ≤ 2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
          (2 * √c₀ / π * D' + 11 * √c₀ / π * q) +
          (3 * c₁ / (2 * c₂) * q + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
            2 * (√3 * √(c₀ * c₁)) / π * q + 2 * √(c₀ * c₁) / π * (D - R) +
            √(c₀ * c₁) / π * q * logPlus (D / (q / 2))) := by linarith
      _ ≤ 2 * √(c₀ * c₁) / π * D + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
          √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) +
          2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
          (2 * (√3 * √(c₀ * c₁)) / π * q + 3 * c₁ / (2 * c₂) * q + 11 * √c₀ / π * q) := by
          linarith
      _ = _ := by ring
  · -- Range (R3) is empty.
    rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hRD)), sum_empty, add_zero]
    have hcancel : 2 * √c₀ / π * D' ≤ 2 * √(c₀ * c₁) / π * D := by
      have := Real.pi_pos
      gcongr
    calc _ ≤ 2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
          (2 * √c₀ / π * D' + 11 * √c₀ / π * q) := by linarith
      _ ≤ 2 * √(c₀ * c₁) / π * D + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
          √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) +
          2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
          (2 * (√3 * √(c₀ * c₁)) / π * q + 3 * c₁ / (2 * c₂) * q + 11 * √c₀ / π * q) := by
          linarith
      _ = _ := by ring

/-- **[B, Lemma 4.2.2], case (b)** (`|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`), for `η = η₂`: (4.30) + (4.31),
with `M = Mof x δ q D`.  Proved; it depends only on the trusted bound `eta2_fourier_bound'`. -/
theorem lemma_4_2_2_caseB {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hD : 1 ≤ D) (hDx : D ≤ x) (hcase : |δ| ≤ 1 / (2 * c₂) ∨ D ≤ Q₀ / 2) :
    ‖typeI α x D‖ ≤ bound_4_30 x δ q D + bound_4_31 x q D := by
  obtain ⟨hq, hcop, ⟨k, h2α⟩, hδQ₀, hqQ₀⟩ := h
  have hx : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc2 := c₂_pos
  have hQ₀0 : 0 < Q₀ := by linarith
  -- The approximation parameter `Q` and `M = min(Q/2, D)`.
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
        rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ₀
        rw [le_div_iff₀ (by positivity)]; nlinarith
      refine ⟨x / (|δ| * q), hqQ₀.trans hQ₀le, ?_, ?_, by rw [Mof, if_neg hδ0]⟩
      · rw [abs_div, abs_of_pos hx]; field_simp; rfl
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
      have e : |δ / x| * (q * Q) = |δ| * (q * Q) / x := by rw [abs_div, abs_of_pos hx]; ring
      rw [e, div_le_one hx] at hδ; exact hδ
    have h3 : |δ| * Q ≤ x := by
      have : |δ| * Q ≤ |δ| * (q * Q) := by
        have hQ0 : 0 ≤ Q := by linarith
        have : Q ≤ q * Q := by
          nlinarith [mul_nonneg (sub_nonneg.2 (show (1 : ℝ) ≤ q by exact_mod_cast hq)) hQ0]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      linarith
    linarith
  rw [typeI_eq_main_add_rest hx hq hM0 hMD]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_mainPart_le hx hq h2α hM0 hMδ hMD
  · exact norm_restPart_le_caseB hx hq hcop h2α hqQ hδ hD hD'Q hMD'

/-- **[B, Lemma 4.2.2], case (a)** (`|δ| ≥ 1/2c₂`), for `η = η₂`: (4.30) + (4.32).
Not yet proved: it needs the second approximation `a'/q'` of [B, proof of Lemma 4.2.1]. -/
theorem lemma_4_2_2_caseA {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀ : 16 ≤ Q₀) (hD : 1 ≤ D) (hDx : D ≤ x) (hδ : 1 / (2 * c₂) ≤ |δ|) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ‖typeI α x D‖ ≤ bound_4_30 x δ q D + bound_4_32 x δ q D Q₀ ε := by
  sorry

/-- **[B, Lemma 4.2.2]** for `η = η₂`. -/
theorem lemma_4_2_2 {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀ : 16 ≤ Q₀) (hD : 1 ≤ D) (hDx : D ≤ x) :
    ((|δ| ≤ 1 / (2 * c₂) ∨ D ≤ Q₀ / 2) →
      ‖typeI α x D‖ ≤ bound_4_30 x δ q D + bound_4_31 x q D) ∧
    (1 / (2 * c₂) ≤ |δ| → ∀ ε, 0 < ε → ε ≤ 1 →
      ‖typeI α x D‖ ≤ bound_4_30 x δ q D + bound_4_32 x δ q D Q₀ ε) :=
  ⟨lemma_4_2_2_caseB h hD hDx, fun hδ _ hε hε1 => lemma_4_2_2_caseA h hQ₀ hD hDx hδ hε hε1⟩

end TernaryGoldbach.MinorArcs
