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
-/

open Real Finset

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

end TernaryGoldbach.MinorArcs
