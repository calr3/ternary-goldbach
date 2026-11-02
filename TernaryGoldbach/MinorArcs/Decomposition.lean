import TernaryGoldbach.MinorArcs.TypeI
import TernaryGoldbach.MinorArcs.Vaughan

/-!
# The decomposition [H, (3.9), (3.11)] with `f = 1_{odd}` (`v = 2`)

`S_{η₂}(α, x) = S_{I,1} - S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}` (`decomposition`), from Vaughan's
identity (`MinorArcs/Vaughan.lean`), where `S_{I,1} = typeILog`, `S_{I,2} = typeI2` (the sums of
[H, Lemmas 4.2.3, 4.2.4]), `S_{II} = typeII` [H, (5.1)], `S_{0,∞} = S0inf`, `S_{0,2} = S0two`.
Fully proved.
-/

open Real Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `∑_{n ≤ M odd} (f * g)(n) w(n) = ∑_{a, b ≤ M odd} f(a) g(b) w(ab)` for `w` vanishing beyond `M`. -/
theorem sum_odd_conv (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (M : ℕ)
    (hw : ∀ n, M < n → w n = 0) :
    ∑ n ∈ Icc 1 M, (if Odd n then ((f * g) n : ℂ) * w n else 0) =
      ∑ a ∈ Icc 1 M, if Odd a then ∑ b ∈ Icc 1 M,
        (if Odd b then (f a : ℂ) * g b * w (a * b) else 0) else 0 := by
  have hR : (∑ a ∈ Icc 1 M, if Odd a then ∑ b ∈ Icc 1 M,
        (if Odd b then (f a : ℂ) * g b * w (a * b) else 0) else 0) =
      ∑ p ∈ (Icc 1 M ×ˢ Icc 1 M).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ M),
        if Odd (p.1 * p.2) then (f p.1 : ℂ) * g p.2 * w (p.1 * p.2) else 0 := by
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · refine sum_congr rfl fun b _ => ?_
      by_cases hab : a * b ≤ M
      · simp [hab, Nat.odd_mul, ha]
      · simp [hab, hw _ (not_le.1 hab)]
    · refine (sum_eq_zero fun b _ => ?_).symm
      simp [Nat.odd_mul, ha]
  rw [hR, ← sum_fiberwise_of_maps_to (s := (Icc 1 M ×ˢ Icc 1 M).filter
    (fun p : ℕ × ℕ => p.1 * p.2 ≤ M)) (t := Icc 1 M) (g := fun p : ℕ × ℕ => p.1 * p.2)]
  · refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hfib : ((Icc 1 M ×ˢ Icc 1 M).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ M)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
      constructor
      · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, -⟩
        have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
        have := (mem_Icc.1 hn).2
        refine ⟨⟨⟨⟨ha, ?_⟩, hb, ?_⟩, by omega⟩, h⟩
        · calc a ≤ a * b := Nat.le_mul_of_pos_right a hb
            _ ≤ M := by omega
        · calc b ≤ a * b := Nat.le_mul_of_pos_left b ha
            _ ≤ M := by omega
    rw [hfib, ArithmeticFunction.mul_apply]
    split_ifs with ho
    · push_cast
      rw [sum_mul]
      refine sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.1 hp).1, if_pos ho]
    · exact (sum_eq_zero fun p hp => by rw [(Nat.mem_divisorsAntidiagonal.1 hp).1, if_neg ho]).symm
  · intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (by have := hp.1.1.1; have := hp.1.2.1; positivity),
      hp.2⟩


open TernaryGoldbach.Helfgott (eta2 S)

/-- The weight `e(αn) η₂(n/x)`. -/
noncomputable def wt (α x : ℝ) (n : ℕ) : ℂ := e (α * n) * (eta2 (n / x) : ℂ)

theorem wt_eq_zero {α x : ℝ} (hx : 0 < x) {n : ℕ} (hn : ⌊x⌋₊ < n) : wt α x n = 0 := by
  have : x < n := (Nat.floor_lt hx.le).1 hn
  rw [wt, Helfgott.eta2_eq_zero, Complex.ofReal_zero, mul_zero]
  intro h; have := h.2; rw [div_lt_one hx] at this; linarith

theorem wt_mul (α x : ℝ) (m n : ℕ) :
    wt α x (m * n) = e (α * m * n) * (eta2 (m * n / x) : ℂ) := by
  simp only [wt]; push_cast; ring_nf

open Classical in
/-- `S_{0,∞} = ∑_{n ≤ V odd} Λ(n) e(αn) η₂(n/x)` [H, (3.9)] (with `f = 1_{odd}`). -/
noncomputable def S0inf (α x : ℝ) (V : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 V, if Odd n then (Λ n : ℂ) * wt α x n else 0

open Classical in
/-- `S_{0,2} = ∑_{n even} Λ(n) e(αn) η₂(n/x)` [H, (3.11)] (only powers of `2` contribute). -/
noncomputable def S0two (α x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, if Odd n then 0 else (Λ n : ℂ) * wt α x n

open Classical in
/-- The Type II sum [H, (3.9), (5.1)] with `v = 2`:
`∑_{m odd} (∑_{d > U, d | m} μ(d)) ∑_{n > V odd} Λ(n) e(αmn) η₂(mn/x)`. -/
noncomputable def typeII (α x : ℝ) (U V : ℕ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊x⌋₊, if Odd m then (∑ d ∈ m.divisors.filter (U < ·), (μ d : ℂ)) *
    ∑ n ∈ Icc 1 ⌊x⌋₊, (if Odd n ∧ V < n then (Λ n : ℂ) * e (α * m * n) *
      (eta2 (m * n / x) : ℂ) else 0) else 0

theorem sum_Icc_mono_of_zero {N M : ℕ} (h : N ≤ M) (F : ℕ → ℂ) (hF : ∀ n, N < n → F n = 0) :
    ∑ n ∈ Icc 1 M, F n = ∑ n ∈ Icc 1 N, F n := by
  symm
  refine sum_subset (Icc_subset_Icc le_rfl h) fun n hn hn' => hF n ?_
  simp only [mem_Icc, not_and, not_le] at hn hn'; exact hn' hn.1

theorem S_eq_sum {α x : ℝ} (hx : 0 < x) (M : ℕ) (hM : ⌊x⌋₊ ≤ M) :
    S eta2 x α = ∑ n ∈ Icc 1 M, (Λ n : ℂ) * wt α x n := by
  rw [S, tsum_eq_sum (s := Icc 1 M)]
  · refine sum_congr rfl fun n _ => ?_
    simp only [wt]; push_cast; ring_nf
  · intro n hn
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · have : n = 0 := by omega
      subst this; simp
    · have := wt_eq_zero (α := α) hx (lt_of_le_of_lt hM h)
      simp only [wt] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (by simp [e, Complex.exp_ne_zero])
      · rw [Complex.ofReal_eq_zero] at h'; simp [h']

theorem wt_mul3 (α x : ℝ) (a b c : ℕ) :
    wt α x (a * (b * c)) = e (α * a * b * c) * (eta2 (a * b * c / x) : ℂ) := by
  simp only [wt]; push_cast; ring_nf

theorem ite_sum_zero' (p : Prop) [Decidable p] (s : Finset ℕ) (f : ℕ → ℂ) :
    (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem zeta_apply_pos {n : ℕ} (hn : 1 ≤ n) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n) = 1 := by
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, show n ≠ 0 by omega]

/-- (a): the `Λ_{≤V}` term is `S_{0,∞}`. -/
theorem odd_part_a (α x : ℝ) {V M : ℕ} (hVM : V ≤ M) :
    ∑ n ∈ Icc 1 M, (if Odd n then (((trunc Λ V) n : ℝ) : ℂ) * wt α x n else 0) =
      S0inf α x V := by
  rw [S0inf, sum_Icc_mono_of_zero hVM]
  · refine sum_congr rfl fun n hn => ?_
    rw [trunc_apply, if_pos (mem_Icc.1 hn).2]
  · intro n hn; simp [trunc_apply, not_le.2 hn]

/-- (b): the `μ_{≤U} * log` term is `S_{I,1}` (`typeILog`). -/
theorem odd_part_b (α : ℝ) {x : ℝ} (hx : 0 < x) {U M : ℕ} (hUM : U ≤ M) (hNM : ⌊x⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 M, (if Odd n then (((trunc μ U * ArithmeticFunction.log) n : ℝ) : ℂ) *
      wt α x n else 0) = typeILog α x U := by
  rw [sum_odd_conv _ _ _ M (fun n hn => wt_eq_zero hx (lt_of_le_of_lt hNM hn)), typeILog,
    Nat.floor_natCast, sum_Icc_mono_of_zero hUM]
  · refine sum_congr rfl fun a ha => ?_
    have ha1 := (mem_Icc.1 ha).1
    split_ifs with hao
    · rw [mul_sum, sum_Icc_mono_of_zero hNM]
      · refine sum_congr rfl fun b _ => ?_
        rw [trunc_apply, if_pos (mem_Icc.1 ha).2, wt_mul, ArithmeticFunction.log_apply]
        split_ifs <;> (try simp only [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast]) <;> ring
      · intro b hb
        have : ⌊x⌋₊ < a * b := lt_of_lt_of_le hb (Nat.le_mul_of_pos_left b ha1)
        simp [wt_eq_zero hx this]
    · rfl
  · intro a ha; simp [trunc_apply, not_le.2 ha]

/-- (c): the `μ_{≤U} * Λ_{≤V} * 1` term is `S_{I,2}` (`typeI2`). -/
theorem odd_part_c (α : ℝ) {x : ℝ} (hx : 0 < x) {U V M : ℕ} (hUM : U ≤ M) (hVM : V ≤ M)
    (hNM : ⌊x⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 M, (if Odd n then (((trunc μ U * trunc Λ V * ArithmeticFunction.zeta) n : ℝ) : ℂ) *
      wt α x n else 0) = typeI2 α x U V := by
  have hw : ∀ n, M < n → wt α x n = 0 := fun n hn => wt_eq_zero hx (lt_of_le_of_lt hNM hn)
  rw [show trunc μ U * trunc Λ V * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      trunc Λ V * (trunc μ U * ArithmeticFunction.zeta) by ring, sum_odd_conv _ _ _ M hw, typeI2,
    Nat.floor_natCast, Nat.floor_natCast, sum_Icc_mono_of_zero hVM]
  · refine sum_congr rfl fun a ha => ?_
    have ha1 := (mem_Icc.1 ha).1
    split_ifs with hao
    · have hwa : ∀ n, M < n → wt α x (a * n) = 0 := fun n hn =>
        hw _ (lt_of_lt_of_le hn (Nat.le_mul_of_pos_left n ha1))
      rw [show (∑ b ∈ Icc 1 M, if Odd b then (((trunc Λ V) a : ℝ) : ℂ) *
            (((trunc μ U * ArithmeticFunction.zeta) b : ℝ) : ℂ) * wt α x (a * b) else 0) =
          (((trunc Λ V) a : ℝ) : ℂ) * ∑ b ∈ Icc 1 M, if Odd b then
            (((trunc μ U * ArithmeticFunction.zeta) b : ℝ) : ℂ) * wt α x (a * b) else 0 by
        rw [mul_sum]; refine sum_congr rfl fun b _ => ?_; split_ifs <;> ring,
        sum_odd_conv _ _ (fun n => wt α x (a * n)) M hwa, trunc_apply, if_pos (mem_Icc.1 ha).2]
      congr 1
      rw [sum_Icc_mono_of_zero hUM]
      · refine sum_congr rfl fun u hu => ?_
        have hu1 := (mem_Icc.1 hu).1
        split_ifs with huo
        · rw [mul_sum, sum_Icc_mono_of_zero hNM]
          · refine sum_congr rfl fun n hn => ?_
            rw [trunc_apply, if_pos (mem_Icc.1 hu).2, zeta_apply_pos (mem_Icc.1 hn).1, wt_mul3]
            split_ifs <;> (try simp only [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast, Complex.ofReal_one]) <;> ring
          · intro n hn
            have : ⌊x⌋₊ < a * (u * n) := lt_of_lt_of_le hn
              (le_trans (Nat.le_mul_of_pos_left n hu1) (Nat.le_mul_of_pos_left _ ha1))
            simp [wt_eq_zero hx this]
        · rfl
      · intro u hu; simp [trunc_apply, not_le.2 hu]
    · rfl
  · intro a ha; simp [trunc_apply, not_le.2 ha]

/-- (d): the `μ_{>U} * Λ_{>V} * 1` term is `S_{II}` (`typeII`). -/
theorem odd_part_d (α : ℝ) {x : ℝ} (hx : 0 < x) {U V M : ℕ} (hNM : ⌊x⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 M, (if Odd n then (((((μ : ArithmeticFunction ℝ) - trunc μ U) *
      (Λ - trunc Λ V) * ArithmeticFunction.zeta) n : ℝ) : ℂ) * wt α x n else 0) =
      typeII α x U V := by
  have hw : ∀ n, M < n → wt α x n = 0 := fun n hn => wt_eq_zero hx (lt_of_le_of_lt hNM hn)
  rw [show ((μ : ArithmeticFunction ℝ) - trunc μ U) * (Λ - trunc Λ V) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      (((μ : ArithmeticFunction ℝ) - trunc μ U) * ArithmeticFunction.zeta) * (Λ - trunc Λ V) by
    ring, sum_odd_conv _ _ _ M hw, typeII, sum_Icc_mono_of_zero hNM]
  · refine sum_congr rfl fun m hm => ?_
    have hm1 := (mem_Icc.1 hm).1
    split_ifs with hmo
    · have hdiv : ((((μ : ArithmeticFunction ℝ) - trunc μ U) * ArithmeticFunction.zeta) m : ℝ) =
          ∑ d ∈ m.divisors.filter (U < ·), (μ d : ℝ) := by
        rw [ArithmeticFunction.coe_mul_zeta_apply, sum_filter]
        refine sum_congr rfl fun d _ => ?_
        rw [sub_apply', trunc_apply]
        split_ifs with h1 h2 h2 <;> first | omega | simp
      rw [mul_sum, sum_Icc_mono_of_zero hNM]
      · refine sum_congr rfl fun n _ => ?_
        rw [hdiv, sub_apply', trunc_apply, wt_mul]
        by_cases hno : Odd n <;> by_cases hnV : V < n
        · simp only [hno, hnV, and_self, if_true, if_neg (not_le.2 hnV), sub_zero]
          push_cast; ring
        · simp only [hno, hnV, and_false, if_true, if_false, if_pos (not_lt.1 hnV), sub_self]
          simp
        · simp [hno]
        · simp [hno]
      · intro n hn
        have : ⌊x⌋₊ < m * n := lt_of_lt_of_le hn (Nat.le_mul_of_pos_left n hm1)
        simp [wt_eq_zero hx this]
    · rfl
  · intro m hm
    split_ifs
    · refine sum_eq_zero fun n hn => ?_
      have : ⌊x⌋₊ < m * n := lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m (mem_Icc.1 hn).1)
      simp [wt_eq_zero hx this]
    · rfl

/-- **The decomposition [H, (3.11)]** with `f = 1_{odd}` (`v = 2`):
`S_{η₂}(α, x) = S_{I,1} - S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}`. -/
theorem decomposition (α : ℝ) {x : ℝ} (hx : 0 < x) (U V : ℕ) :
    S eta2 x α = typeILog α x U - typeI2 α x U V + typeII α x U V + S0inf α x V + S0two α x := by
  set N := ⌊x⌋₊
  set M := N + U + V
  have hNM : N ≤ M := by omega
  have hwM : ∀ n, M < n → wt α x n = 0 := fun n hn => wt_eq_zero hx (by omega)
  rw [S_eq_sum hx M hNM]
  have hsplit : ∑ n ∈ Icc 1 M, (Λ n : ℂ) * wt α x n =
      ∑ n ∈ Icc 1 M, (if Odd n then (Λ n : ℂ) * wt α x n else 0) +
      ∑ n ∈ Icc 1 M, (if Odd n then 0 else (Λ n : ℂ) * wt α x n) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_; split_ifs <;> simp
  have heven : ∑ n ∈ Icc 1 M, (if Odd n then 0 else (Λ n : ℂ) * wt α x n) = S0two α x := by
    rw [S0two, sum_Icc_mono_of_zero hNM]
    intro n hn; split_ifs <;> simp [wt_eq_zero hx hn]
  -- Vaughan's identity.
  have hV : ∀ n, (Λ n : ℂ) = ((trunc Λ V) n : ℝ) +
      ((trunc μ U * ArithmeticFunction.log) n : ℝ) -
      ((trunc μ U * trunc Λ V * ArithmeticFunction.zeta) n : ℝ) +
      ((((μ : ArithmeticFunction ℝ) - trunc μ U) *
        (Λ - trunc Λ V) * ArithmeticFunction.zeta) n : ℝ) := by
    intro n
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan U V)
    simp only [ArithmeticFunction.add_apply, sub_apply'] at h
    exact_mod_cast h
  have hodd : ∑ n ∈ Icc 1 M, (if Odd n then (Λ n : ℂ) * wt α x n else 0) =
      ∑ n ∈ Icc 1 M, (if Odd n then (((trunc Λ V) n : ℝ) : ℂ) * wt α x n else 0) +
      ∑ n ∈ Icc 1 M, (if Odd n then (((trunc μ U * ArithmeticFunction.log) n : ℝ) : ℂ) *
        wt α x n else 0) -
      ∑ n ∈ Icc 1 M, (if Odd n then (((trunc μ U * trunc Λ V * ArithmeticFunction.zeta) n : ℝ)
        : ℂ) * wt α x n else 0) +
      ∑ n ∈ Icc 1 M, (if Odd n then (((((μ : ArithmeticFunction ℝ) - trunc μ U) *
        (Λ - trunc Λ V) * ArithmeticFunction.zeta) n : ℝ) : ℂ) * wt α x n else 0) := by
    rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [hV n]; ring
    · ring
  rw [hsplit, heven, hodd, odd_part_a α x (by omega : V ≤ M), odd_part_b α hx (by omega) hNM,
    odd_part_c α hx (by omega) (by omega) hNM, odd_part_d α hx hNM]
  ring

end TernaryGoldbach.MinorArcs
