import Mathlib

/-!
# `f(X) ≤ 1.27 X` ([B, p. 83]), with kernel-checked numerics

`f(X) = #{m ≤ X squarefree} + (X²/2) ∑_{m > X squarefree} 1/m²`. With `n = ⌊X⌋`,
`f(X) = Q(n) + (X²/2) S(n)`, where `Q(n)` counts the squarefree `m ≤ n` and
`S(n) = ∑_{m > n squarefree} 1/m²`.
* `n ≥ 200`: `Q(n) ≤ n − ⌊n/4⌋` (no multiple of `4` is squarefree) and `S(n) ≤ ∑_{m > n} 1/m² ≤ 1/n`.
* `n < 200`: `Q(n) ≤ Q_c(n)` and `S(n) ≤ ∑_{n < m ≤ M} c(m)/m² + 1/M`, where `c(m) ∈ {0, 1}` is a
  trial-division test that every squarefree `m ≠ 0` passes and `M = 3000` for `n = 2`, `M = 400`
  otherwise. `X ↦ 1.27X − Q_c − (X²/2) S_c` is concave, so it suffices to check `X = n` and `X = n + 1`.
  These rational inequalities are checked by `decide +kernel`. The maximum, `f(2)/2 = 15/π² − 1/4 =
  1.26982…`, is the tightest case.
-/

open Finset

namespace TernaryGoldbach.Prelim.Small

/-- The summand of `f(X)`. -/
noncomputable def fsqTerm (X : ℝ) (m : ℕ) : ℝ :=
  if Squarefree m ∧ m ≠ 0 then (if (m : ℝ) ≤ X then 1 else X ^ 2 / (2 * (m : ℝ) ^ 2)) else 0

/-- `[m squarefree, m ≠ 0]`. -/
noncomputable def sqInd (m : ℕ) : ℝ := if Squarefree m ∧ m ≠ 0 then 1 else 0

theorem sqInd_nonneg (m : ℕ) : 0 ≤ sqInd m := by unfold sqInd; split_ifs <;> norm_num

theorem sqInd_le_one (m : ℕ) : sqInd m ≤ 1 := by unfold sqInd; split_ifs <;> norm_num

theorem summable_fsqTerm (X : ℝ) : Summable (fsqTerm X) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left (1 + X ^ 2))
  · unfold fsqTerm; split_ifs <;> positivity
  · unfold fsqTerm
    split_ifs with h1 h2
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h1.2
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      have : (m : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      linarith
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h1.2
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg X, sq_nonneg (m : ℝ)]
    · positivity

/-- Trial division: `m ≠ 0` and no `d²` with `2 ≤ d ≤ 56`, `d² ≤ m`, divides `m`. -/
def sqCheck (m : ℕ) : Bool :=
  m != 0 && (List.range' 2 55).all (fun d => m < d * d || m % (d * d) != 0)

def cq (m : ℕ) : ℚ := if sqCheck m then 1 else 0

theorem sqCheck_of_squarefree {m : ℕ} (h : Squarefree m) (hm : m ≠ 0) : sqCheck m = true := by
  unfold sqCheck
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, hm, not_false_eq_true, true_and,
    List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, decide_eq_true_eq]
  intro d hd
  by_contra hc
  push Not at hc
  have hdvd : d * d ∣ m := Nat.dvd_of_mod_eq_zero hc.2
  have hu := h d hdvd
  rw [Nat.isUnit_iff] at hu
  omega

theorem sqInd_le_cq (m : ℕ) : sqInd m ≤ ((cq m : ℚ) : ℝ) := by
  unfold sqInd cq
  by_cases h : Squarefree m ∧ m ≠ 0
  · rw [if_pos h, if_pos (sqCheck_of_squarefree h.1 h.2)]; norm_num
  · rw [if_neg h]; split_ifs <;> norm_num

/-- `∑_{k ≥ 0} 1/(k + M)² ≤ 1/(M − 1)` for `M ≥ 2`. -/
theorem tsum_inv_sq_tail {M : ℕ} (hM : 2 ≤ M) :
    ∑' k : ℕ, 1 / ((k + M : ℕ) : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have key : ∀ K : ℕ, ∑ k ∈ range K, 1 / ((k + M : ℕ) : ℝ) ^ 2 ≤
      1 / ((M : ℝ) - 1) - 1 / ((K : ℝ) + M - 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ]
      have hx : (2 : ℝ) ≤ (K : ℝ) + M := by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith
      have h1 : 1 / ((K + M : ℕ) : ℝ) ^ 2 ≤ 1 / ((K : ℝ) + M - 1) - 1 / (((K + 1 : ℕ) : ℝ) + M - 1) := by
        push_cast
        rw [show (K : ℝ) + 1 + M - 1 = K + M by ring, div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun K => ?_
  have h := key K
  have : 0 ≤ 1 / ((K : ℝ) + M - 1) := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact div_nonneg zero_le_one (by linarith)
  linarith

theorem summable_sqInd_div (N : ℕ) :
    Summable (fun k : ℕ => sqInd (k + N) / ((k + N : ℕ) : ℝ) ^ 2) := by
  have hs : Summable (fun k : ℕ => 1 / ((k + N : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff N).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine Summable.of_nonneg_of_le (fun k => div_nonneg (sqInd_nonneg _) (by positivity))
    (fun k => ?_) hs
  exact div_le_div_of_nonneg_right (sqInd_le_one _) (by positivity)

/-- The tail `∑_{m ≥ N} [m sq-free]/m² ≤ ∑_{N ≤ m < N + L} c(m)/m² + 1/(N + L − 1)`. -/
theorem tail_le (N L : ℕ) (hN : 1 ≤ N) (hL : 1 ≤ L) :
    ∑' k, sqInd (k + N) / ((k + N : ℕ) : ℝ) ^ 2 ≤
      ∑ k ∈ range L, ((cq (k + N) : ℚ) : ℝ) / ((k + N : ℕ) : ℝ) ^ 2 + 1 / (((L + N : ℕ) : ℝ) - 1) := by
  set g : ℕ → ℝ := fun k => sqInd (k + N) / ((k + N : ℕ) : ℝ) ^ 2 with hg
  have hgs : Summable g := summable_sqInd_div N
  have hsplit := hgs.sum_add_tsum_nat_add L
  have hfin : ∑ k ∈ range L, g k ≤ ∑ k ∈ range L, ((cq (k + N) : ℚ) : ℝ) / ((k + N : ℕ) : ℝ) ^ 2 :=
    sum_le_sum fun k _ => div_le_div_of_nonneg_right (sqInd_le_cq _) (by positivity)
  have hs : Summable (fun k : ℕ => 1 / ((k + (L + N) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (L + N)).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  have htail : ∑' k, g (k + L) ≤ ∑' k, 1 / ((k + (L + N) : ℕ) : ℝ) ^ 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff L).2 hgs) hs
    simp only [hg]
    rw [show k + L + N = k + (L + N) by omega]
    exact div_le_div_of_nonneg_right (sqInd_le_one _) (by positivity)
  have h2 := tsum_inv_sq_tail (M := L + N) (by omega)
  rw [← hsplit]
  linarith

/-- `f(X) = Q(n) + (X²/2) S(n)` for `n = ⌊X⌋`. -/
theorem fsq_split {X : ℝ} (hX : 0 ≤ X) :
    ∑' m, fsqTerm X m = ∑ m ∈ range (⌊X⌋₊ + 1), sqInd m +
      X ^ 2 / 2 * ∑' k, sqInd (k + (⌊X⌋₊ + 1)) / ((k + (⌊X⌋₊ + 1) : ℕ) : ℝ) ^ 2 := by
  set n := ⌊X⌋₊
  rw [← (summable_fsqTerm X).sum_add_tsum_nat_add (n + 1), ← tsum_mul_left]
  congr 1
  · refine sum_congr rfl fun m hm => ?_
    have hmX : (m : ℝ) ≤ X :=
      (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hm))).trans (Nat.floor_le hX)
    unfold fsqTerm sqInd
    split_ifs <;> simp_all
  · refine tsum_congr fun k => ?_
    have hX' : X < ((k + (n + 1) : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one X
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    unfold fsqTerm sqInd
    split_ifs with h1 h2
    · linarith
    · field_simp
    · simp

/-- The kernel-checked part. -/
def Mn (n : ℕ) : ℕ := if n = 2 then 3000 else 400

def Qc (n : ℕ) : ℚ := ∑ m ∈ range (n + 1), cq m

def Sc (n : ℕ) : ℚ :=
  ∑ k ∈ range (Mn n - n), cq (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℚ) ^ 2 + 1 / (Mn n : ℚ)

def chkN (n : ℕ) : Bool :=
  decide (Qc n + (n : ℚ) ^ 2 / 2 * Sc n ≤ 127 / 100 * n) &&
    decide (Qc n + ((n : ℚ) + 1) ^ 2 / 2 * Sc n ≤ 127 / 100 * (n + 1))

theorem chk_0 : ∀ n ∈ (Ico 0 4).erase 2, chkN n = true := by decide +kernel

theorem chk_4 : ∀ n ∈ Ico 4 8, chkN n = true := by decide +kernel

theorem chk_8 : ∀ n ∈ Ico 8 12, chkN n = true := by decide +kernel

theorem chk_12 : ∀ n ∈ Ico 12 16, chkN n = true := by decide +kernel

theorem chk_16 : ∀ n ∈ Ico 16 20, chkN n = true := by decide +kernel

theorem chk_20 : ∀ n ∈ Ico 20 24, chkN n = true := by decide +kernel

theorem chk_24 : ∀ n ∈ Ico 24 28, chkN n = true := by decide +kernel

theorem chk_28 : ∀ n ∈ Ico 28 32, chkN n = true := by decide +kernel

theorem chk_32 : ∀ n ∈ Ico 32 36, chkN n = true := by decide +kernel

theorem chk_36 : ∀ n ∈ Ico 36 40, chkN n = true := by decide +kernel

theorem chk_40 : ∀ n ∈ Ico 40 44, chkN n = true := by decide +kernel

theorem chk_44 : ∀ n ∈ Ico 44 48, chkN n = true := by decide +kernel

theorem chk_48 : ∀ n ∈ Ico 48 52, chkN n = true := by decide +kernel

theorem chk_52 : ∀ n ∈ Ico 52 56, chkN n = true := by decide +kernel

theorem chk_56 : ∀ n ∈ Ico 56 60, chkN n = true := by decide +kernel

theorem chk_60 : ∀ n ∈ Ico 60 64, chkN n = true := by decide +kernel

theorem chk_64 : ∀ n ∈ Ico 64 68, chkN n = true := by decide +kernel

theorem chk_68 : ∀ n ∈ Ico 68 72, chkN n = true := by decide +kernel

theorem chk_72 : ∀ n ∈ Ico 72 76, chkN n = true := by decide +kernel

theorem chk_76 : ∀ n ∈ Ico 76 80, chkN n = true := by decide +kernel

theorem chk_80 : ∀ n ∈ Ico 80 84, chkN n = true := by decide +kernel

theorem chk_84 : ∀ n ∈ Ico 84 88, chkN n = true := by decide +kernel

theorem chk_88 : ∀ n ∈ Ico 88 92, chkN n = true := by decide +kernel

theorem chk_92 : ∀ n ∈ Ico 92 96, chkN n = true := by decide +kernel

theorem chk_96 : ∀ n ∈ Ico 96 100, chkN n = true := by decide +kernel

theorem chk_100 : ∀ n ∈ Ico 100 104, chkN n = true := by decide +kernel

theorem chk_104 : ∀ n ∈ Ico 104 108, chkN n = true := by decide +kernel

theorem chk_108 : ∀ n ∈ Ico 108 112, chkN n = true := by decide +kernel

theorem chk_112 : ∀ n ∈ Ico 112 116, chkN n = true := by decide +kernel

theorem chk_116 : ∀ n ∈ Ico 116 120, chkN n = true := by decide +kernel

theorem chk_120 : ∀ n ∈ Ico 120 124, chkN n = true := by decide +kernel

theorem chk_124 : ∀ n ∈ Ico 124 128, chkN n = true := by decide +kernel

theorem chk_128 : ∀ n ∈ Ico 128 132, chkN n = true := by decide +kernel

theorem chk_132 : ∀ n ∈ Ico 132 136, chkN n = true := by decide +kernel

theorem chk_136 : ∀ n ∈ Ico 136 140, chkN n = true := by decide +kernel

theorem chk_140 : ∀ n ∈ Ico 140 144, chkN n = true := by decide +kernel

theorem chk_144 : ∀ n ∈ Ico 144 148, chkN n = true := by decide +kernel

theorem chk_148 : ∀ n ∈ Ico 148 152, chkN n = true := by decide +kernel

theorem chk_152 : ∀ n ∈ Ico 152 156, chkN n = true := by decide +kernel

theorem chk_156 : ∀ n ∈ Ico 156 160, chkN n = true := by decide +kernel

theorem chk_160 : ∀ n ∈ Ico 160 164, chkN n = true := by decide +kernel

theorem chk_164 : ∀ n ∈ Ico 164 168, chkN n = true := by decide +kernel

theorem chk_168 : ∀ n ∈ Ico 168 172, chkN n = true := by decide +kernel

theorem chk_172 : ∀ n ∈ Ico 172 176, chkN n = true := by decide +kernel

theorem chk_176 : ∀ n ∈ Ico 176 180, chkN n = true := by decide +kernel

theorem chk_180 : ∀ n ∈ Ico 180 184, chkN n = true := by decide +kernel

theorem chk_184 : ∀ n ∈ Ico 184 188, chkN n = true := by decide +kernel

theorem chk_188 : ∀ n ∈ Ico 188 192, chkN n = true := by decide +kernel

theorem chk_192 : ∀ n ∈ Ico 192 196, chkN n = true := by decide +kernel

theorem chk_196 : ∀ n ∈ Ico 196 200, chkN n = true := by decide +kernel

theorem blk_0 : ∑ k ∈ Ico 0 250, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.267402529923521 := by
  decide +kernel

theorem blk_1 : ∑ k ∈ Ico 250 500, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.001210860054547 := by
  decide +kernel

theorem blk_2 : ∑ k ∈ Ico 500 750, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000394161677598 := by
  decide +kernel

theorem blk_3 : ∑ k ∈ Ico 750 1000, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000203413072564 := by
  decide +kernel

theorem blk_4 : ∑ k ∈ Ico 1000 1250, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000120212568379 := by
  decide +kernel

theorem blk_5 : ∑ k ∈ Ico 1250 1500, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000083056752555 := by
  decide +kernel

theorem blk_6 : ∑ k ∈ Ico 1500 1750, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000056372472530 := by
  decide +kernel

theorem blk_7 : ∑ k ∈ Ico 1750 2000, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000043287094198 := by
  decide +kernel

theorem blk_8 : ∑ k ∈ Ico 2000 2250, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000033681963827 := by
  decide +kernel

theorem blk_9 : ∑ k ∈ Ico 2250 2500, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000027485319689 := by
  decide +kernel

theorem blk_10 : ∑ k ∈ Ico 2500 2750, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000021766144379 := by
  decide +kernel

theorem blk_11 : ∑ k ∈ Ico 2750 2998, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤ 0.000018153962485 := by
  decide +kernel

theorem Sc_two : Sc 2 ≤ 0.267402529923521 + 0.001210860054547 + 0.000394161677598 + 0.000203413072564 + 0.000120212568379 + 0.000083056752555 + 0.000056372472530 + 0.000043287094198 + 0.000033681963827 + 0.000027485319689 + 0.000021766144379 + 0.000018153962485 + 1 / 3000 := by
  have e : Sc 2 = ∑ k ∈ Ico 0 2998, cq (k + 3) / ((k + 3 : ℕ) : ℚ) ^ 2 + 1 / 3000 := by
    rw [Sc, show Mn 2 = 3000 from rfl, ← range_eq_Ico]; norm_num
  rw [e, ← sum_Ico_consecutive _ (show 0 ≤ 250 by norm_num) (show 250 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 250 ≤ 500 by norm_num) (show 500 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 500 ≤ 750 by norm_num) (show 750 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 750 ≤ 1000 by norm_num) (show 1000 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 1000 ≤ 1250 by norm_num) (show 1250 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 1250 ≤ 1500 by norm_num) (show 1500 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 1500 ≤ 1750 by norm_num) (show 1750 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 1750 ≤ 2000 by norm_num) (show 2000 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 2000 ≤ 2250 by norm_num) (show 2250 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 2250 ≤ 2500 by norm_num) (show 2500 ≤ 2998 by norm_num), ← sum_Ico_consecutive _ (show 2500 ≤ 2750 by norm_num) (show 2750 ≤ 2998 by norm_num)]
  linarith [blk_0, blk_1, blk_2, blk_3, blk_4, blk_5, blk_6, blk_7, blk_8, blk_9, blk_10, blk_11]

theorem Qc_two : Qc 2 = 2 := by decide +kernel

/-- The two endpoint inequalities, for every `n < 200`. -/
theorem chk_prop {n : ℕ} (hn : n < 200) :
    Qc n + (n : ℚ) ^ 2 / 2 * Sc n ≤ 127 / 100 * n ∧
      Qc n + ((n : ℚ) + 1) ^ 2 / 2 * Sc n ≤ 127 / 100 * (n + 1) := by
  have unpack : ∀ {m : ℕ}, chkN m = true → Qc m + (m : ℚ) ^ 2 / 2 * Sc m ≤ 127 / 100 * m ∧
      Qc m + ((m : ℚ) + 1) ^ 2 / 2 * Sc m ≤ 127 / 100 * (m + 1) := by
    intro m h
    simp only [chkN, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  have two_case : Qc 2 + ((2 : ℕ) : ℚ) ^ 2 / 2 * Sc 2 ≤ 127 / 100 * (2 : ℕ) ∧
      Qc 2 + (((2 : ℕ) : ℚ) + 1) ^ 2 / 2 * Sc 2 ≤ 127 / 100 * ((2 : ℕ) + 1) := by
    have h1 := Sc_two
    rw [Qc_two]
    push_cast
    constructor <;> linarith
  rcases (show (0 ≤ n ∧ n < 4) ∨ (4 ≤ n ∧ n < 8) ∨ (8 ≤ n ∧ n < 12) ∨ (12 ≤ n ∧ n < 16) ∨ (16 ≤ n ∧ n < 20) ∨ (20 ≤ n ∧ n < 24) ∨ (24 ≤ n ∧ n < 28) ∨ (28 ≤ n ∧ n < 32) ∨ (32 ≤ n ∧ n < 36) ∨ (36 ≤ n ∧ n < 40) ∨ (40 ≤ n ∧ n < 44) ∨ (44 ≤ n ∧ n < 48) ∨ (48 ≤ n ∧ n < 52) ∨ (52 ≤ n ∧ n < 56) ∨ (56 ≤ n ∧ n < 60) ∨ (60 ≤ n ∧ n < 64) ∨ (64 ≤ n ∧ n < 68) ∨ (68 ≤ n ∧ n < 72) ∨ (72 ≤ n ∧ n < 76) ∨ (76 ≤ n ∧ n < 80) ∨ (80 ≤ n ∧ n < 84) ∨ (84 ≤ n ∧ n < 88) ∨ (88 ≤ n ∧ n < 92) ∨ (92 ≤ n ∧ n < 96) ∨ (96 ≤ n ∧ n < 100) ∨ (100 ≤ n ∧ n < 104) ∨ (104 ≤ n ∧ n < 108) ∨ (108 ≤ n ∧ n < 112) ∨ (112 ≤ n ∧ n < 116) ∨ (116 ≤ n ∧ n < 120) ∨ (120 ≤ n ∧ n < 124) ∨ (124 ≤ n ∧ n < 128) ∨ (128 ≤ n ∧ n < 132) ∨ (132 ≤ n ∧ n < 136) ∨ (136 ≤ n ∧ n < 140) ∨ (140 ≤ n ∧ n < 144) ∨ (144 ≤ n ∧ n < 148) ∨ (148 ≤ n ∧ n < 152) ∨ (152 ≤ n ∧ n < 156) ∨ (156 ≤ n ∧ n < 160) ∨ (160 ≤ n ∧ n < 164) ∨ (164 ≤ n ∧ n < 168) ∨ (168 ≤ n ∧ n < 172) ∨ (172 ≤ n ∧ n < 176) ∨ (176 ≤ n ∧ n < 180) ∨ (180 ≤ n ∧ n < 184) ∨ (184 ≤ n ∧ n < 188) ∨ (188 ≤ n ∧ n < 192) ∨ (192 ≤ n ∧ n < 196) ∨ (196 ≤ n ∧ n < 200) by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases (show n = 2 ∨ n ≠ 2 by omega) with h2 | h2
    · subst h2; exact two_case
    · exact unpack (chk_0 n (mem_erase.2 ⟨h2, mem_Ico.2 h⟩))
  · exact unpack (chk_4 n (mem_Ico.2 h))
  · exact unpack (chk_8 n (mem_Ico.2 h))
  · exact unpack (chk_12 n (mem_Ico.2 h))
  · exact unpack (chk_16 n (mem_Ico.2 h))
  · exact unpack (chk_20 n (mem_Ico.2 h))
  · exact unpack (chk_24 n (mem_Ico.2 h))
  · exact unpack (chk_28 n (mem_Ico.2 h))
  · exact unpack (chk_32 n (mem_Ico.2 h))
  · exact unpack (chk_36 n (mem_Ico.2 h))
  · exact unpack (chk_40 n (mem_Ico.2 h))
  · exact unpack (chk_44 n (mem_Ico.2 h))
  · exact unpack (chk_48 n (mem_Ico.2 h))
  · exact unpack (chk_52 n (mem_Ico.2 h))
  · exact unpack (chk_56 n (mem_Ico.2 h))
  · exact unpack (chk_60 n (mem_Ico.2 h))
  · exact unpack (chk_64 n (mem_Ico.2 h))
  · exact unpack (chk_68 n (mem_Ico.2 h))
  · exact unpack (chk_72 n (mem_Ico.2 h))
  · exact unpack (chk_76 n (mem_Ico.2 h))
  · exact unpack (chk_80 n (mem_Ico.2 h))
  · exact unpack (chk_84 n (mem_Ico.2 h))
  · exact unpack (chk_88 n (mem_Ico.2 h))
  · exact unpack (chk_92 n (mem_Ico.2 h))
  · exact unpack (chk_96 n (mem_Ico.2 h))
  · exact unpack (chk_100 n (mem_Ico.2 h))
  · exact unpack (chk_104 n (mem_Ico.2 h))
  · exact unpack (chk_108 n (mem_Ico.2 h))
  · exact unpack (chk_112 n (mem_Ico.2 h))
  · exact unpack (chk_116 n (mem_Ico.2 h))
  · exact unpack (chk_120 n (mem_Ico.2 h))
  · exact unpack (chk_124 n (mem_Ico.2 h))
  · exact unpack (chk_128 n (mem_Ico.2 h))
  · exact unpack (chk_132 n (mem_Ico.2 h))
  · exact unpack (chk_136 n (mem_Ico.2 h))
  · exact unpack (chk_140 n (mem_Ico.2 h))
  · exact unpack (chk_144 n (mem_Ico.2 h))
  · exact unpack (chk_148 n (mem_Ico.2 h))
  · exact unpack (chk_152 n (mem_Ico.2 h))
  · exact unpack (chk_156 n (mem_Ico.2 h))
  · exact unpack (chk_160 n (mem_Ico.2 h))
  · exact unpack (chk_164 n (mem_Ico.2 h))
  · exact unpack (chk_168 n (mem_Ico.2 h))
  · exact unpack (chk_172 n (mem_Ico.2 h))
  · exact unpack (chk_176 n (mem_Ico.2 h))
  · exact unpack (chk_180 n (mem_Ico.2 h))
  · exact unpack (chk_184 n (mem_Ico.2 h))
  · exact unpack (chk_188 n (mem_Ico.2 h))
  · exact unpack (chk_192 n (mem_Ico.2 h))
  · exact unpack (chk_196 n (mem_Ico.2 h))

/-- `Q(n) ≤ n − ⌊n/4⌋`. -/
theorem Q_le (n : ℕ) : ∑ m ∈ range (n + 1), sqInd m ≤ ((n - n / 4 : ℕ) : ℝ) := by
  have h1 : ∀ m ∈ range (n + 1), sqInd m ≤ if m ≠ 0 ∧ ¬ 4 ∣ m then (1 : ℝ) else 0 := by
    intro m _
    unfold sqInd
    split_ifs with h h'
    · exact le_rfl
    · exfalso
      push Not at h'
      have h4 : 2 * 2 ∣ m := h' h.2
      have hu := h.1 2 h4
      rw [Nat.isUnit_iff] at hu; omega
    · norm_num
    · norm_num
  refine (sum_le_sum h1).trans (le_of_eq ?_)
  rw [sum_boole]
  congr 1
  have e : (range (n + 1)).filter (fun m => m ≠ 0 ∧ ¬ 4 ∣ m) = (Ioc 0 n).filter (fun m => ¬ 4 ∣ m) := by
    ext m; simp only [mem_filter, mem_range, mem_Ioc]; omega
  rw [e]
  have h2 := card_filter_add_card_filter_not (s := Ioc 0 n) (fun m => 4 ∣ m)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc] at h2
  omega

set_option maxHeartbeats 1000000 in
/-- **`f(X) ≤ 1.27 X` for `X ≥ 0`** ([B, p. 83]). -/
theorem fsq_le' {X : ℝ} (hX : 0 ≤ X) : ∑' m, fsqTerm X m ≤ 1.27 * X := by
  rw [fsq_split hX]
  obtain ⟨n, hn⟩ : ∃ n, ⌊X⌋₊ = n := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ X := by rw [← hn]; exact Nat.floor_le hX
  have hn2 : X < n + 1 := by rw [← hn]; exact Nat.lt_floor_add_one X
  rw [hn]
  obtain ⟨S, hSdef⟩ : ∃ S, ∑' k, sqInd (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ) ^ 2 = S :=
    ⟨_, rfl⟩
  rw [hSdef]
  have hS0 : 0 ≤ S := by
    rw [← hSdef]; exact tsum_nonneg fun k => div_nonneg (sqInd_nonneg _) (by positivity)
  have hX2 : 0 ≤ X ^ 2 / 2 := by positivity
  rcases lt_or_ge n 200 with h200 | h200
  · -- the kernel-checked range
    obtain ⟨hc1, hc2⟩ := chk_prop h200
    have hQ : ∑ m ∈ range (n + 1), sqInd m ≤ ((Qc n : ℚ) : ℝ) := by
      unfold Qc; push_cast; exact sum_le_sum fun m _ => sqInd_le_cq m
    have hS : S ≤ ((Sc n : ℚ) : ℝ) := by
      have hMn : n < Mn n := by unfold Mn; split_ifs <;> omega
      have h := tail_le (n + 1) (Mn n - n) (by omega) (by omega)
      have e : ((Mn n - n + (n + 1) : ℕ) : ℝ) - 1 = (Mn n : ℝ) := by
        rw [show Mn n - n + (n + 1) = Mn n + 1 by omega]; push_cast; ring
      rw [e, hSdef] at h
      unfold Sc; push_cast at h ⊢; exact h
    have hSc0 : (0 : ℝ) ≤ ((Sc n : ℚ) : ℝ) := hS0.trans hS
    have hc1' := (Rat.cast_le (K := ℝ)).2 hc1
    have hc2' := (Rat.cast_le (K := ℝ)).2 hc2
    push_cast at hc1' hc2'
    have hmono : X ^ 2 / 2 * S ≤ X ^ 2 / 2 * ((Sc n : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hS hX2
    -- concavity between `n` and `n + 1`
    have ht0 : 0 ≤ X - n := by linarith
    have ht1 : 0 ≤ n + 1 - X := by linarith
    have hconc : ((Qc n : ℚ) : ℝ) + X ^ 2 / 2 * ((Sc n : ℚ) : ℝ) ≤ 1.27 * X := by
      nlinarith [mul_nonneg ht1 (sub_nonneg.2 hc1'), mul_nonneg ht0 (sub_nonneg.2 hc2'),
        mul_nonneg (mul_nonneg ht0 ht1) hSc0]
    linarith
  · -- `n ≥ 200`
    have hQ := Q_le n
    have hn0 : (200 : ℝ) ≤ n := by exact_mod_cast h200
    have hS : S ≤ 1 / (n : ℝ) := by
      have hs : Summable (fun k : ℕ => 1 / ((k + (n + 1) : ℕ) : ℝ) ^ 2) :=
        (summable_nat_add_iff (n + 1)).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      have h1 : ∑' k, sqInd (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ) ^ 2 ≤
          ∑' k : ℕ, 1 / ((k + (n + 1) : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum (fun k => div_le_div_of_nonneg_right (sqInd_le_one _) (by positivity))
          (summable_sqInd_div (n + 1)) hs
      have h2 := tsum_inv_sq_tail (M := n + 1) (by omega)
      have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
      rw [e] at h2
      rw [hSdef] at h1
      linarith
    have hQ' : ((n - n / 4 : ℕ) : ℝ) ≤ (3 * n + 3) / 4 := by
      have h4 : n ≤ 4 * (n / 4) + 3 := by omega
      have h4' : ((n : ℕ) : ℝ) ≤ 4 * ((n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast h4
      rw [Nat.cast_sub (Nat.div_le_self n 4)]
      linarith
    have hnpos : (0 : ℝ) < n := by linarith
    have hXS : X ^ 2 / 2 * S ≤ X ^ 2 / 2 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hS hX2
    have hXn : X ^ 2 / 2 * (1 / (n : ℝ)) ≤ X / 2 + X / 400 := by
      have h1 : X ^ 2 ≤ X * (n + 1) := by nlinarith
      have h2 : X ≤ X * n / 200 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      rw [mul_one_div, div_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end TernaryGoldbach.Prelim.Small
