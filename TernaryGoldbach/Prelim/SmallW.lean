import TernaryGoldbach.Prelim.SmallG

/-!
# [MV73, Lemma 8] for `6 ≤ R < 1000`, checked by the kernel

For `A ≤ R < B`, `W(R) = ∑_{r ≤ R} g(r) R/(R+r) ≥ ∑_{r ≤ A} g(r) A/(A+r)`, and the right side is at
least `∑_{T ⊆ P, ∏T ≤ A} ∏_{p ∈ T} 1/(p−1) · A/(A + ∏T)` for any set `P` of primes. A depth-first
search over the primes of `SmallG.PL` computes this in fixed point, rounding down (`dfsW`). With
`log B < u/10⁸` (`chkStep`), 18 blocks `[A, B)` cover `[6, 1000)`. Only lower bounds are used.
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallW

open TernaryGoldbach.Prelim.MV (gS WR gS_nonneg)
open TernaryGoldbach.Prelim.SmallG (PL PL_nodup PL_prime gS_prod_primes)
open TernaryGoldbach.Prelim.Small (chkStep log_lt_of_chk)

/-- The weight `n/(n + k)`. -/
noncomputable def wt (n k : ℕ) : ℝ := (n : ℝ) / (n + k)

theorem wt_nonneg (n k : ℕ) : 0 ≤ wt n k := by unfold wt; positivity

/-- The weighted search: `w` carries `⌊10¹⁵ ∏ 1/(p−1)⌋`, each node contributes `⌊w n/(n + m)⌋`. -/
def dfsW (n : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], m, w => w * n / (n + m)
  | p :: l, m, w => if m * p ≤ n then dfsW n l m w + dfsW n l (m * p) (w / (p - 1)) else w * n / (n + m)

/-- `Φ_W = ∑_{T ⊆ s} [m ∏T ≤ n] ∏_{q ∈ T} 1/(q−1) · n/(n + m ∏T)`. -/
noncomputable def PhiW (n m : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ T ∈ s.powerset, if m * ∏ q ∈ T, q ≤ n then (∏ q ∈ T, (1 / ((q : ℝ) - 1))) * wt n (m * ∏ q ∈ T, q)
    else 0

theorem PhiW_term_nonneg {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) (n m : ℕ) (T : Finset ℕ)
    (hT : T ∈ s.powerset) :
    0 ≤ (if m * ∏ q ∈ T, q ≤ n then (∏ q ∈ T, (1 / ((q : ℝ) - 1))) * wt n (m * ∏ q ∈ T, q)
      else 0) := by
  split_ifs
  · refine mul_nonneg (prod_nonneg fun q hq => ?_) (wt_nonneg _ _)
    have : (2 : ℝ) ≤ q := by exact_mod_cast (hs q (mem_powerset.1 hT hq)).two_le
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

theorem PhiW_nonneg {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) (n m : ℕ) : 0 ≤ PhiW n m s :=
  sum_nonneg fun T hT => PhiW_term_nonneg hs n m T hT

theorem wt_le_PhiW {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {n m : ℕ} (hm : m ≤ n) :
    wt n m ≤ PhiW n m s := by
  unfold PhiW
  have h := single_le_sum (f := fun T => if m * ∏ q ∈ T, q ≤ n then
      (∏ q ∈ T, (1 / ((q : ℝ) - 1))) * wt n (m * ∏ q ∈ T, q) else 0)
    (fun T hT => PhiW_term_nonneg hs n m T hT) (empty_mem_powerset s)
  simpa [hm] using h

theorem PhiW_insert {s : Finset ℕ} {p : ℕ} (hp : p ∉ s) (n m : ℕ) :
    PhiW n m (insert p s) = PhiW n m s + 1 / ((p : ℝ) - 1) * PhiW n (m * p) s := by
  unfold PhiW
  rw [sum_powerset_insert hp, mul_sum]
  congr 1
  refine sum_congr rfl fun T hT => ?_
  have hpT : p ∉ T := fun h => hp (mem_powerset.1 hT h)
  rw [prod_insert hpT, prod_insert hpT]
  simp only [mul_assoc]
  split_ifs <;> ring

theorem dfsW_le (n : ℕ) : ∀ (l : List ℕ), l.Nodup → (∀ p ∈ l, p.Prime) → ∀ m w : ℕ, m ≤ n →
    (dfsW n l m w : ℝ) ≤ w * PhiW n m l.toFinset := by
  have hleaf : ∀ m w : ℕ, ((w * n / (n + m) : ℕ) : ℝ) ≤ w * wt n m := by
    intro m w
    have := Nat.cast_div_le (α := ℝ) (m := w * n) (n := n + m)
    push_cast at this
    unfold wt
    calc _ ≤ ((w : ℝ) * n) / (n + m) := this
      _ = _ := by ring
  intro l
  induction l with
  | nil =>
    intro _ _ m w hm
    have := hleaf m w
    simp only [dfsW, List.toFinset_nil, PhiW, powerset_empty, sum_singleton, prod_empty, mul_one,
      if_pos hm, one_mul]
    exact this
  | cons p l ih =>
    intro hnd hpr m w hm
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    have hlp : ∀ q ∈ l, q.Prime := fun q hq => hpr q (List.mem_cons_of_mem p hq)
    have hpp : p.Prime := hpr p List.mem_cons_self
    have hs : ∀ q ∈ l.toFinset, q.Prime := fun q hq => hlp q (List.mem_toFinset.1 hq)
    rw [List.toFinset_cons, PhiW_insert (by simpa using hpl)]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    unfold dfsW
    split_ifs with h
    · push_cast
      have h1 := ih hl hlp m w hm
      have h2 := ih hl hlp (m * p) (w / (p - 1)) h
      have h3 : ((w / (p - 1) : ℕ) : ℝ) ≤ (w : ℝ) / ((p : ℝ) - 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := w) (n := p - 1)
        rwa [Nat.cast_sub hpp.one_le, Nat.cast_one] at this
      have hP2 : 0 ≤ PhiW n (m * p) l.toFinset := PhiW_nonneg hs _ _
      have h4 : ((w / (p - 1) : ℕ) : ℝ) * PhiW n (m * p) l.toFinset ≤
          (w : ℝ) / ((p : ℝ) - 1) * PhiW n (m * p) l.toFinset :=
        mul_le_mul_of_nonneg_right h3 hP2
      have e : (w : ℝ) * (PhiW n m l.toFinset + 1 / ((p : ℝ) - 1) * PhiW n (m * p) l.toFinset) =
          w * PhiW n m l.toFinset + (w : ℝ) / ((p : ℝ) - 1) * PhiW n (m * p) l.toFinset := by ring
      rw [e]; linarith
    · have h1 := wt_le_PhiW hs hm
      have h2 : 0 ≤ 1 / ((p : ℝ) - 1) * PhiW n (m * p) l.toFinset :=
        mul_nonneg (div_nonneg (by norm_num) (by linarith)) (PhiW_nonneg hs _ _)
      have h3 := hleaf m w
      have h4 : (w : ℝ) * wt n m ≤ w * (PhiW n m l.toFinset + 1 / ((p : ℝ) - 1) * PhiW n (m * p) l.toFinset) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
      linarith

/-- `Φ_W(n, 1, P) ≤ ∑_{r ≤ n} g(r) n/(n + r)` for a set `P` of primes. -/
theorem PhiW_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    PhiW n 1 P ≤ ∑ r ∈ Icc 1 n, gS r * wt n r := by
  unfold PhiW
  simp only [one_mul]
  rw [← sum_filter]
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ q ∈ T, q)
      ((P.powerset.filter fun T => ∏ q ∈ T, q ≤ n : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro T1 h1 T2 h2 he
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at h1 h2
    have e1 := Nat.primeFactors_prod (fun p hp => hP p (h1.1 hp))
    have e2 := Nat.primeFactors_prod (fun p hp => hP p (h2.1 hp))
    simp only at he
    rw [← e1, ← e2, he]
  have hval : ∀ T ∈ P.powerset.filter (fun T => ∏ q ∈ T, q ≤ n),
      (∏ q ∈ T, (1 / ((q : ℝ) - 1))) * wt n (∏ q ∈ T, q) =
        (fun r => gS r * wt n r) (∏ q ∈ T, q) := fun T hT => by
    simp only
    rw [gS_prod_primes T fun p hp => hP p ((mem_powerset.1 (mem_filter.1 hT).1) hp)]
  rw [sum_congr rfl hval, ← sum_image (f := fun r => gS r * wt n r) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => mul_nonneg (gS_nonneg r) (wt_nonneg _ _)
  intro r hr
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hr
  have hT' := mem_filter.1 hT
  exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp =>
    (hP p ((mem_powerset.1 hT'.1) hp)).ne_zero), hT'.2⟩

/-- `W(R) ≥ ∑_{r ≤ A} g(r) A/(A + r)` for `1 ≤ A ≤ R`. -/
theorem WR_ge {A : ℕ} {R : ℝ} (hA : 1 ≤ A) (hAR : (A : ℝ) ≤ R) :
    ∑ r ∈ Icc 1 A, gS r * wt A r ≤ WR R := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hR0 : 0 < R := by linarith
  have hfl : A ≤ ⌊R⌋₊ := Nat.le_floor hAR
  unfold WR
  calc ∑ r ∈ Icc 1 A, gS r * wt A r ≤ ∑ r ∈ Icc 1 A, gS r * (R / (R + r)) := by
        refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (gS_nonneg r)
        unfold wt
        have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ ∑ r ∈ Icc 1 ⌊R⌋₊, gS r * (R / (R + r)) := by
        refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hfl) fun r _ _ => ?_
        exact mul_nonneg (gS_nonneg r) (div_nonneg hR0.le (by positivity))

theorem block_ok {A B u d : ℕ} (hA : 6 ≤ A) (hd : dfsW A PL 1 (10 ^ 15) = d)
    (hc : (u + 25068000) * 10 ^ 15 < 10 ^ 8 * d) (hu : chkStep u (10 ^ 8) 1 B = true)
    {R : ℝ} (hAR : (A : ℝ) ≤ R) (hRB : R < B) : Real.log R + 0.25068 < WR R := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hR0 : 0 < R := by linarith
  have h1 := dfsW_le A PL PL_nodup PL_prime 1 (10 ^ 15) (by omega)
  rw [hd] at h1
  have h2 := PhiW_le PL.toFinset (fun p hp => PL_prime p (List.mem_toFinset.1 hp)) A
  have h3 := WR_ge (by omega) hAR
  have hB : 0 < B := by
    have : (0 : ℝ) < B := by linarith
    exact_mod_cast this
  have hlB := log_lt_of_chk (by norm_num) hB hu
  push_cast at hlB h1
  have hlR : Real.log R < Real.log B := Real.log_lt_log hR0 hRB
  have hc' : ((u : ℝ) + 25068000) * 10 ^ 15 < 10 ^ 8 * d := by exact_mod_cast hc
  linarith

theorem d_0 : dfsW 6 PL 1 (10 ^ 15) = 2326839826839826 := by decide +kernel
theorem u_0 : chkStep 194591016 (10 ^ 8) 1 7 = true := by decide +kernel
theorem d_1 : dfsW 7 PL 1 (10 ^ 15) = 2501175213675212 := by decide +kernel
theorem u_1 : chkStep 219722459 (10 ^ 8) 1 9 = true := by decide +kernel
theorem d_2 : dfsW 9 PL 1 (10 ^ 15) = 2647646103896102 := by decide +kernel
theorem u_2 : chkStep 230258510 (10 ^ 8) 1 10 = true := by decide +kernel
theorem d_3 : dfsW 10 PL 1 (10 ^ 15) = 2829245509392566 := by decide +kernel
theorem u_3 : chkStep 256494937 (10 ^ 8) 1 13 = true := by decide +kernel
theorem d_4 : dfsW 13 PL 1 (10 ^ 15) = 3069619928444293 := by decide +kernel
theorem u_4 : chkStep 277258873 (10 ^ 8) 1 16 = true := by decide +kernel
theorem d_5 : dfsW 16 PL 1 (10 ^ 15) = 3333660016674939 := by decide +kernel
theorem u_5 : chkStep 304452245 (10 ^ 8) 1 21 = true := by decide +kernel
theorem d_6 : dfsW 21 PL 1 (10 ^ 15) = 3585640799247463 := by decide +kernel
theorem u_6 : chkStep 333220452 (10 ^ 8) 1 28 = true := by decide +kernel
theorem d_7 : dfsW 28 PL 1 (10 ^ 15) = 3856875332925247 := by decide +kernel
theorem u_7 : chkStep 358351895 (10 ^ 8) 1 36 = true := by decide +kernel
theorem d_8 : dfsW 36 PL 1 (10 ^ 15) = 4166074210115670 := by decide +kernel
theorem u_8 : chkStep 391202302 (10 ^ 8) 1 50 = true := by decide +kernel
theorem d_9 : dfsW 50 PL 1 (10 ^ 15) = 4508099125939181 := by decide +kernel
theorem u_9 : chkStep 424849525 (10 ^ 8) 1 70 = true := by decide +kernel
theorem d_10 : dfsW 70 PL 1 (10 ^ 15) = 4863409658581554 := by decide +kernel
theorem u_10 : chkStep 460517020 (10 ^ 8) 1 100 = true := by decide +kernel
theorem d_11 : dfsW 100 PL 1 (10 ^ 15) = 5205709278133787 := by decide +kernel
theorem u_11 : chkStep 494875990 (10 ^ 8) 1 141 = true := by decide +kernel
theorem d_12 : dfsW 141 PL 1 (10 ^ 15) = 5571319008757823 := by decide +kernel
theorem u_12 : chkStep 531812000 (10 ^ 8) 1 204 = true := by decide +kernel
theorem d_13 : dfsW 204 PL 1 (10 ^ 15) = 5939683651839357 := by decide +kernel
theorem u_13 : chkStep 568697537 (10 ^ 8) 1 295 = true := by decide +kernel
theorem d_14 : dfsW 295 PL 1 (10 ^ 15) = 6317709151715226 := by decide +kernel
theorem u_14 : chkStep 606610810 (10 ^ 8) 1 431 = true := by decide +kernel
theorem d_15 : dfsW 431 PL 1 (10 ^ 15) = 6697361318914343 := by decide +kernel
theorem u_15 : chkStep 644571983 (10 ^ 8) 1 630 = true := by decide +kernel
theorem d_16 : dfsW 630 PL 1 (10 ^ 15) = 7081049995216847 := by decide +kernel
theorem u_16 : chkStep 682979375 (10 ^ 8) 1 925 = true := by decide +kernel
theorem d_17 : dfsW 925 PL 1 (10 ^ 15) = 7465400419530687 := by decide +kernel
theorem u_17 : chkStep 690775529 (10 ^ 8) 1 1000 = true := by decide +kernel

/-- **[MV73, Lemma 8] for `6 ≤ R < 1000`** (kernel-checked). -/
theorem lemma8_mid {R : ℝ} (h6 : 6 ≤ R) (hR : R < 1000) : Real.log R + 0.25068 < WR R := by
  by_cases h0 : R < 7
  · exact block_ok (A := 6) (B := 7) (by norm_num) d_0 (by norm_num) u_0 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h1 : R < 9
  · exact block_ok (A := 7) (B := 9) (by norm_num) d_1 (by norm_num) u_1 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h2 : R < 10
  · exact block_ok (A := 9) (B := 10) (by norm_num) d_2 (by norm_num) u_2 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h3 : R < 13
  · exact block_ok (A := 10) (B := 13) (by norm_num) d_3 (by norm_num) u_3 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h4 : R < 16
  · exact block_ok (A := 13) (B := 16) (by norm_num) d_4 (by norm_num) u_4 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h5 : R < 21
  · exact block_ok (A := 16) (B := 21) (by norm_num) d_5 (by norm_num) u_5 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h6 : R < 28
  · exact block_ok (A := 21) (B := 28) (by norm_num) d_6 (by norm_num) u_6 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h7 : R < 36
  · exact block_ok (A := 28) (B := 36) (by norm_num) d_7 (by norm_num) u_7 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h8 : R < 50
  · exact block_ok (A := 36) (B := 50) (by norm_num) d_8 (by norm_num) u_8 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h9 : R < 70
  · exact block_ok (A := 50) (B := 70) (by norm_num) d_9 (by norm_num) u_9 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h10 : R < 100
  · exact block_ok (A := 70) (B := 100) (by norm_num) d_10 (by norm_num) u_10 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h11 : R < 141
  · exact block_ok (A := 100) (B := 141) (by norm_num) d_11 (by norm_num) u_11 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h12 : R < 204
  · exact block_ok (A := 141) (B := 204) (by norm_num) d_12 (by norm_num) u_12 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h13 : R < 295
  · exact block_ok (A := 204) (B := 295) (by norm_num) d_13 (by norm_num) u_13 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h14 : R < 431
  · exact block_ok (A := 295) (B := 431) (by norm_num) d_14 (by norm_num) u_14 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h15 : R < 630
  · exact block_ok (A := 431) (B := 630) (by norm_num) d_15 (by norm_num) u_15 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h16 : R < 925
  · exact block_ok (A := 630) (B := 925) (by norm_num) d_16 (by norm_num) u_16 (by norm_num; linarith) (by norm_num; linarith)
  exact block_ok (A := 925) (B := 1000) (by norm_num) d_17 (by norm_num) u_17 (by norm_num; linarith) (by norm_num; linarith)

end TernaryGoldbach.Prelim.SmallW
