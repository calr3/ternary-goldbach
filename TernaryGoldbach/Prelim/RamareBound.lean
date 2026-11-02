import TernaryGoldbach.Prelim.RamareLocal
import TernaryGoldbach.Prelim.SmallProdAp

/-!
# `∑_a |h_d(a)| a^{1/3} ≤ 11 f₁(d)`

`∑_{a ≤ A} w_d(a) ≤ ∏_{p ≤ A} W_d(p)` (Euler product of the non-negative multiplicative `w_d`), and
`W_d(p) ≤ W'(p) f₁(p)^{[p ∣ d]}` with `W'(2) = 1 + 2^{1/3}`, `W'(p) = 1 + (p^{1/3} + p^{2/3})/(p(p−1))`.
For `A ≥ 1000`: `∏_{p ≤ 1000} W'(p) ≤ 7.2863` (rational cube roots, checked by the kernel), and
`∏_{1000 < p ≤ A} W'(p) ≤ exp(1.102 ∑_{n > 1000} n^{−4/3}) ≤ e^{0.3306} ≤ 1.494`.
-/

open Finset Real ArithmeticFunction

namespace TernaryGoldbach.Prelim.RamPf

open TernaryGoldbach.Prelim (f1pP f1qP)
open TernaryGoldbach.Prelim.Small (PK primesBelow_eq PK_nodup)

/-- `W'(p)`. -/
noncomputable def Wp (p : ℕ) : ℝ :=
  if p = 2 then 1 + (2 : ℝ) ^ ((1 : ℝ) / 3)
  else 1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1))

theorem Wp_one_le {p : ℕ} (hp : 2 ≤ p) : 1 ≤ Wp p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  unfold Wp; split_ifs
  · have : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    linarith
  · have : 0 ≤ ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      apply div_nonneg (by positivity); nlinarith
    linarith

theorem rpow_two_thirds (x : ℝ) (hx : 0 ≤ x) : x ^ ((2 : ℝ) / 3) = (x ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem rpow_third_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem rpow_sq_third (p : ℕ) :
    ((p ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = ((p : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [Nat.cast_pow, ← Real.rpow_natCast ((p : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_natCast (((p : ℝ) ^ ((1 : ℝ) / 3))), ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- The `t = p^{1/3}` forms. -/
theorem Wp_t {p : ℕ} (hp : p.Prime) :
    Wp p = if p = 2 then 1 + (p : ℝ) ^ ((1 : ℝ) / 3) else
      1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + ((p : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  unfold Wp
  by_cases h : p = 2
  · rw [if_pos h, if_pos h, h]; norm_num
  · rw [if_neg h, if_neg h, rpow_two_thirds _ (Nat.cast_nonneg _)]

theorem f1pP_t {p : ℕ} (hp : p.Prime) :
    f1pP p = (1 + 1 / ((p : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) /
      (1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + ((p : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold f1pP
  rw [Real.rpow_neg hp0.le, show (2 / 3 : ℝ) = 2 / 3 from rfl, rpow_two_thirds _ hp0.le, inv_eq_one_div]

/-- The local factor: `W_d(p) ≤ W'(p) · (f₁(p) if p ∣ d)`. -/
theorem Wd_le {d p : ℕ} (hp : p.Prime) :
    1 + |hD d p| * (p : ℝ) ^ ((1 : ℝ) / 3) + |hD d (p ^ 2)| * ((p ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      Wp p * (if p ∣ d then f1pP p else 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Wp_t hp, f1pP_t hp, rpow_sq_third, hD_p' hp, hD_p2' hp]
  set t := (p : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have ht3 : t ^ 3 = p := rpow_third_cube _ hp0.le
  have ht1 : 1 ≤ t := Real.one_le_rpow hp1.le (by norm_num)
  by_cases h2 : p = 2
  · subst h2
    have ht126 : t ≤ 1.26 := by
      rw [ht]; exact rpow_third_le_of (by norm_num) (by norm_num) (by norm_num)
    by_cases hd : 2 ∣ d
    · simp only [hd, if_true, zero_add, zero_mul, abs_zero, add_zero]
      norm_num
      have hden : 0 < 1 + (t + t ^ 2) / 2 := by positivity
      rw [mul_div_assoc', le_div_iff₀ hden, one_mul]
      have hinv : 0.6 ≤ (t ^ 2)⁻¹ := by
        rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    · simp only [hd, if_false, if_true, mul_one]
      norm_num
  · have hp3 : (3 : ℝ) ≤ p := by
      have := hp.two_le; exact_mod_cast (by omega : 3 ≤ p)
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    by_cases hd : p ∣ d
    · simp only [hd, if_true, h2, if_false, zero_add, zero_mul, abs_zero, add_zero]
      have hL : 0 < 1 + (t + t ^ 2) / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hL.ne', abs_div, abs_neg, abs_one,
        abs_of_pos hp0, ← ht3]
      rw [show 1 + 1 / t ^ 3 * t = 1 + 1 / t ^ 2 by field_simp]
    · simp only [hd, if_false, h2, mul_one]
      have hden1 : 0 < (p : ℝ) - 1 := by linarith
      have e1 : 1 / ((p : ℝ) - 1) + -1 / (p : ℝ) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        field_simp; ring
      have e2 : 1 / ((p : ℝ) - 1) * (-1 / (p : ℝ)) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        field_simp
      rw [e1, e2, abs_neg, abs_of_pos (by positivity)]
      rw [show 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) * t + 1 / ((p : ℝ) * ((p : ℝ) - 1)) * t ^ 2 =
        1 + (t + t ^ 2) / ((p : ℝ) * ((p : ℝ) - 1)) by ring]

theorem cube_root_1000 {p : ℕ} (hp : 1000 ≤ p) : 10 ≤ (p : ℝ) ^ ((1 : ℝ) / 3) := by
  have hp1 : (1000 : ℝ) ≤ p := by exact_mod_cast hp
  have := Real.rpow_le_rpow (by norm_num) hp1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [show (1000 : ℝ) = 10 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at this

/-- `f₁(p) ≥ 1` for `p ≥ 1000`. -/
theorem one_le_f1pP {p : ℕ} (hpp : p.Prime) (hp : 1000 ≤ p) : 1 ≤ f1pP p := by
  have hp0 : (0 : ℝ) < p := by positivity
  rw [f1pP_t hpp]
  set t := (p : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht3 : t ^ 3 = p := rpow_third_cube _ hp0.le
  have ht10 : 10 ≤ t := cube_root_1000 hp
  have ht0 : 0 < t := by linarith
  rw [← ht3]
  have ht31 : 1 < t ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) ht10 3; linarith
  have hden : 0 < t ^ 3 * (t ^ 3 - 1) := mul_pos (by positivity) (by linarith)
  have hL : 0 < 1 + (t + t ^ 2) / (t ^ 3 * (t ^ 3 - 1)) := by positivity
  rw [le_div_iff₀ hL, one_mul, add_le_add_iff_left, div_le_div_iff₀ hden (by positivity)]
  have h1 : t + 2 ≤ t ^ 3 := by nlinarith
  have h2 : 0 ≤ t ^ 3 * (t ^ 3 - t - 2) := mul_nonneg (by positivity) (by linarith)
  nlinarith

/-! ### The head `p ≤ 1000` -/

/-- `(p, ⌈10⁴ p^{1/3}⌉)` for odd primes `p ≤ 1000`. -/
def CR : List (ℕ × ℕ) := [(3, 14423), (5, 17100), (7, 19130), (11, 22240), (13, 23514), (17, 25713), (19, 26685), (23, 28439), (29, 30724), (31, 31414), (37, 33323), (41, 34483), (43, 35034), (47, 36089), (53, 37563), (59, 38930), (61, 39365), (67, 40616), (71, 41409), (73, 41794), (79, 42909), (83, 43621), (89, 44648), (97, 45948), (101, 46571), (103, 46876), (107, 47475), (109, 47769), (113, 48346), (127, 50266), (131, 50788), (137, 51552), (139, 51802), (149, 53015), (151, 53251), (157, 53947), (163, 54626), (167, 55069), (173, 55721), (179, 56358), (181, 56567), (191, 57590), (193, 57790), (197, 58187), (199, 58383), (211, 59534), (223, 60642), (227, 61002), (229, 61181), (233, 61535), (239, 62059), (241, 62231), (251, 63080), (257, 63579), (263, 64070), (269, 64554), (271, 64713), (277, 65187), (281, 65500), (283, 65655), (293, 66419), (307, 67460), (311, 67752), (313, 67897), (317, 68185), (331, 69174), (337, 69590), (347, 70272), (349, 70406), (353, 70674), (359, 71072), (367, 71596), (373, 71985), (379, 72368), (383, 72622), (389, 72999), (397, 73496), (401, 73742), (409, 74230), (419, 74830), (421, 74949), (431, 75537), (433, 75654), (439, 76002), (443, 76232), (449, 76575), (457, 77027), (461, 77251), (463, 77362), (467, 77585), (479, 78243), (487, 78677), (491, 78891), (499, 79318), (503, 79529), (509, 79844), (521, 80467), (523, 80569), (541, 81483), (547, 81783), (557, 82279), (563, 82573), (569, 82865), (571, 82962), (577, 83252), (587, 83730), (593, 84014), (599, 84297), (601, 84391), (607, 84671), (613, 84949), (617, 85133), (619, 85225), (631, 85772), (641, 86223), (643, 86312), (647, 86491), (653, 86757), (659, 87022), (661, 87110), (673, 87634), (677, 87808), (683, 88066), (691, 88409), (701, 88833), (709, 89170), (719, 89587), (727, 89918), (733, 90165), (739, 90410), (743, 90573), (751, 90897), (757, 91138), (761, 91299), (769, 91617), (773, 91776), (787, 92327), (797, 92716), (809, 93179), (811, 93256), (821, 93638), (823, 93714), (827, 93865), (829, 93941), (839, 94317), (853, 94839), (857, 94987), (859, 95060), (863, 95208), (877, 95720), (881, 95865), (883, 95938), (887, 96082), (907, 96799), (911, 96941), (919, 97224), (929, 97576), (937, 97855), (941, 97994), (947, 98202), (953, 98409), (967, 98888), (971, 99024), (977, 99228), (983, 99431), (991, 99700), (997, 99900)]

theorem CR_fst : (PK.map Prod.fst).filter (· < 1001) = 2 :: CR.map Prod.fst := by decide +kernel

theorem CR_ok : CR.all (fun pc => decide (pc.1 * 10 ^ 12 ≤ pc.2 ^ 3) && decide (3 ≤ pc.1)) = true := by
  decide +kernel

/-- Lookup in a list of pairs. -/
def lk : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (a, b) :: l, p => if a = p then b else lk l p

theorem lk_mem : ∀ (l : List (ℕ × ℕ)), (l.map Prod.fst).Nodup → ∀ pc ∈ l, lk l pc.1 = pc.2
  | [], _, pc, h => by simp at h
  | (a, b) :: l, hnd, pc, h => by
    rcases List.mem_cons.1 h with h | h
    · subst h; simp [lk]
    · have ha : a ≠ pc.1 := by
        intro e
        have := (List.nodup_cons.1 hnd).1
        exact this (by rw [e]; exact List.mem_map.2 ⟨pc, h, rfl⟩)
      simp only [lk, if_neg ha]
      exact lk_mem l (List.nodup_cons.1 hnd).2 pc h

/-- The rational bound for `W'(p)`. -/
def qQ (p : ℕ) : ℚ :=
  if p = 2 then 226 / 100 else
    1 + ((lk CR p : ℚ) / 10 ^ 4 + ((lk CR p : ℚ) / 10 ^ 4) ^ 2) / (p * (p - 1))

theorem qQ_prod : ((2 :: CR.map Prod.fst).map qQ).prod ≤ 72863 / 10000 := by decide +kernel

theorem Wp_le_qQ {p : ℕ} (hp : p ∈ 2 :: CR.map Prod.fst) : Wp p ≤ (qQ p : ℝ) := by
  rcases List.mem_cons.1 hp with h | h
  · subst h
    simp only [Wp, qQ, if_true]
    have : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 1.26 := rpow_third_le_of (by norm_num) (by norm_num) (by norm_num)
    push_cast; linarith
  · obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 h
    have hok := List.all_eq_true.1 CR_ok pc hpc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hcube, hp3⟩ := hok
    have hlk : lk CR pc.1 = pc.2 := lk_mem CR (by decide +kernel) pc hpc
    simp only [qQ, show pc.1 ≠ 2 by omega, if_false, hlk, Wp]
    have hp0 : (0 : ℝ) < pc.1 := by positivity
    have hp3' : (3 : ℝ) ≤ pc.1 := by exact_mod_cast hp3
    set c : ℝ := (pc.2 : ℝ) / 10 ^ 4 with hc
    have hc0 : 0 ≤ c := by positivity
    have ht : (pc.1 : ℝ) ^ ((1 : ℝ) / 3) ≤ c := rpow_third_le_of hp0.le hc0 (by
      have h1 : ((pc.1 * 10 ^ 12 : ℕ) : ℝ) ≤ ((pc.2 ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcube
      push_cast at h1
      rw [hc, div_pow, le_div_iff₀ (by positivity)]; linarith)
    have ht0 : 0 ≤ (pc.1 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hp0.le _
    rw [rpow_two_thirds _ hp0.le]
    have hden : 0 < (pc.1 : ℝ) * ((pc.1 : ℝ) - 1) := by nlinarith
    have hnum : (pc.1 : ℝ) ^ ((1 : ℝ) / 3) + ((pc.1 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ≤ c + c ^ 2 := by
      nlinarith
    have := div_le_div_of_nonneg_right hnum hden.le
    push_cast
    rw [← hc]
    linarith

theorem primesBelow_1001 : Nat.primesBelow 1001 = (2 :: CR.map Prod.fst).toFinset := by
  rw [← CR_fst, List.toFinset_filter, ← primesBelow_eq]
  ext p
  simp only [Nat.mem_primesBelow, mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨a, b⟩ => ⟨⟨by omega, b⟩, a⟩, fun ⟨⟨_, b⟩, a⟩ => ⟨a, b⟩⟩

theorem prod_head : ∏ p ∈ Nat.primesBelow 1001, Wp p ≤ 7.2863 := by
  have hnd : (2 :: CR.map Prod.fst).Nodup := by rw [← CR_fst]; exact PK_nodup.filter _
  have h1 : ∏ p ∈ Nat.primesBelow 1001, Wp p ≤ ∏ p ∈ Nat.primesBelow 1001, (qQ p : ℝ) := by
    refine Finset.prod_le_prod₀ (fun p hp => le_trans (by norm_num) (Wp_one_le
      (Nat.mem_primesBelow.1 hp).2.two_le)) (fun p hp => Wp_le_qQ ?_)
    rw [primesBelow_1001, List.mem_toFinset] at hp; exact hp
  refine h1.trans ?_
  rw [← Rat.cast_prod, primesBelow_1001, List.prod_toFinset _ hnd]
  have := (Rat.cast_le (K := ℝ)).2 qQ_prod
  push_cast at this ⊢
  linarith

/-! ### The tail `p > 1000` -/

theorem Wp_le_tail {p : ℕ} (hp : p.Prime) (h : 1000 < p) :
    Wp p ≤ 1 + 1.102 * (p : ℝ) ^ (-(4 / 3 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by positivity
  rw [Wp_t hp, if_neg (by omega)]
  set t := (p : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht3 : t ^ 3 = p := rpow_third_cube _ hp0.le
  have ht10 : 10 ≤ t := cube_root_1000 h.le
  have ht0 : 0 < t := by linarith
  have h43 : (p : ℝ) ^ (-(4 / 3 : ℝ)) = 1 / t ^ 4 := by
    rw [Real.rpow_neg hp0.le, ht, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, one_div]; norm_num
  rw [h43, ← ht3]
  have ht31 : 1 < t ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) ht10 3; linarith
  have hden : 0 < t ^ 3 * (t ^ 3 - 1) := mul_pos (by positivity) (by linarith)
  rw [add_le_add_iff_left, mul_one_div, div_le_div_iff₀ hden (by positivity)]
  have key : t ^ 2 + 1.102 ≤ 0.102 * t ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.2 ht10) (sq_nonneg t)]
  have : 0 ≤ t ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ t ^ 4)]

theorem sum_rpow_tail (A : ℕ) (hA : 1000 ≤ A) :
    ∑ n ∈ Ioc 1000 A, (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(4 / 3 : ℝ))) (Set.Icc (1000 : ℕ) (A : ℕ)) := by
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a := by
      have := ha.1; push_cast at this; linarith
    exact Real.rpow_le_rpow_of_nonpos ha0 hab (by norm_num)
  have h := hanti.sum_le_integral_Ico hA
  have hre : ∑ n ∈ Ioc 1000 A, (n : ℝ) ^ (-(4 / 3 : ℝ)) =
      ∑ i ∈ Ico 1000 A, ((i + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have e : Ioc 1000 A = Ico (1000 + 1) (A + 1) := by
      ext n; simp only [mem_Ioc, mem_Ico]; omega
    rw [e, ← Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-(4 / 3 : ℝ))) 1000 A 1]
  rw [hre]
  refine h.trans ?_
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [Set.uIcc_of_le (by exact_mod_cast hA)]; intro h0; have := h0.1; norm_num at this⟩)]
  have h1000 : ((1000 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ) + 1) = 1 / 10 := by
    rw [show (-(4 / 3 : ℝ) + 1) = -(1 / 3) by norm_num, Real.rpow_neg (by norm_num)]
    rw [show ((1000 : ℕ) : ℝ) = 10 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h1000]
  have hA0 : 0 ≤ ((A : ℕ) : ℝ) ^ (-(4 / 3 : ℝ) + 1) := by positivity
  rw [show (-(4 / 3 : ℝ) + 1) = -(1 / 3) by norm_num] at hA0 ⊢
  rw [show (-(1 / 3 : ℝ)) = -(1 / 3) from rfl]
  have : (((A : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) - 1 / 10) / (-(1 / 3)) =
      3 * (1 / 10 - ((A : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
  rw [this]; linarith

theorem prod_tail {A : ℕ} (hA : 1000 ≤ A) :
    ∏ p ∈ (Nat.primesBelow (A + 1)).filter (fun p => ¬ p ≤ 1000), Wp p ≤ 1.494 := by
  set S := (Nat.primesBelow (A + 1)).filter (fun p => ¬ p ≤ 1000)
  have hsub : S ⊆ Ioc 1000 A := by
    intro p hp
    simp only [S, mem_filter, Nat.mem_primesBelow] at hp
    exact mem_Ioc.2 ⟨by omega, by omega⟩
  set y : ℕ → ℝ := fun n => 1.102 * (n : ℝ) ^ (-(4 / 3 : ℝ))
  have hy0 : ∀ n, 0 ≤ y n := fun n => by simp only [y]; positivity
  have h1 : ∏ p ∈ S, Wp p ≤ ∏ p ∈ S, (1 + y p) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le
      exact le_trans (by norm_num) (Wp_one_le this)
    · have hp := mem_filter.1 hp
      exact Wp_le_tail (Nat.mem_primesBelow.1 hp.1).2 (by omega)
  have h2 : ∏ p ∈ S, (1 + y p) ≤ ∏ n ∈ Ioc 1000 A, (1 + y n) :=
    prod_le_prod_of_subset_of_one_le₀ hsub (fun n _ => by linarith [hy0 n])
      (fun n _ _ => by linarith [hy0 n])
  have h3 : ∏ n ∈ Ioc 1000 A, (1 + y n) ≤ Real.exp (∑ n ∈ Ioc 1000 A, y n) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun n _ => by linarith [hy0 n]) (fun n _ => ?_)
    have := Real.add_one_le_exp (y n); linarith
  have hs : ∑ n ∈ Ioc 1000 A, y n ≤ 0.3306 := by
    simp only [y]; rw [← mul_sum]
    have := sum_rpow_tail A hA; nlinarith
  have h4 : Real.exp (∑ n ∈ Ioc 1000 A, y n) ≤ Real.exp 0.3306 := Real.exp_le_exp.2 hs
  have h5 : Real.exp 0.3306 ≤ 1.494 := by
    have := Real.add_one_le_exp (-0.3306)
    have he : Real.exp 0.3306 * Real.exp (-0.3306) = 1 := by rw [← Real.exp_add]; norm_num
    have hp0 := Real.exp_pos 0.3306
    nlinarith
  linarith

/-- **`∑_{a ≤ A} |h_d(a)| a^{1/3} ≤ 11 f₁(d)`** for `d ≥ 1`. -/
theorem sum_wD_le {d : ℕ} (hd : 1 ≤ d) (A : ℕ) : ∑ a ∈ Icc 1 A, wD d a ≤ 11 * f1qP d := by
  set A' := max A 1000 with hA'
  have hA1 : 1000 ≤ A' := le_max_right _ _
  have hmono : ∑ a ∈ Icc 1 A, wD d a ≤ ∑ a ∈ Icc 1 A', wD d a :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (le_max_left _ _)) fun a _ _ => wD_nonneg d a
  refine hmono.trans ?_
  have hE := sum_le_euler' (f := wD d) (wD_nonneg d) (wD_one d) (fun h => wD_mul d h)
    (fun hp => by simpa [Real.norm_eq_abs, abs_of_nonneg (wD_nonneg _ _)] using (hasSum_wD (d := d) hp).summable) A'
  refine hE.trans ?_
  set P := Nat.primesBelow (A' + 1)
  have hloc : ∀ p ∈ P, ∑' e, wD d (p ^ e) ≤ Wp p * (if p ∣ d then f1pP p else 1) := by
    intro p hp
    rw [(hasSum_wD (Nat.mem_primesBelow.1 hp).2).tsum_eq]
    exact Wd_le (Nat.mem_primesBelow.1 hp).2
  have hf1 : ∀ p : ℕ, p.Prime → 0 < f1pP p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    unfold f1pP
    have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    positivity
  have h1 : ∏ p ∈ P, ∑' e, wD d (p ^ e) ≤ ∏ p ∈ P, (Wp p * (if p ∣ d then f1pP p else 1)) :=
    Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun e => wD_nonneg d _) hloc
  refine h1.trans ?_
  rw [prod_mul_distrib]
  -- the `f₁` part
  have hg : ∏ p ∈ P, (if p ∣ d then f1pP p else 1) ≤ f1qP d := by
    rw [prod_ite, prod_const_one, mul_one, f1qP]
    refine prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, P, Nat.mem_primesBelow] at hp
      exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, by omega⟩
    · intro p hp
      exact (hf1 p (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2).le
    · intro p hp hnot
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have : ¬ p < A' + 1 := by
        intro hlt
        exact hnot (mem_filter.2 ⟨Nat.mem_primesBelow.2 ⟨hlt, hpp⟩, hpd⟩)
      exact one_le_f1pP hpp (by omega)
  have hg0 : 0 ≤ ∏ p ∈ P, (if p ∣ d then f1pP p else 1) :=
    prod_nonneg fun p hp => by
      split_ifs
      · exact (hf1 p (Nat.mem_primesBelow.1 hp).2).le
      · norm_num
  -- the `W'` part
  have hW : ∏ p ∈ P, Wp p ≤ 11 := by
    rw [← prod_filter_mul_prod_filter_not P (fun p => p ≤ 1000)]
    have hhead : P.filter (fun p => p ≤ 1000) = Nat.primesBelow 1001 := by
      ext p; simp only [mem_filter, P, Nat.mem_primesBelow]
      exact ⟨fun ⟨⟨_, b⟩, c⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨⟨by omega, b⟩, by omega⟩⟩
    rw [hhead]
    have a1 := prod_head
    have a2 := prod_tail hA1
    have b1 : 0 ≤ ∏ p ∈ Nat.primesBelow 1001, Wp p :=
      prod_nonneg fun p hp => le_trans (by norm_num) (Wp_one_le (Nat.mem_primesBelow.1 hp).2.two_le)
    have b2 : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p ≤ 1000), Wp p :=
      prod_nonneg fun p hp => le_trans (by norm_num)
        (Wp_one_le (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le)
    nlinarith
  have hW0 : 0 ≤ ∏ p ∈ P, Wp p :=
    prod_nonneg fun p hp => le_trans (by norm_num) (Wp_one_le (Nat.mem_primesBelow.1 hp).2.two_le)
  exact mul_le_mul hW hg hg0 (by norm_num)

end TernaryGoldbach.Prelim.RamPf
