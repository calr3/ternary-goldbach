import TernaryGoldbach.Prelim.SmallProdAp
import TernaryGoldbach.Prelim.SmallPsi

/-!
# `ψ(n) − θ(n) < 1.4262 √n` for `n ≤ 10⁶`, checked by the kernel

`ψ(n) − θ(n) = ∑_{n' ≤ n, not prime} Λ(n') ≤ ∑_{p < 1001} ∑_{2 ≤ k ≤ 20} [p^k ≤ n] log p`
(`nonprime_le_T`). With upper bounds `log p < u_p/10⁹` (checked by `chkStep`), the right side is at
most `T(n)/10⁹`, where `T` is computed by the kernel; `T` is nondecreasing, so on each of 31 blocks
`[a, b)` it suffices that `T(b − 1)² < 1.4262² a · 10¹⁸`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim.SmallNP

open TernaryGoldbach.Prelim.Small (PK chkStep log_lt_of_chk)

/-- The primes `p < 1001` with `u_p > 10⁹ log p`. -/
def PU : List (ℕ × ℕ) := [(2, 693147184), (3, 1098612292), (5, 1609437916), (7, 1945910153), (11, 2397895276), (13, 2564949361), (17, 2833213348), (19, 2944438983), (23, 3135494219), (29, 3367295833), (31, 3433987208), (37, 3610917916), (41, 3713572070), (43, 3761200119), (47, 3850147605), (53, 3970291917), (59, 4077537447), (61, 4110873868), (67, 4204692623), (71, 4262679881), (73, 4290459445), (79, 4369447856), (83, 4418840611), (89, 4488636373), (97, 4574710982), (101, 4615120520), (103, 4634728992), (107, 4672828838), (109, 4691347886), (113, 4727387822), (127, 4844187090), (131, 4875197327), (137, 4919980929), (139, 4934473937), (149, 5003946309), (151, 5017279840), (157, 5056245809), (163, 5093750204), (167, 5117993816), (173, 5153291598), (179, 5187385809), (181, 5198497035), (191, 5252273432), (193, 5262690192), (197, 5283203732), (199, 5293304828), (211, 5351858137), (223, 5407171775), (227, 5424950021), (229, 5433722007), (233, 5451038457), (239, 5476463555), (241, 5484796937), (251, 5525452943), (257, 5549076088), (263, 5572154036), (269, 5594711383), (271, 5602118824), (277, 5624017510), (281, 5638354673), (283, 5645446901), (293, 5680172613), (307, 5726847751), (311, 5739792916), (313, 5746203194), (317, 5758901777), (331, 5802118379), (337, 5820082934), (347, 5849324783), (349, 5855071926), (353, 5866468060), (359, 5883322392), (367, 5905361852), (373, 5921578423), (379, 5937536209), (383, 5948034993), (389, 5963579347), (397, 5983936284), (401, 5993961431), (409, 6013715160), (419, 6037870923), (421, 6042632837), (431, 6066108094), (433, 6070737732), (439, 6084499417), (443, 6093569774), (449, 6107022891), (457, 6124683394), (461, 6133398046), (463, 6137727058), (467, 6146329261), (479, 6171700601), (487, 6188264127), (491, 6196444131), (499, 6212606099), (503, 6220590174), (509, 6232448020), (521, 6255750045), (523, 6259581468), (541, 6293419282), (547, 6304448806), (557, 6322565243), (563, 6333279632), (569, 6343880438), (571, 6347389213), (577, 6357842270), (587, 6375024823), (593, 6385194402), (599, 6395261602), (601, 6398594938), (607, 6408528795), (613, 6418364939), (617, 6424869027), (619, 6428105276), (631, 6447305866), (641, 6463029460), (643, 6466144728), (647, 6472346298), (653, 6481577133), (659, 6490723538), (661, 6493753843), (673, 6511745333), (677, 6517671276), (683, 6526494863), (691, 6538139827), (701, 6552507891), (709, 6563855530), (719, 6577861361), (727, 6588926481), (733, 6597145705), (739, 6605297924), (743, 6610696048), (751, 6621405655), (757, 6629363257), (761, 6634633361), (769, 6645090973), (773, 6650279052), (787, 6668228252), (797, 6680854682), (809, 6695798921), (811, 6698268058), (821, 6710523113), (823, 6712956204), (827, 6717804699), (829, 6720220159), (839, 6732210710), (853, 6748759551), (857, 6753437922), (859, 6755768925), (863, 6760414695), (877, 6776506996), (881, 6781057629), (883, 6783325204), (887, 6787844986), (907, 6810142454), (911, 6814542901), (919, 6823286126), (929, 6834108742), (937, 6842683286), (941, 6846943143), (947, 6853299097), (953, 6859614907), (967, 6874198499), (971, 6878326472), (977, 6884486656), (983, 6890609124), (991, 6898714538), (997, 6904750773)]

theorem PU_fst : PU.map Prod.fst = (PK.map Prod.fst).filter (· < 1001) := by decide +kernel

theorem PU_log_chk : PU.all (fun pu => chkStep pu.2 (10 ^ 9) 1 pu.1) = true := by decide +kernel

/-- `#{2 ≤ k ≤ 20 : p^k ≤ n} · u`. -/
def cntU (n : ℕ) (pu : ℕ × ℕ) : ℕ := ((Finset.Icc 2 20).filter (fun k => pu.1 ^ k ≤ n)).card * pu.2

/-- `T(n) = ∑_{p} #{2 ≤ k ≤ 20 : p^k ≤ n} u_p`. -/
def T (n : ℕ) : ℕ := (PU.map (cntU n)).sum

theorem blk_0 : T 8 ^ 2 * 10 ^ 8 < 203404644 * 1 * 10 ^ 18 := by decide +kernel
theorem blk_1 : T 24 ^ 2 * 10 ^ 8 < 203404644 * 9 * 10 ^ 18 := by decide +kernel
theorem blk_2 : T 48 ^ 2 * 10 ^ 8 < 203404644 * 25 * 10 ^ 18 := by decide +kernel
theorem blk_3 : T 80 ^ 2 * 10 ^ 8 < 203404644 * 49 * 10 ^ 18 := by decide +kernel
theorem blk_4 : T 124 ^ 2 * 10 ^ 8 < 203404644 * 81 * 10 ^ 18 := by decide +kernel
theorem blk_5 : T 168 ^ 2 * 10 ^ 8 < 203404644 * 125 * 10 ^ 18 := by decide +kernel
theorem blk_6 : T 242 ^ 2 * 10 ^ 8 < 203404644 * 169 * 10 ^ 18 := by decide +kernel
theorem blk_7 : T 342 ^ 2 * 10 ^ 8 < 203404644 * 243 * 10 ^ 18 := by decide +kernel
theorem blk_8 : T 360 ^ 2 * 10 ^ 8 < 203404644 * 343 * 10 ^ 18 := by decide +kernel
theorem blk_9 : T 511 ^ 2 * 10 ^ 8 < 203404644 * 361 * 10 ^ 18 := by decide +kernel
theorem blk_10 : T 624 ^ 2 * 10 ^ 8 < 203404644 * 512 * 10 ^ 18 := by decide +kernel
theorem blk_11 : T 840 ^ 2 * 10 ^ 8 < 203404644 * 625 * 10 ^ 18 := by decide +kernel
theorem blk_12 : T 1330 ^ 2 * 10 ^ 8 < 203404644 * 841 * 10 ^ 18 := by decide +kernel
theorem blk_13 : T 1848 ^ 2 * 10 ^ 8 < 203404644 * 1331 * 10 ^ 18 := by decide +kernel
theorem blk_14 : T 2208 ^ 2 * 10 ^ 8 < 203404644 * 1849 * 10 ^ 18 := by decide +kernel
theorem blk_15 : T 2808 ^ 2 * 10 ^ 8 < 203404644 * 2209 * 10 ^ 18 := by decide +kernel
theorem blk_16 : T 3720 ^ 2 * 10 ^ 8 < 203404644 * 2809 * 10 ^ 18 := by decide +kernel
theorem blk_17 : T 5040 ^ 2 * 10 ^ 8 < 203404644 * 3721 * 10 ^ 18 := by decide +kernel
theorem blk_18 : T 6858 ^ 2 * 10 ^ 8 < 203404644 * 5041 * 10 ^ 18 := by decide +kernel
theorem blk_19 : T 10200 ^ 2 * 10 ^ 8 < 203404644 * 6859 * 10 ^ 18 := by decide +kernel
theorem blk_20 : T 14640 ^ 2 * 10 ^ 8 < 203404644 * 10201 * 10 ^ 18 := by decide +kernel
theorem blk_21 : T 22200 ^ 2 * 10 ^ 8 < 203404644 * 14641 * 10 ^ 18 := by decide +kernel
theorem blk_22 : T 32040 ^ 2 * 10 ^ 8 < 203404644 * 22201 * 10 ^ 18 := by decide +kernel
theorem blk_23 : T 50652 ^ 2 * 10 ^ 8 < 203404644 * 32041 * 10 ^ 18 := by decide +kernel
theorem blk_24 : T 76728 ^ 2 * 10 ^ 8 < 203404644 * 50653 * 10 ^ 18 := by decide +kernel
theorem blk_25 : T 120408 ^ 2 * 10 ^ 8 < 203404644 * 76729 * 10 ^ 18 := by decide +kernel
theorem blk_26 : T 187488 ^ 2 * 10 ^ 8 < 203404644 * 120409 * 10 ^ 18 := by decide +kernel
theorem blk_27 : T 310248 ^ 2 * 10 ^ 8 < 203404644 * 187489 * 10 ^ 18 := by decide +kernel
theorem blk_28 : T 493038 ^ 2 * 10 ^ 8 < 203404644 * 310249 * 10 ^ 18 := by decide +kernel
theorem blk_29 : T 822648 ^ 2 * 10 ^ 8 < 203404644 * 493039 * 10 ^ 18 := by decide +kernel
theorem blk_30 : T 1000000 ^ 2 * 10 ^ 8 < 203404644 * 822649 * 10 ^ 18 := by decide +kernel

theorem PU_nodup : PU.Nodup := by
  have h : (PU.map Prod.fst).Nodup := by
    rw [PU_fst]; exact TernaryGoldbach.Prelim.Small.PK_nodup.filter _
  exact h.of_map _

theorem mem_PU_fst {p : ℕ} : p ∈ PU.map Prod.fst ↔ p.Prime ∧ p < 1001 := by
  rw [PU_fst, List.mem_filter]
  have h := TernaryGoldbach.Prelim.Small.primesBelow_eq
  have e : p ∈ PK.map Prod.fst ↔ p ∈ Nat.primesBelow 10000 := by
    rw [h, List.mem_toFinset]
  rw [e, Nat.mem_primesBelow]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, hp⟩, h1⟩; exact ⟨hp, h1⟩
  · rintro ⟨hp, h1⟩; exact ⟨⟨by omega, hp⟩, h1⟩

theorem log_lt_PU {pu : ℕ × ℕ} (h : pu ∈ PU) : Real.log pu.1 < (pu.2 : ℝ) / 10 ^ 9 := by
  have hc := List.all_eq_true.1 PU_log_chk pu h
  have hp : pu.1.Prime := (mem_PU_fst.1 (List.mem_map_of_mem h)).1
  have := log_lt_of_chk (by norm_num) hp.pos hc
  push_cast at this; linarith

/-- Pointwise domination of the non-prime prime powers `m ≤ 10⁶`. -/
theorem nonprime_term_le' {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 10 ^ 6) :
    (if m.Prime then 0 else (Λ m : ℝ)) ≤
      ∑ pu ∈ PU.toFinset, ∑ k ∈ Icc 2 20, (if m = pu.1 ^ k then Real.log pu.1 else 0) := by
  have hnonneg : ∀ pu ∈ PU.toFinset, ∀ k ∈ Icc 2 20,
      0 ≤ (if m = pu.1 ^ k then Real.log pu.1 else 0) := by
    intro pu _ k _
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  split_ifs with hprime
  · exact sum_nonneg fun pu hpu => sum_nonneg fun k hk => hnonneg pu hpu k hk
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h; have : k = 1 := by omega
      subst this; exact hprime (by simpa using hp)
    have hp2 := hp.two_le
    have hpk : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
    have hp1001 : p < 1001 := by
      by_contra h; push Not at h
      have : 1001 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h 2
      omega
    have hk20 : k ≤ 20 := by
      by_contra h; push Not at h
      have : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
      have : 2 ^ 21 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    obtain ⟨pu, hpu, hpu1⟩ := List.mem_map.1 (mem_PU_fst.2 ⟨hp, hp1001⟩)
    have hΛ : (Λ (p ^ k) : ℝ) = Real.log p := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [hΛ]
    have hmem : pu ∈ PU.toFinset := List.mem_toFinset.2 hpu
    refine le_trans ?_ (single_le_sum (fun pu hpu => sum_nonneg fun k hk => hnonneg pu hpu k hk) hmem)
    refine le_trans ?_ (single_le_sum (fun k hk => hnonneg pu hmem k hk) (mem_Icc.2 ⟨hk2, hk20⟩))
    simp [hpu1]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
    exact sum_nonneg fun pu hpu => sum_nonneg fun k hk => hnonneg pu hpu k hk

theorem T_eq (n : ℕ) : T n = ∑ pu ∈ PU.toFinset, cntU n pu := by
  unfold T; rw [List.sum_toFinset _ PU_nodup]

/-- **`ψ(n) − θ(n) ≤ T(n)/10⁹`** for `n ≤ 10⁶`. -/
theorem nonprime_le_T {n : ℕ} (hn : n ≤ 10 ^ 6) :
    ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) ≤ (T n : ℝ) / 10 ^ 9 := by
  refine (sum_le_sum fun m hm => nonprime_term_le' (mem_Icc.1 hm).1
    ((mem_Icc.1 hm).2.trans hn)).trans ?_
  rw [sum_comm]
  have hpu : ∀ pu ∈ PU.toFinset, ∑ m ∈ Icc 1 n, ∑ k ∈ Icc 2 20,
      (if m = pu.1 ^ k then Real.log pu.1 else 0) ≤ (cntU n pu : ℝ) / 10 ^ 9 := by
    intro pu hpu
    have hpu' := List.mem_toFinset.1 hpu
    have hp : pu.1.Prime := (mem_PU_fst.1 (List.mem_map_of_mem hpu')).1
    have hl := log_lt_PU hpu'
    rw [sum_comm]
    have h1 : ∀ k ∈ Icc 2 20, ∑ m ∈ Icc 1 n, (if m = pu.1 ^ k then Real.log pu.1 else 0) =
        if pu.1 ^ k ≤ n then Real.log pu.1 else 0 := by
      intro k _
      rw [sum_ite_eq']
      have : 1 ≤ pu.1 ^ k := Nat.one_le_pow _ _ hp.pos
      simp only [mem_Icc]
      split_ifs <;> first | rfl | omega
    rw [sum_congr rfl h1, ← sum_filter, sum_const, nsmul_eq_mul]
    unfold cntU; push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hl.le (Nat.cast_nonneg _)
  refine (sum_le_sum hpu).trans (le_of_eq ?_)
  rw [T_eq, Nat.cast_sum, sum_div]

theorem T_mono {n n' : ℕ} (h : n ≤ n') : T n ≤ T n' := by
  rw [T_eq, T_eq]
  refine sum_le_sum fun pu _ => ?_
  unfold cntU
  refine Nat.mul_le_mul_right _ (card_le_card fun k hk => ?_)
  simp only [mem_filter] at hk ⊢
  exact ⟨hk.1, le_trans hk.2 h⟩

theorem block_ok {a c n : ℕ} (hblk : T c ^ 2 * 10 ^ 8 < 203404644 * a * 10 ^ 18)
    (han : a ≤ n) (hnc : n ≤ c) (hn : n ≤ 10 ^ 6) (ha : 1 ≤ a) :
    ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) < 1.4262 * √n := by
  refine (nonprime_le_T hn).trans_lt ?_
  have hT : T n ≤ T c := T_mono hnc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hblk' : ((T c : ℝ)) ^ 2 * 10 ^ 8 < 203404644 * a * 10 ^ 18 := by exact_mod_cast hblk
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  have hT' : (T n : ℝ) ≤ T c := Nat.cast_le.2 hT
  have hs : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hx0 : (0 : ℝ) ≤ (T n : ℝ) / 10 ^ 9 := by positivity
  have hsq : ((T n : ℝ) / 10 ^ 9) ^ 2 < (1.4262 * √(n : ℝ)) ^ 2 := by
    rw [div_pow, mul_pow, hs]
    have h1 : ((T n : ℝ)) ^ 2 ≤ ((T c : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hT' 2
    set X := ((T n : ℝ)) ^ 2
    set Y := ((T c : ℝ)) ^ 2
    have h2 : Y < 2.03404644 * a * 10 ^ 18 := by linarith
    have h3 : (2.03404644 : ℝ) * a * 10 ^ 18 ≤ 2.03404644 * n * 10 ^ 18 := by
      have := mul_le_mul_of_nonneg_left han' (by norm_num : (0 : ℝ) ≤ 2.03404644 * 10 ^ 18)
      linarith
    have e : (1.4262 : ℝ) ^ 2 * n = 2.03404644 * n * 10 ^ 18 / (10 ^ 9) ^ 2 := by ring
    rw [e, div_lt_div_iff_of_pos_right (by positivity)]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- **`ψ(n) − θ(n) < 1.4262 √n` for `1 ≤ n ≤ 10⁶`** (kernel-checked). -/
theorem nonprime_small_kernel (n : ℕ) (h1 : 1 ≤ n) (h : n ≤ 10 ^ 6) :
    ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) < 1.4262 * √n := by
  by_cases h0 : n < 9
  · exact block_ok (c := 8) blk_0 (by omega) (by omega) h (by norm_num)
  by_cases h1 : n < 25
  · exact block_ok (c := 24) blk_1 (by omega) (by omega) h (by norm_num)
  by_cases h2 : n < 49
  · exact block_ok (c := 48) blk_2 (by omega) (by omega) h (by norm_num)
  by_cases h3 : n < 81
  · exact block_ok (c := 80) blk_3 (by omega) (by omega) h (by norm_num)
  by_cases h4 : n < 125
  · exact block_ok (c := 124) blk_4 (by omega) (by omega) h (by norm_num)
  by_cases h5 : n < 169
  · exact block_ok (c := 168) blk_5 (by omega) (by omega) h (by norm_num)
  by_cases h6 : n < 243
  · exact block_ok (c := 242) blk_6 (by omega) (by omega) h (by norm_num)
  by_cases h7 : n < 343
  · exact block_ok (c := 342) blk_7 (by omega) (by omega) h (by norm_num)
  by_cases h8 : n < 361
  · exact block_ok (c := 360) blk_8 (by omega) (by omega) h (by norm_num)
  by_cases h9 : n < 512
  · exact block_ok (c := 511) blk_9 (by omega) (by omega) h (by norm_num)
  by_cases h10 : n < 625
  · exact block_ok (c := 624) blk_10 (by omega) (by omega) h (by norm_num)
  by_cases h11 : n < 841
  · exact block_ok (c := 840) blk_11 (by omega) (by omega) h (by norm_num)
  by_cases h12 : n < 1331
  · exact block_ok (c := 1330) blk_12 (by omega) (by omega) h (by norm_num)
  by_cases h13 : n < 1849
  · exact block_ok (c := 1848) blk_13 (by omega) (by omega) h (by norm_num)
  by_cases h14 : n < 2209
  · exact block_ok (c := 2208) blk_14 (by omega) (by omega) h (by norm_num)
  by_cases h15 : n < 2809
  · exact block_ok (c := 2808) blk_15 (by omega) (by omega) h (by norm_num)
  by_cases h16 : n < 3721
  · exact block_ok (c := 3720) blk_16 (by omega) (by omega) h (by norm_num)
  by_cases h17 : n < 5041
  · exact block_ok (c := 5040) blk_17 (by omega) (by omega) h (by norm_num)
  by_cases h18 : n < 6859
  · exact block_ok (c := 6858) blk_18 (by omega) (by omega) h (by norm_num)
  by_cases h19 : n < 10201
  · exact block_ok (c := 10200) blk_19 (by omega) (by omega) h (by norm_num)
  by_cases h20 : n < 14641
  · exact block_ok (c := 14640) blk_20 (by omega) (by omega) h (by norm_num)
  by_cases h21 : n < 22201
  · exact block_ok (c := 22200) blk_21 (by omega) (by omega) h (by norm_num)
  by_cases h22 : n < 32041
  · exact block_ok (c := 32040) blk_22 (by omega) (by omega) h (by norm_num)
  by_cases h23 : n < 50653
  · exact block_ok (c := 50652) blk_23 (by omega) (by omega) h (by norm_num)
  by_cases h24 : n < 76729
  · exact block_ok (c := 76728) blk_24 (by omega) (by omega) h (by norm_num)
  by_cases h25 : n < 120409
  · exact block_ok (c := 120408) blk_25 (by omega) (by omega) h (by norm_num)
  by_cases h26 : n < 187489
  · exact block_ok (c := 187488) blk_26 (by omega) (by omega) h (by norm_num)
  by_cases h27 : n < 310249
  · exact block_ok (c := 310248) blk_27 (by omega) (by omega) h (by norm_num)
  by_cases h28 : n < 493039
  · exact block_ok (c := 493038) blk_28 (by omega) (by omega) h (by norm_num)
  by_cases h29 : n < 822649
  · exact block_ok (c := 822648) blk_29 (by omega) (by omega) h (by norm_num)
  exact block_ok (c := 1000000) blk_30 (by omega) (by omega) h (by norm_num)

end TernaryGoldbach.Prelim.SmallNP
