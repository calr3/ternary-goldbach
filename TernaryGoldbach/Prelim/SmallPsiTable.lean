import Mathlib
import TernaryGoldbach.Prelim.SmallMertens

/-!
# A kernel-checked table of `θ` and `ψ` on `[12, 10⁶]` (route D, step P9a)

Trial division by the primes `≤ 1000` (`spf`), prime powers by dividing out the smallest factor
(`isPowOf`). Bounds are scaled by `S = 10⁹`. Checkpoints `N_j`; on `(N_j, N_{j+1}]` every prime
`p` has `LL_j ≤ S log p ≤ LH_{j+1}`, where the log chain is `LH_{j+1} = LH_j + ⌈S(N_{j+1} − N_j)/N_j⌉`
and `LL_{j+1} = LL_j + ⌊S(N_{j+1} − N_j)/N_{j+1}⌋`. No `native_decide`.
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallTab

/-! ### Primes up to 1000 -/

def P1000 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- Trial division by `2 ≤ d ≤ 32`. -/
def isPrimeSlow (n : ℕ) : Bool := 2 ≤ n && (List.range' 2 31).all (fun d => n < d * d || n % d != 0)

theorem P1000_complete : ∀ n ∈ List.range 1001, (n ∈ P1000 ↔ isPrimeSlow n = true) := by decide +kernel

theorem isPrimeSlow_iff {n : ℕ} (hn : n ≤ 1000) : isPrimeSlow n = true ↔ n.Prime := by
  unfold isPrimeSlow
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n * Nat.minFac n ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp)); nlinarith
    have hm2 := hmp.two_le
    have hm32 : Nat.minFac n ≤ 32 := by nlinarith
    rcases h (Nat.minFac n) ⟨hm2, by omega⟩ with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d hd => ?_⟩
    by_cases hdd : n < d * d
    · exact Or.inl hdd
    · right
      intro h0
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · omega
      · subst h; nlinarith [hp.two_le]

theorem mem_P1000 {p : ℕ} (hp : p ≤ 1000) : p ∈ P1000 ↔ p.Prime := by
  rw [P1000_complete p (List.mem_range.2 (by omega)), isPrimeSlow_iff hp]

theorem prime_of_mem_P1000 {p : ℕ} (h : p ∈ P1000) : p.Prime := by
  have : p ≤ 1000 := by
    have := List.mem_iff_get.1 h
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    exact (show ∀ i : Fin P1000.length, P1000.get i ≤ 1000 by decide +kernel) i
  exact (mem_P1000 this).1 h

theorem P1000_sorted : P1000.Pairwise (· < ·) := by decide +kernel

/-! ### Smallest prime factor by trial division -/

/-- The first `p` in the list with `p ∣ n`, `p² ≤ n`; `0` if there is none before `p² > n`. -/
def spf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, n => if n < p * p then 0 else if n % p = 0 then p else spf ps n

theorem spf_eq_zero {L : List ℕ} {n : ℕ} (h : spf L n = 0) (hL : L.Pairwise (· < ·))
    (hpos : ∀ p ∈ L, 0 < p) : ∀ p ∈ L, p * p ≤ n → ¬ p ∣ n := by
  induction L with
  | nil => intro p hp; simp at hp
  | cons a ps ih =>
    intro p hp hpp hdvd
    unfold spf at h
    split_ifs at h with h1 h2
    · -- n < a*a: then p ≥ a, so p*p ≥ a*a > n
      rcases List.mem_cons.1 hp with rfl | hp'
      · omega
      · have : a < p := (List.pairwise_cons.1 hL).1 p hp'
        nlinarith
    · -- returned a, so a = 0
      exact absurd h (hpos a (List.mem_cons_self ..)).ne'
    · -- spf ps n = 0
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h (List.pairwise_cons.1 hL).2 (fun q hq => hpos q (List.mem_cons_of_mem _ hq)) p hp' hpp hdvd

theorem spf_pos {L : List ℕ} {n q : ℕ} (h : spf L n = q) (hq : q ≠ 0) (hL : L.Pairwise (· < ·)) :
    q ∈ L ∧ q * q ≤ n ∧ q ∣ n ∧ ∀ p ∈ L, p < q → ¬ p ∣ n := by
  induction L generalizing q with
  | nil => simp [spf] at h; exact absurd h.symm hq
  | cons a ps ih =>
    unfold spf at h
    split_ifs at h with h1 h2
    · exact absurd h.symm hq
    · subst h
      refine ⟨List.mem_cons_self .., by omega, Nat.dvd_of_mod_eq_zero h2, fun p hp hpa => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · omega
      · have := (List.pairwise_cons.1 hL).1 p hp'; omega
    · obtain ⟨hm, hqq, hdvd, hlt⟩ := ih h hq (List.pairwise_cons.1 hL).2
      refine ⟨List.mem_cons_of_mem _ hm, hqq, hdvd, fun p hp hpq => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
      · exact hlt p hp' hpq

theorem P1000_pos : ∀ p ∈ P1000, 0 < p := fun p hp => (prime_of_mem_P1000 hp).pos

/-- **Trial division decides primality** for `2 ≤ n ≤ 10⁶`. -/
theorem spf_eq_zero_iff {n : ℕ} (h2 : 2 ≤ n) (h6 : n ≤ 1000000) : spf P1000 n = 0 ↔ n.Prime := by
  constructor
  · intro h
    have hno := spf_eq_zero h P1000_sorted P1000_pos
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n * Nat.minFac n ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp)); nlinarith
    have hm1000 : Nat.minFac n ≤ 1000 := by nlinarith
    exact hno _ ((mem_P1000 hm1000).2 hmp) hsq (Nat.minFac_dvd n)
  · intro hp
    by_contra hq
    obtain ⟨hm, hqq, hdvd, -⟩ := spf_pos rfl hq P1000_sorted
    have hqp := prime_of_mem_P1000 hm
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact hqp.one_lt.ne' h
    · rw [h] at hqq; nlinarith [hp.two_le]

/-- A nonzero `spf` is the least prime factor. -/
theorem spf_eq_minFac {n q : ℕ} (h2 : 2 ≤ n) (h : spf P1000 n = q) (hq : q ≠ 0) :
    q = n.minFac ∧ q.Prime ∧ ¬ n.Prime := by
  obtain ⟨hm, hqq, hdvd, hlt⟩ := spf_pos h hq P1000_sorted
  have hqp := prime_of_mem_P1000 hm
  have hmin : n.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hdvd
  have hq1000 : q ≤ 1000 := by
    have := List.mem_iff_get.1 hm
    obtain ⟨i, hi⟩ := this
    rw [← hi]; exact (show ∀ i : Fin P1000.length, P1000.get i ≤ 1000 by decide +kernel) i
  have heq : q = n.minFac := by
    by_contra hne
    have hlt' : n.minFac < q := lt_of_le_of_ne hmin (Ne.symm hne)
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    exact hlt _ ((mem_P1000 (by omega)).2 hmp) hlt' (Nat.minFac_dvd n)
  refine ⟨heq, hqp, fun hp => ?_⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact hqp.one_lt.ne' h
  · rw [h] at hqq; nlinarith [hp.two_le]

/-! ### Prime powers -/

/-- `m` is a power of `q` (within `k` divisions). -/
def isPowOf (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, m => if m = 1 then true else if m % q = 0 then isPowOf q k (m / q) else false

theorem isPowOf_true {q : ℕ} : ∀ {k m : ℕ}, isPowOf q k m = true → ∃ j, m = q ^ j := by
  intro k
  induction k with
  | zero => intro m h; simp [isPowOf] at h
  | succ k ih =>
    intro m h
    unfold isPowOf at h
    split_ifs at h with h1 h2
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨j, hj⟩ := ih h
      refine ⟨j + 1, ?_⟩
      rw [pow_succ, ← hj]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)).symm

theorem isPowOf_pow {q : ℕ} (hq : 2 ≤ q) : ∀ {k j : ℕ}, j < k → isPowOf q k (q ^ j) = true := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    unfold isPowOf
    rcases j with _ | j
    · simp
    · have h1 : q ^ (j + 1) ≠ 1 := (Nat.one_lt_pow (Nat.succ_ne_zero j) (by omega : 1 < q)).ne'
      have h2 : q ^ (j + 1) % q = 0 := by rw [pow_succ]; simp
      rw [if_neg h1, if_pos h2, pow_succ, Nat.mul_div_cancel _ (by omega)]
      exact ih (by omega)

open ArithmeticFunction in
/-- `Λ` from the trial division. -/
theorem vonMangoldt_of_spf {m q : ℕ} (h2 : 2 ≤ m) (h6 : m ≤ 1000000) (h : spf P1000 m = q) (hq : q ≠ 0) :
    (Λ m : ℝ) = if isPowOf q 20 m then Real.log q else 0 := by
  obtain ⟨heq, hqp, hnp⟩ := spf_eq_minFac h2 h hq
  split_ifs with hpow
  · obtain ⟨j, hj⟩ := isPowOf_true hpow
    have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
    rw [hj, vonMangoldt_apply_pow hj0, vonMangoldt_apply_prime hqp]
  · rw [vonMangoldt_eq_zero_iff.2]
    intro hpp
    obtain ⟨r, j, hr, hj, hrj⟩ := (isPrimePow_nat_iff m).1 hpp
    have hrm : r = m.minFac := by
      rw [← hrj, Nat.Prime.pow_minFac hr hj.ne']
    apply hpow
    rw [← hrj, heq.trans hrm.symm]
    refine isPowOf_pow hr.two_le ?_
    have : 2 ^ j ≤ r ^ j := Nat.pow_le_pow_left hr.two_le j
    have h20 : 2 ^ j ≤ 1000000 := by rw [hrj] at this; omega
    by_contra hc; push Not at hc
    have : 2 ^ 20 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hc
    omega

/-! ### Logarithms of the primes `≤ 1000` (scaled by `S = 10⁹`) -/

def S : ℕ := 1000000000

open TernaryGoldbach.Prelim.Small (chkStep chkLow log_lt_of_chk le_log_of_chk)

def LQ : List (ℕ × ℕ × ℕ) := [(2, 693147178, 693147183), (3, 1098612286, 1098612291), (5, 1609437910, 1609437915), (7, 1945910147, 1945910152), (11, 2397895270, 2397895275), (13, 2564949355, 2564949360), (17, 2833213342, 2833213347), (19, 2944438977, 2944438982), (23, 3135494213, 3135494218), (29, 3367295827, 3367295832), (31, 3433987202, 3433987207), (37, 3610917910, 3610917915), (41, 3713572064, 3713572069), (43, 3761200113, 3761200118), (47, 3850147599, 3850147604), (53, 3970291911, 3970291916), (59, 4077537441, 4077537446), (61, 4110873862, 4110873867), (67, 4204692617, 4204692622), (71, 4262679875, 4262679880), (73, 4290459439, 4290459444), (79, 4369447850, 4369447855), (83, 4418840605, 4418840610), (89, 4488636367, 4488636372), (97, 4574710976, 4574710981), (101, 4615120514, 4615120519), (103, 4634728986, 4634728991), (107, 4672828832, 4672828837), (109, 4691347880, 4691347885), (113, 4727387816, 4727387821), (127, 4844187084, 4844187089), (131, 4875197321, 4875197326), (137, 4919980923, 4919980928), (139, 4934473931, 4934473936), (149, 5003946303, 5003946308), (151, 5017279834, 5017279839), (157, 5056245803, 5056245808), (163, 5093750198, 5093750203), (167, 5117993810, 5117993815), (173, 5153291592, 5153291597), (179, 5187385803, 5187385808), (181, 5198497029, 5198497034), (191, 5252273426, 5252273431), (193, 5262690186, 5262690191), (197, 5283203726, 5283203731), (199, 5293304822, 5293304827), (211, 5351858131, 5351858136), (223, 5407171769, 5407171774), (227, 5424950015, 5424950020), (229, 5433722001, 5433722006), (233, 5451038451, 5451038456), (239, 5476463549, 5476463554), (241, 5484796931, 5484796936), (251, 5525452937, 5525452942), (257, 5549076082, 5549076087), (263, 5572154030, 5572154035), (269, 5594711377, 5594711382), (271, 5602118818, 5602118823), (277, 5624017504, 5624017509), (281, 5638354667, 5638354672), (283, 5645446895, 5645446900), (293, 5680172607, 5680172612), (307, 5726847745, 5726847750), (311, 5739792910, 5739792915), (313, 5746203188, 5746203193), (317, 5758901771, 5758901776), (331, 5802118373, 5802118378), (337, 5820082928, 5820082933), (347, 5849324777, 5849324782), (349, 5855071920, 5855071925), (353, 5866468054, 5866468059), (359, 5883322386, 5883322391), (367, 5905361846, 5905361851), (373, 5921578417, 5921578422), (379, 5937536203, 5937536208), (383, 5948034987, 5948034992), (389, 5963579341, 5963579346), (397, 5983936278, 5983936283), (401, 5993961425, 5993961430), (409, 6013715154, 6013715159), (419, 6037870917, 6037870922), (421, 6042632831, 6042632836), (431, 6066108088, 6066108093), (433, 6070737726, 6070737731), (439, 6084499411, 6084499416), (443, 6093569768, 6093569773), (449, 6107022885, 6107022890), (457, 6124683388, 6124683393), (461, 6133398040, 6133398045), (463, 6137727052, 6137727057), (467, 6146329255, 6146329260), (479, 6171700595, 6171700600), (487, 6188264121, 6188264126), (491, 6196444125, 6196444130), (499, 6212606093, 6212606098), (503, 6220590168, 6220590173), (509, 6232448014, 6232448019), (521, 6255750039, 6255750044), (523, 6259581462, 6259581467), (541, 6293419276, 6293419281), (547, 6304448800, 6304448805), (557, 6322565237, 6322565242), (563, 6333279626, 6333279631), (569, 6343880432, 6343880437), (571, 6347389207, 6347389212), (577, 6357842264, 6357842269), (587, 6375024817, 6375024822), (593, 6385194396, 6385194401), (599, 6395261596, 6395261601), (601, 6398594932, 6398594937), (607, 6408528789, 6408528794), (613, 6418364933, 6418364938), (617, 6424869021, 6424869026), (619, 6428105270, 6428105275), (631, 6447305860, 6447305865), (641, 6463029454, 6463029459), (643, 6466144722, 6466144727), (647, 6472346292, 6472346297), (653, 6481577127, 6481577132), (659, 6490723532, 6490723537), (661, 6493753837, 6493753842), (673, 6511745327, 6511745332), (677, 6517671270, 6517671275), (683, 6526494857, 6526494862), (691, 6538139821, 6538139826), (701, 6552507885, 6552507890), (709, 6563855524, 6563855529), (719, 6577861355, 6577861360), (727, 6588926475, 6588926480), (733, 6597145699, 6597145704), (739, 6605297918, 6605297923), (743, 6610696042, 6610696047), (751, 6621405649, 6621405654), (757, 6629363251, 6629363256), (761, 6634633355, 6634633360), (769, 6645090967, 6645090972), (773, 6650279046, 6650279051), (787, 6668228246, 6668228251), (797, 6680854676, 6680854681), (809, 6695798915, 6695798920), (811, 6698268052, 6698268057), (821, 6710523107, 6710523112), (823, 6712956198, 6712956203), (827, 6717804693, 6717804698), (829, 6720220153, 6720220158), (839, 6732210704, 6732210709), (853, 6748759545, 6748759550), (857, 6753437916, 6753437921), (859, 6755768919, 6755768924), (863, 6760414689, 6760414694), (877, 6776506990, 6776506995), (881, 6781057623, 6781057628), (883, 6783325198, 6783325203), (887, 6787844980, 6787844985), (907, 6810142448, 6810142453), (911, 6814542895, 6814542900), (919, 6823286120, 6823286125), (929, 6834108736, 6834108741), (937, 6842683280, 6842683285), (941, 6846943137, 6846943142), (947, 6853299091, 6853299096), (953, 6859614901, 6859614906), (967, 6874198493, 6874198498), (971, 6878326466, 6878326471), (977, 6884486650, 6884486655), (983, 6890609118, 6890609123), (991, 6898714532, 6898714537), (997, 6904750767, 6904750772)]

def lqLo (q : ℕ) : ℕ := ((LQ.find? (fun t => t.1 == q)).map (fun t => t.2.1)).getD 0
def lqHi (q : ℕ) : ℕ := ((LQ.find? (fun t => t.1 == q)).map (fun t => t.2.2)).getD 0

theorem LQ_ok : ∀ t ∈ LQ, chkLow t.2.1 S t.1 = true ∧ chkStep t.2.2 S 1 t.1 = true := by decide +kernel
theorem LQ_cover : ∀ q ∈ P1000, (LQ.find? (fun t => t.1 == q)).isSome = true := by decide +kernel

theorem lq_spec {q : ℕ} (hq : q ∈ P1000) :
    (lqLo q : ℝ) / S ≤ Real.log q ∧ Real.log q ≤ (lqHi q : ℝ) / S := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (LQ_cover q hq)
  have hmem := List.mem_of_find?_eq_some ht
  have hq1 : t.1 = q := by simpa using List.find?_some ht
  obtain ⟨h1, h2⟩ := LQ_ok t hmem
  have hpos : 0 < q := (prime_of_mem_P1000 hq).pos
  have hS : 0 < S := by unfold S; norm_num
  have hlo := le_log_of_chk hS (by rw [hq1]; exact hpos) h1
  have hhi := log_lt_of_chk hS (by rw [hq1]; exact hpos) h2
  unfold lqLo lqHi
  rw [ht]
  simp only [Option.map_some, Option.getD_some]
  rw [hq1] at hlo hhi
  push_cast at hlo hhi ⊢
  exact ⟨hlo, by linarith⟩

/-! ### `θ` and the prime-power part -/

open ArithmeticFunction in
noncomputable def ppS (m : ℕ) : ℝ := ∑ k ∈ Icc 1 m, (if k.Prime then 0 else (Λ k : ℝ))
noncomputable def thS (m : ℕ) : ℝ := ∑ p ∈ (Icc 1 m).filter Nat.Prime, Real.log p

theorem thS_succ (m : ℕ) : thS (m + 1) = thS m + (if (m + 1).Prime then Real.log (m + 1 : ℕ) else 0) := by
  unfold thS
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]

open ArithmeticFunction in
theorem ppS_succ (m : ℕ) : ppS (m + 1) = ppS m + (if (m + 1).Prime then 0 else (Λ (m + 1) : ℝ)) := by
  unfold ppS; rw [Finset.sum_Icc_succ_top (by omega)]

theorem thS_mono {a b : ℕ} (h : a ≤ b) : thS a ≤ thS b := by
  unfold thS
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl h))
    fun p _ _ => Real.log_natCast_nonneg p

open ArithmeticFunction in
theorem ppS_mono {a b : ℕ} (h : a ≤ b) : ppS a ≤ ppS b := by
  unfold ppS
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h) fun k _ _ => ?_
  split_ifs
  · exact le_rfl
  · exact_mod_cast vonMangoldt_nonneg

def Inv (m tlo thi plo phi : ℕ) : Prop :=
  (tlo : ℝ) / S ≤ thS m ∧ thS m ≤ (thi : ℝ) / S ∧ (plo : ℝ) / S ≤ ppS m ∧ ppS m ≤ (phi : ℝ) / S

/-- Processes `m + 1, …, m + k`; primes get `[LL, LH]/S` for `log p`. -/
def inner (LL LH : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ)
  | _, tlo, thi, plo, phi, 0 => some (tlo, thi, plo, phi)
  | m, tlo, thi, plo, phi, k + 1 =>
    match spf P1000 (m + 1) with
    | 0 => if thi + LH ≤ 10 ^ 20 then inner LL LH (m + 1) (tlo + LL) (thi + LH) plo phi k else none
    | q + 1 =>
      if isPowOf (q + 1) 20 (m + 1) then
        (if phi + lqHi (q + 1) ≤ 10 ^ 20 then
          inner LL LH (m + 1) tlo thi (plo + lqLo (q + 1)) (phi + lqHi (q + 1)) k else none)
      else inner LL LH (m + 1) tlo thi plo phi k

theorem S_pos : (0 : ℝ) < S := by unfold S; norm_num

open ArithmeticFunction in
theorem inner_spec {LL LH : ℕ} : ∀ (k m tlo thi plo phi a b c d : ℕ), 1 ≤ m → m + k ≤ 1000000 →
    (∀ p : ℕ, m < p → p ≤ m + k → p.Prime → (LL : ℝ) / S ≤ Real.log p ∧ Real.log p ≤ (LH : ℝ) / S) →
    Inv m tlo thi plo phi → inner LL LH m tlo thi plo phi k = some (a, b, c, d) → Inv (m + k) a b c d := by
  intro k
  induction k with
  | zero =>
    intro m tlo thi plo phi a b c d _ _ _ hI h
    simp only [inner, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simpa using hI
  | succ k ih =>
    intro m tlo thi plo phi a b c d hm hk hL hI h
    obtain ⟨h1, h2, h3, h4⟩ := hI
    have hS := S_pos
    unfold inner at h
    rcases hq : spf P1000 (m + 1) with _ | q
    · -- `m + 1` is prime
      rw [hq] at h
      simp only at h
      split_ifs at h with hb
      have hp : (m + 1).Prime := (spf_eq_zero_iff (by omega) (by omega)).1 hq
      have hlog := hL (m + 1) (by omega) (by omega) hp
      have := ih (m + 1) _ _ _ _ a b c d (by omega) (by omega)
        (fun p hp1 hp2 hpp => hL p (by omega) (by omega) hpp) ?_ h
      · rwa [show m + 1 + k = m + (k + 1) by omega] at this
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [thS_succ, if_pos hp]; push_cast; rw [add_div]; push_cast at hlog; linarith [hlog.1]
      · rw [thS_succ, if_pos hp]; push_cast; rw [add_div]; push_cast at hlog; linarith [hlog.2]
      · rw [ppS_succ, if_pos hp]; linarith
      · rw [ppS_succ, if_pos hp]; linarith
    · rw [hq] at h
      simp only at h
      have hmin := spf_eq_minFac (by omega) hq (by omega)
      have hnp := hmin.2.2
      have hΛ := vonMangoldt_of_spf (by omega) (by omega) hq (by omega)
      have hmem := (spf_pos hq (by omega) P1000_sorted).1
      split_ifs at h with hpow hb
      · have hlq := lq_spec hmem
        rw [if_pos hpow] at hΛ
        have := ih (m + 1) _ _ _ _ a b c d (by omega) (by omega)
          (fun p hp1 hp2 hpp => hL p (by omega) (by omega) hpp) ?_ h
        · rwa [show m + 1 + k = m + (k + 1) by omega] at this
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [thS_succ, if_neg hnp]; linarith
        · rw [thS_succ, if_neg hnp]; linarith
        · rw [ppS_succ, if_neg hnp, hΛ]; push_cast at hlq ⊢; rw [add_div]; linarith [hlq.1]
        · rw [ppS_succ, if_neg hnp, hΛ]; push_cast at hlq ⊢; rw [add_div]; linarith [hlq.2]
      · rw [if_neg hpow] at hΛ
        have := ih (m + 1) _ _ _ _ a b c d (by omega) (by omega)
          (fun p hp1 hp2 hpp => hL p (by omega) (by omega) hpp) ?_ h
        · rwa [show m + 1 + k = m + (k + 1) by omega] at this
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [thS_succ, if_neg hnp]; linarith
        · rw [thS_succ, if_neg hnp]; linarith
        · rw [ppS_succ, if_neg hnp, hΛ]; linarith
        · rw [ppS_succ, if_neg hnp, hΛ]; linarith

/-! ### Checkpoints -/

/-- `(a − b)/S ≤ (cN/cD) √n`, decided in `ℕ`. -/
def leSq (a b n cN cD : ℕ) : Bool := Nat.ble a b || Nat.ble ((a - b) ^ 2 * cD ^ 2) (S ^ 2 * cN ^ 2 * n)

theorem leSq_spec {a b n cN cD : ℕ} (hcD : 0 < cD) (h : leSq a b n cN cD = true) :
    (a : ℝ) / S - (b : ℝ) / S ≤ (cN : ℝ) / cD * √(n : ℝ) := by
  have hS := S_pos
  have hR : 0 ≤ (cN : ℝ) / cD * √(n : ℝ) := by positivity
  unfold leSq at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have : (a : ℝ) ≤ b := by exact_mod_cast Nat.le_of_ble_eq_true h
    have : (a : ℝ) / S - (b : ℝ) / S ≤ 0 := by rw [← sub_div]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
    linarith
  · have h' := Nat.le_of_ble_eq_true h
    by_cases hab : a ≤ b
    · have : (a : ℝ) ≤ b := by exact_mod_cast hab
      have : (a : ℝ) / S - (b : ℝ) / S ≤ 0 := by rw [← sub_div]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
      linarith
    · push Not at hab
      have hcast : ((a - b : ℕ) : ℝ) = (a : ℝ) - b := by push_cast [hab.le]; ring
      have h'' : (((a - b : ℕ) : ℝ)) ^ 2 * (cD : ℝ) ^ 2 ≤ (S : ℝ) ^ 2 * (cN : ℝ) ^ 2 * n := by exact_mod_cast h'
      rw [hcast] at h''
      rw [← sub_div]
      have hcD' : (0 : ℝ) < cD := by exact_mod_cast hcD
      have hlhs : 0 ≤ ((a : ℝ) - b) / S := div_nonneg (by have : (b : ℝ) < a := by exact_mod_cast hab
                                                          linarith) hS.le
      have hsq : (((a : ℝ) - b) / S) ^ 2 ≤ ((cN : ℝ) / cD * √(n : ℝ)) ^ 2 := by
        rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_mul_eq_mul_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (pow_le_pow_iff_left₀ hlhs hR two_ne_zero).1 hsq

/-- The four checks on a window `(n, e]`, with start bounds `tlo, plo` and end bounds `thi', phi'`. -/
def winOK (n e tlo plo thi' phi' cN cD tN tD : ℕ) : Bool :=
  leSq (thi' + phi') (S * n) n cN cD && leSq (S * e) (tlo + plo) n cN cD && Nat.ble thi' (S * n) &&
    leSq (S * e) tlo n tN tD

/-- The bounds at real `t`. -/
def Rt (cN cD tN tD : ℕ) (t : ℝ) : Prop :=
  thS ⌊t⌋₊ + ppS ⌊t⌋₊ - t ≤ (cN : ℝ) / cD * √t ∧ t - (thS ⌊t⌋₊ + ppS ⌊t⌋₊) ≤ (cN : ℝ) / cD * √t ∧
    thS ⌊t⌋₊ ≤ t ∧ t - thS ⌊t⌋₊ ≤ (tN : ℝ) / tD * √t

theorem window_ok {n G tlo thi plo phi a b c d cN cD tN tD : ℕ} (hn : 1 ≤ n) (hcD : 0 < cD) (htD : 0 < tD)
    (h0 : Inv n tlo thi plo phi) (h1 : Inv (n + G) a b c d) (hw : winOK n (n + G) tlo plo b d cN cD tN tD = true)
    {t : ℝ} (ht1 : (n : ℝ) ≤ t) (ht2 : t < ((n + G : ℕ) : ℝ)) : Rt cN cD tN tD t := by
  have hS := S_pos
  unfold winOK at hw
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨w1, w2⟩, w3⟩, w4⟩ := hw
  have l1 := leSq_spec hcD w1
  have l2 := leSq_spec hcD w2
  have l4 := leSq_spec htD w4
  have w3' : (b : ℝ) ≤ S * n := by exact_mod_cast Nat.le_of_ble_eq_true w3
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  have hfl1 : n ≤ ⌊t⌋₊ := Nat.le_floor ht1
  have hfl2 : ⌊t⌋₊ ≤ n + G := by
    have := Nat.floor_lt ht0 |>.2 ht2; omega
  have hsq : √(n : ℝ) ≤ √t := Real.sqrt_le_sqrt ht1
  have hcn : 0 ≤ (cN : ℝ) / cD := by positivity
  have htn : 0 ≤ (tN : ℝ) / tD := by positivity
  obtain ⟨a0, a1, a2, a3⟩ := h0
  obtain ⟨b0, b1, b2, b3⟩ := h1
  have m1 := thS_mono hfl1; have m2 := thS_mono hfl2; have m3 := ppS_mono hfl1; have m4 := ppS_mono hfl2
  have eS : ∀ x : ℕ, ((S * x : ℕ) : ℝ) / S = x := fun x => by push_cast; field_simp
  rw [eS] at l1 l2 l4
  push_cast at l1 l2 l4 ht2
  rw [add_div] at l1 l2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hsq hcn; linarith
  · have := mul_le_mul_of_nonneg_left hsq hcn; linarith
  · have : (b : ℝ) / S ≤ n := by rw [div_le_iff₀ hS]; linarith
    linarith
  · have := mul_le_mul_of_nonneg_left hsq htn; linarith

/-- The checkpoint loop. Each window is `(G, L1, H1)`: `L1 = 0` means the log chain, otherwise
`L1 ≤ S log e < H1` is certified. -/
def outer (cN cD tN tD : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) →
    Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
  | n, tlo, thi, plo, phi, LL, LH, [] => some (n, tlo, thi, plo, phi, LL, LH)
  | n, tlo, thi, plo, phi, LL, LH, (G, L1, H1) :: gs =>
    let LLe := if L1 = 0 then LL + S * G / (n + G) else L1
    let LHe := if L1 = 0 then LH + (S * G + n - 1) / n else H1
    if L1 = 0 ∨ (chkLow L1 S (n + G) = true ∧ chkStep H1 S 1 (n + G) = true) then
      match inner (if G = 1 then LLe else LL) LHe n tlo thi plo phi G with
      | none => none
      | some (a, b, c, d) =>
        if winOK n (n + G) tlo plo b d cN cD tN tD = true then outer cN cD tN tD (n + G) a b c d LLe LHe gs
        else none
    else none

theorem log_chain_lo {n G LL : ℕ} (hn : 1 ≤ n) (h : (LL : ℝ) / S ≤ Real.log n) :
    ((LL + S * G / (n + G) : ℕ) : ℝ) / S ≤ Real.log ((n + G : ℕ) : ℝ) := by
  have hS := S_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnG : (0 : ℝ) < ((n + G : ℕ) : ℝ) := by push_cast; positivity
  have h1 : ((S * G / (n + G) : ℕ) : ℝ) ≤ (S : ℝ) * G / ((n + G : ℕ) : ℝ) := by
    rw [le_div_iff₀ hnG]; exact_mod_cast Nat.div_mul_le_self _ _
  have h2 : (G : ℝ) / ((n + G : ℕ) : ℝ) ≤ Real.log ((n + G : ℕ) : ℝ) - Real.log n := by
    rw [← Real.log_div hnG.ne' hn'.ne']
    have := Real.one_sub_inv_le_log_of_pos (x := ((n + G : ℕ) : ℝ) / n) (by positivity)
    rw [inv_div] at this
    have e : 1 - (n : ℝ) / ((n + G : ℕ) : ℝ) = (G : ℝ) / ((n + G : ℕ) : ℝ) := by
      field_simp; push_cast; ring
    linarith
  push_cast at h1 ⊢
  rw [add_div]
  have : ((S * G / (n + G) : ℕ) : ℝ) / S ≤ (G : ℝ) / ((n : ℝ) + G) := by
    rw [div_le_iff₀ hS]; push_cast at h1 ⊢; field_simp at h1 ⊢; nlinarith
  push_cast at this h2
  linarith

theorem log_chain_hi {n G LH : ℕ} (hn : 1 ≤ n) (h : Real.log n ≤ (LH : ℝ) / S) :
    Real.log ((n + G : ℕ) : ℝ) ≤ ((LH + (S * G + n - 1) / n : ℕ) : ℝ) / S := by
  have hS := S_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (S : ℝ) * G / n ≤ (((S * G + n - 1) / n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hn']
    have : S * G ≤ (S * G + n - 1) / n * n := by
      have := Nat.div_add_mod' (S * G + n - 1) n
      have hm := Nat.mod_lt (S * G + n - 1) (by omega : 0 < n)
      omega
    exact_mod_cast this
  have h2 : Real.log ((n + G : ℕ) : ℝ) - Real.log n ≤ (G : ℝ) / n := by
    rw [← Real.log_div (by positivity) hn'.ne']
    have := Real.log_le_sub_one_of_pos (x := ((n + G : ℕ) : ℝ) / n) (by positivity)
    have e : ((n + G : ℕ) : ℝ) / n - 1 = (G : ℝ) / n := by field_simp; push_cast; ring
    linarith
  have : (G : ℝ) / n ≤ (((S * G + n - 1) / n : ℕ) : ℝ) / S := by
    rw [le_div_iff₀ hS]
    have e : (G : ℝ) / n * S = (S : ℝ) * G / n := by ring
    rw [e]; exact h1
  push_cast at h2 ⊢
  rw [add_div]
  linarith

theorem outer_spec {cN cD tN tD : ℕ} (hcD : 0 < cD) (htD : 0 < tD) :
    ∀ (gs : List (ℕ × ℕ × ℕ)) (n tlo thi plo phi LL LH n' tlo' thi' plo' phi' LL' LH' : ℕ),
    1 ≤ n → n + (gs.map (fun g => g.1)).sum ≤ 1000000 → Inv n tlo thi plo phi →
    (LL : ℝ) / S ≤ Real.log n → Real.log n ≤ (LH : ℝ) / S →
    outer cN cD tN tD n tlo thi plo phi LL LH gs = some (n', tlo', thi', plo', phi', LL', LH') →
    (∀ t : ℝ, (n : ℝ) ≤ t → t < n' → Rt cN cD tN tD t) ∧ Inv n' tlo' thi' plo' phi' ∧
      (LL' : ℝ) / S ≤ Real.log n' ∧ Real.log n' ≤ (LH' : ℝ) / S := by
  intro gs
  induction gs with
  | nil =>
    intro n tlo thi plo phi LL LH n' tlo' thi' plo' phi' LL' LH' _ _ hI hL hH h
    simp only [outer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨fun t h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _), hI, hL, hH⟩
  | cons g gs ih =>
    obtain ⟨G, L1, H1⟩ := g
    intro n tlo thi plo phi LL LH n' tlo' thi' plo' phi' LL' LH' hn hsum hI hL hH h
    simp only [List.map_cons, List.sum_cons] at hsum
    have hS := S_pos
    have hS0 : (0 : ℕ) < S := by unfold S; norm_num
    unfold outer at h
    simp only at h
    by_cases hc : L1 = 0 ∨ (chkLow L1 S (n + G) = true ∧ chkStep H1 S 1 (n + G) = true)
    swap
    · rw [if_neg hc] at h; exact absurd h (by simp)
    rw [if_pos hc] at h
    -- the log bounds at `n + G`
    have hlog : ((if L1 = 0 then LL + S * G / (n + G) else L1 : ℕ) : ℝ) / S ≤ Real.log ((n + G : ℕ) : ℝ) ∧
        Real.log ((n + G : ℕ) : ℝ) ≤ ((if L1 = 0 then LH + (S * G + n - 1) / n else H1 : ℕ) : ℝ) / S := by
      by_cases h0 : L1 = 0
      · simp only [h0, if_true]
        exact ⟨log_chain_lo hn hL, log_chain_hi hn hH⟩
      · simp only [h0, if_false]
        rcases hc with hc | ⟨hc1, hc2⟩
        · exact absurd hc h0
        · have hpos : 0 < n + G := by omega
          exact ⟨le_log_of_chk hS0 hpos hc1, (log_lt_of_chk hS0 hpos hc2).le.trans (by simp)⟩
    set LLe := (if L1 = 0 then LL + S * G / (n + G) else L1 : ℕ) with hLLe
    set LHe := (if L1 = 0 then LH + (S * G + n - 1) / n else H1 : ℕ) with hLHe
    rcases hin : inner (if G = 1 then LLe else LL) LHe n tlo thi plo phi G with _ | ⟨a, b, c, d⟩
    · rw [hin] at h; simp at h
    rw [hin] at h
    simp only at h
    by_cases hw : winOK n (n + G) tlo plo b d cN cD tN tD = true
    swap
    · rw [if_neg hw] at h; exact absurd h (by simp)
    rw [if_pos hw] at h
    -- primes in the window
    have hp : ∀ p : ℕ, n < p → p ≤ n + G → p.Prime →
        ((if G = 1 then LLe else LL : ℕ) : ℝ) / S ≤ Real.log p ∧ Real.log p ≤ (LHe : ℝ) / S := by
      intro p hp1 hp2 _
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hle : Real.log p ≤ Real.log ((n + G : ℕ) : ℝ) :=
        Real.log_le_log hp0 (by exact_mod_cast hp2)
      refine ⟨?_, hle.trans hlog.2⟩
      by_cases hG : G = 1
      · rw [if_pos hG]
        have : p = n + G := by omega
        rw [this]; exact hlog.1
      · rw [if_neg hG]
        exact hL.trans (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hp1.le))
    have hI1 := inner_spec G n tlo thi plo phi a b c d hn (by omega) hp hI hin
    obtain ⟨ihR, ihI, ihL, ihH⟩ := ih (n + G) a b c d LLe LHe n' tlo' thi' plo' phi' LL' LH' (by omega)
      (by omega) hI1 hlog.1 hlog.2 h
    refine ⟨fun t ht1 ht2 => ?_, ihI, ihL, ihH⟩
    by_cases htG : t < ((n + G : ℕ) : ℝ)
    · exact window_ok hn hcD htD hI hI1 hw ht1 htG
    · push Not at htG
      exact ihR t htG ht2

end TernaryGoldbach.Prelim.SmallTab
