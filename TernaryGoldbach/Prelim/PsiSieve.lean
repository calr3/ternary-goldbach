import TernaryGoldbach.Prelim.SmallPsiTable

/-!
# A bit sieve in the kernel: `θ` on `[10⁶, 5·10⁷)` (route D, P9c)

The trial-division table (`SmallPsiTable`) costs about `3·10⁻³ s` per integer near `10⁶`. Here a window
`(n, n + W]` (`W ≤ 2¹⁵`) is sieved with one bit mask per prime `p ≤ 7100`, built by doubling
(`maskP`), or-ed together (`orAll`) and counted by halves (`pc`); every step is a GMP operation on
a `W`-bit `Nat`. `cnt_spec`: `cnt n W` is the number of primes in `(n, n + W]` for
`7100 ≤ n`, `n + W < 7103²`.

The window chain `outerT` (the analogue of `SmallTab.outer`, tracking `θ` only) then gives
`t − 5√t ≤ θ(t) ≤ t + 3√t` on `[10⁶, 5·10⁷)` (`Prelim/PsiSieveMain.lean`).
-/

open Finset

namespace TernaryGoldbach.Prelim.SieveTab
open SmallTab
open TernaryGoldbach.Prelim.Small (chkStep chkLow log_lt_of_chk le_log_of_chk)

/-! ### Periodic bit masks -/

/-- Doubling, at most `f` times, until the length reaches `W`. -/
def rep (m len W : ℕ) : ℕ → ℕ
  | 0 => m
  | f + 1 => if W ≤ len then m else rep (m ||| (m <<< len)) (2 * len) W f

theorem sub_mod_of_dvd {i len p : ℕ} (hl : p ∣ len) (h : len ≤ i) : (i - len) % p = i % p := by
  obtain ⟨c, rfl⟩ := hl
  conv_rhs => rw [show i = (i - p * c) + p * c by omega]
  rw [Nat.add_mul_mod_self_left]

theorem rep_spec {p r W : ℕ} : ∀ (f m len : ℕ), p ∣ len → 0 < len →
    (∀ i, m.testBit i = decide (i < len ∧ i % p = r)) →
    ∃ len', (W ≤ len' ∨ len' = len * 2 ^ f) ∧
      ∀ i, (rep m len W f).testBit i = decide (i < len' ∧ i % p = r) := by
  intro f
  induction f with
  | zero => intro m len _ _ hm; exact ⟨len, Or.inr (by simp), by simpa [rep] using hm⟩
  | succ f ih =>
    intro m len hl hl0 hm
    unfold rep
    split_ifs with hW
    · exact ⟨len, Or.inl hW, hm⟩
    · obtain ⟨len', h2, h3⟩ := ih (m ||| (m <<< len)) (2 * len) (dvd_mul_of_dvd_right hl 2)
        (by omega) (fun i => by
          rw [Nat.testBit_or, Nat.testBit_shiftLeft, hm]
          by_cases h : i < len
          · have h' : ¬ len ≤ i := by omega
            simp [h, h', show i < 2 * len by omega]
          · push Not at h
            rw [hm, sub_mod_of_dvd hl h]
            have h1 : ¬ i < len := by omega
            by_cases h2 : i < 2 * len
            · simp [h1, h2, h, show i - len < len by omega]
            · simp [h1, h2, h, show ¬ i - len < len by omega])
      refine ⟨len', ?_, h3⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · right; rw [h2, pow_succ]; ring

/-- The bits `i < W` with `i ≡ r (mod p)`. -/
def maskP (p r W : ℕ) : ℕ := rep (1 <<< r) p W 64 &&& ((1 <<< W) - 1)

theorem maskP_spec {p r W : ℕ} (hp : 0 < p) (hr : r < p) (hW : W ≤ 2 ^ 64) (i : ℕ) :
    (maskP p r W).testBit i = decide (i < W ∧ i % p = r) := by
  obtain ⟨len', h2, h3⟩ := rep_spec (p := p) (r := r) (W := W) 64 (1 <<< r) p dvd_rfl hp (fun i => by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : i = r
    · subst h; simp [hr, Nat.mod_eq_of_lt hr]
    · have : ¬ (i < p ∧ i % p = r) := fun ⟨h1, h2⟩ => h (by rwa [Nat.mod_eq_of_lt h1] at h2)
      simp only [this, decide_false]
      exact decide_eq_false (Ne.symm h))
  have hWl : W ≤ len' := by
    rcases h2 with h2 | h2
    · exact h2
    · rw [h2]; calc W ≤ 2 ^ 64 := hW
        _ ≤ p * 2 ^ 64 := Nat.le_mul_of_pos_left _ hp
  unfold maskP
  rw [Nat.testBit_and, h3, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : i < W
  · simp [h, show i < len' by omega]
  · simp [h]

/-- The residue `r` with `p ∣ n + 1 + i ↔ i ≡ r (mod p)`. -/
theorem dvd_iff_mod {p n i : ℕ} (hp : 0 < p) :
    p ∣ n + 1 + i ↔ i % p = (p - (n + 1) % p) % p := by
  have h1 := Nat.mod_add_div (n + 1) p
  have h2 := Nat.mod_add_div i p
  have ha := Nat.mod_lt (n + 1) hp
  have hk := Nat.mod_lt i hp
  set a := (n + 1) % p
  set k := i % p
  have e : n + 1 + i = (a + k) + p * ((n + 1) / p + i / p) := by rw [mul_add]; omega
  rw [Nat.dvd_iff_mod_eq_zero, e, Nat.add_mul_mod_self_left]
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0, Nat.sub_zero, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hk]
  · rw [Nat.mod_eq_of_lt (show p - a < p by omega)]
    constructor
    · intro h
      by_cases hlt : a + k < p
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · push Not at hlt
        rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
    · intro h
      rw [show a + k = p by omega, Nat.mod_self]

def orAll (W n : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => maskP p ((p - (n + 1) % p) % p) W ||| orAll W n ps

theorem orAll_spec (W n : ℕ) (hW : W ≤ 2 ^ 64) : ∀ (Ps : List ℕ), (∀ p ∈ Ps, 0 < p) → ∀ i,
    (orAll W n Ps).testBit i = decide (i < W ∧ ∃ p ∈ Ps, p ∣ n + 1 + i) := by
  intro Ps
  induction Ps with
  | nil => intro _ i; simp [orAll]
  | cons p ps ih =>
    intro hP i
    have hp : 0 < p := hP p (by simp)
    rw [orAll, Nat.testBit_or, maskP_spec hp (Nat.mod_lt _ hp) hW, ih (fun q hq => hP q (by simp [hq]))]
    have hd := (dvd_iff_mod (n := n) (i := i) hp).symm
    simp only [hd]
    by_cases h : i < W
    · by_cases h' : p ∣ n + 1 + i
      · simp [h, h']
      · simp [h, h']
    · simp [h]

/-! ### Counting by halves -/

def pc : ℕ → ℕ → ℕ
  | 0, x => x % 2
  | k + 1, x => pc k (x % (1 <<< (1 <<< k))) + pc k (x >>> (1 <<< k))

theorem pc_spec : ∀ k x, pc k x = ∑ i ∈ range (2 ^ k), (if x.testBit i then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro x
    simp only [pc, pow_zero, sum_range_one, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | succ k ih =>
    intro x
    rw [pc, ih, ih, Nat.one_shiftLeft, Nat.one_shiftLeft, pow_succ, mul_two, sum_range_add]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      rw [Nat.testBit_mod_two_pow]
      simp [mem_range.1 hi]
    · refine sum_congr rfl fun i _ => ?_
      rw [Nat.testBit_shiftRight]

/-! ### The primes up to `7100` -/

set_option maxRecDepth 100000 in
def PS : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079]

/-- Trial division by `2, …, 84` (`85² > 7100`). -/
def isPrimeSlow' (n : ℕ) : Bool := 2 ≤ n && (List.range' 2 83).all (fun d => n < d * d || n % d != 0)

set_option maxRecDepth 100000 in
theorem PS_eq : PS = (List.range 7101).filter isPrimeSlow' := by decide +kernel

theorem isPrimeSlow'_iff {n : ℕ} (hn : n ≤ 7100) : isPrimeSlow' n = true ↔ n.Prime := by
  unfold isPrimeSlow'
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
    have hm84 : Nat.minFac n ≤ 84 := by nlinarith
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

theorem mem_PS {p : ℕ} : p ∈ PS ↔ p ≤ 7100 ∧ p.Prime := by
  rw [PS_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, (isPrimeSlow'_iff (by omega)).1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, (isPrimeSlow'_iff h1).2 h2⟩

/-- No prime in `(7100, 7103)`. -/
theorem prime_le_7100 {p : ℕ} (hp : p.Prime) (h : p < 7103) : p ≤ 7100 := by
  by_contra hc
  interval_cases p <;> norm_num at hp

/-- For `7100 < m < 7103²`: `m` is prime iff no `p ∈ PS` divides it. -/
theorem prime_iff_PS {m : ℕ} (h1 : 7100 < m) (h2 : m < 50452609) : m.Prime ↔ ∀ p ∈ PS, ¬ p ∣ m := by
  constructor
  · intro hm p hp hpm
    have := (mem_PS.1 hp)
    rcases (Nat.dvd_prime hm).1 hpm with h | h
    · exact this.2.one_lt.ne' h
    · omega
  · intro h
    by_contra hm
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hle := Nat.minFac_sq_le_self (show 0 < m by omega) hm
    have hlt : m.minFac < 7103 := by nlinarith
    exact h _ (mem_PS.2 ⟨prime_le_7100 hmf hlt, hmf⟩) (Nat.minFac_dvd m)

/-! ### Prime counts of windows -/

def cnt (n W : ℕ) : ℕ := W - pc (W.log2 + 1) (orAll W n PS)

theorem cnt_spec {n W : ℕ} (h1 : 7100 ≤ n) (h2 : n + W < 50452609) (hW : W ≤ 32768) :
    cnt n W = ((Ioc n (n + W)).filter Nat.Prime).card := by
  have hP : ∀ p ∈ PS, 0 < p := fun p hp => (mem_PS.1 hp).2.pos
  have hlog := Nat.lt_log2_self (n := W)
  have hpc : pc (W.log2 + 1) (orAll W n PS) =
      ∑ i ∈ range W, (if ∃ p ∈ PS, p ∣ n + 1 + i then 1 else 0) := by
    rw [pc_spec, show (2 : ℕ) ^ (W.log2 + 1) = W + (2 ^ (W.log2 + 1) - W) by omega, sum_range_add]
    have e2 : ∑ i ∈ range (2 ^ (W.log2 + 1) - W), (if (orAll W n PS).testBit (W + i) then 1 else 0) = 0 := by
      refine sum_eq_zero fun i _ => ?_
      simp [orAll_spec W n (by omega) PS hP]
    rw [e2, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [orAll_spec W n (by omega) PS hP]
    simp [mem_range.1 hi]
  have hcard : ((Ioc n (n + W)).filter Nat.Prime).card =
      ∑ i ∈ range W, (if (n + 1 + i).Prime then 1 else 0) := by
    rw [card_eq_sum_ones, sum_filter, show Ioc n (n + W) = Ico (n + 1) (n + W + 1) by ext; simp only [mem_Ioc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show n + W + 1 - (n + 1) = W by omega]
  rw [cnt, hpc, hcard]
  have hsplit : ∀ i ∈ range W, (if (n + 1 + i).Prime then 1 else 0) =
      1 - (if ∃ p ∈ PS, p ∣ n + 1 + i then 1 else 0) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hiff := prime_iff_PS (m := n + 1 + i) (by omega) (by omega)
    by_cases hp : (n + 1 + i).Prime
    · have : ¬ ∃ p ∈ PS, p ∣ n + 1 + i := by push Not; exact hiff.1 hp
      rw [if_pos hp, if_neg this]
    · have : ∃ p ∈ PS, p ∣ n + 1 + i := by
        by_contra hc; push Not at hc; exact hp (hiff.2 hc)
      rw [if_neg hp, if_pos this]
  rw [sum_congr rfl hsplit]
  have hle : ∀ i ∈ range W, (if ∃ p ∈ PS, p ∣ n + 1 + i then 1 else 0) ≤ 1 := fun i _ => by
    split_ifs <;> norm_num
  rw [sum_tsub_distrib _ hle, sum_const, card_range, smul_eq_mul, mul_one]

/-! ### The window chain (`θ` only) -/

theorem thS_sub {a b : ℕ} (hab : a ≤ b) :
    thS b - thS a = ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  rw [thS, thS, sum_filter, sum_filter, sum_filter, show Icc 1 b = Ioc 0 b from rfl,
    show Icc 1 a = Ioc 0 a from rfl, ← sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

def InvT (m tlo thi : ℕ) : Prop := (tlo : ℝ) / S ≤ thS m ∧ thS m ≤ (thi : ℝ) / S

/-- The checks on a window `(n, e]`: `θ(e) ≤ n + (bN/bD)√n` and `e − θ(n) ≤ (aN/aD)√n`. -/
def winOKT (n e tlo thi' aN aD bN bD : ℕ) : Bool := leSq thi' (S * n) n bN bD && leSq (S * e) tlo n aN aD

/-- The bounds at real `t`. -/
def RtT (aN aD bN bD : ℕ) (t : ℝ) : Prop :=
  thS ⌊t⌋₊ - t ≤ (bN : ℝ) / bD * √t ∧ t - thS ⌊t⌋₊ ≤ (aN : ℝ) / aD * √t

theorem window_okT {n G tlo thi a b aN aD bN bD : ℕ} (haD : 0 < aD) (hbD : 0 < bD)
    (h0 : InvT n tlo thi) (h1 : InvT (n + G) a b) (hw : winOKT n (n + G) tlo b aN aD bN bD = true)
    {t : ℝ} (ht1 : (n : ℝ) ≤ t) (ht2 : t < ((n + G : ℕ) : ℝ)) : RtT aN aD bN bD t := by
  have hS := S_pos
  unfold winOKT at hw
  simp only [Bool.and_eq_true] at hw
  obtain ⟨w1, w2⟩ := hw
  have l1 := leSq_spec hbD w1
  have l2 := leSq_spec haD w2
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  have hfl1 : n ≤ ⌊t⌋₊ := Nat.le_floor ht1
  have hfl2 : ⌊t⌋₊ ≤ n + G := by
    have := Nat.floor_lt ht0 |>.2 ht2; omega
  have hsq : √(n : ℝ) ≤ √t := Real.sqrt_le_sqrt ht1
  have hb : 0 ≤ (bN : ℝ) / bD := by positivity
  have ha : 0 ≤ (aN : ℝ) / aD := by positivity
  obtain ⟨a0, a1⟩ := h0
  obtain ⟨b0, b1⟩ := h1
  have m1 := thS_mono hfl1; have m2 := thS_mono hfl2
  have eS : ∀ x : ℕ, ((S * x : ℕ) : ℝ) / S = x := fun x => by push_cast; field_simp
  rw [eS] at l1 l2
  push_cast at l1 l2 ht2
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hsq hb; linarith
  · have := mul_le_mul_of_nonneg_left hsq ha; linarith

/-- The checkpoint loop: each window `(G, L1, H1)` (`L1 = 0`: the log chain; otherwise
`L1 ≤ S log e < H1` is certified) is sieved, `θ` grows by `cnt · [LL, LHe]/S`. -/
def outerT (aN aD bN bD : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) →
    Option (ℕ × ℕ × ℕ × ℕ × ℕ)
  | n, tlo, thi, LL, LH, [] => some (n, tlo, thi, LL, LH)
  | n, tlo, thi, LL, LH, (G, L1, H1) :: gs =>
    let LLe := if L1 = 0 then LL + S * G / (n + G) else L1
    let LHe := if L1 = 0 then LH + (S * G + n - 1) / n else H1
    if (L1 = 0 ∨ (chkLow L1 S (n + G) = true ∧ chkStep H1 S 1 (n + G) = true)) ∧ 1 ≤ G ∧ G ≤ 32768 ∧
        7100 ≤ n ∧ n + G < 50452609 then
      let c := cnt n G
      if winOKT n (n + G) tlo (thi + c * LHe) aN aD bN bD = true then
        outerT aN aD bN bD (n + G) (tlo + c * LL) (thi + c * LHe) LLe LHe gs
      else none
    else none

theorem outerT_spec {aN aD bN bD : ℕ} (haD : 0 < aD) (hbD : 0 < bD) :
    ∀ (gs : List (ℕ × ℕ × ℕ)) (n tlo thi LL LH n' tlo' thi' LL' LH' : ℕ),
    1 ≤ n → InvT n tlo thi → (LL : ℝ) / S ≤ Real.log n → Real.log n ≤ (LH : ℝ) / S →
    outerT aN aD bN bD n tlo thi LL LH gs = some (n', tlo', thi', LL', LH') →
    (∀ t : ℝ, (n : ℝ) ≤ t → t < n' → RtT aN aD bN bD t) ∧ InvT n' tlo' thi' ∧
      (LL' : ℝ) / S ≤ Real.log n' ∧ Real.log n' ≤ (LH' : ℝ) / S := by
  intro gs
  induction gs with
  | nil =>
    intro n tlo thi LL LH n' tlo' thi' LL' LH' _ hI hL hH h
    simp only [outerT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨fun t h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _), hI, hL, hH⟩
  | cons g gs ih =>
    obtain ⟨G, L1, H1⟩ := g
    intro n tlo thi LL LH n' tlo' thi' LL' LH' hn hI hL hH h
    have hS := S_pos
    have hS0 : (0 : ℕ) < S := by unfold S; norm_num
    unfold outerT at h
    simp only at h
    by_cases hc : (L1 = 0 ∨ (chkLow L1 S (n + G) = true ∧ chkStep H1 S 1 (n + G) = true)) ∧ 1 ≤ G ∧
        G ≤ 32768 ∧ 7100 ≤ n ∧ n + G < 50452609
    swap
    · rw [if_neg hc] at h; exact absurd h (by simp)
    rw [if_pos hc] at h
    obtain ⟨hc, hG1, hG2, hn1, hn2⟩ := hc
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
    by_cases hw : winOKT n (n + G) tlo (thi + cnt n G * LHe) aN aD bN bD = true
    swap
    · rw [if_neg hw] at h; exact absurd h (by simp)
    rw [if_pos hw] at h
    -- the window's primes
    have hcnt := cnt_spec hn1 hn2 hG2
    have hsub := thS_sub (show n ≤ n + G by omega)
    have hlo : (cnt n G : ℝ) * ((LL : ℝ) / S) ≤ thS (n + G) - thS n := by
      rw [hsub, hcnt, ← nsmul_eq_mul]
      refine card_nsmul_le_sum _ _ _ fun p hp => ?_
      have hp' := mem_filter.1 hp
      have hp1 := (mem_Ioc.1 hp'.1).1
      exact hL.trans (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hp1.le))
    have hhi : thS (n + G) - thS n ≤ (cnt n G : ℝ) * ((LHe : ℝ) / S) := by
      rw [hsub, hcnt, ← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun p hp => ?_
      have hp' := mem_filter.1 hp
      have hp2 := (mem_Ioc.1 hp'.1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
      exact (Real.log_le_log hp0 (by exact_mod_cast hp2)).trans hlog.2
    have hI1 : InvT (n + G) (tlo + cnt n G * LL) (thi + cnt n G * LHe) := by
      obtain ⟨i1, i2⟩ := hI
      constructor
      · push_cast; rw [add_div, mul_div_assoc]; linarith
      · push_cast; rw [add_div, mul_div_assoc]; linarith
    obtain ⟨ihR, ihI, ihL, ihH⟩ := ih (n + G) _ _ LLe LHe n' tlo' thi' LL' LH' (by omega) hI1
      hlog.1 hlog.2 h
    refine ⟨fun t ht1 ht2 => ?_, ihI, ihL, ihH⟩
    by_cases htG : t < ((n + G : ℕ) : ℝ)
    · exact window_okT haD hbD hI hI1 hw ht1 htG
    · push Not at htG
      exact ihR t htG ht2

/-- Component-wise comparison with a given state. -/
def resEqT : Option (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | some (a, b, c, d, e), a', b', c', d', e' =>
    Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d' && Nat.beq e e'
  | none, _, _, _, _, _ => false

theorem resEqT_spec {r : Option (ℕ × ℕ × ℕ × ℕ × ℕ)} {a' b' c' d' e' : ℕ}
    (h : resEqT r a' b' c' d' e' = true) : r = some (a', b', c', d', e') := by
  rcases r with _ | ⟨a, b, c, d, e⟩
  · simp [resEqT] at h
  · simp only [resEqT, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [Nat.beq_eq] at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl

end TernaryGoldbach.Prelim.SieveTab
