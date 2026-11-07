import TernaryGoldbach.Prelim.SmallPsiTable

/-!
# A bit sieve in the kernel: `θ` on `[10⁶, 5·10⁷)`

The trial-division table (`SmallPsiTable`) costs about `3·10⁻³ s` per integer near `10⁶`. Here a window
`(n, n + W]` (`W ≤ 2¹⁵`) is sieved with one bit mask per prime `p ≤ 7100`, built by doubling
(`maskP`) once per declaration (`pats`); per window each mask is shifted into place and or-ed in
(`orP`, three operations per prime). The primes are the set bits of the complement, counted by halving
down to 256-bit leaves and clearing the lowest set bit there (`pcL`, `popc`). Every step is a GMP
operation on a `W`-bit `Nat`. `cnt_spec`: `cnt n W` is the number of primes in `(n, n + W]` for
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

/-! ### Counting set bits -/

/-- The number of set bits among the first `B`. -/
def nbits (B y : ℕ) : ℕ := ∑ i ∈ range B, (if y.testBit i then 1 else 0)

/-- `f` minus the number of set bits of `y`, if there are at most `f`: clear the lowest set bit
(`y &&& (y − 1)`, GMP operations in the kernel) until `y = 0`, and return the fuel left. One step per
set bit; returning the fuel (a literal at each step) instead of a count avoids a chain of
unevaluated additions. -/
noncomputable def popc (f : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun n ih y => Bool.rec (ih (Nat.land y (Nat.sub y 1))) (Nat.succ n) (Nat.beq y 0)) f

theorem popc_succ (f y : ℕ) : popc (f + 1) y =
    Bool.rec (popc f (Nat.land y (Nat.sub y 1))) (Nat.succ f) (Nat.beq y 0) := rfl

/-- `y &&& (y − 1)` is `y` without its lowest set bit `k`. -/
theorem testBit_land_sub_one {y : ℕ} (hy : y ≠ 0) : ∃ k, y.testBit k = true ∧
    ∀ j, (y &&& (y - 1)).testBit j = (y.testBit j && decide (j ≠ k)) := by
  have hex := Nat.exists_testBit_of_ne_zero hy
  classical
  set k := Nat.find hex with hk
  have hkb : y.testBit k = true := Nat.find_spec hex
  have hlow : ∀ j < k, y.testBit j = false := fun j hj => by
    have := Nat.find_min hex hj; simpa using this
  -- `y = 2^k q` with `q` odd
  have hmod : y % 2 ^ k = 0 := Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hj : j < k
    · simp [hj, hlow j hj]
    · simp [hj]
  set q := y / 2 ^ k with hq
  have hyq : y = 2 ^ k * q + 0 := by
    rw [add_zero, hq]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
  have hq0 : q.testBit 0 = true := by rw [hq, Nat.testBit_div_two_pow, zero_add]; exact hkb
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.zero_testBit] at hq0; exact absurd hq0 (by simp)
    · exact h
  have hy1 : y - 1 = 2 ^ k * (q - 1) + (2 ^ k - 1) := by
    have : 2 ^ k * (q - 1) + 2 ^ k = 2 ^ k * q := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq1]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  -- `q − 1` is `q` without bit `0`
  have hqq : ∀ m, (q - 1).testBit m = (q.testBit m && decide (m ≠ 0)) := by
    intro m
    have hqo : q % 2 = 1 := by simpa using hq0
    obtain ⟨r, hr⟩ : ∃ r, q = 2 ^ 1 * r + 1 := ⟨q / 2, by have := Nat.div_add_mod q 2; omega⟩
    have e2 : q - 1 = 2 ^ 1 * r + 0 := by omega
    rw [e2, hr, Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_mul_add _ (by norm_num)]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · simp [show ¬ m < 1 by omega, show m ≠ 0 by omega]
  refine ⟨k, hkb, fun j => ?_⟩
  rw [Nat.testBit_and, hy1, Nat.testBit_two_pow_mul_add _ (Nat.sub_lt (Nat.two_pow_pos k) one_pos),
    hyq, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos k), Nat.testBit_two_pow_sub_one]
  by_cases hj : j < k
  · simp [hj, show j ≠ k by omega]
  · simp only [hj, ↓reduceIte]
    rw [hqq]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [show j - k ≠ 0 by omega, hjk]

/-- Clearing the lowest set bit removes one set bit. -/
theorem nbits_clear {B y : ℕ} (hy : y ≠ 0) (hB : y < 2 ^ B) :
    nbits B y = nbits B (y &&& (y - 1)) + 1 := by
  obtain ⟨k, hk, hbits⟩ := testBit_land_sub_one hy
  have hkB : k < B := by
    by_contra h
    push Not at h
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) h))] at hk
    exact absurd hk (by simp)
  have hbit : ∀ i, (if y.testBit i then 1 else 0) =
      (if (y &&& (y - 1)).testBit i then 1 else 0) + (if i = k then 1 else 0) := by
    intro i
    rw [hbits]
    by_cases hi : i = k
    · subst hi; simp [hk]
    · simp [hi]
  unfold nbits
  rw [sum_congr rfl fun i _ => hbit i, sum_add_distrib, sum_ite_eq' (range B) k (fun _ => 1)]
  simp [mem_range.2 hkB]

theorem nbits_le (B y : ℕ) : nbits B y ≤ B := by
  unfold nbits
  calc ∑ i ∈ range B, (if y.testBit i then 1 else 0) ≤ ∑ _i ∈ range B, 1 :=
        sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = B := by simp

theorem popc_spec {B : ℕ} : ∀ f y, y < 2 ^ B → nbits B y ≤ f → popc f y = f - nbits B y := by
  intro f
  induction f with
  | zero => intro y _ hf; rw [Nat.zero_sub]; rfl
  | succ f ih =>
    intro y hy hf
    rw [popc_succ]
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      have : nbits B 0 = 0 := by simp [nbits]
      rw [this]; rfl
    · have hb : Nat.beq y 0 = false := by
        rw [Bool.eq_false_iff]; intro h; exact h0.ne' (Nat.eq_of_beq_eq_true h)
      rw [hb]
      show popc f (Nat.land y (Nat.sub y 1)) = f + 1 - nbits B y
      rw [Nat.sub_eq, Nat.land_eq]
      have hc := nbits_clear h0.ne' hy
      have hlt : y &&& (y - 1) < 2 ^ B := lt_of_le_of_lt Nat.and_le_left hy
      rw [ih _ hlt (by omega)]
      omega

/-- The set bits of `x` below `2^(k+8)`: halve `k` times, then count each 256-bit leaf with `popc`
(the kernel's whnf recursion depth grows with the length of a loop, so loops stay short). -/
noncomputable def pcL (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ)
    (fun x => Nat.sub 256 (popc 256 (Nat.mod x 115792089237316195423570985008687907853269984665640564039457584007913129639936)))
    (fun k ih x => Nat.add (ih (Nat.mod x (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add k 8)))))
      (ih (Nat.shiftRight x (Nat.shiftLeft 1 (Nat.add k 8))))) k

theorem pcL_zero : pcL 0 = fun x => Nat.sub 256 (popc 256 (Nat.mod x
    115792089237316195423570985008687907853269984665640564039457584007913129639936)) := rfl

theorem pcL_succ (k : ℕ) : pcL (k + 1) = fun x => Nat.add (pcL k (Nat.mod x (Nat.shiftLeft 1
    (Nat.shiftLeft 1 (Nat.add k 8))))) (pcL k (Nat.shiftRight x (Nat.shiftLeft 1 (Nat.add k 8)))) := rfl

theorem natMod_eq (x y : ℕ) : Nat.mod x y = x % y := rfl

theorem nbits_mod_two_pow (B x : ℕ) : nbits B (x % 2 ^ B) = nbits B x := by
  unfold nbits
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (mem_range.1 hi), Bool.true_and]

theorem pcL_spec : ∀ k x, pcL k x = nbits (2 ^ (k + 8)) x := by
  intro k
  induction k with
  | zero =>
    intro x
    rw [pcL_zero]
    show Nat.sub 256 (popc 256 (Nat.mod x _)) = _
    rw [Nat.sub_eq, show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : ℕ)
      = 2 ^ 256 by norm_num, natMod_eq, popc_spec (B := 256) 256 _ (Nat.mod_lt _ (by positivity))
      (nbits_le _ _), Nat.sub_sub_self (nbits_le _ _), nbits_mod_two_pow, zero_add,
      show (2 : ℕ) ^ 8 = 256 by norm_num]
  | succ k ih =>
    intro x
    rw [pcL_succ]
    show Nat.add (pcL k (Nat.mod x _)) (pcL k (Nat.shiftRight x _)) = _
    rw [Nat.add_eq, ih, ih, Nat.shiftLeft_eq', Nat.shiftLeft_eq', Nat.add_eq, Nat.one_shiftLeft,
      Nat.one_shiftLeft, natMod_eq, Nat.shiftRight_eq', nbits_mod_two_pow]
    unfold nbits
    have e : 2 ^ (k + 1 + 8) = 2 ^ (k + 8) + 2 ^ (k + 8) := by
      rw [show k + 1 + 8 = (k + 8) + 1 by ring, pow_succ]; ring
    rw [e, sum_range_add]
    congr 1
    refine sum_congr rfl fun i _ => ?_
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

/-! ### Shifted patterns -/

/-- Each `p ∈ PS` with its pattern: the bits at the multiples of `p` below `40000 ≥ 2¹⁵ + 7100`.
The kernel builds it once per declaration. -/
def pats : List (ℕ × ℕ) := PS.map fun p => (p, maskP p 0 40000)

/-- The or of the patterns, each shifted by `(n + 1) mod p`: bit `i` (for `i + 7100 ≤ 40000`) is set
iff some `p ∈ PS` divides `n + 1 + i`. Three GMP operations per prime. -/
noncomputable def orP (n : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  @List.rec (ℕ × ℕ) (fun _ => ℕ) 0
    (fun hd _ ih => Nat.lor (Nat.shiftRight hd.2 (Nat.mod (Nat.add n 1) hd.1)) ih) ps

theorem orP_cons (n : ℕ) (q : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    orP n (q :: ps) = Nat.lor (Nat.shiftRight q.2 (Nat.mod (Nat.add n 1) q.1)) (orP n ps) := rfl

theorem orP_spec (n : ℕ) : ∀ (ps : List (ℕ × ℕ)), (∀ q ∈ ps, 0 < q.1 ∧ q.1 ≤ 7100 ∧
    q.2 = maskP q.1 0 40000) → ∀ i, i + 7100 ≤ 40000 →
    (orP n ps).testBit i = decide (∃ q ∈ ps, q.1 ∣ n + 1 + i) := by
  intro ps
  induction ps with
  | nil => intro _ i _; simp [orP]
  | cons q ps ih =>
    intro hq i hi
    obtain ⟨h0, h1, h2⟩ := hq q (by simp)
    rw [orP_cons, Nat.lor_eq, Nat.testBit_or, Nat.shiftRight_eq', Nat.testBit_shiftRight,
      h2, maskP_spec h0 h0 (by norm_num), ih (fun r hr => hq r (by simp [hr])) i hi]
    have hs : Nat.mod (Nat.add n 1) q.1 + i < 40000 := by
      have := Nat.mod_lt (n + 1) h0; show (n + 1) % q.1 + i < 40000; omega
    have hdvd : (Nat.mod (Nat.add n 1) q.1 + i) % q.1 = 0 ↔ q.1 ∣ n + 1 + i := by
      show ((n + 1) % q.1 + i) % q.1 = 0 ↔ _
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    by_cases hd : q.1 ∣ n + 1 + i
    · simp [hs, hdvd.2 hd, hd]
    · have : ¬ (Nat.mod (Nat.add n 1) q.1 + i) % q.1 = 0 := fun h => hd (hdvd.1 h)
      simp only [hs, this, and_false, decide_false, Bool.false_or, List.mem_cons, exists_eq_or_imp, hd,
        false_or]

theorem mem_pats {q : ℕ × ℕ} : q ∈ pats ↔ ∃ p ∈ PS, q = (p, maskP p 0 40000) := by
  simp only [pats, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-! ### Prime counts of windows -/

/-- The number of primes in `(n, n + W]`: the set bits of the complement of the sieve. -/
noncomputable def cnt (n W : ℕ) : ℕ := pcL 7 ((2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1)))

theorem cnt_spec {n W : ℕ} (h1 : 7100 ≤ n) (h2 : n + W < 50452609) (hW : W ≤ 32768) :
    cnt n W = ((Ioc n (n + W)).filter Nat.Prime).card := by
  have hq : ∀ q ∈ pats, 0 < q.1 ∧ q.1 ≤ 7100 ∧ q.2 = maskP q.1 0 40000 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_pats.1 hq
    exact ⟨(mem_PS.1 hp).2.pos, (mem_PS.1 hp).1, rfl⟩
  have hex : ∀ m, (∃ q ∈ pats, q.1 ∣ m) ↔ ∃ p ∈ PS, p ∣ m := by
    intro m
    constructor
    · rintro ⟨q, hq', hd⟩
      obtain ⟨p, hp, rfl⟩ := mem_pats.1 hq'
      exact ⟨p, hp, hd⟩
    · rintro ⟨p, hp, hd⟩
      exact ⟨(p, maskP p 0 40000), mem_pats.2 ⟨p, hp, rfl⟩, hd⟩
  have hbits : ∀ i, ((2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1))).testBit i =
      decide (i < W ∧ ¬ ∃ p ∈ PS, p ∣ n + 1 + i) := by
    intro i
    rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < W
    · rw [orP_spec n pats hq i (by omega)]
      by_cases he : ∃ p ∈ PS, p ∣ n + 1 + i
      · have : ∃ q ∈ pats, q.1 ∣ n + 1 + i := (hex _).2 he
        simp [hi, he, this]
      · have : ¬ ∃ q ∈ pats, q.1 ∣ n + 1 + i := fun h => he ((hex _).1 h)
        simp [hi, he, this]
    · simp [hi]
  have hlt : (2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1)) < 2 ^ W :=
    Nat.lt_pow_two_of_testBit _ fun i hi => by rw [hbits]; simp; omega
  have hpc : pcL 7 ((2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1))) = nbits W ((2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1))) := by
    rw [pcL_spec, show (2 : ℕ) ^ (7 + 8) = W + (32768 - W) by norm_num; omega]
    unfold nbits
    rw [sum_range_add]
    have : ∑ i ∈ range (32768 - W), (if ((2 ^ W - 1) ^^^ (orP n pats &&& (2 ^ W - 1))).testBit (W + i) then 1 else 0) = 0 :=
      sum_eq_zero fun i _ => by rw [hbits]; simp
    rw [this, add_zero]
  have hcard : ((Ioc n (n + W)).filter Nat.Prime).card =
      ∑ i ∈ range W, (if (n + 1 + i).Prime then 1 else 0) := by
    rw [card_eq_sum_ones, sum_filter, show Ioc n (n + W) = Ico (n + 1) (n + W + 1) by ext; simp only [mem_Ioc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show n + W + 1 - (n + 1) = W by omega]
  rw [cnt, hpc, hcard, nbits]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have hiff := prime_iff_PS (m := n + 1 + i) (by omega) (by omega)
  rw [hbits]
  by_cases hp : (n + 1 + i).Prime
  · have : ¬ ∃ p ∈ PS, p ∣ n + 1 + i := by push Not; exact hiff.1 hp
    simp [hi', this, hp]
  · have : ∃ p ∈ PS, p ∣ n + 1 + i := by
      by_contra hc; push Not at hc; exact hp (hiff.2 hc)
    simp [hi', this, hp]

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
noncomputable def outerT (aN aD bN bD : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) →
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
