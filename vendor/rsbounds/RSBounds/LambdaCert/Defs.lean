/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

/-!
# The checker for the von Mangoldt computations (L)

`Nat`-only, with structural recursion (`Nat.rec`, `List.foldr`), for evaluation by the kernel.

One step processes `k = n + 1` and carries, in fixed point with scale `S = 10^24`:

* `q`, the last prime power `≤ n` (or `1`), with bounds `llo, lhi` for `log q`; at a prime power
  `k`, `log k = log q + log ((1 + x)/(1 - x))` with `x = (k - q)/(k + q) ≤ 1/3`, by the `artanh`
  series;
* an upper bound `ahi` for `A(k)`, checked against `2 (k - 1)` at every `k`;
* lower and upper bounds for `G(k)` and `H(k)`;
* `sq = ⌊√(k · 10^30)⌋`, checked at every step.

The work is cut into segments `[L, L + B)`.  For each segment the checker builds two bit masks: the
multiples `m ≥ 2p` of the primes `p ≤ 1024` (a sieve: an unmarked `k ≥ 2` is prime), and the
prime powers `p^j`, `j ≥ 2`, of `hpList`.  A marked `k` that is not in `hpList` is not a prime
power.  For `k` in `hpList`, `j` is read off the list.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

/-- Fixed-point scale: `10^24`. -/
def S : Nat := 1000000000000000000000000

/-- `2 S`. -/
def S2 : Nat := 2000000000000000000000000

/-- Square-root scale: `10^15`. -/
def R : Nat := 1000000000000000

/-- `R^2 = 10^30`. -/
def RR : Nat := 1000000000000000000000000000000

/-- `S R = 10^39`. -/
def SR : Nat := 1000000000000000000000000000000000000000

/-- `2^20`. -/
def TOP : Nat := 1048576

/-- The primes up to `1024`. -/
def smallPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021]

/-- The prime powers `q = p^j ≤ 2^20` with `j ≥ 2`, as `(q, p, j)`. -/
def hpList : List (Nat × Nat × Nat) := [(4, 2, 2), (8, 2, 3), (9, 3, 2), (16, 2, 4), (25, 5, 2), (27, 3, 3), (32, 2, 5), (49, 7, 2), (64, 2, 6), (81, 3, 4), (121, 11, 2), (125, 5, 3), (128, 2, 7), (169, 13, 2), (243, 3, 5), (256, 2, 8), (289, 17, 2), (343, 7, 3), (361, 19, 2), (512, 2, 9), (529, 23, 2), (625, 5, 4), (729, 3, 6), (841, 29, 2), (961, 31, 2), (1024, 2, 10), (1331, 11, 3), (1369, 37, 2), (1681, 41, 2), (1849, 43, 2), (2048, 2, 11), (2187, 3, 7), (2197, 13, 3), (2209, 47, 2), (2401, 7, 4), (2809, 53, 2), (3125, 5, 5), (3481, 59, 2), (3721, 61, 2), (4096, 2, 12), (4489, 67, 2), (4913, 17, 3), (5041, 71, 2), (5329, 73, 2), (6241, 79, 2), (6561, 3, 8), (6859, 19, 3), (6889, 83, 2), (7921, 89, 2), (8192, 2, 13), (9409, 97, 2), (10201, 101, 2), (10609, 103, 2), (11449, 107, 2), (11881, 109, 2), (12167, 23, 3), (12769, 113, 2), (14641, 11, 4), (15625, 5, 6), (16129, 127, 2), (16384, 2, 14), (16807, 7, 5), (17161, 131, 2), (18769, 137, 2), (19321, 139, 2), (19683, 3, 9), (22201, 149, 2), (22801, 151, 2), (24389, 29, 3), (24649, 157, 2), (26569, 163, 2), (27889, 167, 2), (28561, 13, 4), (29791, 31, 3), (29929, 173, 2), (32041, 179, 2), (32761, 181, 2), (32768, 2, 15), (36481, 191, 2), (37249, 193, 2), (38809, 197, 2), (39601, 199, 2), (44521, 211, 2), (49729, 223, 2), (50653, 37, 3), (51529, 227, 2), (52441, 229, 2), (54289, 233, 2), (57121, 239, 2), (58081, 241, 2), (59049, 3, 10), (63001, 251, 2), (65536, 2, 16), (66049, 257, 2), (68921, 41, 3), (69169, 263, 2), (72361, 269, 2), (73441, 271, 2), (76729, 277, 2), (78125, 5, 7), (78961, 281, 2), (79507, 43, 3), (80089, 283, 2), (83521, 17, 4), (85849, 293, 2), (94249, 307, 2), (96721, 311, 2), (97969, 313, 2), (100489, 317, 2), (103823, 47, 3), (109561, 331, 2), (113569, 337, 2), (117649, 7, 6), (120409, 347, 2), (121801, 349, 2), (124609, 353, 2), (128881, 359, 2), (130321, 19, 4), (131072, 2, 17), (134689, 367, 2), (139129, 373, 2), (143641, 379, 2), (146689, 383, 2), (148877, 53, 3), (151321, 389, 2), (157609, 397, 2), (160801, 401, 2), (161051, 11, 5), (167281, 409, 2), (175561, 419, 2), (177147, 3, 11), (177241, 421, 2), (185761, 431, 2), (187489, 433, 2), (192721, 439, 2), (196249, 443, 2), (201601, 449, 2), (205379, 59, 3), (208849, 457, 2), (212521, 461, 2), (214369, 463, 2), (218089, 467, 2), (226981, 61, 3), (229441, 479, 2), (237169, 487, 2), (241081, 491, 2), (249001, 499, 2), (253009, 503, 2), (259081, 509, 2), (262144, 2, 18), (271441, 521, 2), (273529, 523, 2), (279841, 23, 4), (292681, 541, 2), (299209, 547, 2), (300763, 67, 3), (310249, 557, 2), (316969, 563, 2), (323761, 569, 2), (326041, 571, 2), (332929, 577, 2), (344569, 587, 2), (351649, 593, 2), (357911, 71, 3), (358801, 599, 2), (361201, 601, 2), (368449, 607, 2), (371293, 13, 5), (375769, 613, 2), (380689, 617, 2), (383161, 619, 2), (389017, 73, 3), (390625, 5, 8), (398161, 631, 2), (410881, 641, 2), (413449, 643, 2), (418609, 647, 2), (426409, 653, 2), (434281, 659, 2), (436921, 661, 2), (452929, 673, 2), (458329, 677, 2), (466489, 683, 2), (477481, 691, 2), (491401, 701, 2), (493039, 79, 3), (502681, 709, 2), (516961, 719, 2), (524288, 2, 19), (528529, 727, 2), (531441, 3, 12), (537289, 733, 2), (546121, 739, 2), (552049, 743, 2), (564001, 751, 2), (571787, 83, 3), (573049, 757, 2), (579121, 761, 2), (591361, 769, 2), (597529, 773, 2), (619369, 787, 2), (635209, 797, 2), (654481, 809, 2), (657721, 811, 2), (674041, 821, 2), (677329, 823, 2), (683929, 827, 2), (687241, 829, 2), (703921, 839, 2), (704969, 89, 3), (707281, 29, 4), (727609, 853, 2), (734449, 857, 2), (737881, 859, 2), (744769, 863, 2), (769129, 877, 2), (776161, 881, 2), (779689, 883, 2), (786769, 887, 2), (822649, 907, 2), (823543, 7, 7), (829921, 911, 2), (844561, 919, 2), (863041, 929, 2), (877969, 937, 2), (885481, 941, 2), (896809, 947, 2), (908209, 953, 2), (912673, 97, 3), (923521, 31, 4), (935089, 967, 2), (942841, 971, 2), (954529, 977, 2), (966289, 983, 2), (982081, 991, 2), (994009, 997, 2), (1018081, 1009, 2), (1026169, 1013, 2), (1030301, 101, 3), (1038361, 1019, 2), (1042441, 1021, 2), (1048576, 2, 20)]

/-! ## Masks -/

/-- `∑_{t < c} 2^(t p)`. -/
def geom (p c : Nat) : Nat := (2 ^ (c * p) - 1) / (2 ^ p - 1)

/-- First multiple of `p` that is `≥ max(2p, L)`. -/
def firstMult (p L : Nat) : Nat := p * max 2 ((L + p - 1) / p)

/-- Bit `m - L` set for each multiple `m ≥ 2p` of `p` in `[L, L + B)`. -/
def pat (p L B : Nat) : Nat :=
  if firstMult p L < L + B then
    2 ^ (firstMult p L - L) * geom p ((L + B - firstMult p L + p - 1) / p)
  else 0

/-- The sieve mask of the segment `[L, L + B)`. -/
def compMask (L B : Nat) : Nat := smallPrimes.foldr (fun p acc => pat p L B ||| acc) 0

/-- The mask of the elements of `hpList` in `[L, L + B)`. -/
def hpMask (L B : Nat) : Nat :=
  hpList.foldr (fun e acc => (if L ≤ e.1 ∧ e.1 < L + B then 2 ^ (e.1 - L) else 0) ||| acc) 0

/-- The exponent `j` of `k` in `hpList`, or `0`. -/
def hpLookup (k : Nat) (l : List (Nat × Nat × Nat)) : Nat :=
  l.foldr (fun e r => cond (Nat.beq e.1 k) e.2.2 r) 0

/-! ## Logarithms -/

/-- Terms `i, i + 1, …` of `2 S ∑ x^(2i+1)/(2i+1)`, `x = g/D`, given `pn = g^(2i+1)`,
`pd = D^(2i+1)`, `g2 = g^2`, `D2 = D^2`: a lower bound and an upper bound (with the tail). -/
def serTail (g2 D2 fuel : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun _ pn pd => (0, Nat.div (Nat.sub (Nat.add (Nat.mul S pn) pd) 1) pd))
    (fun _ ih i pn pd =>
      cond (Nat.blt (Nat.mul S pn) pd) (0, 1)
        ((fun (t : Nat) (r : Nat × Nat) => (Nat.add t r.1, Nat.add (Nat.add t 1) r.2))
          (Nat.div (Nat.mul S2 pn) (Nat.mul (Nat.add (Nat.mul 2 i) 1) pd))
          (ih (Nat.add i 1) (Nat.mul pn g2) (Nat.mul pd D2)))) fuel

/-- Bounds, at scale `S`, for `log (1 + x) - log (1 - x)`, `x = g/D`. -/
def logRatio (g D : Nat) : Nat × Nat :=
  (fun (t : Nat) (r : Nat × Nat) => (Nat.add t r.1, Nat.add (Nat.add t 1) r.2))
    (Nat.div (Nat.mul S2 g) D)
    (serTail (Nat.mul g g) (Nat.mul D D) 30 1 (Nat.mul (Nat.mul g g) g) (Nat.mul (Nat.mul D D) D))

/-! ## Square roots -/

/-- Newton's iteration for `⌊√N⌋` from `x`, at most `fuel` steps. -/
def newton (N fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => (fun y => cond (Nat.blt y x) (ih y) x) (Nat.div (Nat.add x (Nat.div N x)) 2)) fuel

/-! ## One step -/

/-- Bounds for `|λ - 1|` from bounds `lo, hi` for `λ` (scale `S`); first component: success. -/
def aBounds (lo hi : Nat) : Bool × Nat × Nat :=
  cond (Nat.ble hi S) (true, Nat.sub S hi, Nat.sub S lo)
    (cond (Nat.ble S lo) (true, Nat.sub lo S, Nat.sub hi S) (false, 0, 0))

/-- The state after processing `2, …, n`. -/
structure State where
  n : Nat
  q : Nat
  llo : Nat
  lhi : Nat
  ahi : Nat
  glo : Nat
  ghi : Nat
  hlo : Nat
  hhi : Nat
  sq : Nat
deriving Repr

/-- Field-by-field equality test. -/
def State.beq (a b : State) : Bool :=
  Nat.beq a.n b.n && Nat.beq a.q b.q && Nat.beq a.llo b.llo && Nat.beq a.lhi b.lhi &&
    Nat.beq a.ahi b.ahi && Nat.beq a.glo b.glo && Nat.beq a.ghi b.ghi && Nat.beq a.hlo b.hlo &&
    Nat.beq a.hhi b.hhi && Nat.beq a.sq b.sq

/-- The new state when `k` is not a prime power (`a_k = 1`). -/
def nextNP (s : State) (k x : Nat) : State :=
  ⟨k, s.q, s.llo, s.lhi, Nat.add s.ahi S, Nat.add s.glo (Nat.div S k),
    Nat.add s.ghi (Nat.add (Nat.div S k) 1), Nat.add s.hlo (Nat.div SR (Nat.add x 1)),
    Nat.add s.hhi (Nat.add (Nat.div SR x) 1), x⟩

/-- The new state when `k = p^j`, `j ≥ 1`, given bounds `l1, l2` for `log k` and bounds
`al, ah` for `|log p - 1|`. -/
def nextPP (s : State) (k x l1 l2 al ah : Nat) : State :=
  ⟨k, k, l1, l2, Nat.add s.ahi ah, Nat.add s.glo (Nat.div al k),
    Nat.add s.ghi (Nat.add (Nat.div ah k) 1), Nat.add s.hlo (Nat.div (Nat.mul al R) (Nat.add x 1)),
    Nat.add s.hhi (Nat.add (Nat.div (Nat.mul ah R) x) 1), x⟩

/-- The checks common to all steps (the last four only force evaluation). -/
def commonOK (s t : State) (k x : Nat) : Bool :=
  Nat.ble 1 x && Nat.ble (Nat.mul x x) (Nat.mul k RR) &&
    Nat.ble (Nat.mul k RR) (Nat.mul (Nat.add x 1) (Nat.add x 1)) && Nat.ble k TOP &&
    Nat.ble t.ahi (Nat.mul (Nat.mul 2 s.n) S) && Nat.ble t.q k && Nat.ble t.llo t.lhi &&
    Nat.ble t.glo t.ghi && Nat.ble t.hlo t.hhi

/-- Last stage of a prime-power step: the checks, given bounds `l1, l2` for `log k` and the result
`a` of `aBounds`. -/
def ppFinish (s : State) (k x l1 l2 : Nat) (a : Bool × Nat × Nat) : Option State :=
  (fun (t : State) =>
    cond (a.1 && Nat.blt s.q k && Nat.ble (Nat.mul 3 (Nat.sub k s.q)) (Nat.add k s.q) &&
        commonOK s t k x) (some t) none)
    (nextPP s k x l1 l2 a.2.1 a.2.2)

/-- Middle stage of a prime-power step, given the increment `d` of the logarithm. -/
def ppLogs (s : State) (k x j : Nat) (d : Nat × Nat) : Option State :=
  (fun (l1 l2 : Nat) => ppFinish s k x l1 l2 (aBounds (Nat.div l1 j) (Nat.add (Nat.div l2 j) 1)))
    (Nat.add s.llo d.1) (Nat.add s.lhi d.2)

/-- Step for a prime power `k = p^j`. -/
def stepPP (s : State) (k x j : Nat) : Option State :=
  ppLogs s k x j (logRatio (Nat.sub k s.q) (Nat.add k s.q))

/-- Step for a `k` that is not a prime power. -/
def stepNP (s : State) (k x : Nat) : Option State :=
  (fun (t : State) => cond (commonOK s t k x) (some t) none) (nextNP s k x)

/-- Step for an element of `hpList`, with exponent `j` (`0`: not found). -/
def stepHP (s : State) (k x j : Nat) : Option State :=
  cond (Nat.beq j 0) none (stepPP s k x j)

/-- One step, given `k = s.n + 1` and the candidate `x` for `⌊√(k · 10^30)⌋`. -/
def advanceX (s : State) (cb hb k x : Nat) : Option State :=
  cond (Nat.beq hb 1) (stepHP s k x (hpLookup k hpList))
    (cond (Nat.beq cb 0) (stepPP s k x 1) (stepNP s k x))

/-- One step: process `k = s.n + 1`, given the sieve bit `cb` and the `hpList` bit `hb` of `k`. -/
def advance (s : State) (cb hb : Nat) : Option State :=
  advanceX s cb hb (Nat.add s.n 1)
    (newton (Nat.mul (Nat.add s.n 1) RR) 8 (Nat.add s.sq (Nat.add (Nat.div RR (Nat.mul 2 s.sq)) 1)))

/-- Run `fuel` steps; `cm`, `hm` hold the mask bits of the next `k` and the following ones. -/
def runSeg (fuel : Nat) : State → Nat → Nat → Option State :=
  Nat.rec (motive := fun _ => State → Nat → Nat → Option State) (fun s _ _ => some s)
    (fun _ ih s cm hm =>
      (advance s (Nat.mod cm 2) (Nat.mod hm 2)).bind (fun t => ih t (Nat.div cm 2) (Nat.div hm 2)))
    fuel

/-- Running from `a` over the segment `[a.n + 1, b.n]` reaches exactly `b`. -/
def checkSeg (a b : State) : Bool :=
  match runSeg (b.n - a.n) a (compMask (a.n + 1) (b.n - a.n)) (hpMask (a.n + 1) (b.n - a.n)) with
  | some c => c.beq b
  | none => false

/-- The initial state: nothing processed (`n = 1`), `q = 1`, `log 1 = 0`, `⌊√(10^30)⌋ = 10^15`. -/
def init : State := ⟨1, 1, 0, 0, 0, 0, 0, 0, 0, R⟩

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
