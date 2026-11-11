import MoebiusCert.PrimeData
/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

/-!
# Kernel-evaluated definitions

Everything here is written for the Lean kernel: recursion is by `Nat.rec`/`List.rec` directly and
arithmetic uses the GMP-accelerated `Nat` primitives (`Nat.add`, `Nat.shiftLeft`, `Nat.land`, …)
without type-class indirection. Soundness is proved in `MoebiusCert.Sieve`.

Layouts: an *8-bit layout* number holds one 8-bit field per integer `L + i`, `i < S`; a *1-bit
layout* number holds one bit per integer. `S = 2^K` throughout.
-/

namespace MoebiusCert

noncomputable section

/-- `repB base d fuel m = ∑_{j<m} base * 2^(d*j)` for `m < 2^fuel`, by binary doubling. -/
def repB (base d : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih m => cond (Nat.beq m 0) 0
      (let h := Nat.div m 2
       let R := ih h
       let R2 := Nat.add R (Nat.shiftLeft R (Nat.mul d h))
       cond (Nat.beq (Nat.mod m 2) 0) R2
         (Nat.add R2 (Nat.shiftLeft base (Nat.mul d (Nat.mul 2 h)))))) fuel

/-- First offset `r ≥ 0` with `q ∣ L + r`. -/
def firstOff (L q : Nat) : Nat := Nat.mod (Nat.sub q (Nat.mod L q)) q

/-- The pattern with weight `c` in field `i` (width `w`) for every `i < S` with `q ∣ L + i`. -/
def patt (w L S q c : Nat) : Nat :=
  let r := firstOff L q
  cond (Nat.blt r S)
    (repB (Nat.shiftLeft c (Nat.mul w r)) (Nat.mul w q) 32
      (Nat.add (Nat.div (Nat.sub (Nat.sub S 1) r) q) 1))
    0

/-- `acc + patt w L S q c`, skipping the addition when the pattern is empty. -/
def addPatt (w L S q c acc : Nat) : Nat :=
  let r := firstOff L q
  cond (Nat.blt r S)
    (Nat.add acc (repB (Nat.shiftLeft c (Nat.mul w r)) (Nat.mul w q) 32
      (Nat.add (Nat.div (Nat.sub (Nat.sub S 1) r) q) 1)))
    acc

/-- `acc ||| patt 1 L S q 1`, skipping when the pattern is empty. -/
def orPatt (L S q acc : Nat) : Nat :=
  let r := firstOff L q
  cond (Nat.blt r S)
    (Nat.lor acc (repB (Nat.shiftLeft 1 r) q 32 (Nat.add (Nat.div (Nat.sub (Nat.sub S 1) r) q) 1)))
    acc

/-- Small-prime pass (8-bit layout): adds weight `a` at the multiples of `p`, for `(p, a) ∈ l`. -/
def vPass (L S : Nat) (l : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun pa _ ih acc => ih (addPatt 8 L S pa.1 pa.2 acc)) l

/-- Medium-prime pass (1-bit layout): saturating 2-bit counter `(c0, c1)` = (count ≥ 1, count ≥ 2)
of the primes of `l` dividing `L + i`. -/
def mPass (L S : Nat) (l : List Nat) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun c0 c1 => (c0, c1))
    (fun p _ ih c0 c1 =>
      let P := patt 1 L S p 1
      ih (Nat.lor c0 P) (Nat.lor c1 (Nat.land c0 P))) l

/-- Square pass (1-bit layout): marks `i` if `p^2 ∣ L + i` for some `p ∈ l`. -/
def fPass (L S : Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => ih (orPatt L S (Nat.mul p p) acc)) l

/-- One Morton level: blocks of `2h` bits at stride `16h` → blocks of `h` bits at stride `8h`. -/
def spStep (S h X : Nat) : Nat :=
  let LO := repB (Nat.sub (Nat.shiftLeft 1 h) 1) (Nat.mul 16 h) 32 (Nat.div S (Nat.mul 2 h))
  Nat.lor (Nat.land X LO) (Nat.shiftLeft (Nat.land X (Nat.shiftLeft LO h)) (Nat.mul 7 h))

/-- Levels `h = 2^(t-1), …, 2^0`. -/
def spreadAux (S : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun t ih X => ih (spStep S (Nat.shiftLeft 1 t) X))

/-- Spread a 1-bit layout number with `2^K` bits into the 8-bit layout. -/
def spread8 (K X : Nat) : Nat := spreadAux (Nat.shiftLeft 1 K) K X

/-- `∑_{i<n} 2^(d*i)`. -/
def ones (d n : Nat) : Nat := repB 1 d 32 n

/-- Decode (8-bit layout): fields `μ + 1` from the small-prime weights `V`, the spread medium
counter planes `C0, C1` and the spread square plane `F`. -/
def decode (S θ0 θ1 V C0 C1 F : Nat) : Nat :=
  let O := ones 8 S
  let NB0 := Nat.land (Nat.shiftRight (Nat.add V (Nat.mul (Nat.sub 128 θ0) O)) 7) O
  let NB1 := Nat.land (Nat.shiftRight (Nat.add V (Nat.mul (Nat.sub 128 θ1) O)) 7) O
  let PAR := Nat.land V O
  let BIG := Nat.land (Nat.xor C1 O)
    (Nat.lor (Nat.land (Nat.xor C0 O) (Nat.xor NB0 O)) (Nat.land C0 (Nat.xor NB1 O)))
  let ODD := Nat.xor (Nat.xor (Nat.xor PAR C0) C1) BIG
  Nat.add F (Nat.shiftLeft (Nat.land (Nat.xor F O) (Nat.xor ODD O)) 1)

/-- The packed `μ + 1` (8-bit layout) of the segment `[L, L + 2^K)`. -/
def segMu1 (sp : List (Nat × Nat)) (mp : List Nat) (L K θ0 θ1 : Nat) : Nat :=
  let S := Nat.shiftLeft 1 K
  let V := vPass L S sp 0
  let C := mPass L S mp 0 0
  let F := fPass L S mp (fPass L S (List.map Prod.fst sp) 0)
  decode S θ0 θ1 V (spread8 K C.1) (spread8 K C.2) (spread8 K F)

/-- Group sums of 4 consecutive 8-bit fields, into 32-bit fields. -/
def group4 (S X : Nat) : Nat :=
  Nat.land (Nat.add (Nat.add X (Nat.shiftRight X 8)) (Nat.add (Nat.shiftRight X 16) (Nat.shiftRight X 24)))
    (Nat.mul 255 (ones 32 (Nat.div S 4)))

/-- Prefix sums of `n` 32-bit fields by `T` doubling steps (Hillis–Steele). -/
def scan (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun s ih X =>
      let Y := ih X
      Nat.mod (Nat.add Y (Nat.shiftLeft Y (Nat.mul 32 (Nat.shiftLeft 1 s)))) (Nat.shiftLeft 1 (Nat.mul 32 n)))

/-- Large-mode check of `[L, L + 2^K)` (`K ≥ 2`): with `n = 2^K/4` groups of four, verifies
`|M0 + P_j - 4(j+1)| ≤ B - 2` for every `j < n`, where `P_j` are the prefix sums of `μ + 1` over the
groups. `K1 = B - 2 + M0`, `K2 = B - 2 - M0` (both `≥ 0`). Returns the last prefix sum. -/
def bandCheck (n T K1 K2 G : Nat) : Bool × Nat :=
  let O := ones 32 n
  let P := scan n T G
  let R := Nat.mul 4 (scan n T O)
  let H := Nat.shiftLeft 1 31
  let E1 := Nat.sub (Nat.add P (Nat.mul (Nat.add H K1) O)) R
  let E2 := Nat.sub (Nat.add R (Nat.mul (Nat.add H K2) O)) P
  let HM := Nat.mul H O
  (Nat.beq (Nat.land (Nat.land E1 E2) HM) HM, Nat.shiftRight P (Nat.mul 32 (Nat.sub n 1)))

/-- The full large-mode check of the segment `[L, L + 2^K)`: side conditions, then the band check
`|M(n)| ≤ B` for all `n` in the segment, given `M(L-1) = M0`; `Mend` must be `M(L + 2^K - 1)`. -/
def largeCheck (L K lam B : Nat) (M0 Mend : Int) : Bool :=
  let S := Nat.shiftLeft 1 K
  let r := bandCheck (Nat.shiftLeft 1 (Nat.sub K 2)) (Nat.sub K 2)
    (Int.toNat (Int.ofNat B - 2 + M0)) (Int.toNat (Int.ofNat B - 2 - M0))
    (group4 S (segMu1 spData mpData L K (Nat.sub (Nat.mul 5 lam) 69) (Nat.sub (Nat.mul 5 lam) 119)))
  Nat.ble 2 K && Nat.ble K 24 && Nat.ble 1 L && Nat.ble (Nat.shiftLeft 1 lam) L &&
  Nat.ble (Nat.add L S) (Nat.shiftLeft 1 (Nat.add lam 1)) && Nat.ble lam 29 &&
  Nat.ble (Nat.add L S) 1000014129 &&
  Nat.ble (Nat.mul 1000000 (Nat.mul B B)) (Nat.mul 326041 L) &&
  Nat.ble (Nat.add (Int.natAbs M0) 2) B &&
  r.1 && Int.beq' Mend (M0 + Int.ofNat r.2 - Int.ofNat S)


end

end MoebiusCert
