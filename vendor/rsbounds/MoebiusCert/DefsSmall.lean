/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import MoebiusCert.Defs

/-!
# Kernel-evaluated per-element checkers

Used for `n < 2^18` in `(M)` and for all of `(m)`.
-/

namespace MoebiusCert

noncomputable section

/-- Per-element Mertens check: consumes the fields `μ + 1` of `X` (8-bit layout) for `n, n+1, …`,
updating `M` and checking `10^6 M(n)^2 ≤ 326041 n` for `n ≥ 33`. -/
def smallLoop : Nat → Nat → Nat → Int → Bool × Int :=
  Nat.rec (motive := fun _ => Nat → Nat → Int → Bool × Int) (fun _ _ M => (true, M))
    (fun _ ih X n M =>
      let M' := M + (Int.ofNat (Nat.mod X 256) - 1)
      cond (Nat.blt n 33 || Nat.ble (Nat.mul 1000000 (Nat.mul (Int.natAbs M') (Int.natAbs M'))) (Nat.mul 326041 n))
        (ih (Nat.shiftRight X 8) (Nat.add n 1) M') (false, M'))

/-- Small-mode check of `[L, L + 2^K)`: per-element, given `M(L-1) = M0`; `Mend = M(L + 2^K - 1)`. -/
def smallCheck (L K lam : Nat) (M0 Mend : Int) : Bool :=
  let S := Nat.shiftLeft 1 K
  let r := smallLoop S (segMu1 spData mpData L K (Nat.sub (Nat.mul 5 lam) 69) (Nat.sub (Nat.mul 5 lam) 119)) L M0
  Nat.ble K 24 && Nat.ble 1 L && Nat.ble (Nat.shiftLeft 1 lam) L &&
  Nat.ble (Nat.add L S) (Nat.shiftLeft 1 (Nat.add lam 1)) && Nat.ble lam 29 &&
  Nat.ble (Nat.add L S) 1000014129 && r.1 && Int.beq' Mend r.2

/-- Per-element check for `m(n) = ∑_{k ≤ n} μ(k)/k`. State: `lo ≤ D·m(k-1) ≤ hi` with `D = 10^20`,
and `e` with `k^16 ≤ 2^e` (used once `k ≥ 11815`). For `k ≥ 11815` checks
`max(|lo|,|hi|)·e·6931471808 ≤ 48·D·10^8`, i.e. `|m(k)| · (e/16) · 0.6931471808 ≤ 0.03`. -/
def msLoop : Nat → Nat → Nat → Int → Int → Nat → Bool × (Int × Int × Nat) :=
  Nat.rec (motive := fun _ => Nat → Nat → Int → Int → Nat → Bool × (Int × Int × Nat))
    (fun _ _ lo hi e => (true, (lo, hi, e)))
    (fun _ ih X k lo hi e =>
      let f := Nat.mod X 256
      let D := 100000000000000000000
      let fl := Int.ofNat (Nat.div D k)
      let ce := Int.ofNat (Nat.div (Nat.add D (Nat.sub k 1)) k)
      let lo' := lo + cond (Nat.beq f 2) fl (cond (Nat.beq f 0) (-ce) 0)
      let hi' := hi + cond (Nat.beq f 2) ce (cond (Nat.beq f 0) (-fl) 0)
      let big := Nat.ble 11815 k
      let e' := Nat.add e (cond (big && !Nat.ble (Nat.pow (Nat.add k 1) 16) (Nat.pow 2 e)) 1 0)
      let A := Nat.max (Int.natAbs lo') (Int.natAbs hi')
      cond (!big || (Nat.ble (Nat.pow (Nat.add k 1) 16) (Nat.pow 2 e') &&
          Nat.ble (Nat.mul (Nat.mul A e') 6931471808) (Nat.mul 48 (Nat.mul D 100000000))))
        (ih (Nat.shiftRight X 8) (Nat.add k 1) lo' hi' e') (false, (lo', hi', e')))

/-- `(m)`-check of `[L, L + 2^K)` from state `(lo0, hi0, e0)` at `L` to `(lo1, hi1, e1)`. -/
def msCheck (L K lam : Nat) (lo0 hi0 : Int) (e0 : Nat) (lo1 hi1 : Int) (e1 : Nat) : Bool :=
  let S := Nat.shiftLeft 1 K
  let r := msLoop S (segMu1 spData mpData L K (Nat.sub (Nat.mul 5 lam) 69) (Nat.sub (Nat.mul 5 lam) 119))
    L lo0 hi0 e0
  Nat.ble K 24 && Nat.ble 1 L && Nat.ble (Nat.shiftLeft 1 lam) L &&
  Nat.ble (Nat.add L S) (Nat.shiftLeft 1 (Nat.add lam 1)) && Nat.ble lam 29 &&
  Nat.ble (Nat.add L S) 1000014129 && r.1 && Int.beq' lo1 r.2.1 && Int.beq' hi1 r.2.2.1 && Nat.beq e1 r.2.2.2

end

end MoebiusCert
