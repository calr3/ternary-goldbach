/-!
# The prime ladder: the kernel check

Rung `i ≥ 1` of the ladder is a prime `c = (iS − t)·2⁴⁵ + 1` with `S = 111616` and `0 ≤ t < 2048`.
Its certificate is Proth's: `3^((c−1)/2) ≡ −1 (mod c)`. Consecutive rungs are less than
`(S + 2047)·2⁴⁵ < 4·10¹⁸ − 4` apart (`TernaryGoldbach/Ladder/Spec.lean`).

The offsets `t` are not stored in the repository: `ladder_hints% i₀` (`LadderHints.lean`) computes
them for a chunk of 4096 rungs during elaboration and packs them into one literal. The kernel then
checks `run 128 i₀ h = true` by evaluation (`decide +kernel`).

`run` checks 128 blocks of 32 rungs. A block is checked modulo the product `M` of its 32
candidates (`prodC`): from `B ≡ 3^(2⁴⁴)`, `A ≡ B^S` and `U ≡ A^i₀ (mod M)` (`sqPow`, `powM`), rung
`i₀ + j` has `U·A^j ≡ 3^(2⁴⁴·iS)`, and the test is `c ∣ 3^(2⁴⁴·iS) + 3^(2⁴⁴·t)` (`chk`), with
`3 ∤ M`. So each rung costs a few operations on 3000-bit numbers instead of a modular
exponentiation of its own. All loops are `Nat.rec` with `Bool.rec` branches and use the GMP-backed
`Nat` operations of the kernel directly. `blk` and `run` are written for arbitrary loop functions
(`blkWith`, `runWith`): in the proofs about them the branch conditions are then stuck terms, and the
kernel does not try to unroll the loops on symbolic arguments.

This file imports nothing, so that the generated data files `Ladder/Data/L*.lean` stay light.
-/

namespace TernaryGoldbach.Ladder

/-- The candidate `(iS − t)·2⁴⁵ + 1`. -/
def cand (iS t : Nat) : Nat := Nat.add (Nat.mul (Nat.sub iS t) 35184372088832) 1

/-- `acc · ∏_{j<n} cand (iS + jS) tⱼ` with `tⱼ = (h >>> 11j) &&& 2047`. -/
noncomputable def prodC (n : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih iS h acc => ih (Nat.add iS 111616) (Nat.shiftRight h 11)
      (Nat.mul acc (cand iS (Nat.land h 2047)))) n

/-- `x^(2^f) mod m`, by repeated squaring. -/
noncomputable def sqPow (m f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => ih (Nat.mod (Nat.mul x x) m)) f

/-- `r · b^e mod m` for `e < 2^f`, by the binary method from the low bit. -/
noncomputable def powM (m f : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ r => r)
    (fun _ ih b e r =>
      Bool.rec (ih (Nat.mod (Nat.mul b b) m) (Nat.shiftRight e 1) r)
        (ih (Nat.mod (Nat.mul b b) m) (Nat.shiftRight e 1) (Nat.mod (Nat.mul r b) m))
        (Nat.beq (Nat.land e 1) 1)) f

/-- The rung test for `n` consecutive rungs from `iS`, with `U ≡ 3^(2⁴⁴·iS)`, `A ≡ 3^(2⁴⁴·S)` and
`B ≡ 3^(2⁴⁴) (mod M)`: `c ∣ U + (B mod c)^t` for each candidate `c = cand iS t`. -/
noncomputable def chk (M B A n : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun _ ih iS U h =>
      let t := Nat.land h 2047
      let c := cand iS t
      Bool.rec false (ih (Nat.add iS 111616) (Nat.mod (Nat.mul U A) M) (Nat.shiftRight h 11))
        (Nat.beq (Nat.mod (Nat.add U (Nat.mod (Nat.pow (Nat.mod B c) t) c)) c) 0)) n

/-- The check of the 32 rungs `[i₀, i₀ + 32)` with offsets packed in `h`, written for loop functions
`P, Q, W, C` (instantiated with `prodC`, `sqPow`, `powM`, `chk` in `blk`). The candidates are prime to
`3` because their product `M` is. -/
noncomputable def blkWith (P : Nat → Nat → Nat → Nat → Nat) (Q : Nat → Nat → Nat → Nat)
    (W : Nat → Nat → Nat → Nat → Nat → Nat) (C : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (i0 h : Nat) : Bool :=
  let iS := i0 * 111616
  let M := P 32 iS h 1
  let B := Q M 44 3
  let A := W M 17 B 111616 1
  let U := W M 28 A i0 1
  Bool.rec (C M B A 32 iS U h) false (Nat.beq (M % 3) 0)

/-- The check of the 32 rungs `[i₀, i₀ + 32)`. -/
noncomputable def blk : Nat → Nat → Bool := blkWith prodC sqPow powM chk

/-- `2³⁵² − 1`: the hints of one block of 32 rungs. -/
def mask352 : Nat := 2 ^ 352 - 1

theorem mask352_eq : mask352 = 2 ^ 352 - 1 := rfl

/-- The check of the `32n` rungs `[i₀, i₀ + 32n)` with the block check `b`. -/
noncomputable def runWith (b : Nat → Nat → Bool) (n : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih i0 h => Bool.rec false (ih (i0 + 32) (h >>> 352)) (b i0 (h &&& mask352))) n

/-- The check of the `32n` rungs `[i₀, i₀ + 32n)`. -/
noncomputable def run : Nat → Nat → Nat → Bool := runWith blk

/-- The chunk of rungs `[i₀, i₀ + 4096)` passes the check for some hint. -/
def ChunkOK (i0 : Nat) : Prop := ∃ h, run 128 i0 h = true

/-- The `n` chunks from `a` pass. -/
def RunsOK (a n : Nat) : Prop := ∀ j, j < n → ChunkOK (a + 4096 * j)

theorem RunsOK.one {a : Nat} (h : ChunkOK a) : RunsOK a 1 := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simpa using h

theorem RunsOK.cons {a b n : Nat} (h : ChunkOK a) (t : RunsOK b n) (hb : b = a + 4096) :
    RunsOK a (n + 1) := by
  intro j hj
  rcases j with _ | j
  · simpa using h
  · have e : b + 4096 * j = a + 4096 * (j + 1) := by rw [hb]; omega
    have := t j (by omega)
    rwa [e] at this

theorem RunsOK.append {a b c m n : Nat} (h₁ : RunsOK a m) (h₂ : RunsOK b n)
    (hb : b = a + 4096 * m) (hc : c = m + n) : RunsOK a c := by
  intro j hj
  by_cases hjm : j < m
  · exact h₁ j hjm
  · have := h₂ (j - m) (by omega)
    rw [hb, Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this
    exact this

end TernaryGoldbach.Ladder
