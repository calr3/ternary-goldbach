import Lean

/-!
# Hints for the prime ladder

`ladder_hints% i₀` elaborates to a natural number literal that packs, in 11-bit fields, one offset
`tᵢ < 2048` for each `i ∈ [i₀, i₀ + 4096)`: the least `t` such that
`c = (111616·i − t)·2⁴⁵ + 1` satisfies `c ≡ 2 (mod 3)` and `3^((c−1)/2) ≡ −1 (mod c)`.
Candidates with a prime factor in `[5, 2000)` are skipped first.

`ladder_chunks a n` declares the chunk theorems of one data file (`Ladder/Data/L*.lean`).

This is untrusted search code. The kernel checks each rung from the hint
(`TernaryGoldbach.Ladder.run`, `TernaryGoldbach/Ladder/Check.lean`). The library is compiled to
native code (`precompileModules`), so the search runs at native speed during elaboration.
-/

namespace LadderHints

open Lean Elab Term

/-- The primes `5 ≤ p < 2000`, each with `2⁻⁴⁵ mod p`. -/
def smallPrimes : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for p in [5:2000] do
    if (List.range' 2 (p - 2)).all (fun d => p < d * d || p % d != 0) then
      out := out.push (p, Nat.powMod 2 (p - 1 - 45 % (p - 1)) p)
  return out

/-- Proth test with base `3` for `c = (iS − t)·2⁴⁵ + 1`. -/
def passes (iS t : Nat) : Bool :=
  let k := iS - t
  let c := k * 35184372088832 + 1
  c % 3 == 2 && Nat.powMod 3 (k * 17592186044416) c == c - 1

/-- The least valid offset `t < 2048` for rung `i`, if any. -/
def hintFor (i : Nat) : Option Nat := Id.run do
  let iS := i * 111616
  -- `p ∣ c ⟺ t ≡ iS + 2⁻⁴⁵ (mod p)`
  let mut bad := Array.replicate 512 false
  for (p, inv) in smallPrimes do
    let mut t := (iS + inv) % p
    while t < 512 do
      bad := bad.set! t true
      t := t + p
  for t in [0:512] do
    if !bad[t]! && passes iS t then return some t
  for t in [512:2048] do
    if passes iS t then return some t
  return none

/-- The packed hints for `[i₀, i₀ + 4096)`. -/
def chunkHints (i0 : Nat) : Except String Nat := do
  let mut h := 0
  for j in [0:4096] do
    match hintFor (i0 + j) with
    | some t => h := h ||| (t <<< (11 * j))
    | none => throw s!"no ladder prime for rung {i0 + j}"
  return h

/-- `ladder_hints% i₀`: the packed hints for the chunk of rungs `[i₀, i₀ + 4096)`. -/
elab "ladder_hints% " i0:num : term => do
  match chunkHints i0.getNat with
  | .ok h => return mkRawNatLit h
  | .error e => throwError e

open Command in
/-- `ladder_chunks a n` declares `cⱼ : ChunkOK (a + 4096j)` for `j < n`, each proved as
`⟨ladder_hints% (a + 4096j), by decide +kernel⟩`, and `all : RunsOK a n` from them
(`RunsOK.cons`). -/
elab "ladder_chunks " a:num n:num : command => do
  let a := a.getNat
  let n := n.getNat
  -- unhygienic: these constants live in `TernaryGoldbach.Ladder`, which this file does not import
  let chunkOK := mkIdent `TernaryGoldbach.Ladder.ChunkOK
  let runsOK := mkIdent `TernaryGoldbach.Ladder.RunsOK
  let one := mkIdent `TernaryGoldbach.Ladder.RunsOK.one
  let cons := mkIdent `TernaryGoldbach.Ladder.RunsOK.cons
  for j in [0:n] do
    let aj := Syntax.mkNumLit (toString (a + 4096 * j))
    let id := mkIdent (Name.mkSimple s!"c{j}")
    elabCommand (← `(theorem $id : $chunkOK $aj := ⟨ladder_hints% $aj, by decide +kernel⟩))
  let mut t ← `($one $(mkIdent (Name.mkSimple s!"c{n - 1}")))
  for j' in [0:n - 1] do
    let j := n - 2 - j'
    t ← `($cons $(mkIdent (Name.mkSimple s!"c{j}")) $t rfl)
  elabCommand (← `(theorem $(mkIdent `all) : $runsOK $(Syntax.mkNumLit (toString a))
      $(Syntax.mkNumLit (toString n)) := $t))

end LadderHints
