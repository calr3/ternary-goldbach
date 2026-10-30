import TernaryGoldbach
open Lean Elab Command

partial def directSorries (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut out := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let consts := ci.getUsedConstantsAsSet
    if consts.contains ``sorryAx then out := out.push n
    for c in consts do
      if !seen.contains c then todo := todo.push c
  return out

elab "#sorry_deps " id:ident : command => do
  let ns ← liftCoreM <| directSorries id.getId
  logInfo m!"{ns.size}: {ns.qsort (·.toString < ·.toString)}"




-- Usage: lake env lean scripts/sorry_deps.lean, after adding e.g.
-- #sorry_deps TernaryGoldbach.MinorArcs.prop_11_2_3
