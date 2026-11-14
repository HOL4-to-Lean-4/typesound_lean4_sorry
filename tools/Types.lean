import LeanTypeSound
open Lean Elab Command
/- Writes types.tsv: for every theorem of the LeanTypeSound modules, its name and its
    type as an expression string (binder names included). Comparing this file between
    two repositories with the same definitions checks that the statements are equal. -/
run_cmd do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    lines := lines.push s!"{n}\t{(toString ci.type).replace "\n" " "}"
  IO.FS.writeFile "types.tsv" ("\n".intercalate (lines.qsort (· < ·)).toList)
