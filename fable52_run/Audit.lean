import LeanTypeSound
open Lean Elab Command
/- Writes audit_thms.tsv (theorem name, axioms used, type) and audit_defs.tsv
   (non-theorem constant, kind, hash of type, hash of value) for the LeanTypeSound modules. -/
run_cmd do
  let env ← getEnv
  let mut thms : Array String := #[]
  let mut defs : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ =>
      let ax ← Lean.collectAxioms n
      let axs := ",".intercalate ((ax.map toString).qsort (· < ·)).toList
      let direct := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstantsAsSet.contains ``sorryAx | none => false
      thms := thms.push s!"{n}\t{mod}\t{axs}\t{direct}\t{(toString ci.type).replace "\n" " "}"
    | _ =>
      let k := match ci with
        | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | _ => "other"
      let vh := match ci.value? (allowOpaque := true) with | some v => toString v.hash | none => "-"
      defs := defs.push s!"{n}\t{mod}\t{k}\t{ci.type.hash}\t{vh}"
  IO.FS.writeFile "audit_thms.tsv" ("\n".intercalate (thms.qsort (· < ·)).toList)
  IO.FS.writeFile "audit_defs.tsv" ("\n".intercalate (defs.qsort (· < ·)).toList)
