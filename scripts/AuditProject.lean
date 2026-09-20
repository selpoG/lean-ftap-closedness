import FTAPTheorem42

/-! Audit every declaration originating in a project module, including private
declarations and declarations added to other namespaces. Inspect types and opaque
values, rejecting project axioms and direct uses of `sorryAx`. Transitive axiom
and proof-chain checks for the main theorem live in AuditMainTheorem. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FTAPTheorem42).isPrefixOf mod do continue
    count := count + 1
    if let .axiomInfo _ := info then
      throwError "Project axiom: {name} (module {mod})"
    for e in #[info.type] ++ (info.value? true).toArray do
      if e.getUsedConstants.contains ``sorryAx then
        throwError "Unproved project declaration: {name} (module {mod})"
  if count == 0 then throwError "No project declarations were inspected"
  logInfo m!"Audited {count} project declarations: no project axioms or sorryAx uses"
