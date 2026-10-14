import GenericValueSemigroups

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := ["GenericValueSemigroups"]
  let names := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | none => none
    | some idx =>
      let origin := env.allImportedModuleNames[idx.toNat]!.toString
      if roots.any (fun r => origin == r || origin.startsWith (r ++ ".")) then some n else none
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  let permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let axioms ← collectAxioms n
    for a in axioms do
      unless permitted.contains a do
        throwError "Unexpected axiom {a} in {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"Checked {names.size} project declarations."
