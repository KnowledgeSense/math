import BoseBurton

/-! Exhaustive inventory of every local declaration, including reused proofs,
private helpers and generated theorem declarations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := ["BoseBurton.", "Fan.", "MatroidInverseZ.", "ThagomizerTuran.",
    "_private.BoseBurton.", "_private.Fan.", "_private.ThagomizerTuran."]
  let names := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (fun p => n.toString.startsWith p) then some n else none
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  let permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let axioms ← collectAxioms n
    for a in axioms do
      unless permitted.contains a do
        throwError "Unexpected axiom {a} in {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"Checked {names.size} project declarations, including private helpers."
