import Fan

/-! Exhaustive axiom inventory of all project declarations, including private helpers
and generated theorem declarations. Each entry is checked and passed to `#print axioms`.
The permitted axioms are exactly Lean's standard propositional extensionality,
classical choice, and quotient soundness. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "Fan." ||
        n.toString.startsWith "_private.Fan." ||
        n.toString.startsWith "ThagomizerTuran." ||
        n.toString.startsWith "MatroidInverseZ." ||
        n.toString.startsWith "_private.ThagomizerTuran." then some n else none
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  let permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let axioms ← collectAxioms n
    for a in axioms do
      unless permitted.contains a do
        throwError "Unexpected axiom {a} in {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"Checked {names.size} project declarations, including private helpers."
