import Formalization
import Lean.Util.CollectAxioms

/-! Transitive kernel axiom audit of all declarations in the project namespace. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`StatisticalRL).isPrefixOf name then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      checked := checked + 1
  if checked == 0 then
    throwError "The axiom audit found no project declarations"
  for axiomName in auditState.axioms do
    unless allowed.contains axiomName do
      throwError "Unapproved axiom {axiomName} in project dependency closure"
  logInfo m!"Axiom audit passed for {checked} project declarations."
