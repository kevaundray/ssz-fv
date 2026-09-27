import Lean

/-! Reject admitted proofs and custom axioms in the native refinement closure. -/

open Lean Elab Command in
elab "audit_native" : command => do
  let environment ← getEnv
  for (name, _) in environment.constants.toList do
    let publicName := (privateToUserName? name).getD name
    if [`SszArm, `SszX86, `SszNative].any (fun ns => ns.isPrefixOf publicName) then
      let axioms ← Lean.collectAxioms name
      for assumption in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
          throwError "{name} depends on forbidden axiom {assumption}"
