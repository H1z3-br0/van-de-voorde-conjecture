import BSWCheck
import Lean

open Lean Elab Command

elab "#audit_bsw" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`BSWCheck).isPrefixOf mod do continue
    let axs ← collectAxioms name
    checked := checked + 1
    for a in axs do
      unless allowed.contains a do bad := bad.push (name, a)
  if bad.isEmpty then
    logInfo m!"AUDIT OK: {checked} constants from BSWCheck.* depend only on propext, Classical.choice, Quot.sound"
  else
    throwError m!"AUDIT FAILED: {bad.toList}"

#audit_bsw
