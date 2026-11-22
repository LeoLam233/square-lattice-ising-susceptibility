import Lean

/-! Read-only elaboration-time inspection of the actual transitive constant
closure. This diagnostic is not invoked by any mathematical proof. It walks
both types and proof/definition bodies, rather than counting imported files.
The official leanchecker remains the independent kernel replay authority. -/
namespace IsoProof.DependencyAudit
open Lean Elab Command

structure ClosureState where
  seen : NameSet := {}
  missing : NameSet := {}
  axioms : NameSet := {}

partial def visit (env : Environment) (name : Name) : StateM ClosureState Unit := do
  if (← get).seen.contains name then return
  modify fun s => { s with seen := s.seen.insert name }
  match env.checked.get.find? name with
  | none => modify fun s => { s with missing := s.missing.insert name }
  | some info =>
    match info with
    | .axiomInfo _ => modify fun s => { s with axioms := s.axioms.insert name }
    | _ => pure ()
    for dependency in info.getUsedConstantsAsSet.toArray do
      visit env dependency

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient-primitive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

syntax (name := auditProofClosure) "#audit_proof_closure " "[" ident,* "]" : command

elab_rules : command
  | `(#audit_proof_closure [$roots:ident,*]) => do
    let env := (← getEnv).setExporting false
    let names := roots.getElems.map (·.getId)
    for name in names do
      unless (env.checked.get.find? name).isSome do
        throwError "Unknown proof-audit root {name}"
      logInfo m!"AUDIT_ROOT|{name}"
    let state := ((names.forM (visit env)).run ({} : ClosureState)).2
    for name in state.missing.toArray.qsort Name.lt do
      logInfo m!"AUDIT_MISSING|{name}"
    unless state.missing.isEmpty do
      throwError "Actual proof closure contains missing constants"
    let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
    for name in state.axioms.toArray.qsort Name.lt do
      logInfo m!"AUDIT_AXIOM|{name}"
      unless standard.contains name do
        throwError "Nonstandard axiom in actual proof closure: {name}"
    for name in state.seen.toArray.qsort Name.lt do
      if let some info := env.checked.get.find? name then
        let origin := match env.getModuleIdxFor? name with
          | some idx => env.header.moduleNames[idx.toNat]!
          | none => env.mainModule
        if origin.getRoot == `IsoProof || origin.getRoot == `IsingBulk then
          logInfo m!"AUDIT_USED|{name}|{constantKind info}|{origin}"
    logInfo m!"AUDIT_CLOSURE_TOTAL|{state.seen.size}"
    logInfo m!"AUDIT_CLOSURE_ACCEPTED|no missing constants; only standard foundational axioms"

end IsoProof.DependencyAudit
