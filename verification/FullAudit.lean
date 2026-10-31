import Paper
import Lean.Util.CollectAxioms

/-! Audit the union of dependencies of every declaration in the source package.
Unlike Audit.lean, this includes general library theorems not used by endpoints.
Legacy library axioms and reviewed external results are reported explicitly,
never counted as Lean proofs of those external statements.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut declaredAxioms : Array Name := #[]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.toString.startsWith "Paper." || modName.toString.startsWith "GraphTheory." then
        names := names.push name
        match info with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | .axiomInfo _ => declaredAxioms := declaredAxioms.push name
        | _ => pure ()
  let action : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  if result.axioms.contains ``sorryAx then
    throwError "A source declaration transitively depends on sorryAx"
  liftIO <| IO.println ("FULL_AUDIT " ++ (Json.mkObj [
    ("declarations", toJson names.size),
    ("theorems_including_generated", toJson theoremCount),
    ("declared_axioms", toJson (declaredAxioms.map Name.toString)),
    ("transitive_axioms", toJson (result.axioms.map Name.toString))]).compress)
