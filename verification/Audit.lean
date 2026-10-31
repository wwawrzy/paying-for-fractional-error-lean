import Paper
import Lean.Util.CollectAxioms

-- The original Mader-only adapters retain their exact external-axiom scope.
@[noinline] private def reviewedMaderUse (name ax : Lean.Name) : Bool :=
  ax == ``Paper.External.Mader1968.k7_edge_bound &&
    (name == ``Paper.SevenCliqueMader.edge_bound ||
     name == ``Paper.SevenCliqueMader.weak_bound ||
     name == ``Paper.SevenCliqueMader.minor_density ||
     name == ``Paper.SevenCliqueMader.exact_KT0)

-- The three uniform 3≤t≤9 roots may use exactly the three reviewed density axioms.
@[noinline] private def reviewedCliqueUse (name ax : Lean.Name) : Bool :=
  reviewedMaderUse name ax ||
    ((name == ``Paper.ExcludedCliqueDensity.edge_bound ||
      name == ``Paper.ExcludedCliqueDensity.minor_density ||
      name == ``Paper.ExcludedCliqueDensity.exact_KT0) &&
     (ax == ``Paper.External.Mader1968.k7_edge_bound ||
      ax == ``Paper.External.CliqueDensity.k8_edge_bound ||
      ax == ``Paper.External.CliqueDensity.k9_edge_bound))

-- Exact independently reviewed topology inputs, with user authorization.
@[noinline] private def reviewedSurfaceUse (name ax : Lean.Name) : Bool :=
  (ax == ``Paper.External.SurfaceTopology.exists_cellulation &&
    (name == ``SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq ||
     name == ``SimpleGraph.OrdinarySurface.signedRotation_of_genus ||
     name == ``SimpleGraph.OrdinarySurface.signedRotation_real ||
     name == ``Paper.OrdinarySurfaceAlgorithm.parameters)) ||
  (ax == ``Paper.External.SurfaceTopology.cellulation_euler_eq &&
    name == ``SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq) ||
  (ax == ``Paper.External.SurfaceTopology.rotation_of_embedding &&
    (name == ``SimpleGraph.OrdinarySurface.signedRotation_of_genus ||
     name == ``SimpleGraph.OrdinarySurface.signedRotation_real ||
     name == ``Paper.OrdinarySurfaceAlgorithm.parameters))

-- Ordinary-premise transfers use only the two extraction inputs.
@[noinline] private def reviewedSurfaceTransferUse (name ax : Lean.Name) : Bool :=
  (ax == ``Paper.External.SurfaceTopology.exists_cellulation ||
   ax == ``Paper.External.SurfaceTopology.rotation_of_embedding) &&
  (name == ``Paper.OrdinarySurfaceBounds.minor_bound ||
   name == ``Paper.OrdinarySurfaceBounds.minor_density ||
   name == ``Paper.OrdinarySurfaceBounds.subgraph_girth_density ||
   name == ``Paper.OrdinarySurfaceBounds.subgraph_density ||
   name == ``Paper.OrdinarySurfaceBounds.actual_bounds ||
   name == ``Paper.OrdinarySurfaceGirth.parameters ||
   name == ``Paper.OrdinarySurfaceImprovedGirth.parameters ||
   name == ``Paper.RedBlueOrdinarySurface.additive_parameters ||
   name == ``Paper.RedBlueOrdinarySurface.large_optimum_parameters ||
   name == ``Paper.RedBlueOrdinarySurface.absorbed_parameters ||
   name == ``Paper.OrdinarySurfaceTwoFractional.parameters)

-- Final simultaneous-girth and ordinary-surface LOCAL lower roots.
@[noinline] private def reviewedFinalSurfaceUse (name ax : Lean.Name) : Bool :=
  (name == ``Paper.OrdinarySurfaceGirthBoth.parameters &&
    (ax == ``Paper.External.SurfaceTopology.exists_cellulation ||
     ax == ``Paper.External.SurfaceTopology.rotation_of_embedding)) ||
  ((name == ``Paper.OrdinarySurfaceLocalLower.integral ||
    name == ``Paper.RedBlueOrdinarySurfaceLower.lower) &&
    (ax == ``Paper.External.Planarity.planar_euler_zero ||
     ax == ``Paper.External.SurfaceTopology.exists_cellulation))

open Lean Elab Command in
run_cmd do
  -- Read the manifest-pinned root list at audit time instead of compiling a huge literal.
  let rootText ← liftIO <| IO.FS.readFile "verification/roots.json"
  let rootJson ← match Json.parse rootText with
    | .ok value => pure value
    | .error error => throwError "Invalid root JSON: {error}"
  let values ← match rootJson.getArr? with
    | .ok values => pure values
    | .error error => throwError "Root list must be an array: {error}"
  let mut names : Array Name := #[]
  for value in values do
    let str ← match value.getStr? with
      | .ok str => pure str
      | .error error => throwError "Root name must be a string: {error}"
    let name := str.toName
    if names.contains name then
      throwError "Duplicate audit root: {name}"
    names := names.push name
  let env ← getEnv
  for name in names do
    unless (env.find? name).isSome do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound ||
          reviewedCliqueUse name ax || reviewedSurfaceUse name ax || reviewedSurfaceTransferUse name ax || reviewedFinalSurfaceUse name ax do
        throwError "Unaccepted axiom {ax} in {name}"
    liftIO <| IO.println ("AUDIT " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]).compress)
