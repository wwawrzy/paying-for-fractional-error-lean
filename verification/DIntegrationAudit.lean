import Paper.Solver.LocalSearch.GeneralCoveringRandomIntegralApproximation
import Paper.Solver.LocalSearch.GeneralCoveringDeterministicApproximation
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    `Paper.GeneralCoveringRandomIntegralApproximation.sourceEquiv,
    `Paper.GeneralCoveringRandomIntegralApproximation.source_card,
    `Paper.GeneralCoveringRandomIntegralApproximation.source_pos,
    `Paper.GeneralCoveringRandomIntegralApproximation.original,
    `Paper.GeneralCoveringRandomIntegralApproximation.centers_eq,
    `Paper.GeneralCoveringRandomIntegralApproximation.centers_cost,
    `Paper.GeneralCoveringRandomIntegralApproximation.pointwise_cost,
    `Paper.GeneralCoveringRandomIntegralApproximation.empty_demands,
    `Paper.GeneralCoveringRandomIntegralApproximation.zero_benchmark,
    `Paper.GeneralCoveringRandomIntegralApproximation.empty_physical,
    `Paper.GeneralCoveringRandomIntegralApproximation.uniform_approximation,
    `Paper.GeneralCoveringRandomIntegralApproximation.resources,
    `Paper.GeneralCoveringRandomIntegralApproximation.packet_bound,
    `Paper.GeneralCoveringRandomIntegralApproximation.uniform_scheme,
    `Paper.GeneralCoveringRandomIntegralApproximation.randomized_scheme,
    `Paper.GeneralCoveringDeterministicApproximation.Initialization.factor_pos,
    `Paper.GeneralCoveringDeterministicApproximation.initialization_exists,
    `Paper.GeneralCoveringDeterministicApproximation.public_cutoff,
    `Paper.GeneralCoveringDeterministicApproximation.error_budgets,
    `Paper.GeneralCoveringDeterministicApproximation.count_budget,
    `Paper.GeneralCoveringDeterministicApproximation.additive_to_approximation,
    `Paper.GeneralCoveringDeterministicApproximation.centers_cost,
    `Paper.GeneralCoveringDeterministicApproximation.empty_demands,
    `Paper.GeneralCoveringDeterministicApproximation.zero_benchmark,
    `Paper.GeneralCoveringDeterministicApproximation.empty_physical,
    `Paper.GeneralCoveringDeterministicApproximation.uniform_approximation,
    `Paper.GeneralCoveringDeterministicApproximation.uniform_scheme,
    `Paper.GeneralCoveringDeterministicApproximation.deterministic_scheme,
    `Paper.GeneralCoveringInitializerRun.spec,
    `Paper.GeneralCoveringInitializerRunBounds.selected_card,
    `Paper.GeneralCoveringInitializedPhysical.run_program,
    `Paper.GeneralCoveringInitializedRandomIntegral.run_program,
    `Paper.GeneralCoveringInitializedRandomIntegral.centers_spec,
    `Paper.GeneralCoveringInitializedRandomIntegral.boundary_eq,
    `Paper.GeneralCoveringInputNormalization.admissible_integral_covers,
    `Paper.GeneralCoveringInputNormalization.supported_cost,
    `Paper.GeneralCoveringNormalizedIntegral.optimal,
    `Paper.GeneralCoveringTaskRoles.capacity,
    `Paper.GeneralCoveringTaskParallel.masked_spec,
    `Paper.GeneralCoveringTaskAggregate.aggregate_spec,
    `Paper.GeneralCoveringOwnerSimulation.translate_correct,
    `Paper.GeneralCoveringOwnerRepair.core_correct,
    `Paper.GeneralCoveringOwnerRepair.cost,
    `Paper.GeneralCoveringTaskRandomPhysicalMarks.fields_spec,
    `Paper.GeneralCoveringRandomIntegralPhysical.covers,
    `Paper.GeneralCoveringRandomIntegralPhysical.cost,
    `Paper.GeneralCoveringRandomBoundaryBound.parameters,
    `Paper.GeneralCoveringPhysicalBoundaryBound.initialized_parameters,
    `Paper.ActiveFiniteBitPartition.parameters,
    `Paper.CurrentFiniteBitPartition.parameters,
    `Paper.DeterministicPartitionEndpoint.sc_det_partition,
    `Paper.DeterministicPartitionComputedProgram.color_proper_ball,
    `Paper.DeterministicPartitionComputedProgram.uniform_cut,
    `Paper.DeterministicColorReductionPhysicalProgram.parameters,
    `Paper.DeterministicColorReductionIdentifiers.numeric_parameters]
  let env ← getEnv
  for name in names do
    unless (env.find? name).isSome do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unaccepted axiom {ax} in {name}"
    liftIO <| IO.println ("AUDIT " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]).compress)
