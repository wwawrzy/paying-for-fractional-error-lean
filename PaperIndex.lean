import Paper
import verification.Proposition2Planar

/-!
# Paper-to-Lean index

Each entry links a numbered paper result to its formal declarations.
Use Go to Definition in a Lean editor to open a proof.

Environment: Lean 4.29.0; Mathlib v4.29.0.
Run `python verify.py` for compilation and axiom audits.
Run `python verify.py --recorded-only` to check archived evidence only.

Coverage: 81 named results; 73 use standard Lean axioms only and eight
also depend on the external mathematical inputs listed below.
The index identifies formal statements; mathematical correspondence with
informal statements requires review. See README.md and docs/proof-guide.md.

## Contents (paper result | stable label | printed page)

Theorem A | sc:thmA | 2
Theorem B | sc:thmB | 2
Theorem C | sc:thmC | 3
Corollary 1.1 | sc:optimal | 3
Theorem D | sc:thmD | 4
Theorem E | fv:thmE | 5
Lemma 4.1 | simp:orientation | 15
Proposition 5.1 | sc:principle | 17
Lemma 5.2 | prop:planar-rounding | 19
Theorem 6.1 | simp:initializer | 23
Lemma 6.2 | simp:list-pairs | 24
Lemma 6.3 | simp:bounded-lists | 25
Lemma 6.4 | simp:residual-bound | 26
Lemma 6.5 | simp:heavy | 29
Lemma 6.6 | simp:owner-density | 29
Lemma 6.7 | simp:owner-separator | 30
Lemma 6.8 | simp:simulation | 31
Lemma 6.9 | simp:partition | 32
Lemma 6.10 | simp:certificate | 34
Corollary 6.11 | simp:integrality-gap | 35
Lemma 6.12 | simp:local-solver | 35
Theorem 6.13 | simp:weighted-solver | 37
Lemma 6.14 | simp:tasks | 37
Lemma 7.1 | simp:endpoint:rounding | 44
Lemma 7.2 | simp:endpoint:paying | 45
Lemma 7.3 | simp:endpoint:budget | 46
Lemma 7.4 | simp:endpoint:count | 46
Lemma 8.1 | sc:integral-task | 48
Lemma 8.2 | sc:det-partition | 49
Theorem 9.1 | new:surface-seven | 50
Lemma 9.2 | new:surface-rounding | 52
Lemma A.1 | sc:face | 61
Lemma A.2 | sc:girth:count | 62
Lemma B.1 | new:forced-selection | 65
Proposition B.2 | new:ordinary-lower | 66
Proposition C.1 | sc:rounds-lower | 67
Corollary D.1 | sc:rounding-all | 68
Lemma E.1 | fv:imp:additive | 70
Lemma E.2 | fv:imp:lemma | 71
Corollary E.3 | fv:imp:girth | 73
Lemma E.4 | fv:imp:exact | 74
Lemma E.5 | fv:imp:absorb | 75
Lemma E.6 | fv:imp:euler | 75
Corollary E.7 | fv:imp:surface-girth | 76
Theorem F.1 | fv:total:exact | 77
Lemma F.2 | fv:total:rounding | 78
Lemma F.3 | fv:total:noncrit | 79
Corollary F.4 | fv:total:noncrit-cor | 79
Lemma F.5 | fv:total:budget | 80
Lemma F.6 | fv:total:setup | 81
Lemma F.7 | fv:total:oversupply | 82
Lemma F.8 | fv:total:defects | 82
Lemma F.9 | fv:total:count | 83
Corollary F.10 | fv:total:girth | 84
Corollary F.11 | fv:total:treewidth | 85
Theorem F.12 | fv:total:lower | 86
Proposition F.13 | fv:total:lower-tw | 86
Lemma F.14 | fv:total:forced | 87
Lemma G.1 | fv:hg:budget | 89
Lemma G.2 | fv:hg:saving | 90
Lemma G.3 | fv:hg:residual | 91
Lemma G.4 | fv:hg:free | 92
Lemma G.5 | fv:hg:half | 92
Lemma G.6 | fv:hg:count | 93
Theorem G.7 | fv:hg:three | 94
Corollary G.8 | fv:hg:planar17 | 94
Lemma G.9 | fv:hg:dilute | 95
Corollary G.10 | fv:hg:minor-three | 96
Lemma G.11 | fv:hg:t-budget | 96
Lemma G.12 | fv:hg:t-saving | 97
Lemma G.13 | fv:hg:t-residual | 98
Lemma G.14 | fv:hg:t-free | 98
Lemma G.15 | fv:hg:t-bad | 99
Lemma G.16 | fv:hg:t-count | 100
Theorem G.17 | fv:hg:total-two | 101
Corollary G.18 | fv:hg:minor-total-two | 101
Corollary H.1 | fv:rb:upper | 102
Theorem H.2 | fv:rb:lower | 103
Proposition H.3 | fv:rb:surface | 104
Corollary H.4 | fv:rb:surface-opt | 105
Proposition I.1 | sc:gap | 106
-/

/-!
## Theorem A
Paper label: sc:thmA; printed page: 2.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Solver/LocalSearch/GeneralCoveringFractionalEndpoint.lean
#check Paper.GeneralCoveringFractionalEndpoint.parameters
#check Paper.GeneralCoveringFractionalEndpoint.rounds
#check Paper.GeneralCoveringFractionalEndpoint.logarithmic_bits

/-!
## Theorem B
Paper label: sc:thmB; printed page: 2.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Bounds/CurrentTheoremB.lean
#check Paper.CurrentTheoremB.pays_for_fractional_error
#check Paper.CurrentTheoremB.integer_branch
#check Paper.CurrentTheoremB.noninteger_branch
#check Paper.CurrentTheoremB.noninteger_encoded_correct

/-!
## Theorem C
Paper label: sc:thmC; printed page: 3.
Other labels: sc:thmC:minor, sc:thmC:sub, sc:thmC:girth.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/MinorDensityKT0.lean
#check Paper.MinorDensityKT0.exact_minor_density
#check Paper.MinorDensityKT0.exact_planar
-- Source: Paper/Endpoints/Bounds/SeparateDensities.lean
#check Paper.SeparateDensities.exact_separate_densities
-- Source: Paper/Endpoints/Bounds/CurrentGirthKT0.lean
#check Paper.CurrentGirthKT0.parameters

/-!
## Corollary 1.1
Paper label: sc:optimal; printed page: 3.
Additional axioms in the mapped declarations:
- Paper.External.CliqueDensity.k8_edge_bound
- Paper.External.CliqueDensity.k9_edge_bound
- Paper.External.Mader1968.k7_edge_bound
- Paper.External.Planarity.planar_euler_zero
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Endpoints/Rounding/MinorDensityKT0.lean
#check Paper.MinorDensityKT0.exact_planar
-- Source: Paper/Endpoints/Bounds/CurrentGirthKT0.lean
#check Paper.CurrentGirthKT0.parameters
-- Source: Paper/Optimality/LowerBounds/OrdinaryPlanarLower.lean
#check Paper.OrdinaryPlanarLower.triangle_free
-- Source: Paper/Optimality/LowerBounds/PlanarLocalLower.lean
#check Paper.PlanarLocalLower.integral
-- Source: Paper/Optimality/Treewidth/TreewidthBroadcast.lean
#check Paper.TreewidthBroadcast.exact_KT0
-- Source: Paper/Optimality/Treewidth/PathwidthBroadcast.lean
#check Paper.PathwidthBroadcast.exact_KT0
-- Source: Paper/Optimality/LowerBounds/ClassLocalLower.lean
#check Paper.ClassLocalLower.pathwidth
-- Source: Paper/Optimality/LowerBounds/TreewidthLocalLower.lean
#check Paper.TreewidthLocalLower.exact_lower
-- Source: Paper/Optimality/LowerBounds/ClassLocalLower.lean
#check Paper.ClassLocalLower.excluded_clique
-- Source: Paper/Optimality/Treewidth/ExcludedCliqueDensity.lean
#check Paper.ExcludedCliqueDensity.exact_KT0
-- Source: Paper/Endpoints/Rounding/OrdinarySurfaceTwoFractional.lean
#check Paper.OrdinarySurfaceTwoFractional.parameters
-- Source: Paper/Optimality/LowerBounds/OrdinarySurfaceLocalLower.lean
#check Paper.OrdinarySurfaceLocalLower.integral
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Theorem D
Paper label: sc:thmD; printed page: 4.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Solver/LocalSearch/GeneralCoveringRandomIntegralApproximation.lean
#check Paper.GeneralCoveringRandomIntegralApproximation.randomized_scheme
-- Source: Paper/Solver/LocalSearch/GeneralCoveringDeterministicApproximation.lean
#check Paper.GeneralCoveringDeterministicApproximation.deterministic_scheme

/-!
## Theorem E
Paper label: fv:thmE; printed page: 5.
Other labels: new:surface-main.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Communication/OrdinarySurfacePort.lean
#check Paper.OrdinarySurfaceAlgorithm.parameters
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Lemma 4.1
Paper label: simp:orientation; printed page: 15.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Certificates/Counting/HallOrientation.lean
#check Paper.HallOrientation.exists_orientation
#check Paper.HallOrientation.outEdges_card_le

/-!
## Proposition 5.1
Paper label: sc:principle; printed page: 17.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/Slack.lean
#check Paper.Slack.pays_for_error
#check Paper.Slack.finite_certificate

/-!
## Lemma 5.2
Paper label: prop:planar-rounding; printed page: 19.
Other labels: new:planar-rounding-bounds.
Axioms: standard Lean axioms only.
-/

-- Source: verification/Proposition2Planar.lean
#check Paper.Proposition2PlanarAudit.planar_rounding
#check Paper.Proposition2PlanarAudit.planar_rounding_on_residual

/-!
## Theorem 6.1
Paper label: simp:initializer; printed page: 23.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Initialization/Pruning/SimpleD0.lean
#check Paper.SimpleD0.spec
#check Paper.SimpleD0.weighted_spec
#check Paper.SimpleD0.rounds
#check Paper.SimpleD0.logarithmic_bits

/-!
## Lemma 6.2
Paper label: simp:list-pairs; printed page: 24.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Initialization/Lists/DirectListPairs.lean
#check Paper.DirectListPairs.card_pairs_le

/-!
## Lemma 6.3
Paper label: simp:bounded-lists; printed page: 25.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Initialization/Lists/MarkedLists.lean
#check Paper.MarkedLists.output_card_le
#check Paper.MarkedLists.output_covers
-- Source: Paper/Initialization/Lists/MarkedBroadcast.lean
#check Paper.MarkedBroadcast.correct
#check Paper.MarkedBroadcast.rounds
#check Paper.MarkedBroadcast.maxBits

/-!
## Lemma 6.4
Paper label: simp:residual-bound; printed page: 26.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Initialization/Pruning/SuccessorPaths.lean
#check Paper.SuccessorPaths.residual_bound
#check Paper.SuccessorPaths.exists_successors

/-!
## Lemma 6.5
Paper label: simp:heavy; printed page: 29.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Owners/Construction/HeavyRepair.lean
#check Paper.HeavyRepair.count_div

/-!
## Lemma 6.6
Paper label: simp:owner-density; printed page: 29.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Owners/Construction/SharpOwnerDensity.lean
#check Paper.SharpOwnerDensity.augmented_density
-- Source: Paper/Owners/Construction/OwnerInteraction.lean
#check Paper.OwnerInteraction.graph_le_augmented

/-!
## Lemma 6.7
Paper label: simp:owner-separator; printed page: 30.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Owners/Separators/SharpOwnerSeparator.lean
#check Paper.SharpOwnerSeparator.published_profile

/-!
## Lemma 6.8
Paper label: simp:simulation; printed page: 31.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Owners/Construction/CurrentOwnerSimulation.lean
#check Paper.CurrentOwnerSimulation.discovery
#check Paper.CurrentOwnerSimulation.simulation
#check Paper.CurrentOwnerSimulation.simulation_KT0

/-!
## Lemma 6.9
Paper label: simp:partition; printed page: 32.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Partitions/Local/CurrentFiniteBitPartition.lean
#check Paper.CurrentFiniteBitPartition.parameters
#check Paper.CurrentFiniteBitPartition.cut_eq
#check Paper.CurrentFiniteBitPartition.bits_per_vertex
#check Paper.CurrentFiniteBitPartition.output_part
#check Paper.CurrentFiniteBitPartition.local_output
#check Paper.CurrentFiniteBitPartition.rounds
#check Paper.CurrentFiniteBitPartition.logarithmic_bits

/-!
## Lemma 6.10
Paper label: simp:certificate; printed page: 34.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Certificates/Counting/SubgraphCertificates.lean
#check Paper.SubgraphCertificates.certificate_optimum

/-!
## Corollary 6.11
Paper label: simp:integrality-gap; printed page: 35.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Certificates/Counting/SubgraphCertificates.lean
#check Paper.SubgraphCertificates.integral_optimum

/-!
## Lemma 6.12
Paper label: simp:local-solver; printed page: 35.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Solver/LocalSearch/BoundedLocalFractionalKT0.lean
#check Paper.BoundedLocalFractionalKT0.local_solver

/-!
## Theorem 6.13
Paper label: simp:weighted-solver; printed page: 37.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Solver/LocalSearch/GeneralFractionalBroadcast.lean
#check Paper.GeneralFractionalBroadcast.parameters
#check Paper.GeneralFractionalBroadcast.rounds
#check Paper.GeneralFractionalBroadcast.logarithmic_bits

/-!
## Lemma 6.14
Paper label: simp:tasks; printed page: 37.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Averaging/Tasks/TaskCostSum.lean
#check Paper.TaskCostSum.optimum_bound
-- Source: Paper/Owners/Construction/OwnerTasks.lean
#check Paper.OwnerTasks.service_disjoint

/-!
## Lemma 7.1
Paper label: simp:endpoint:rounding; printed page: 44.
Other labels: simp:endpoint:excess, simp:endpoint:leftover, simp:endpoint:saving.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/CurrentRounding.lean
#check Paper.CurrentRounding.common_rounding

/-!
## Lemma 7.2
Paper label: simp:endpoint:paying; printed page: 45.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/Slack.lean
#check Paper.Slack.bounded_components_pay

/-!
## Lemma 7.3
Paper label: simp:endpoint:budget; printed page: 46.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/CurrentBudgetBridge.lean
#check Paper.CurrentBudgetBridge.current_budget_on_residual_lp
#check Paper.CurrentBudgetBridge.residual_optimum_attained
#check Paper.CurrentBudgetBridge.global_fractional_minimum
-- Source: Paper/Endpoints/Rounding/CurrentBudget.lean
#check Paper.CurrentBudget.cost_eq_open
#check Paper.CurrentBudget.cheap_degree_and_not_demand

/-!
## Lemma 7.4
Paper label: simp:endpoint:count; printed page: 46.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/CurrentCountBound.lean
#check Paper.CurrentCountBound.output_card_le
#check Paper.CurrentCountBound.output_slack

/-!
## Lemma 8.1
Paper label: sc:integral-task; printed page: 48.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Solver/LocalSearch/GeneralCoveringTaskIntegral.lean
#check Paper.GeneralCoveringTaskIntegral.part_spec
-- Source: Paper/Solver/LocalSearch/GeneralCoveringTaskParallel.lean
#check Paper.GeneralCoveringTaskParallel.part_spec
#check Paper.GeneralCoveringTaskParallel.rounds
#check Paper.GeneralCoveringTaskParallel.logarithmic_bits
-- Source: Paper/Solver/LocalSearch/GeneralCoveringTaskAggregate.lean
#check Paper.GeneralCoveringTaskAggregate.solved
#check Paper.GeneralCoveringTaskAggregate.services_disjoint
#check Paper.GeneralCoveringTaskAggregate.sum_optimal

/-!
## Lemma 8.2
Paper label: sc:det-partition; printed page: 49.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Partitions/Local/DeterministicPartitionEndpoint.lean
#check Paper.DeterministicPartitionEndpoint.sc_det_partition

/-!
## Theorem 9.1
Paper label: new:surface-seven; printed page: 50.
Other labels: fv:imp:surface.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Communication/OrdinarySurfacePort.lean
#check Paper.OrdinarySurfaceAlgorithm.parameters
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Lemma 9.2
Paper label: new:surface-rounding; printed page: 52.
Other labels: new:surface-saving, new:surface-count, new:surface-slack.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Endpoints/Rounding/OrdinarySurfaceBounds.lean
#check Paper.OrdinarySurfaceBounds.actual_bounds
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Lemma A.1
Paper label: sc:face; printed page: 61.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/CurrentPlanarFaceBound.lean
#check Paper.CurrentPlanarFaceBound.real_edge_bound
#check Paper.CurrentPlanarFaceBound.induced_density

/-!
## Lemma A.2
Paper label: sc:girth:count; printed page: 62.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/CurrentGirthCounting.lean
#check Paper.CurrentGirthCounting.incident_bound
#check Paper.CurrentGirthCounting.overlap_bound
-- Source: Paper/Endpoints/Girth/CurrentGirthOutput.lean
#check Paper.CurrentGirthOutput.count_four
#check Paper.CurrentGirthOutput.count_six

/-!
## Lemma B.1
Paper label: new:forced-selection; printed page: 65.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Preliminaries/LatticeForcedSelection.lean
#check Paper.LatticeBlock.forced_parameters

/-!
## Proposition B.2
Paper label: new:ordinary-lower; printed page: 66.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Optimality/LowerBounds/OrdinaryPlanarLower.lean
#check Paper.OrdinaryPlanarLower.planar
#check Paper.OrdinaryPlanarLower.triangle_free
-- Source: Paper/Optimality/LowerBounds/TreewidthLocalLower.lean
#check Paper.TreewidthLocalLower.exact_lower

/-!
## Proposition C.1
Paper label: sc:rounds-lower; printed page: 67.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Optimality/LowerBounds/CycleRoundsLower.lean
#check Paper.CycleRoundsLower.local_algorithm

/-!
## Corollary D.1
Paper label: sc:rounding-all; printed page: 68.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/CoveringApplications.lean
#check Paper.CoveringApplications.parameters
-- Source: Paper/Endpoints/Rounding/CoveringApplicationResources.lean
#check Paper.CoveringApplicationResources.rounds
#check Paper.CoveringApplicationResources.logarithmic_bits

/-!
## Lemma E.1
Paper label: fv:imp:additive; printed page: 70.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Communication/AdditiveThresholdProgram.lean
#check Paper.AdditiveThresholdProgram.endpoint

/-!
## Lemma E.2
Paper label: fv:imp:lemma; printed page: 71.
Other labels: fv:imp:mu.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/ImprovedExcessEndpoint.lean
#check Paper.ImprovedExcessEndpoint.rounding
-- Source: Paper/Endpoints/Rounding/ImprovedExcessRounding.lean
#check Paper.ImprovedExcess.output_bound_no_excess
-- Source: Paper/Endpoints/Rounding/ImprovedExcessProgram.lean
#check Paper.ImprovedExcessProgram.correct

/-!
## Corollary E.3
Paper label: fv:imp:girth; printed page: 73.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/ImprovedGirth.lean
#check Paper.ImprovedGirth.parameters
#check Paper.ImprovedGirth.output_eq
#check Paper.ImprovedGirth.rounds
#check Paper.ImprovedGirth.logarithmic_bits

/-!
## Lemma E.4
Paper label: fv:imp:exact; printed page: 74.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Components/SmallComponentExactEndpoint.lean
#check Paper.SmallComponentExactEndpoint.endpoint

/-!
## Lemma E.5
Paper label: fv:imp:absorb; printed page: 75.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Rounding/UniformAbsorption.lean
#check Paper.UniformAbsorption.uniform_absorption

/-!
## Lemma E.6
Paper label: fv:imp:euler; printed page: 75.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Endpoints/Rounding/OrdinarySurfaceBounds.lean
#check Paper.OrdinarySurfaceBounds.subgraph_girth_density
#check Paper.OrdinarySurfaceBounds.subgraph_density
#check Paper.OrdinarySurfaceBounds.minor_bound
#check Paper.OrdinarySurfaceBounds.minor_density
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Corollary E.7
Paper label: fv:imp:surface-girth; printed page: 76.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/Communication/OrdinarySurfaceGirth.lean
#check Paper.OrdinarySurfaceGirth.parameters
-- Source: Paper/Communication/OrdinarySurfaceImprovedGirth.lean
#check Paper.OrdinarySurfaceImprovedGirth.parameters
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq
-- Source: Paper/Communication/OrdinarySurfaceGirthBoth.lean
#check Paper.OrdinarySurfaceGirthBoth.parameters
#check Paper.OrdinarySurfaceGirthBoth.coefficient_le_basic

/-!
## Theorem F.1
Paper label: fv:total:exact; printed page: 77.
Other labels: fv:total:exact:minor, fv:total:exact:sub.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/ExactEndpoint.lean
#check Paper.TotalDomination.ExactEndpoint.minor_parameters
#check Paper.TotalDomination.ExactEndpoint.subgraph_parameters

/-!
## Lemma F.2
Paper label: fv:total:rounding; printed page: 78.
Other labels: fv:total:E, fv:total:size, fv:total:saving.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/Rounding.lean
#check Paper.TotalDomination.output_covers
#check Paper.TotalDomination.output_card_le
#check Paper.TotalDomination.excess_le
#check Paper.TotalDomination.surplus_nonneg
-- Source: Paper/TotalDomination/CostSaving.lean
#check Paper.TotalDomination.rounding_saving

/-!
## Lemma F.3
Paper label: fv:total:noncrit; printed page: 79.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/EncodedRounding.lean
#check Paper.TotalDomination.EncodedRounding.rounding_bound
-- Source: Paper/TotalDomination/RealInputRounding.lean
#check Paper.TotalDomination.RealInputRounding.rounding_bound
#check Paper.TotalDomination.RealInputRounding.resources

/-!
## Corollary F.4
Paper label: fv:total:noncrit-cor; printed page: 79.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/MaximumGain.lean
#check Paper.TotalDomination.Noninteger.admissible_iff_le_muMax
-- Source: Paper/TotalDomination/FractionalSolver.lean
#check Paper.TotalDomination.FractionalSolver.parameters
-- Source: Paper/TotalDomination/GainAccuracy.lean
#check Paper.TotalDomination.Noninteger.gain_accuracy_below_max
#check Paper.TotalDomination.Noninteger.gain_accuracy_near_max
-- Source: Paper/TotalDomination/NonintegerSolver.lean
#check Paper.TotalDomination.NonintegerSolver.parameters
-- Source: Paper/TotalDomination/GainParameters.lean
#check Paper.TotalDomination.Noninteger.parameters_of_gain_rat
-- Source: Paper/TotalDomination/NonintegerEndpoint.lean
#check Paper.TotalDomination.NonintegerEndpoint.parameters_below_max
#check Paper.TotalDomination.NonintegerEndpoint.parameters_near_max
#check Paper.TotalDomination.NonintegerEndpoint.parameters_exact_two_a

/-!
## Lemma F.5
Paper label: fv:total:budget; printed page: 80.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/InitialBudget.lean
#check Paper.TotalDomination.InitialSelection.first_selection_budget
#check Paper.TotalDomination.InitialSelection.exists_residual_optimum

/-!
## Lemma F.6
Paper label: fv:total:setup; printed page: 81.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/IntegerLowCoverage.lean
#check Paper.TotalDomination.IntegerSetup.setup

/-!
## Lemma F.7
Paper label: fv:total:oversupply; printed page: 82.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/IntegerOversupply.lean
#check Paper.TotalDomination.IntegerSetup.oversupply_bound

/-!
## Lemma F.8
Paper label: fv:total:defects; printed page: 82.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/IntegerMinorDefects.lean
#check Paper.TotalDomination.IntegerSetup.minor_defects
-- Source: Paper/TotalDomination/IntegerPlanarDefects.lean
#check Paper.TotalDomination.IntegerSetup.planar_defects

/-!
## Lemma F.9
Paper label: fv:total:count; printed page: 83.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/IntegerSelectedCount.lean
#check Paper.TotalDomination.IntegerSetup.selected_count

/-!
## Corollary F.10
Paper label: fv:total:girth; printed page: 84.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/PlanarGirthEndpoint.lean
#check Paper.TotalDomination.PlanarGirthEndpoint.parameters
-- Source: Paper/TotalDomination/PlanarGainEndpoint.lean
#check Paper.TotalDomination.PlanarGainEndpoint.finite_parameters
#check Paper.TotalDomination.PlanarGainEndpoint.five_parameters
#check Paper.TotalDomination.PlanarGainEndpoint.large_parameters
-- Source: Paper/TotalDomination/HighGirthEndpoint.lean
#check Paper.TotalDomination.HighGirthEndpoint.planar_parameters
-- Source: Paper/TotalDomination/PlanarTotalLower.lean
#check Paper.TotalDomination.PlanarTotalLower.planar
#check Paper.TotalDomination.PlanarTotalLower.triangle_free

/-!
## Corollary F.11
Paper label: fv:total:treewidth; printed page: 85.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/TreewidthEndpoint.lean
#check Paper.TotalDomination.TreewidthEndpoint.parameters
-- Source: Paper/TotalDomination/TreewidthFractionalLower.lean
#check Paper.TotalDomination.TreewidthFractionalLower.lower

/-!
## Theorem F.12
Paper label: fv:total:lower; printed page: 86.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/PlanarTotalLower.lean
#check Paper.TotalDomination.PlanarTotalLower.planar
#check Paper.TotalDomination.PlanarTotalLower.triangle_free

/-!
## Proposition F.13
Paper label: fv:total:lower-tw; printed page: 86.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/TreewidthFractionalLower.lean
#check Paper.TotalDomination.TreewidthFractionalLower.lower
-- Source: Paper/TotalDomination/TreewidthIntegralLower.lean
#check Paper.TotalDomination.TreewidthIntegralLower.lower

/-!
## Lemma F.14
Paper label: fv:total:forced; printed page: 87.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Preliminaries/LatticeTotalForced.lean
#check Paper.LatticeBlock.total_forced_parameters

/-!
## Lemma G.1
Paper label: fv:hg:budget; printed page: 89.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthBudget.lean
#check Paper.HighGirthBudget.endpoint

/-!
## Lemma G.2
Paper label: fv:hg:saving; printed page: 90.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthSaving.lean
#check Paper.HighGirthSaving.saving_endpoint

/-!
## Lemma G.3
Paper label: fv:hg:residual; printed page: 91.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthResidual.lean
#check Paper.HighGirthResidual.residual_endpoint

/-!
## Lemma G.4
Paper label: fv:hg:free; printed page: 92.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthFree.lean
#check Paper.HighGirthFree.free_path_endpoint

/-!
## Lemma G.5
Paper label: fv:hg:half; printed page: 92.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthFewAttachments.lean
#check Paper.HighGirthFewAttachments.few_attachment_endpoint
#check Paper.HighGirthFewAttachments.two_attachment_half_slack
#check Paper.HighGirthFewAttachments.half_slack
#check Paper.HighGirthFewAttachments.count_bound
#check Paper.HighGirthFewAttachments.oneFamily
#check Paper.HighGirthFewAttachments.twoFamily
#check Paper.HighGirthFewAttachments.families

/-!
## Lemma G.6
Paper label: fv:hg:count; printed page: 93.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthSelectedCount.lean
#check Paper.HighGirthSelectedCount.selected_vertex_bound
-- Source: Paper/Endpoints/Girth/HighGirthPathComponentCount.lean
#check Paper.HighGirthPathComponentCount.path_component_count
-- Source: Paper/Endpoints/Girth/HighGirthMiddleMultiplicity.lean
#check Paper.HighGirthMiddleMultiplicity.middle_component_multiplicity
-- Source: Paper/Endpoints/Girth/HighGirthAttachmentBudget.lean
#check Paper.HighGirthAttachmentBudget.component_attachment_budget
-- Source: Paper/Endpoints/Girth/HighGirthFreeClassBounds.lean
#check Paper.HighGirthFreeClassBounds.free_attachment_class_bounds
-- Source: Paper/Endpoints/Girth/HighGirthPathTree.lean
#check Paper.HighGirthPathTree.path_component_is_tree
-- Source: Paper/Endpoints/Girth/HighGirthPathMetric.lean
#check Paper.HighGirthPathMetric.attachment_radius_two
-- Source: Paper/Endpoints/Girth/HighGirthPathIndices.lean
#check Paper.HighGirthPathIndices.ordered_index_distance
-- Source: Paper/Endpoints/Girth/HighGirthAttachmentGap.lean
#check Paper.HighGirthAttachmentGap.consecutive_attachment_gap
-- Source: Paper/Endpoints/Girth/HighGirthAttachmentPositions.lean
#check Paper.HighGirthAttachmentPositions.positions
-- Source: Paper/Endpoints/Girth/HighGirthAttachmentPositionCount.lean
#check Paper.HighGirthAttachmentPositionCount.attachment_positions_count
-- Source: Paper/Endpoints/Girth/HighGirthFiniteGapSpan.lean
#check Paper.HighGirthFiniteGapSpan.span_of_gaps
-- Source: Paper/Endpoints/Girth/HighGirthTrimmedPath.lean
#check Paper.HighGirthTrimmedPath.indices
#check Paper.HighGirthTrimmedPath.vertices
-- Source: Paper/Endpoints/Girth/HighGirthTrimmedSize.lean
#check Paper.HighGirthTrimmedSize.trimmed_path_size_and_attachments
-- Source: Paper/Endpoints/Girth/HighGirthTrimmedSupport.lean
#check Paper.HighGirthTrimmedSupport.trimmed_path_support
-- Source: Paper/Endpoints/Girth/HighGirthTrimmedConnected.lean
#check Paper.HighGirthTrimmedConnected.trimmed_path_connected
-- Source: Paper/Endpoints/Girth/HighGirthTrimmedTwoAttachments.lean
#check Paper.HighGirthTrimmedTwoAttachments.two_attachments_trimmed_size
-- Source: Paper/Endpoints/Girth/HighGirthFreeTrim.lean
#check Paper.HighGirthFreeTrim.exists_trim
-- Source: Paper/Endpoints/Girth/HighGirthRetainedParts.lean
#check Paper.HighGirthRetainedParts.retained_component_parts_exist
-- Source: Paper/Endpoints/Girth/HighGirthRetainedSet.lean
#check Paper.HighGirthRetainedSet.parts
#check Paper.HighGirthRetainedSet.parts_spec
#check Paper.HighGirthRetainedSet.vertices
-- Source: Paper/Endpoints/Girth/HighGirthRetainedPartition.lean
#check Paper.HighGirthRetainedPartition.retained_set_partition
-- Source: Paper/Endpoints/Girth/HighGirthComponentBalls.lean
#check Paper.HighGirthComponentBalls.adjacent_member
#check Paper.HighGirthComponentBalls.ball_stays_in_component
-- Source: Paper/Endpoints/Girth/HighGirthNonfreeRegion.lean
#check Paper.HighGirthNonfreeRegion.freeVertices
#check Paper.HighGirthNonfreeRegion.vertices
#check Paper.HighGirthNonfreeRegion.attachments
-- Source: Paper/Endpoints/Girth/HighGirthNonfreeSize.lean
#check Paper.HighGirthNonfreeSize.nonfree_region_size_bound
-- Source: Paper/Endpoints/Girth/HighGirthSplitAttachmentBudget.lean
#check Paper.HighGirthSplitAttachmentBudget.nonfree_and_free_attachment_budget
-- Source: Paper/Endpoints/Girth/HighGirthRetainedSize.lean
#check Paper.HighGirthRetainedSize.retained_set_size_bound
-- Source: Paper/Endpoints/Girth/HighGirthRetainedPathEdges.lean
#check Paper.HighGirthRetainedPathEdges.retained_path_is_tree_and_edge_count
-- Source: Paper/Endpoints/Girth/HighGirthSpanningCycleEdges.lean
#check Paper.HighGirthSpanningCycleEdges.spanning_cycle_edges
-- Source: Paper/Endpoints/Girth/HighGirthRetainedCycleEdges.lean
#check Paper.HighGirthRetainedCycleEdges.retained_nonpath_edge_count
-- Source: Paper/Endpoints/Girth/HighGirthInducedEdgeSets.lean
#check Paper.HighGirthInducedEdgeSets.edges
#check Paper.HighGirthInducedEdgeSets.edges_card
-- Source: Paper/Endpoints/Girth/HighGirthRetainedEdgeSum.lean
#check Paper.HighGirthRetainedEdgeSum.retained_edge_card_sum
-- Source: Paper/Endpoints/Girth/HighGirthRetainedEdgeCount.lean
#check Paper.HighGirthRetainedEdgeCount.retained_edge_count
-- Source: Paper/Endpoints/Girth/HighGirthRetainedDensity.lean
#check Paper.HighGirthRetainedDensity.retained_density_bound
-- Source: Paper/Endpoints/Girth/HighGirthCountEndpoint.lean
#check Paper.HighGirthCountEndpoint.selected_vertex_count_bounds

/-!
## Theorem G.7
Paper label: fv:hg:three; printed page: 94.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthCountEnvelope.lean
#check Paper.HighGirthCountEnvelope.actual_count_envelope
-- Source: Paper/Endpoints/Girth/HighGirthRoundingSlack.lean
#check Paper.HighGirthRoundingSlack.actual_rounding_slack
-- Source: Paper/Endpoints/Girth/HighGirthSlackParameter.lean
#check Paper.HighGirthSlackParameter.beta
#check Paper.HighGirthSlackParameter.bw
#check Paper.HighGirthSlackParameter.bl
#check Paper.HighGirthSlackParameter.bP
#check Paper.HighGirthSlackParameter.bO
#check Paper.HighGirthSlackParameter.delta
#check Paper.HighGirthSlackParameter.delta_cast
#check Paper.HighGirthSlackParameter.at_seventeen_fifteenths
-- Source: Paper/Endpoints/Girth/HighGirthStaticThree.lean
#check Paper.HighGirthStaticThree.coefficient_three_static
-- Source: Paper/Endpoints/Girth/HighGirthPortObservation.lean
#check Paper.HighGirthPortObservation.program
#check Paper.HighGirthPortObservation.rounds
#check Paper.HighGirthPortObservation.maxBits
#check Paper.HighGirthPortObservation.port_neighbor_count
-- Source: Paper/Endpoints/Girth/HighGirthPortObservationCorrect.lean
#check Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct
-- Source: Paper/Endpoints/Girth/HighGirthSelectionProgram.lean
#check Paper.HighGirthSelectionProgram.rounds
#check Paper.HighGirthSelectionProgram.maxBits
#check Paper.HighGirthSelectionProgram.threshold
#check Paper.HighGirthSelectionProgram.count_zero_iff
#check Paper.HighGirthSelectionProgram.start_correct
-- Source: Paper/Endpoints/Girth/HighGirthSelectionCorrect.lean
#check Paper.HighGirthSelectionCorrect.encoded_three_round_selection_correct
-- Source: Paper/Endpoints/Girth/HighGirthInitializationProgram.lean
#check Paper.HighGirthInitializationProgram.rounds
#check Paper.HighGirthInitializationProgram.maxBits
#check Paper.HighGirthInitializationProgram.start_correct
#check Paper.HighGirthInitializationProgram.count_pos_iff
#check Paper.HighGirthInitializationProgram.closed_count
-- Source: Paper/Endpoints/Girth/HighGirthInitializationCorrect.lean
#check Paper.HighGirthInitializationCorrect.encoded_initialization_correct
-- Source: Paper/Endpoints/Girth/HighGirthFullProgram.lean
#check Paper.HighGirthFullProgram.rounds
#check Paper.HighGirthFullProgram.maxBits
#check Paper.HighGirthFullProgram.thresholdBit_correct
#check Paper.HighGirthFullProgram.selection_state_correct
#check Paper.HighGirthFullProgram.first_threshold_eq
#check Paper.HighGirthFullProgram.output_threshold_eq
-- Source: Paper/Endpoints/Girth/HighGirthThreeEndpoint.lean
#check Paper.HighGirthThreeEndpoint.coefficient_three_encoded

/-!
## Corollary G.8
Paper label: fv:hg:planar17; printed page: 94.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthMaskedInput.lean
#check Paper.HighGirthMaskedInput.weight_pos
#check Paper.HighGirthMaskedInput.weight_at
#check Paper.HighGirthMaskedInput.closed_at_demand
-- Source: Paper/Endpoints/Girth/HighGirthMaskedCap.lean
#check Paper.HighGirthMaskedCap.masked_capped_solver_input
-- Source: Paper/Endpoints/Girth/HighGirthMaskedLPBridge.lean
#check Paper.HighGirthMaskedLPBridge.auxiliary_to_masked
#check Paper.HighGirthMaskedLPBridge.auxiliary_objective
#check Paper.HighGirthMaskedLPBridge.auxiliary_costs_nonempty
#check Paper.HighGirthMaskedLPBridge.auxiliary_costs_bddBelow
-- Source: Paper/Endpoints/Girth/HighGirthMaskedOptimum.lean
#check Paper.HighGirthMaskedOptimum.masked_number_eq_auxiliary
-- Source: Paper/Endpoints/Girth/HighGirthNearOptimalInput.lean
#check Paper.HighGirthNearOptimalInput.transfer
#check Paper.HighGirthNearOptimalInput.masked_planar_density
#check Paper.HighGirthNearOptimalInput.weighted_solver_guarantee
-- Source: Paper/Endpoints/Girth/HighGirthSolverParameters.lean
#check Paper.HighGirthSolverParameters.planar_solver_input_parameters
-- Source: Paper/Endpoints/Girth/HighGirthPhysicalSolver.lean
#check Paper.HighGirthPhysicalSolver.rounds
#check Paper.HighGirthPhysicalSolver.maxBits
#check Paper.HighGirthPhysicalSolver.inputWeight_correct
-- Source: Paper/Endpoints/Girth/HighGirthPhysicalSolverCorrect.lean
#check Paper.HighGirthPhysicalSolverCorrect.kernel_correct
#check Paper.HighGirthPhysicalSolverCorrect.core_correct
#check Paper.HighGirthPhysicalSolverCorrect.physical_solver_encoded_correct
-- Source: Paper/Endpoints/Girth/HighGirthPhysicalRounding.lean
#check Paper.HighGirthPhysicalRounding.rounds
#check Paper.HighGirthPhysicalRounding.maxBits
#check Paper.HighGirthPhysicalRounding.threshold_cap
#check Paper.HighGirthPhysicalRounding.squeeze_correct
-- Source: Paper/Endpoints/Girth/HighGirthFullOutput.lean
#check Paper.HighGirthFullOutput.encoded_output
-- Source: Paper/Endpoints/Girth/HighGirthPhysicalRoundingCorrect.lean
#check Paper.HighGirthPhysicalRoundingCorrect.physical_rounding_encoded_correct
-- Source: Paper/Endpoints/Girth/HighGirthPlanar17Program.lean
#check Paper.HighGirthPlanar17Program.rounds
#check Paper.HighGirthPlanar17Program.logarithmic_bits
#check Paper.HighGirthPlanar17Program.output_eq
#check Paper.HighGirthPlanar17Program.girth_density
#check Paper.HighGirthPlanar17Program.uniform_solver_input
-- Source: Paper/Endpoints/Girth/HighGirthPlanar17Upper.lean
#check Paper.HighGirthPlanar17Upper.planar_girth_seventeen_upper
-- Source: Paper/Endpoints/Girth/HighGirthPathFamily.lean
#check Paper.HighGirthPathFamily.first_power_eq_path
#check Paper.HighGirthPathFamily.acyclic
#check Paper.HighGirthPathFamily.planar
#check Paper.HighGirthPathFamily.girth
-- Source: Paper/Endpoints/Girth/HighGirthPlanar17Lower.lean
#check Paper.HighGirthPlanar17Lower.planar_girth_seventeen_lower

/-!
## Lemma G.9
Paper label: fv:hg:dilute; printed page: 95.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Endpoints/Girth/HighGirthCenters.lean
#check Paper.HighGirthCenters.exists_centers
#check Paper.HighGirthCenters.centers_nonempty
-- Source: Paper/Endpoints/Girth/HighGirthVoronoi.lean
#check Paper.HighGirthVoronoi.exists_best
#check Paper.HighGirthVoronoi.best_unique
#check Paper.HighGirthVoronoi.owner_radius
#check Paper.HighGirthVoronoi.owner_center
#check Paper.HighGirthVoronoi.owner_toward
#check Paper.HighGirthVoronoi.exists_step
#check Paper.HighGirthVoronoi.cluster_walk
#check Paper.HighGirthVoronoi.cluster_connected
#check Paper.HighGirthVoronoi.center_ball_subset
-- Source: Paper/Endpoints/Girth/HighGirthClusterSize.lean
#check Paper.HighGirthClusterSize.ball_card
#check Paper.HighGirthClusterSize.cluster_card
#check Paper.HighGirthClusterSize.cluster_sum
#check Paper.HighGirthClusterSize.center_count
-- Source: Paper/Endpoints/Girth/HighGirthRadiusTree.lean
#check Paper.HighGirthRadiusTree.acyclic
#check Paper.HighGirthRadiusTree.subgraph
#check Paper.HighGirthRadiusTree.root_walk
#check Paper.HighGirthRadiusTree.connected
#check Paper.HighGirthRadiusTree.short_walk
#check Paper.HighGirthRadiusTree.short_cycle_of_extra_edge
#check Paper.HighGirthRadiusTree.acyclic_of_radius_girth
-- Source: Paper/Endpoints/Girth/HighGirthClusterTree.lean
#check Paper.HighGirthClusterTree.induced_radius
#check Paper.HighGirthClusterTree.induced_tree
-- Source: Paper/Endpoints/Girth/HighGirthDisjointPaths.lean
#check Paper.HighGirthDisjointPaths.cross_cycle
-- Source: Paper/Endpoints/Girth/HighGirthClusterCross.lean
#check Paper.HighGirthClusterCross.cluster_path
#check Paper.HighGirthClusterCross.unique_cross_edge
-- Source: Paper/Endpoints/Girth/HighGirthClusterMinor.lean
#check Paper.HighGirthClusterMinor.isMinor
#check Paper.HighGirthClusterMinor.internal_card
#check Paper.HighGirthClusterMinor.partition_card
#check Paper.HighGirthClusterMinor.cross_card_le
-- Source: Paper/Endpoints/Girth/HighGirthDilutionConnected.lean
#check Paper.HighGirthDilutionConnected.internal_sum
#check Paper.HighGirthDilutionConnected.density_connected
-- Source: Paper/Endpoints/Girth/HighGirthDensityPartitions.lean
#check Paper.HighGirthDensityPartitions.induced_card
#check Paper.HighGirthDensityPartitions.edge_split
#check Paper.HighGirthDensityPartitions.vertex_split
-- Source: Paper/Endpoints/Girth/HighGirthDilution.lean
#check Paper.HighGirthDilution.minor_induce
#check Paper.HighGirthDilution.girth_induce
#check Paper.HighGirthDilution.density
#check Paper.HighGirthDilution.minor_of_injective
#check Paper.HighGirthDilution.subgraph_density
#check Paper.HighGirthDilution.all_subgraphs

/-!
## Corollary G.10
Paper label: fv:hg:minor-three; printed page: 96.
Axioms: standard Lean axioms only.
Correspondence note: The class wording now says excludes a fixed minor. Apply the upper bound to the minor-closed superclass of all graphs excluding that minor, then restrict the algorithm to the stated class. The lower bound requires all paths (of order at least two for total domination), as explicitly stated. This is a mathematical correspondence argument, not a new compiled adapter.
-/

-- Source: Paper/Endpoints/Girth/HighGirthMinorParameters.lean
#check Paper.HighGirthMinorParameters.radius_integer_formula
#check Paper.HighGirthMinorParameters.radius_pos
#check Paper.HighGirthMinorParameters.girth_strict
#check Paper.HighGirthMinorParameters.density_range
#check Paper.HighGirthMinorParameters.delta_pos
#check Paper.HighGirthMinorParameters.accuracy_pos
#check Paper.HighGirthMinorParameters.planar_parameters
-- Source: Paper/Endpoints/Girth/HighGirthMinorUpper.lean
#check Paper.HighGirthMinorUpper.uniform_input
#check Paper.HighGirthMinorUpper.diluted_density
#check Paper.HighGirthMinorUpper.upper
-- Source: Paper/Endpoints/Girth/HighGirthProperClass.lean
#check Paper.HighGirthProperClass.rational_density
#check Paper.HighGirthProperClass.excluded_finite_witness
-- Source: Paper/Endpoints/Girth/HighGirthClassEndpoints.lean
#check Paper.HighGirthClassEndpoints.proper_upper
#check Paper.HighGirthClassEndpoints.all_paths_lower
-- Source: Paper/Endpoints/Girth/HighGirthMinorPaths.lean
#check Paper.HighGirthMinorPaths.density
-- Source: Paper/Endpoints/Girth/HighGirthMinorLower.lean
#check Paper.HighGirthMinorLower.minor_density_large_girth_lower

/-!
## Lemma G.11
Paper label: fv:hg:t-budget; printed page: 96.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthBudget.lean
#check Paper.TotalDomination.HighGirthSelection.exterior_budget
#check Paper.TotalDomination.HighGirthSelection.exists_residual_optimum

/-!
## Lemma G.12
Paper label: fv:hg:t-saving; printed page: 97.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthSaving.lean
#check Paper.TotalDomination.HighGirthSetup.rounding_saving

/-!
## Lemma G.13
Paper label: fv:hg:t-residual; printed page: 98.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthResidualGeometry.lean
#check Paper.TotalDomination.HighGirthSetup.low_residual_degree
#check Paper.TotalDomination.HighGirthSetup.core_neighbor_partition
#check Paper.TotalDomination.HighGirthSetup.core_components_path_or_cycle
#check Paper.TotalDomination.HighGirthSetup.outside_neighbor_connector
#check Paper.TotalDomination.HighGirthSetup.branch_attachment
-- Source: Paper/TotalDomination/HighGirthResidualEndpoint.lean
#check Paper.TotalDomination.HighGirthSetup.component_access
-- Source: Paper/TotalDomination/HighGirthResidualSize.lean
#check Paper.TotalDomination.HighGirthSetup.residual_size_edges
#check Paper.TotalDomination.HighGirthSetup.attachment_edge_correspondence

/-!
## Lemma G.14
Paper label: fv:hg:t-free; printed page: 98.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthFreeComponents.lean
#check Paper.TotalDomination.HighGirthSetup.free_external_connectors
#check Paper.TotalDomination.HighGirthSetup.connectors_cost_two
#check Paper.TotalDomination.HighGirthSetup.free_cost_two
#check Paper.TotalDomination.HighGirthSetup.free_all_neighbors_internal
-- Source: Paper/TotalDomination/HighGirthResidualGeometry.lean
#check Paper.TotalDomination.HighGirthSetup.branch_attachment
-- Source: Paper/TotalDomination/HighGirthFreeAccess.lean
#check Paper.TotalDomination.HighGirthSetup.free_short_access
-- Source: Paper/TotalDomination/HighGirthFreeComponents.lean
#check Paper.TotalDomination.HighGirthSetup.free_branch_weight
-- Source: Paper/TotalDomination/HighGirthFreePathEnds.lean
#check Paper.TotalDomination.HighGirthSetup.free_path_end_hits
#check Paper.TotalDomination.HighGirthSetup.nontrivial_path_ends_terms
#check Paper.TotalDomination.HighGirthSetup.positive_charge_vertex

/-!
## Lemma G.15
Paper label: fv:hg:t-bad; printed page: 99.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthBadPaths.lean
#check Paper.TotalDomination.HighGirthSetup.bad_paths_endpoint

/-!
## Lemma G.16
Paper label: fv:hg:t-count; printed page: 100.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthCountEndpoint.lean
#check Paper.TotalDomination.HighGirthSetup.count_endpoint

/-!
## Theorem G.17
Paper label: fv:hg:total-two; printed page: 101.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/TotalDomination/HighGirthVectorRounding.lean
#check Paper.TotalDomination.HighGirthVectorRounding.outcome
-- Source: Paper/TotalDomination/HighGirthSlackArithmetic.lean
#check Paper.TotalDomination.HighGirthSlackArithmetic.rational_accuracy_positive
#check Paper.TotalDomination.HighGirthSlackArithmetic.rational_accuracy_numerical
-- Source: Paper/TotalDomination/HighGirthEndpoint.lean
#check Paper.TotalDomination.HighGirthEndpoint.planar_parameters
-- Source: Paper/TotalDomination/HighGirthOptimality.lean
#check Paper.TotalDomination.HighGirthOptimality.lower

/-!
## Corollary G.18
Paper label: fv:hg:minor-total-two; printed page: 101.
Axioms: standard Lean axioms only.
Correspondence note: The class wording now says excludes a fixed minor. Apply the upper bound to the minor-closed superclass of all graphs excluding that minor, then restrict the algorithm to the stated class. The lower bound requires all paths (of order at least two for total domination), as explicitly stated. This is a mathematical correspondence argument, not a new compiled adapter.
-/

-- Source: Paper/TotalDomination/HighGirthMinorParameters.lean
#check Paper.TotalDomination.HighGirthMinorParameters.radius_integer_formula
#check Paper.TotalDomination.HighGirthMinorParameters.density_range
-- Source: Paper/TotalDomination/HighGirthMinorEndpoint.lean
#check Paper.TotalDomination.HighGirthMinorEndpoint.parameters
-- Source: Paper/TotalDomination/HighGirthOptimality.lean
#check Paper.TotalDomination.HighGirthOptimality.lower
#check Paper.TotalDomination.HighGirthOptimality.class_lower

/-!
## Corollary H.1
Paper label: fv:rb:upper; printed page: 102.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/RedBlue/FractionalEndpoint.lean
#check Paper.RedBlue.fractional_parameters
-- Source: Paper/RedBlue/IntegralEndpoint.lean
#check Paper.RedBlue.integral_parameters
-- Source: Paper/RedBlue/Resources.lean
#check Paper.RedBlue.integral_round_bound
#check Paper.RedBlue.integral_logarithmic_bits
-- Source: Paper/RedBlue/Schemes.lean
#check Paper.RedBlue.randomized_parameters
#check Paper.RedBlue.deterministic_parameters
#check Paper.RedBlue.covers_iff
-- Source: Paper/RedBlue/SolverInput.lean
#check Paper.RedBlue.admissible_subset_blue
-- Source: Paper/RedBlue/Benchmarks.lean
#check Paper.RedBlue.fractional_benchmark
#check Paper.RedBlue.all_integral_benchmarks

/-!
## Theorem H.2
Paper label: fv:rb:lower; printed page: 103.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/RedBlue/OddRedBlueLower.lean
#check Paper.OddRedBlue.lower
-- Source: Paper/RedBlue/OddRedBlueOptima.lean
#check Paper.OddRedBlue.exact_optima
-- Source: Paper/Preliminaries/OddPathDegree.lean
#check Paper.OddPathPower.degree_le_four
-- Source: Paper/Optimality/LowerBounds/BipartiteTwin.lean
#check Paper.BipartiteTwin.run_eq

/-!
## Proposition H.3
Paper label: fv:rb:surface; printed page: 104.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/RedBlue/OrdinarySurface.lean
#check Paper.RedBlueOrdinarySurface.additive_parameters
#check Paper.RedBlueOrdinarySurface.large_optimum_parameters
-- Source: Paper/RedBlue/SurfacePort.lean
#check Paper.RedBlue.surface_port_rounds
#check Paper.RedBlue.surface_port_bits
-- Source: Paper/RedBlue/SurfaceResources.lean
#check Paper.RedBlue.surface_integral_round_bound
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Corollary H.4
Paper label: fv:rb:surface-opt; printed page: 105.
Additional axioms in the mapped declarations:
- Paper.External.SurfaceTopology.cellulation_euler_eq
- Paper.External.SurfaceTopology.exists_cellulation
- Paper.External.SurfaceTopology.rotation_of_embedding
-/

-- Source: Paper/RedBlue/OrdinarySurface.lean
#check Paper.RedBlueOrdinarySurface.absorbed_parameters
-- Source: Paper/RedBlue/AbsorbedPort.lean
#check Paper.RedBlueSurfaceAbsorption.port_rounds
#check Paper.RedBlueSurfaceAbsorption.port_bits
-- Source: GraphTheory/Surfaces/OrdinarySurface.lean
#check SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq

/-!
## Proposition I.1
Paper label: sc:gap; printed page: 106.
Axioms: standard Lean axioms only.
-/

-- Source: Paper/Optimality/Examples/SplitGraphGap.lean
#check Paper.SplitGraphGap.fractionalNumber_le_two
#check Paper.SplitGraphGap.dominationNumber_eq_fifteen
#check Paper.SplitGraphGap.strict_gap_above_seven
