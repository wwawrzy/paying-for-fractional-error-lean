# Proof guide

## Theorem B: paying for fractional error

The paper-facing statements are in
[`CurrentTheoremB.lean`](../Paper/Endpoints/Bounds/CurrentTheoremB.lean):

| Declaration | Content |
|---|---|
| `pays_for_fractional_error` | Output-proportional slack absorbs the same relative solver error. |
| `integer_branch` | Rational integer-density case, exact residual budget, universal slack and constant-round preprocessing. |
| `noninteger_branch` | Rational noninteger-density case, exact scaled optimum, universal slack and three one-bit broadcasts. |
| `noninteger_encoded_correct` | Encoded execution agrees with the mathematical rounding, including a local cap. |

Read the supporting modules in this order:

1. `Paper/Endpoints/Rounding/Slack.lean`: the abstract payment principle.
2. `Paper/Endpoints/Rounding/CurrentRounding.lean`: the common selection rule,
   coverage, excess, leftover count and saving.
3. `Paper/Endpoints/Rounding/CurrentBudget.lean` and `CurrentBudgetBridge.lean`:
   the integer-case selected region, candidate costs, residual LP equivalence
   and attained minima.
4. `Paper/Endpoints/Rounding/ComponentMinor.lean`, `CurrentCounting.lean` and
   `CurrentCountBound.lean`: the actual contraction and exact integer-case count.
5. `Paper/Endpoints/Rounding/CurrentNonintegerSlack.lean` and
   `CurrentNonintegerTransformation.lean`: the exact noninteger slack and
   the scaled optimum, with only subgraph density as a hypothesis.
6. `Paper/Communication/CurrentZoneProgram.lean`, `CurrentThresholdProgram.lean`
   and `CurrentNonintegerProgram.lean`: actual broadcast implementations.
7. `Paper/Endpoints/Bounds/CurrentCriticalKT0.lean` and `CurrentTheoremB.lean`:
   the final parameter and model interfaces.

Both cases accept every feasible nonnegative LP vector. The local coordinate
cap preserves feasibility and cannot increase cost. Natural message parameters
are chosen before the graph; the noninteger encoded program is proved equal
to the same capped rounding map used in the universal slack theorem.

## Bounded local fractional solver

[`BoundedLocalFractionalKT0.local_solver`](../Paper/Solver/LocalSearch/BoundedLocalFractionalKT0.lean)
chooses the density ceiling, denominator and copy budget before the graph.
The input at a vertex is its bounded integer cost and demand bit. The actual
encoded program starts with own IDs and numbered ports; its output is a
feasible capped fractional cover of cost at most `(1 + xi)` times the partial
optimum. All coordinates have a common positive denominator. The theorem
includes explicit parameter-bounded rounds and logarithmic message size.

The proof uses a fractional optimum certificate to establish the bounded
search's completeness. That certificate is not an input to the program.
[`BoundedLocalFractional.lean`](../Paper/Solver/LocalSearch/BoundedLocalFractional.lean)
connects the executed search multiplicities to this benchmark and proves that
the local cap preserves feasibility and cost. Only induced-subgraph density
is assumed; no arbitrary-minor density is added.

## Communication on the owner graph

[`CurrentOwnerSimulation.lean`](../Paper/Owners/Construction/CurrentOwnerSimulation.lean)
packages the actual discovery and routing proofs. Owner and residual membership
bits suffice to discover high-degree flags and the complete low-owner neighbor
lists. The public owner graph includes isolated nonowners; its low-owner part
is the graph used in the paper. Ten physical rounds prepare the routing
environment and four physical rounds simulate each virtual round. An initial
own-ID exchange adds one round in the port model. All message bounds are
explicit. Parameter-bounded lists are packed into records, so the schedule
differs from the paper while satisfying its complexity claim.

## Finite-bit local partitions

[`CurrentFiniteBitPartition.lean`](../Paper/Partitions/Local/CurrentFiniteBitPartition.lean)
connects the separator-based expectation bound to an actual finite-bit
distributed program. `parameters` selects positive partition and iteration
parameters before the graph. `sourceEquiv` is a bijection between independent
Boolean tables at the vertices and the finite priorities used in the
expectation proof. Thus the exact finite sum is the uniform fair-bit average.
`cut_eq` identifies the measured cut with the actual output partition.

`output_part` proves that every output is its vertex's complete connected
part, of size at most `k`. `local_output` shows that a local topology-and-bits
frame produces exactly that output. With `r = n * (3*k+1)` communication
rounds, radius `r+1` suffices for the local view, including boundary neighbor
lists. Each vertex supplies exactly `n * 2^((Delta+1)^k) * b` independent bits.
The program and its round bound do not use the number of vertices; the
logarithmic message bound is proved separately from the ID encoding bound.
This construction uses finite priorities and may have different constants
from the paper, while establishing the same existential guarantee.

The equality-instance bridge `cut_source_eq` prevents expensive reduction of
finite-set enumerations: equality tests on the same type are equal by
subsingleton elimination. No distribution, cut bound, or output correctness
assumption is introduced by this implementation detail.

## Other sections

The section entry points are `Paper/Certificates.lean`, `Paper/Initialization.lean`,
`Paper/Owners.lean`, `Paper/Partitions.lean`, `Paper/Averaging.lean`,
`Paper/Solver.lean`, `Paper/Optimality.lean` and `Paper/Endpoints.lean`.
`Paper.lean` imports their complete dependency closure.

Some retained library modules provide more general statements than this paper
needs. They are present because a required proof imports them. Unused source
files outside this module-level dependency closure are excluded.

The [statement map](correspondence.md) links the paper's named results to
their Lean declarations. The general covering solvers are described below.

## Theorem D: both integral approximation schemes

The final declarations are
[`GeneralCoveringRandomIntegralApproximation.randomized_scheme`](../Paper/Solver/LocalSearch/GeneralCoveringRandomIntegralApproximation.lean)
and
[`GeneralCoveringDeterministicApproximation.deterministic_scheme`](../Paper/Solver/LocalSearch/GeneralCoveringDeterministicApproximation.lean).
They choose public parameters before the graph, identifiers and private input.
Both execute the initializer, discover actual optional owners, simulate the
low-owner graph, solve simultaneous integral problems, and repair heavy,
high-owner and boundary classes. The output covers every original required
vertex using admissible candidates from the original arbitrary lists C(r).
Coverage, the initial cover and the output cost bound are derived internally.

Costs use bounded natural values in Fin(B+1), with positivity required only
on admissible vertices. Locality is required only for original required rows.
The approximation compares the output to every admissible integral cover.
This implies comparison to an optimum: the initializer provides a feasible
cover and the admissible covers form a finite nonempty family. Empty required
sets, empty vertex types and zero-cost benchmarks have explicit statements.

The randomized program always produces a cover. Its uniform finite mean cost
is at most (1+epsilon) times every integral benchmark. The sourceEquiv and
source_card declarations identify its source with independent Boolean
coordinates at the physical vertices. The boundary estimate uses the same
public coin assignment and the same actual output partition throughout.
The program has parameter-bounded constant physical rounds. ID capacity and
polynomial-length certificates are used for the message analysis, not as
extra global inputs to its randomized execution.

The deterministic program computes its coloring and partition. It has
parameter-dependent O(1+log-star n) physical rounds and O(log(n+2)) message
bits under the explicit polynomial ID convention. The numeric ID code is
provided, and n=0 and n=1 are included. The partition endpoint is
[`DeterministicPartitionEndpoint.sc_det_partition`](../Paper/Partitions/Local/DeterministicPartitionEndpoint.lean).
Its palette may be larger than the paper's auxiliary O(Delta squared)
palette. The proved constant palette suffices for the stated existential
round and message guarantees; the sharper palette is not claimed here.

Read the proof in this order: GeneralCoveringInitializerRun and its bounds,
GeneralCoveringOwnerSupport/Partners, OwnerDiscovery/OwnerSimulation,
TaskIntegral/TaskParallel/TaskAggregate, the physical partition and boundary
modules, TaskPhysicalRepair, and the two final approximation modules.
The randomized path uses ActiveFiniteBitPartition and
GeneralCoveringRandomBoundaryBound; its finite mean is not a distributed
derandomization of the fractional solver in Theorem A.

The common package check guards 55 D and supporting declarations within
the global core-only audit. The statement map and package check record the
corresponding declarations. The fractional execution and finite averaging
used by Theorem A are described below.

## Theorem A: the actual fractional covering solver

[`GeneralCoveringFractionalEndpoint.parameters`](../Paper/Solver/LocalSearch/GeneralCoveringFractionalEndpoint.lean)
chooses public numeric parameters before the graph, identifier codec and
original private covering input. Its `runtime` executes the initializer once,
then computes the exact finite mean of the fractional solver and its repair.
Each vertex outputs a bounded natural numerator over one positive public
denominator. The `rounds` and `logarithmic_bits` declarations concern that
same execution, not an abstract fractional-solver assumption.

The supported LP uses the union of the original demanded covering lists as
its admissible coordinates. Costs are positive only where admissible, and
rows need to be local and nonempty only for actual demands. `Original`
connects the private candidate and inverse-incidence lists to this LP; it
does not supply a solution, partition, score or globally computed certificate.

Read `GeneralCoveringNormalizedFractional`, the task fractional solver and
repair modules, and `GeneralCoveringInitializedRandomFractionalExpectation`
for feasibility and the expected objective. The owner-frame modules then
compute the same finite mean from locally acquired information.
`GeneralCoveringOwnerFrameAverageMean` and
`GeneralCoveringInitializedFrameAverage.mean` establish this equality for
the executed program. `GeneralCoveringFrameAverageResources` bounds its
rounds and message sizes before the final endpoint assembles the guarantee.

## Theorem C: exact domination coefficients

Parts (i) and (ii) use `MinorDensityKT0.exact_minor_density` and
`SeparateDensities.exact_separate_densities`. Part (iii) is
[`CurrentGirthKT0.parameters`](../Paper/Endpoints/Bounds/CurrentGirthKT0.lean).
For every integer girth at least three it chooses one public configuration
before the vertex type, graph, ports and IDs. The actual encoded KT0 program
returns a dominating set of size at most `(3 + 4/(g-2)) * fractionalNumber`.
Its rounds are fixed by that configuration and messages are logarithmic.
Planarity and the original graph's girth are the only graph hypotheses.

`CurrentPlanarFaceBound` derives facial estimates from abstract planarity.
`CurrentGirthMinor` preserves original girth outside contracted components;
`CurrentGirthCounting` proves the actual incident and overlap counts.
`CurrentGirthOutput` derives the paper's constants at girths four and six,
and `CurrentGirthProgram` connects them to physical execution. Other girths
use `NoncriticalGirth`, with the planar case at girth three handled separately.

## Arbitrary-cover rounding

[`CoveringApplications.parameters`](../Paper/Endpoints/Rounding/CoveringApplications.lean)
uses Theorem A with accuracy `epsilon/(2a+1)` and executes one mixed-threshold
rounding algorithm. Its output is an admissible integral cover of cost at
most `(2a+1+epsilon)` times the original supported fractional optimum.
The same program has factor `(2a+epsilon)` if demanded rows exclude themselves.
No global self-exclusion bit or global test is given to the algorithm.

`CoveringThresholdFlags` broadcasts one bit indicating a self-covering demand.
Each candidate filters received bits through its original inverse-incidence
list. Candidates in any such row use threshold `1/(2a+1)`; all others use
`1/(2a)`. Three subsequent rounds exchange costs, request cheapest candidates
and confirm selections. `MixedCoveringRounding` proves both factors for this
same selection; `CoveringMixedOutput`, `CoveringMixedCost` and
`CoveringMixedFeasible` connect that analysis to the actual encoded output.

`CoveringApplicationInput` preserves the original demands, candidates, costs
and inverse incidences through the fractional solver. Its original LP
coordinates are exactly the numerical inputs of the rounding.
`CoveringApplicationGuarantee` combines feasibility, support and both cost
bounds. `CoveringApplicationResources` proves four extra rounds and an
explicit logarithmic message bound for the composed program.
Only the incidence graph of demanded rows enters the rounding density bound;
non-demand rows are normalized away.

## Optimality and the cycle round lower bound

`Pathwidth` defines finite path decompositions and their minimum width.
`PathwidthBroadcast` gives the actual upper-bound program, while
`ClassLocalLower` derives exact-ID LOCAL obstructions for pathwidth and every
excluded complete-minor class from actual path-power executions.
`SmallCliqueDensity` and `FiveCliqueDensity` prove the sharp density constants
and actual upper endpoints for excluded K3, K4 and K5. The K5 proof constructs
separator fillings, proves elimination in K4-minor-free graphs and reuses
proved dense-core minor constructions. `SixCliqueSharp` proves the actual
K6-free edge bound, minor density four and coefficient-nine KT0 endpoint.
The selected dependency declarations pass the transitive core-axiom audit.
`SevenCliqueTwentySixVertices.edge_bound` proves the sharp K7-free bound
`|E| <= 5|V|-15` for every graph with `5 <= |V| <= 26`, using actual minimal
minors and connected exterior-component arguments. Degree-eight minimal cores
cannot have order 26: their actual residual component boundary would be
at most three, contradicting the minimal-core lower bound four.
Degree-nine affine cores have at least 28.
`SevenCliqueMader` now proves the arbitrary-order K7 sharp and weak bounds,
minor density five and the actual coefficient-eleven KT0 endpoint, conditional
on the independently reviewed `Paper.External.Mader1968.k7_edge_bound` axiom.
The finite-order theorem above remains independent of this literature assumption.
`ExcludedCliqueDensity` now provides one upper endpoint for every 3 <= t <= 9,
with coefficient 2t-3, actual KT0 execution, constant rounds and logarithmic
messages. The K8/K9 cases use independently reviewed Jorgensen/Song-Thomas
weak density axioms, including all exceptions. Together with the core-only
`ClassLocalLower.excluded_clique`, the entire excluded-clique branch is covered.
The ordinary Euler-genus bridge and planar lower-witness transport now use
explicitly reviewed inputs; the entire optimality corollary is verified.

[`CycleRoundsLower.local_algorithm`](../Paper/Optimality/LowerBounds/CycleRoundsLower.lean)
proves the stated log-star lower bound by a finite Ramsey argument for actual
port-local executions. The algorithm may know the order and identifiers are
exactly `1..n`. This avoids assuming a coloring lower bound as an axiom.
The separate bad-packing modules formalize the paper's rearrangement
argument with a maximum over all labelings; that quantifier still needs to
be made explicit in the original prose proof.

## Ordinary topology for the surface bridge

`GraphTheory/Topology/GraphRealization` constructs the actual quotient space of
vertex points and closed edge intervals, with endpoint and reverse-dart gluing.
`Drawing.map_isClosedEmbedding` sends every finite injective-arc drawing into a
Hausdorff target to a closed topological embedding. The canonical barycentric
coordinate drawing proves Hausdorffness of the graph realization and gives an
embedding in `R^V`. `drawing_iff_embeds` proves equivalence of the two ordinary
graph-embedding inputs. Empty graphs and isolated vertices are retained.
These are core-only topology proofs, with no genus/density premise. The ordinary surface bridge is now supplied through three separately authorized,
independently reviewed topology inputs; see the next section. All surface assertions are now certified relative to those inputs, with
matching algorithmic resources and exact source reviews.

## Ordinary surface genus and actual seven approximation

`GraphTheory/Topology/ClosedSurface` defines genuine compact closed surfaces and
finite CW cellulations. `Paper/External/SurfaceTopology` declares the three
exact reviewed topology inputs. `GraphTheory/Surfaces/OrdinarySurface` proves
cellulation invariance and extracts a bounded signed rotation from the actual
topological embedding. `Paper/Communication/OrdinarySurfacePort.parameters`
gives the executed seven-approximation program, uniform constant rounds and
logarithmic messages, without supplying a rotation or embedding to the program.
These four selected roots are reviewed-external, not core-only.
`Paper/RedBlue/SurfacePortLargeOptimum` separately proves the large-optimum
(4+2 epsilon) consequence for the existing actual red-blue port program; this
root remains core-only under its explicit signed-rotation hypothesis.

## Ordinary surface transfers and optimality

OrdinarySurfaceBounds gives exact counting inequalities, arbitrary-girth copy
density, all-minor density and the solver class. OrdinarySurfaceGirth and
OrdinarySurfaceImprovedGirth retain the actual program and all round/bit bounds.
RedBlue/OrdinarySurface transfers additive, large-optimum and absorbed endpoints;
its matching surface and absorbed port resource lemmas are included in coverage.
OrdinarySurfaceTwoFractional proves the ordinary genus<=2 fractional-seven upper
bound. The classical planarity input now supplies ordinary-surface membership
of the LOCAL lower witnesses, completing sc:optimal.

## Final full-paper scope

All81 named assertions are now covered:73 core-only and8 reviewed-external.
The classical planarity input (independently reviewed against Kuratowski1930)
allows OrdinarySurfaceLocalLower.integral to give the missing genuine surface
membership of the LOCAL lower witness. The entire optimality conjunction has
been independently checked, including the supplemental red-blue bounded-genus sharpness and all planar/triangle-free/treewidth/
pathwidth/excluded-clique coefficients and matching resources. GirthBoth gives
both surface-girth bounds for one actual improved protocol; the coefficient
comparison is core-only. Final source correspondence and trust details are in
the statement map and docs/verification.md; external proofs remain assumptions.
