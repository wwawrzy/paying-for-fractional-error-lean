# Verification and trust

For a complete new check of this snapshot, run `python verify.py` from the
repository root; see [README.md](../README.md). It compiles the library,
supplementary adapter, integration audit and paper index, then checks the
paper result index using new evidence in `.lake/verification/`.
Reports under `verification/` are archived and are not overwritten.

`verification/rebuild.py` checks the entire local module dependency graph and
records each source hash, compiled-object hash, exit status and elapsed time.
A resumed run reuses only matching successful modules whose imports also
remain valid. Changing a module invalidates its dependents. Mathlib is pinned
and its cached compiled dependencies are reused.

After compilation, two checks run against the completed object
cache, with separate logs and the same CPU bound. Each has three threads
and the configured per-process memory limit. They run in parallel when
`--jobs` is at least two. Both must pass:

- `Audit.lean` checks every declaration in `roots.json` transitively. The default
  accepted axioms are `propext`, `Classical.choice` and `Quot.sound`. The additional permissions are the seven declared density/topology/planarity inputs,
  restricted to exact roots in `verification/external-results.json`. Four K7 roots
  use Mader alone; three uniform clique roots use the three density results; eighteen
  ordinary-surface roots use their listed topology inputs.
- `FullAudit.lean` examines all local declarations and rejects `sorryAx`.
  It also reports every explicit axiom, including the seven declared density/topology/planarity inputs
  and unused inherited library statements.

## Complete inventory of axioms actually used by the paper proofs

This list is derived from the transitive kernel audit of all 2,592 selected
proof and algorithm declarations in `verification/roots.json`. It includes
**exactly 10 axiom names: three standard Lean foundations and seven declared
external mathematical inputs**. An imported or declared axiom is not counted
unless a selected declaration actually depends on it. The source and per-root
counts are recorded in `verification/used-axioms.json`; counts refer to selected
declarations, not to the number of paper assertions.

### Standard Lean foundations

| Exact Lean name | Meaning | Selected declarations depending on it |
|---|---|---:|
| `propext` | Logically equivalent propositions are equal (propositional extensionality). | 2576 |
| `Classical.choice` | Every nonempty type admits a chosen element (classical choice). | 2513 |
| `Quot.sound` | Related representatives have equal images in the quotient. | 2568 |

These are Lean's usual logical foundations. The phrase "core-only" means
using no axioms beyond these three; it does not mean having no axioms.

### External mathematical inputs

For graph bounds below, n is the number of vertices and m is the number of
undirected edges, counted once. All graphs are finite and simple.

| Exact Lean name | Exact mathematical scope | Selected declarations depending on it |
|---|---|---:|
| `Paper.External.Mader1968.k7_edge_bound` | For a finite simple K7-minor-free graph with n >= 5 vertices and m edges, m + 15 <= 5*n. | 7 |
| `Paper.External.CliqueDensity.k8_edge_bound` | For every finite simple K8-minor-free graph, m <= 6*n, including all exceptional and small-order cases. | 3 |
| `Paper.External.CliqueDensity.k9_edge_bound` | For every finite simple K9-minor-free graph, m <= 7*n, including all exceptional and small-order cases. | 3 |
| `Paper.External.SurfaceTopology.exists_cellulation` | Every genuine compact connected closed topological surface admits a finite CW cellulation of dimension at most two. | 18 |
| `Paper.External.SurfaceTopology.cellulation_euler_eq` | Any two such cellulations of the same closed surface have the same integer Euler characteristic. | 1 |
| `Paper.External.SurfaceTopology.rotation_of_embedding` | A finite graph genuinely embedded in a closed surface admits a signed rotation with Euler genus at most 2 minus the Euler characteristic of the supplied cellulation. | 15 |
| `Paper.External.Planarity.planar_euler_zero` | A finite simple graph excluding K5 and K3,3 as ordinary minors embeds in an ordinary surface of Euler genus zero (the classical planarity-to-sphere corollary, including representation/CW conversion). | 2 |

The external inputs are assumptions in Lean, not Lean proofs of the published
results. `verification/external-results.json` pins the source and definition
hashes and permits each input only in its explicitly
listed roots. The topology/planarity inputs include the documented conversion
into this project's concrete topological, CW and flag definitions.

The 81 complete named assertions split into **73 core-only and eight
external-dependent assertions**. The separate inherited library assumptions
listed below are excluded from this used-axiom inventory: no selected
paper-facing declaration depends on them.

### Inherited assumptions excluded from the paper-proof inventory

The inherited library contains the following assumptions. Some general library
lemmas use them, but none of the selected paper-facing declarations does:

```text
SimpleGraph.wedge_count_edge_bound
SimpleGraph.wagner_edge_bound
SimpleGraph.IsPlanar.hasPlanarRotationSystem
```

The selected paper-facing declarations, including every part of Theorems A, B, C and D,
do not depend on these three axioms. Their presence means that the whole
library must not be described as containing only core-axiom theorems.

## Check the snapshot

`verify.py` compiles all project sources and audits, then invokes
`check_correspondence.py` and `check_package.py` with the new evidence.
These check the 81 statements, their declaration links, source hashes,
permitted axiom dependencies, import closure and `MANIFEST_SHA256.txt`.
The supplementary planar-rounding adapter is checked separately and is
included in `PaperIndex.lean`.

The current mapping is `verification/statement-map.json`.
The reports in `verification/` are archived; newly generated evidence is
written to `.lake/verification/`. See README.md for the complete command.

Comment-only edits made after the archived compilation are recorded in
`verification/comment-edits.json`. The original build hashes are retained.
For these files, the archive check verifies both the current file hash and
the fingerprint of the unchanged text outside comments. This does not replace
a new Lean compilation; checks of a new build require exact source hashes.
