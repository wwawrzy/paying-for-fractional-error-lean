/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Rotation systems and combinatorial planar embeddings

This file develops permutations of darts for simple graphs. A geometric
rotation system describes an embedding on an orientable surface through
local cyclic orders. The structure here records a permutation `σ` and its
preservation of dart sources; it does not separately assert cyclicity at
each vertex. Geometric conclusions require the stated additional hypotheses.

For a graph `G`, Mathlib's `SimpleGraph.Dart` gives oriented edges `(u,v)`.
There are `2|E|` darts. The edge involution `α` reverses each dart, the vertex
permutation is `σ`, and the face permutation is `φ = σ ∘ α`.

The proved results include the face-orbit sum `2|E|`, consequences of the
assumed Euler identity `IsPlanarEmbedding`, and the girth density inequality
`|E|·(g-2) ≤ g·(|V|-2)`. The girth argument explicitly assumes `HasCyclicFaces`;
this file does not prove that every planar graph supplies such a system.

The main definitions are `dartSymmPerm`, `RotationSystem`, `facePerm`, `Face`,
`numFaces`, and `faceDegree`. The main theorems are
`sum_face_partition_eq_two_mul_edges`, `face_degree_ge_girth`,
`edge_bound_from_euler_girth`, `edge_bound_planar`, and
`edge_bound_triangle_free`. The last two retain the embedding and cyclic-face
hypotheses of the general bound.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-! ## Edge involution -/

/-- The edge involution reverses every dart, mapping `(u,v)` to `(v,u)`.
It is a permutation satisfying `α² = id`. -/
def dartSymmPerm (G : SimpleGraph V) : Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv := Dart.symm_symm
  right_inv := Dart.symm_symm

@[simp]
theorem dartSymmPerm_apply {G : SimpleGraph V} (d : G.Dart) :
    dartSymmPerm G d = d.symm := rfl

/-- Squaring the edge involution gives the identity permutation. -/
@[simp]
theorem dartSymmPerm_sq (G : SimpleGraph V) :
    dartSymmPerm G * dartSymmPerm G = 1 := by
  ext d : 1
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, dartSymmPerm, Equiv.coe_fn_mk]
  exact Dart.symm_symm d

/-- The edge reversal map is involutive. -/
theorem dartSymmPerm_involutive (G : SimpleGraph V) :
    Function.Involutive (dartSymmPerm G) :=
  fun d => by simp [dartSymmPerm, Equiv.coe_fn_mk, Dart.symm_symm]

/-- Edge reversal sends the dart's source to its target. -/
theorem dartSymmPerm_source {G : SimpleGraph V} (d : G.Dart) :
    (dartSymmPerm G d).toProd.1 = d.toProd.2 := by
  rw [dartSymmPerm_apply, d.symm_toProd]; rfl

/-- Edge reversal sends the dart's target to its source. -/
theorem dartSymmPerm_target {G : SimpleGraph V} (d : G.Dart) :
    (dartSymmPerm G d).toProd.2 = d.toProd.1 := by
  rw [dartSymmPerm_apply, d.symm_toProd]; rfl

/-- Edge reversal has no fixed points: `α(d) ≠ d` for every dart `d`. -/
theorem dartSymmPerm_ne_self {G : SimpleGraph V} (d : G.Dart) :
    dartSymmPerm G d ≠ d := by
  simp only [dartSymmPerm_apply]
  exact d.symm_ne

/-! ## Rotation-system data -/

/-- A source-preserving permutation of the darts of a simple graph.

In the geometric interpretation, its restriction to darts leaving a vertex
is a cyclic order of the incident edges. This structure stores source
preservation but does not include a separate local cyclicity condition.
Euler and cyclic-face properties are imposed explicitly where needed. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- Vertex permutation on darts. -/
  σ : Equiv.Perm G.Dart
  /-- The vertex permutation preserves each dart's source. -/
  σ_source : ∀ d : G.Dart, (σ d).toProd.1 = d.toProd.1

variable {G : SimpleGraph V}

/-! ## Face permutation -/

/-- The face permutation `φ = σ ∘ α` first reverses a dart and then applies
the vertex permutation. Its orbits are the combinatorial faces. -/
def RotationSystem.facePerm (r : RotationSystem G) : Equiv.Perm G.Dart :=
  r.σ * dartSymmPerm G

/-- Expanding the face permutation: `φ(d) = σ(d.symm)`. -/
@[simp]
theorem RotationSystem.facePerm_apply (r : RotationSystem G) (d : G.Dart) :
    r.facePerm d = r.σ d.symm := by
  simp [RotationSystem.facePerm, Equiv.Perm.mul_apply]

/-! ## Faces -/

/-- Two darts belong to the same face if they lie in the same orbit of `φ`,
equivalently if an integer power of `φ` sends one to the other. -/
def RotationSystem.SameFace (r : RotationSystem G) (d₁ d₂ : G.Dart) : Prop :=
  r.facePerm.SameCycle d₁ d₂

/-- Belonging to the same face is an equivalence relation. -/
theorem RotationSystem.sameFace_equivalence (r : RotationSystem G) :
    Equivalence r.SameFace :=
  Equiv.Perm.SameCycle.equivalence r.facePerm

/-- Faces are the quotient of darts by the orbit relation of `φ`.
A face orbit supplies a closed boundary walk. -/
def RotationSystem.Face (r : RotationSystem G) :=
  Quotient (Equiv.Perm.SameCycle.setoid r.facePerm)

/-- The canonical map sending a dart to its face. -/
def RotationSystem.faceOf (r : RotationSystem G) (d : G.Dart) : r.Face :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid r.facePerm) d

/-! ## Face count and face degree -/

/-- The face count is the number of orbits of `φ`: the number of nontrivial
cycles plus the number of fixed points.

Thus `numFaces = φ.cycleType.card + (|Dart| - |supp(φ)|)`. -/
noncomputable def RotationSystem.numFaces [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) : ℕ :=
  r.facePerm.cycleType.card + (Fintype.card G.Dart - r.facePerm.support.card)

/-- The degree of the face containing `d` is its orbit size under `φ`.
A fixed point has degree one; otherwise the degree is the cycle's support size.
`Equiv.Perm.cycleOf.support` is empty at fixed points, so those must be handled
separately. -/
noncomputable def RotationSystem.faceDegree [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) : ℕ :=
  if d ∈ r.facePerm.support then (r.facePerm.cycleOf d).support.card else 1

/-- A face degree is positive, since each orbit is nonempty. -/
theorem RotationSystem.faceDegree_pos [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) :
    0 < r.faceDegree d := by
  unfold faceDegree
  split
  · next hd =>
    exact Finset.card_pos.mpr ⟨d, Equiv.Perm.mem_support_cycleOf_iff.mpr
      ⟨Equiv.Perm.SameCycle.refl _ d, hd⟩⟩
  · exact Nat.one_pos

/-! ## The face-degree sum is twice the edge count -/

/-- Partitioning darts into face orbits gives a total size of `|Dart|`. -/
theorem RotationSystem.partition_parts_sum [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) :
    r.facePerm.partition.parts.sum = Fintype.card G.Dart :=
  r.facePerm.partition.parts_sum

/-- **The face-degree sum is `2|E|`.** The orbits of `φ` partition the darts,
so their sizes sum to `|Dart| = 2|E|`. This follows from
`Nat.Partition.parts_sum` and `dart_card_eq_twice_card_edges`. -/
theorem RotationSystem.sum_face_partition_eq_two_mul_edges
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V]
    (r : RotationSystem G) :
    r.facePerm.partition.parts.sum = 2 * G.edgeFinset.card := by
  rw [r.facePerm.partition.parts_sum]
  exact G.dart_card_eq_twice_card_edges

/-- The number of parts in the face partition equals `numFaces`. -/
theorem RotationSystem.numFaces_eq_partition_card
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) :
    r.numFaces = r.facePerm.partition.parts.card := by
  unfold numFaces
  simp only [Equiv.Perm.partition]
  rw [Multiset.card_add, Multiset.card_replicate]

/-! ## Genus expression -/

/-- The natural-number genus expression suggested by Euler's formula:
`g = (2 - V + E - F) / 2`.

Subtraction and division here are in the natural numbers. Geometric
interpretation requires appropriate embedding hypotheses; their validity
is not part of this definition. -/
noncomputable def RotationSystem.genus
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G) : ℕ :=
  (2 + G.edgeFinset.card - Fintype.card V - r.numFaces) / 2

/-- The planar-embedding predicate is the Euler identity
`|V| + |F| = |E| + 2`. -/
def RotationSystem.IsPlanarEmbedding
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G) : Prop :=
  Fintype.card V + r.numFaces = G.edgeFinset.card + 2

/-! ## Consequences of the genus-zero Euler identity -/

/-- Assuming `IsPlanarEmbedding`, the genus expression is zero.
The Euler identity is a hypothesis here, rather than a topological theorem
proved from a graph embedding. -/
theorem RotationSystem.genus_zero_of_planar
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G) (hplanar : r.IsPlanarEmbedding) :
    r.genus = 0 := by
  unfold genus IsPlanarEmbedding at *
  omega

/-- Under the planar Euler identity, the face count is `|E| + 2 - |V|`.
The cardinality hypothesis explicitly ensures `|V| ≤ |E| + 2`. -/
theorem RotationSystem.numFaces_eq_of_planar
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G) (hplanar : r.IsPlanarEmbedding)
    (hVE : Fintype.card V ≤ G.edgeFinset.card + 2) :
    r.numFaces = G.edgeFinset.card + 2 - Fintype.card V := by
  unfold IsPlanarEmbedding at hplanar
  omega

/-! ## The face permutation has no fixed points -/

/-- `φ(d) ≠ d`: source preservation by `σ` and reversal by `α` would otherwise
identify the two endpoints of a dart, contradicting simplicity. -/
theorem RotationSystem.facePerm_ne_self (r : RotationSystem G) (d : G.Dart) :
    r.facePerm d ≠ d := by
  rw [r.facePerm_apply]
  intro h
  have hsrc := r.σ_source d.symm
  rw [h] at hsrc
  rw [d.symm_toProd] at hsrc
  simp at hsrc

/-! ## Face-degree bounds from girth -/

/-- `MinGirth G g` states that every cycle in `G` has length at least `g`.
It uses `SimpleGraph.Walk.IsCycle`. -/
def MinGirth (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.IsCycle → g ≤ p.length

/-! ### A walk following a face orbit -/

/-- Starting at dart `d`, follow `n` iterates of the face permutation.
Each step uses the current dart's adjacency; consecutive endpoints agree
by source preservation of the vertex permutation. -/
private noncomputable def RotationSystem.orbitWalk
    (r : RotationSystem G) (d : G.Dart) :
    (n : ℕ) → G.Walk d.toProd.1 ((r.facePerm ^ n) d).toProd.1
  | 0 => by
    have h : ((r.facePerm ^ 0) d).toProd.1 = d.toProd.1 := by simp
    exact h ▸ Walk.nil
  | n + 1 => by
    have hpow : (r.facePerm ^ (n + 1)) d = (r.facePerm ^ n) (r.facePerm d) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    have hsrc : (r.facePerm d).toProd.1 = d.toProd.2 := by
      rw [RotationSystem.facePerm_apply]; rw [r.σ_source]; rw [Dart.symm_toProd]; rfl
    let tail := r.orbitWalk (r.facePerm d) n
    let step : G.Walk d.toProd.2 ((r.facePerm ^ n) (r.facePerm d)).toProd.1 :=
      tail.copy hsrc rfl
    let p : G.Walk d.toProd.1 ((r.facePerm ^ n) (r.facePerm d)).toProd.1 :=
      Walk.cons d.adj step
    exact p.copy rfl (congrArg (fun e : G.Dart => e.toProd.1) hpow.symm)

/-- A complete cycle of the face permutation returns to its starting dart. -/
private theorem RotationSystem.orbit_periodic
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) :
    (r.facePerm ^ (r.facePerm.cycleOf d).support.card) d = d := by
  have h := r.facePerm.pow_mod_card_support_cycleOf_self_apply
      (r.facePerm.cycleOf d).support.card d
  simp at h; exact h.symm

/-! ### Public exact face-boundary API -/

/-- The implementation walk following `n` successive darts of one face orbit.
This is the public wrapper around the recursive construction used internally
by the girth argument. -/
noncomputable def RotationSystem.faceOrbitWalkN
    (r : RotationSystem G) (d : G.Dart) :
    (n : ℕ) → G.Walk d.toProd.1 ((r.facePerm ^ n) d).toProd.1 :=
  r.orbitWalk d

/-- The darts of the implementation walk are exactly the first `n` iterates
of the face permutation. -/
theorem RotationSystem.faceOrbitWalkN_darts
    (r : RotationSystem G) (d : G.Dart) (n : ℕ) :
    (r.faceOrbitWalkN d n).darts = List.iterate r.facePerm d n := by
  induction n generalizing d with
  | zero =>
      change (r.orbitWalk d 0).darts = []
      rw [Walk.darts_eq_nil]
      exact Walk.Nil.nil
  | succ n ih =>
      change (r.orbitWalk d (n + 1)).darts =
        List.iterate r.facePerm d (n + 1)
      simp only [RotationSystem.orbitWalk, Walk.darts_copy, Walk.darts_cons,
        List.iterate, List.cons.injEq]
      constructor
      · trivial
      · simpa [RotationSystem.facePerm_apply] using ih (r.facePerm d)

/-- One complete face orbit returns to its based dart. -/
theorem RotationSystem.faceOrbit_periodic
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) :
    (r.facePerm ^ (r.facePerm.cycleOf d).support.card) d = d :=
  r.orbit_periodic d

/-- The full cyclic list of darts belonging to the face based at `d`. -/
noncomputable def RotationSystem.faceDarts
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) : List G.Dart :=
  r.facePerm.toList d

/-- The exact closed boundary walk of the face orbit based at `d`. -/
noncomputable def RotationSystem.faceBoundaryWalk
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) : G.Walk d.fst d.fst :=
  (r.faceOrbitWalkN d (r.facePerm.cycleOf d).support.card).copy rfl
    (congrArg (fun e : G.Dart => e.fst) (r.faceOrbit_periodic d))

/-- The closed face boundary retains exactly the orbit list, including both
orientations of a bridge and repeated vertex occurrences. -/
theorem RotationSystem.faceBoundaryWalk_darts
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) :
    (r.faceBoundaryWalk d).darts = r.faceDarts d := by
  rw [RotationSystem.faceBoundaryWalk, Walk.darts_copy,
    r.faceOrbitWalkN_darts]
  rfl

/-- The length of the exact boundary walk is the degree of its face orbit. -/
theorem RotationSystem.faceBoundaryWalk_length
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) (d : G.Dart) :
    (r.faceBoundaryWalk d).length = r.faceDegree d := by
  rw [← Walk.length_darts, r.faceBoundaryWalk_darts]
  unfold RotationSystem.faceDarts RotationSystem.faceDegree
  rw [if_pos (Equiv.Perm.mem_support.mpr (r.facePerm_ne_self d))]
  exact Equiv.Perm.length_toList r.facePerm d

/-- A rotation system has cyclic faces if each face orbit in the support
contains a graph cycle no longer than that orbit's face degree.
Diestel Proposition 4.2.5 supplies this property for 2-connected plane graphs;
its availability is an explicit hypothesis in the results below. -/
def RotationSystem.HasCyclicFaces [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G) : Prop :=
  ∀ d : G.Dart, d ∈ r.facePerm.support →
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ r.faceDegree d

/-- Every face has degree at least `g` under the explicit cyclic-face
hypothesis: it contains a cycle of length at most its degree, and `MinGirth`
bounds that cycle's length below by `g`. -/
theorem RotationSystem.face_degree_ge_girth
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : RotationSystem G)
    (g : ℕ) (hg : MinGirth G g) (hg3 : 3 ≤ g)
    (hfaces : r.HasCyclicFaces)
    (d : G.Dart) (hd : d ∈ r.facePerm.support) :
    g ≤ r.faceDegree d := by
  obtain ⟨v, c, hcycle, hle⟩ := hfaces d hd
  calc g ≤ c.length := hg v c hcycle
    _ ≤ r.faceDegree d := hle

/-! ## Density from Euler's formula and girth -/

/-- **Girth density inequality.** Under the planar Euler identity, girth
at least `g ≥ 3`, and the cyclic-face hypothesis:

    |E| * (g - 2) ≤ g * (|V| - 2)

The face-degree sum gives `g * |F| ≤ 2|E|`; substitute Euler's identity
`|F| = |E| - |V| + 2` and rearrange. -/
theorem RotationSystem.edge_bound_from_euler_girth
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G)
    (hplanar : r.IsPlanarEmbedding)
    (g : ℕ) (hg : MinGirth G g) (hg3 : 3 ≤ g)
    (hfaces : r.HasCyclicFaces)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card * (g - 2) ≤ g * (Fintype.card V - 2) := by
  -- φ has no fixed points → support = univ
  have hsup : r.facePerm.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun d =>
      Equiv.Perm.mem_support.mpr (r.facePerm_ne_self d)
  -- partition.parts = cycleType (no fixed-point 1's)
  have hparts : r.facePerm.partition.parts = r.facePerm.cycleType := by
    rw [Equiv.Perm.parts_partition, hsup, Finset.card_univ, Nat.sub_self,
        Multiset.replicate_zero, Multiset.add_zero]
  -- Every cycle of φ has length ≥ g (from face_degree_ge_girth)
  have hcyc : ∀ n ∈ r.facePerm.cycleType, g ≤ n := by
    intro n hn
    rw [Equiv.Perm.cycleType_def] at hn
    simp only [Multiset.mem_map, Function.comp_apply] at hn
    obtain ⟨c, hc, rfl⟩ := hn
    have hcf : c ∈ r.facePerm.cycleFactorsFinset := by rwa [Finset.mem_val] at hc
    obtain ⟨d, hd⟩ :=
      ((r.facePerm.mem_cycleFactorsFinset_iff.mp hcf).1).nonempty_support
    have hds : d ∈ r.facePerm.support := hsup ▸ Finset.mem_univ d
    have hfd := r.face_degree_ge_girth g hg hg3 hfaces d hds
    unfold faceDegree at hfd
    rw [if_pos hds, ← Equiv.Perm.cycle_is_cycleOf hd hcf] at hfd
    exact hfd
  -- g * numFaces ≤ 2 * |E|
  have hgF : g * r.numFaces ≤ 2 * G.edgeFinset.card := by
    have hge : ∀ x ∈ r.facePerm.partition.parts, g ≤ x :=
      fun x hx => hcyc x (hparts ▸ hx)
    have hle := Multiset.card_nsmul_le_sum hge
    rw [r.partition_parts_sum] at hle
    simp only [Fintype.card_eq_nat_card] at hle
    have hnat : Nat.card G.Dart = 2 * G.edgeFinset.card := by
      have h := G.dart_card_eq_twice_card_edges
      simp only [Fintype.card_eq_nat_card] at h; exact h
    rw [hnat] at hle
    rw [r.numFaces_eq_partition_card, mul_comm]
    simpa [nsmul_eq_mul] using hle
  -- Arithmetic: Euler + hgF → density bound
  unfold IsPlanarEmbedding at hplanar
  zify [show 2 ≤ g by omega, show 2 ≤ Fintype.card V by omega] at *
  nlinarith

/-- Specializing `edge_bound_from_euler_girth` to `g = 3` gives
`|E| ≤ 3|V| - 6`, with the stated embedding and cyclic-face hypotheses. -/
theorem RotationSystem.edge_bound_planar
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G)
    (hplanar : r.IsPlanarEmbedding)
    (hg : MinGirth G 3) (hfaces : r.HasCyclicFaces)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  have h := r.edge_bound_from_euler_girth hplanar 3 hg (le_refl 3) hfaces hcard
  omega

/-- Specializing `edge_bound_from_euler_girth` to `g = 4` gives the
triangle-free bound `|E| ≤ 2|V| - 4`, with the stated embedding hypotheses. -/
theorem RotationSystem.edge_bound_triangle_free
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Fintype G.Dart]
    (r : RotationSystem G)
    (hplanar : r.IsPlanarEmbedding)
    (hg : MinGirth G 4) (hfaces : r.HasCyclicFaces)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 2 * Fintype.card V - 4 := by
  have h := r.edge_bound_from_euler_girth hplanar 4 hg (by omega) hfaces hcard
  omega

/-! ## Properties of the face permutation -/

/-- The source of `φ(d)` is the target of `d`, so consecutive darts in a
face orbit meet at a vertex. -/
theorem RotationSystem.facePerm_source (r : RotationSystem G) (d : G.Dart) :
    (r.facePerm d).toProd.1 = d.toProd.2 := by
  rw [r.facePerm_apply]
  rw [r.σ_source]
  rw [d.symm_toProd]; rfl

/-- The face permutation is not the identity, since it has no fixed points. -/
theorem RotationSystem.facePerm_ne_one (r : RotationSystem G)
    (d : G.Dart) :
    r.facePerm ≠ 1 := by
  intro h
  exact r.facePerm_ne_self d (by rw [h]; simp)

end SimpleGraph
