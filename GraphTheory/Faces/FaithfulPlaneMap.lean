import GraphTheory.Faces.FacialOccurrence
import GraphTheory.SimpleGraph.CycleCutDimensions

/-!
# Faithful connected plane maps

The repository's legacy `RotationSystem` only says that its dart permutation
preserves sources.  That admits several disjoint rotation cycles at one vertex
and is too weak for facial separation.  This file adds, without changing the
legacy structure, the missing invariant: the outgoing darts at every vertex
form one cycle.

A `ConnectedPlaneMap` below is a finite connected cellular rotation map with
Euler characteristic two.  It is a supplied combinatorial sphere-map
certificate; this file does not claim that the repository's forbidden-minor
predicate `SimpleGraph.IsPlanar` constructs one.
-/

namespace PlaneTopology.Faces.FaithfulPlaneMap

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## 1. One cyclic rotation at every vertex -/

/-- The set of all darts whose source is `v`. -/
def outDartsAt (G : SimpleGraph V) (v : V) : Set G.Dart :=
  {e | e.fst = v}

namespace RotationSystem

/-- Source preservation makes the raw vertex permutation map each outgoing
dart fibre into itself. -/
theorem sigma_mapsTo_outDartsAt (r : G.RotationSystem) (v : V) :
    Set.MapsTo r.σ (outDartsAt G v) (outDartsAt G v) := by
  intro e he
  change (r.σ e).fst = v
  change e.fst = v at he
  exact (r.σ_source e).trans he

/-- In fact the raw vertex permutation is a bijection of every outgoing dart
fibre; the additional faithful invariant will only need to impose one orbit. -/
theorem sigma_bijOn_outDartsAt (r : G.RotationSystem) (v : V) :
    Set.BijOn r.σ (outDartsAt G v) (outDartsAt G v) := by
  refine ⟨sigma_mapsTo_outDartsAt r v, r.σ.injective.injOn, ?_⟩
  intro e he
  refine ⟨r.σ.symm e, ?_, by simp⟩
  change (r.σ.symm e).fst = v
  change e.fst = v at he
  have hsource := r.σ_source (r.σ.symm e)
  simp only [Equiv.apply_symm_apply] at hsource
  exact hsource.symm.trans he

/-- The raw rotation is faithful at vertices when its restriction to every
outgoing-dart fibre is one cyclic order. -/
def IsVertexCyclic (r : G.RotationSystem) : Prop :=
  ∀ v : V, r.σ.IsCycleOn (outDartsAt G v)

/-- It suffices to prove the pairwise same-cycle clause: preservation and
bijectivity of each source fibre follow from `sigma_source`. -/
theorem isVertexCyclic_of_pairwise_sameCycle
    (r : G.RotationSystem)
    (h : ∀ (v : V) ⦃e⦄, e ∈ outDartsAt G v →
      ∀ ⦃f⦄, f ∈ outDartsAt G v → r.σ.SameCycle e f) :
    IsVertexCyclic r := by
  intro v
  exact ⟨sigma_bijOn_outDartsAt r v, h v⟩

/-- The useful elimination form of vertex faithfulness. -/
theorem IsVertexCyclic.sameCycle
    {r : G.RotationSystem} (hr : IsVertexCyclic r)
    {v : V} {e f : G.Dart}
    (he : e.fst = v) (hf : f.fst = v) :
    r.σ.SameCycle e f :=
  (hr v).2 he hf

end RotationSystem

/-- Compatibility wrapper for a source-preserving rotation which is one cycle
at each non-isolated vertex. -/
structure FaithfulRotationSystem (G : SimpleGraph V) where
  toRotationSystem : G.RotationSystem
  vertexCyclic : RotationSystem.IsVertexCyclic toRotationSystem

namespace FaithfulRotationSystem

instance : Coe (FaithfulRotationSystem G) G.RotationSystem :=
  ⟨FaithfulRotationSystem.toRotationSystem⟩

theorem sameCycle_at_source (R : FaithfulRotationSystem G)
    {e f : G.Dart} (hsource : e.fst = f.fst) :
    R.toRotationSystem.σ.SameCycle e f := by
  exact RotationSystem.IsVertexCyclic.sameCycle R.vertexCyclic rfl hsource.symm

end FaithfulRotationSystem

/-! ## 2. Connected cellular maps of the sphere -/

/-- A connected, edgeful, faithful cellular rotation map.  The dart
nonemptiness field excludes the edgeless case, for which dart orbits do not
encode the unique outer face. -/
structure ConnectedCellularMap (G : SimpleGraph V) where
  rotation : FaithfulRotationSystem G
  connected : G.Connected
  dartNonempty : Nonempty G.Dart

/-- A supplied connected combinatorial sphere map: a faithful connected
cellular rotation map whose face orbits satisfy the sphere Euler equation. -/
structure ConnectedPlaneMap
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    extends ConnectedCellularMap G where
  euler : Fintype.card V + rotation.toRotationSystem.numFaces =
    G.edgeFinset.card + 2

namespace ConnectedPlaneMap

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Forgetting faithfulness and connectedness recovers the legacy numerical
Euler certificate, but not conversely. -/
theorem rotation_isPlanarEmbedding (M : ConnectedPlaneMap G) :
    M.rotation.toRotationSystem.IsPlanarEmbedding :=
  M.euler

/-- Convenient access to the exact raw rotation used by face-orbit APIs. -/
abbrev rawRotation (M : ConnectedPlaneMap G) : G.RotationSystem :=
  M.rotation.toRotationSystem

/-- All outgoing darts at a vertex of a faithful plane map lie in one vertex
rotation orbit. -/
theorem vertexDarts_sameCycle (M : ConnectedPlaneMap G)
    {e f : G.Dart} (hsource : e.fst = f.fst) :
    M.rawRotation.σ.SameCycle e f :=
  M.rotation.sameCycle_at_source hsource

end ConnectedPlaneMap

/-! ## 3. Faces indexed by actual permutation cycles -/

namespace FaceAlgebra

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Since a face permutation has no fixed dart, its nontrivial cycle factors
index all faces, with no separate fixed-point summand. -/
abbrev FaceIndex (r : G.RotationSystem) :=
  ↥r.facePerm.cycleFactorsFinset

/-- The face-cycle factor containing a dart. -/
noncomputable def faceIndex (r : G.RotationSystem) (e : G.Dart) :
    FaceIndex r :=
  ⟨r.facePerm.cycleOf e,
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr (r.facePerm_ne_self e))⟩

/-- Equality of face indices is exactly membership in the same face orbit. -/
theorem faceIndex_eq_iff_sameFace (r : G.RotationSystem) (e f : G.Dart) :
    faceIndex r e = faceIndex r f ↔ r.SameFace e f := by
  have he : e ∈ r.facePerm.support :=
    Equiv.Perm.mem_support.mpr (r.facePerm_ne_self e)
  have hf : f ∈ r.facePerm.support :=
    Equiv.Perm.mem_support.mpr (r.facePerm_ne_self f)
  constructor
  · intro h
    change r.facePerm.SameCycle e f
    apply (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support he hf).mpr
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support he hf).mp h

/-- Advancing one step around a face does not change its face index. -/
theorem faceIndex_facePerm (r : G.RotationSystem) (e : G.Dart) :
    faceIndex r (r.facePerm e) = faceIndex r e := by
  apply (faceIndex_eq_iff_sameFace r _ _).mpr
  change r.facePerm.SameCycle (r.facePerm e) e
  exact Equiv.Perm.sameCycle_apply_left.mpr
    (Equiv.Perm.SameCycle.refl r.facePerm e)

/-- At a vertex, the face preceding an outgoing dart `e` is the face indexed
by `e.symm`; equivalently it is indexed by the next vertex-rotation dart. -/
theorem faceIndex_sigma_eq_symm (r : G.RotationSystem) (e : G.Dart) :
    faceIndex r (r.σ e) = faceIndex r e.symm := by
  have hstep : faceIndex r (r.facePerm e.symm) = faceIndex r e.symm :=
    faceIndex_facePerm r e.symm
  simpa [SimpleGraph.RotationSystem.facePerm_apply] using hstep

/-- The number of cycle-factor indices is the legacy `numFaces`. -/
theorem card_faceIndex_eq_numFaces (r : G.RotationSystem) :
    Fintype.card (FaceIndex r) = r.numFaces := by
  classical
  have hsupp : r.facePerm.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun e =>
      Equiv.Perm.mem_support.mpr (r.facePerm_ne_self e)
  unfold FaceIndex SimpleGraph.RotationSystem.numFaces
  rw [Equiv.Perm.cycleType_def, hsupp]
  simp

/-- A concrete dart chosen from a face-cycle factor. -/
noncomputable def faceRepresentative (r : G.RotationSystem)
    (F : FaceIndex r) : G.Dart :=
  Classical.choose
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp F.property).1.nonempty_support)

theorem faceRepresentative_mem_support (r : G.RotationSystem)
    (F : FaceIndex r) :
    faceRepresentative r F ∈ (F.1 : Equiv.Perm G.Dart).support :=
  Classical.choose_spec
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp F.property).1.nonempty_support)

/-- The chosen representative lies in precisely the indexed face cycle. -/
theorem faceIndex_representative (r : G.RotationSystem)
    (F : FaceIndex r) :
    faceIndex r (faceRepresentative r F) = F := by
  apply Subtype.ext
  symm
  exact Equiv.Perm.cycle_is_cycleOf
    (faceRepresentative_mem_support r F) F.property

end FaceAlgebra

#print axioms RotationSystem.sigma_bijOn_outDartsAt
#print axioms RotationSystem.isVertexCyclic_of_pairwise_sameCycle
#print axioms ConnectedPlaneMap.rotation_isPlanarEmbedding
#print axioms FaceAlgebra.card_faceIndex_eq_numFaces

end PlaneTopology.Faces.FaithfulPlaneMap
