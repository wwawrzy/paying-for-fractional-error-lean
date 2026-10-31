import GraphTheory.Faces.FaithfulPlaneMap

/-!
# Actual faithful vertex rotations on every finite simple graph

The construction here chooses one cyclic permutation on each outgoing-dart
fiber and assembles them into a source-preserving permutation.  It proves the
existence of a faithful rotation, not Euler characteristic two: sphericality
remains a separate geometric assertion.
-/

namespace PlaneTopology.PlaneRotationExists

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A chosen cycle on the outgoing darts at one vertex, extended to all darts. -/
noncomputable def localCycle (v : V) : Equiv.Perm G.Dart :=
  Classical.choose (Finset.exists_cycleOn (Finset.univ.filter fun d : G.Dart => d.fst = v))

/-- The chosen local permutation cycles through the complete outgoing fiber. -/
theorem localCycle_isCycleOn (v : V) :
    (localCycle G v).IsCycleOn (outDartsAt G v) := by
  classical
  have h := (Classical.choose_spec
    (Finset.exists_cycleOn (Finset.univ.filter fun d : G.Dart => d.fst = v))).1
  simpa [localCycle, outDartsAt] using h

/-- Applying a local cycle to a dart in its fiber preserves the source. -/
theorem localCycle_source (d : G.Dart) :
    (localCycle G d.fst d).fst = d.fst :=
  (localCycle_isCycleOn G d.fst).1.mapsTo rfl

/-- The inverse local cycle also preserves the source on its fiber. -/
theorem localCycle_symm_source (d : G.Dart) :
    ((localCycle G d.fst).symm d).fst = d.fst :=
  (localCycle_isCycleOn G d.fst).1.perm_inv.mapsTo rfl

/-- Assembly of the vertex-local cycles into a permutation of all darts. -/
noncomputable def vertexPermutation : Equiv.Perm G.Dart where
  toFun d := localCycle G d.fst d
  invFun d := (localCycle G d.fst).symm d
  left_inv d := by
    change (localCycle G (localCycle G d.fst d).fst).symm (localCycle G d.fst d) = d
    rw [localCycle_source]
    exact Equiv.symm_apply_apply _ _
  right_inv d := by
    change localCycle G ((localCycle G d.fst).symm d).fst ((localCycle G d.fst).symm d) = d
    rw [localCycle_symm_source]
    exact Equiv.apply_symm_apply _ _

/-- The assembled permutation preserves dart sources. -/
theorem vertexPermutation_source (d : G.Dart) :
    (vertexPermutation G d).fst = d.fst := localCycle_source G d

/-- On one fiber, every nonnegative power agrees with the chosen local cycle. -/
theorem vertexPermutation_pow_apply (v : V) (d : G.Dart) (hd : d.fst = v)
    (n : ℕ) :
    (vertexPermutation G ^ n) d = (localCycle G v ^ n) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    have hsource : ((localCycle G v ^ n) d).fst = v :=
      ((localCycle_isCycleOn G v).1.perm_pow n).mapsTo hd
    change localCycle G ((localCycle G v ^ n) d).fst ((localCycle G v ^ n) d) = _
    rw [hsource]

/-- The raw source-preserving rotation assembled from the local cycles. -/
noncomputable def rotationSystem : G.RotationSystem where
  σ := vertexPermutation G
  σ_source := vertexPermutation_source G

/-- Every outgoing fiber is one cycle of the assembled permutation. -/
theorem rotationSystem_isVertexCyclic :
    PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.IsVertexCyclic (rotationSystem G) := by
  apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
  intro v d hd e he
  obtain ⟨n, hn⟩ := (localCycle_isCycleOn G v).exists_pow_eq'
    (Set.toFinite _) hd he
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (vertexPermutation_pow_apply G v d hd n).trans hn

/-- An actual faithful rotation system on any finite simple graph. -/
noncomputable def faithfulRotationSystem : FaithfulRotationSystem G where
  toRotationSystem := rotationSystem G
  vertexCyclic := rotationSystem_isVertexCyclic G

/-- Faithful vertex rotations exist without any planarity hypothesis. -/
theorem nonempty_faithfulRotationSystem : Nonempty (FaithfulRotationSystem G) :=
  ⟨faithfulRotationSystem G⟩

#print axioms rotationSystem_isVertexCyclic
#print axioms nonempty_faithfulRotationSystem

end PlaneTopology.PlaneRotationExists
