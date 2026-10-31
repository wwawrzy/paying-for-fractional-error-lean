import Paper.Endpoints.Girth.FaceCharge
import Paper.Endpoints.Girth.FaceCounting
import Paper.Endpoints.Girth.FaceOccurrenceBudget

/-!
# Face bound for a supplied connected plane map

This file composes the local marked-edge charge, the actual-face occurrence
budget, and the Euler deficit inequality.  It reindexes the sum over actual
face indices to the rotation permutation's cycle partition, then applies the
existing dart-partition perimeter identity.

This theorem is deliberately about a supplied `ConnectedPlaneMap`; obtaining
such a certificate from an arbitrary abstract planar graph is a separate
topological bridge.
-/

namespace Paper.CurrentFaceBound

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra

variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The degree of the actual face cycle indexed by `F`, obtained from its
chosen dart representative. -/
noncomputable def faceLength (M : ConnectedPlaneMap G)
    (F : FaceIndex M.rawRotation) : ℕ :=
  F.1.support.card

/-- The face index's support cardinal is exactly the face degree of its
chosen dart representative. -/
theorem faceLength_eq_representative_degree (M : ConnectedPlaneMap G)
    (F : FaceIndex M.rawRotation) :
    faceLength M F =
      M.rawRotation.faceDegree (faceRepresentative M.rawRotation F) := by
  unfold faceLength SimpleGraph.RotationSystem.faceDegree
  have hmove : faceRepresentative M.rawRotation F ∈
      M.rawRotation.facePerm.support :=
    Equiv.Perm.mem_support.mpr
      (M.rawRotation.facePerm_ne_self (faceRepresentative M.rawRotation F))
  have hcycle : M.rawRotation.facePerm.cycleOf
      (faceRepresentative M.rawRotation F) = F.1 :=
    congrArg Subtype.val (faceIndex_representative M.rawRotation F)
  rw [if_pos hmove, hcycle]

/-- Reindexing the actual `FaceIndex` sum by cycle factors gives the sum of
all dart-orbit lengths, which is twice the number of graph edges. -/
theorem faceLength_sum_eq_two_mul_edges (M : ConnectedPlaneMap G) :
    (∑ F : FaceIndex M.rawRotation, faceLength M F) =
      2 * G.edgeFinset.card := by
  classical
  have hsum :
      (∑ F : FaceIndex M.rawRotation, F.1.support.card) =
        M.rawRotation.facePerm.cycleType.sum := by
    rw [Finset.univ_eq_attach]
    rw [Finset.sum_attach M.rawRotation.facePerm.cycleFactorsFinset
      (fun p => p.support.card)]
    rw [Finset.sum_eq_multiset_sum, Equiv.Perm.cycleType_def]
    rfl
  have hsup : M.rawRotation.facePerm.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun d =>
      Equiv.Perm.mem_support.mpr (M.rawRotation.facePerm_ne_self d)
  have hparts : M.rawRotation.facePerm.partition.parts =
      M.rawRotation.facePerm.cycleType := by
    rw [Equiv.Perm.parts_partition, hsup, Finset.card_univ, Nat.sub_self,
      Multiset.replicate_zero, Multiset.add_zero]
  calc
    (∑ F : FaceIndex M.rawRotation, faceLength M F) =
        ∑ F : FaceIndex M.rawRotation, F.1.support.card := by
      simp [faceLength]
    _ = M.rawRotation.facePerm.cycleType.sum := hsum
    _ = M.rawRotation.facePerm.partition.parts.sum := by rw [hparts]
    _ = 2 * G.edgeFinset.card :=
      M.rawRotation.sum_face_partition_eq_two_mul_edges

/-- The edge set incident with at least one specified vertex. -/
noncomputable def incidentMarkedEdges (A : Finset V) : Finset G.edgeFinset :=
  Paper.GirthFaceOccurrenceBudget.markedEdges (G := G) A

/-- A chosen dart representative and the actual face index define the same
marked boundary-edge set. -/
theorem charge_occurrences_eq_actual_face (M : ConnectedPlaneMap G)
    (A : Finset V) (F : FaceIndex M.rawRotation) :
    Paper.GirthFaceCharge.markedFaceEdges M A
        (faceRepresentative M.rawRotation F) =
    Paper.GirthFaceOccurrenceBudget.faceMarkedEdges M A F := by
  classical
  ext e
  simp [Paper.GirthFaceCharge.markedFaceEdges,
    Paper.GirthFaceCharge.faceSupport,
    Paper.GirthFaceOccurrenceBudget.faceMarkedEdges,
    Paper.GirthFaceOccurrenceBudget.markedEdges,
    Paper.GirthFaceOccurrenceBudget.incidentEdges,
    faceIndex_representative, and_comm]

/-- Under the minimum-girth condition outside `A`, the total natural-number
face deficit is paid by at most `(g-3)` times the number of edges incident
with `A`.  The summation is over actual face indices, so repeated dart
representatives of one face are not counted repeatedly. -/
theorem total_face_deficit_bound
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length) :
    (∑ F : FaceIndex M.rawRotation,
      Paper.GirthFaceCharge.faceDeficit g (faceLength M F)) ≤
        (g - 3) * (incidentMarkedEdges (G := G) A).card := by
  classical
  let occurrences : FaceIndex M.rawRotation → Finset G.edgeFinset := fun F =>
    Paper.GirthFaceCharge.markedFaceEdges M A
      (faceRepresentative M.rawRotation F)
  have hlen : ∀ F : FaceIndex M.rawRotation, 3 ≤ faceLength M F := by
    intro F
    rw [faceLength_eq_representative_degree]
    exact Paper.GirthFaceCharge.faceDegree_ge_three M hna
      (faceRepresentative M.rawRotation F)
  have hshort : ∀ F : FaceIndex M.rawRotation,
      faceLength M F < g → 2 ≤ (occurrences F).card := by
    intro F hF
    rw [faceLength_eq_representative_degree] at hF
    exact Paper.GirthFaceCharge.two_marked_edges_on_short_face M hna A g
      hgirth (faceRepresentative M.rawRotation F) hF
  have hbudget :
      (∑ F : FaceIndex M.rawRotation, (occurrences F).card) ≤
        2 * (incidentMarkedEdges (G := G) A).card := by
    calc
      (∑ F : FaceIndex M.rawRotation, (occurrences F).card) =
          ∑ F : FaceIndex M.rawRotation,
            (Paper.GirthFaceOccurrenceBudget.faceMarkedEdges M A F).card := by
        apply Finset.sum_congr rfl
        intro F hF
        simp [occurrences, charge_occurrences_eq_actual_face]
      _ ≤ 2 * (incidentMarkedEdges (G := G) A).card := by
        simpa [incidentMarkedEdges] using
          (Paper.GirthFaceOccurrenceBudget.markedFaceEdges_global_budget M A)
  simpa [occurrences] using
    (Paper.GirthFaceCharge.sum_faceDeficit_le_of_occurrence_budget
      (faces := (Finset.univ : Finset (FaceIndex M.rawRotation)))
      (length := faceLength M) (markedOccurrences := occurrences)
      g (incidentMarkedEdges (G := G) A).card hg
      (by intro F hF; exact hlen F)
      (by intro F hF hs; exact hshort F hs)
      hbudget)

/-- Integer form of the natural deficit on nonnegative face lengths. -/
theorem int_faceDeficit_eq_nat
    (g j : ℕ) :
    Paper.GirthFaceCounting.faceDeficit (g : ℤ) (j : ℤ) =
      (Paper.GirthFaceCharge.faceDeficit g j : ℤ) := by
  unfold Paper.GirthFaceCounting.faceDeficit
    Paper.GirthFaceCharge.faceDeficit
  by_cases h : j < g
  · rw [if_pos h, Nat.cast_sub (Nat.le_of_lt h)]
    have hpos : 0 ≤ (g : ℤ) - (j : ℤ) := by omega
    rw [max_eq_left hpos]
  · rw [if_neg h]
    have hnonpos : (g : ℤ) - (j : ℤ) ≤ 0 := by
      have h' : g ≤ j := Nat.le_of_not_lt h
      exact_mod_cast (show (g : ℤ) - (j : ℤ) ≤ 0 by omega)
    rw [max_eq_right hnonpos]
    norm_num

/-- Euler's face-deficit estimate for the graph of a supplied connected plane
map. The perimeter identity is derived by reindexing actual face indices to
the rotation permutation's cycle partition; Euler follows from the map's
sphere-Euler certificate. The result is the exact cross-multiplied form used
in the paper's edge bound. -/
theorem connectedPlaneMap_edge_bound
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length) :
    ((g - 2 : ℕ) : ℤ) * (G.edgeFinset.card : ℤ) ≤
      (g : ℤ) * ((Fintype.card V : ℤ) - 2) +
        ((g - 3 : ℕ) : ℤ) *
          ((incidentMarkedEdges (G := G) A).card : ℤ) := by
  classical
  let faces : Finset (FaceIndex M.rawRotation) := Finset.univ
  have hcount : faces.card = M.rawRotation.numFaces := by
    rw [← PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra.card_faceIndex_eq_numFaces]
    simp [faces]
  have heulerNat : faces.card + Fintype.card V =
      G.edgeFinset.card + 2 := by
    rw [hcount]
    simpa [Nat.add_comm] using M.euler
  have heuler : (faces.card : ℤ) + (Fintype.card V : ℤ) =
      (G.edgeFinset.card : ℤ) + 2 := by
    exact_mod_cast heulerNat
  have hperimeter :
      (∑ F : FaceIndex M.rawRotation, (faceLength M F : ℤ)) =
        2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast faceLength_sum_eq_two_mul_edges M
  have hchargeNat := total_face_deficit_bound M hna A g hg hgirth
  have hchargeInt :
      (∑ F ∈ faces,
        Paper.GirthFaceCounting.faceDeficit (g : ℤ)
          (faceLength M F : ℤ)) ≤
        ((g - 3 : ℕ) : ℤ) *
          ((incidentMarkedEdges (G := G) A).card : ℤ) := by
    have hcast : ∀ F : FaceIndex M.rawRotation,
        Paper.GirthFaceCounting.faceDeficit (g : ℤ) (faceLength M F : ℤ) =
          (Paper.GirthFaceCharge.faceDeficit g (faceLength M F) : ℤ) := by
      intro F
      exact int_faceDeficit_eq_nat g (faceLength M F)
    rw [show (∑ F ∈ faces,
        Paper.GirthFaceCounting.faceDeficit (g : ℤ) (faceLength M F : ℤ)) =
      ∑ F : FaceIndex M.rawRotation,
        Paper.GirthFaceCounting.faceDeficit (g : ℤ) (faceLength M F : ℤ) by
          simp [faces]]
    simp_rw [hcast]
    rw [Nat.cast_sub (by omega : 3 ≤ g)]
    norm_num
    exact_mod_cast hchargeNat
  rw [Nat.cast_sub (by omega : 3 ≤ g), Nat.cast_ofNat] at hchargeInt
  have hbound := Paper.GirthFaceCounting.euler_deficit_edge_bound
    (g := (g : ℤ)) (n := (Fintype.card V : ℤ))
    (m := (G.edgeFinset.card : ℤ))
    (p := ((incidentMarkedEdges (G := G) A).card : ℤ))
    (faces := faces) (length := fun F => (faceLength M F : ℤ))
    (by exact_mod_cast hg) heuler hperimeter hchargeInt
  have hg2 : (g : ℤ) - 2 = ((g - 2 : ℕ) : ℤ) := by omega
  have hg3 : (g : ℤ) - 3 = ((g - 3 : ℕ) : ℤ) := by omega
  rw [hg2, hg3] at hbound
  exact hbound

end Paper.CurrentFaceBound
