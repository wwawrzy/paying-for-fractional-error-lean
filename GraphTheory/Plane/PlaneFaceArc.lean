import GraphTheory.Plane.CyclicArcCoordinates
import GraphTheory.Plane.PlaneTwoFans

/-!
# From a cyclic attachment gap to actual two-fan surgery

An exact bridge from vertices of the whole face boundary to iterates of its
face permutation. A closed gap in position coordinates then supplies all
the hypotheses of the already proved geometric two-fan constructor.
-/

namespace PlaneTopology.PlaneFaceArc

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
  PlaneTopology.CyclicAttachment PlaneTopology.CyclicArcCoordinates PlaneTopology.PlaneTwoFans

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An in-range vertex of the full boundary is the source of the exact
corresponding iterate of the facial permutation. -/
theorem getVert_faceBoundaryWalk (r : G.RotationSystem) (d : G.Dart) (i : ℕ)
    (hi : i < (r.faceBoundaryWalk d).length) :
    (r.faceBoundaryWalk d).getVert i = ((r.facePerm ^ i) d).fst := by
  have hlen : i < (r.faceBoundaryWalk d).darts.length := by
    rwa [Walk.length_darts]
  have h := congrArg (fun e : G.Dart => e.fst) (Walk.darts_getElem_eq_getVert
    (p := r.faceBoundaryWalk d) i hlen)
  dsimp only at h
  simp only [r.faceBoundaryWalk_darts] at h
  simpa only [RotationSystem.faceDarts, getElem_toList] using h.symm

/-- Reduction of an arbitrary facial iterate modulo the actual boundary length. -/
theorem facePerm_pow_mod_length (r : G.RotationSystem) (d : G.Dart) (i : ℕ) :
    (r.facePerm ^ (i % (r.faceBoundaryWalk d).length)) d = (r.facePerm ^ i) d := by
  rw [r.faceBoundaryWalk_length]
  unfold RotationSystem.faceDegree
  rw [if_pos (mem_support.mpr (r.facePerm_ne_self d))]
  exact r.facePerm.pow_mod_card_support_cycleOf_self_apply i d

/-- The coordinate bridge also holds across the last-to-first boundary step. -/
theorem getVert_faceBoundaryWalk_mod (r : G.RotationSystem) (d : G.Dart) (i : ℕ) :
    (r.faceBoundaryWalk d).getVert (i % (r.faceBoundaryWalk d).length) =
      ((r.facePerm ^ i) d).fst := by
  have hpos : 0 < (r.faceBoundaryWalk d).length := by
    rw [r.faceBoundaryWalk_length]
    exact r.faceDegree_pos d
  rw [getVert_faceBoundaryWalk r d _ (Nat.mod_lt _ hpos), facePerm_pow_mod_length]

/-- Starting the orbit at position a changes source coordinates by a+i. -/
theorem source_pow_from_position (r : G.RotationSystem) (d : G.Dart) (a i : ℕ) :
    ((r.facePerm ^ i) ((r.facePerm ^ a) d)).fst =
      (r.faceBoundaryWalk d).getVert ((a + i) % (r.faceBoundaryWalk d).length) := by
  rw [getVert_faceBoundaryWalk_mod, pow_add, mul_apply]
  rw [← mul_apply, ← pow_add, Nat.add_comm i a, pow_add, mul_apply]

/-- Targets are the next cyclic vertex, including across position zero. -/
theorem target_pow_from_position (r : G.RotationSystem) (d : G.Dart) (a i : ℕ) :
    ((r.facePerm ^ i) ((r.facePerm ^ a) d)).snd =
      (r.faceBoundaryWalk d).getVert ((a + (i + 1)) % (r.faceBoundaryWalk d).length) := by
  rw [← r.facePerm_source, ← mul_apply, ← pow_succ']
  exact source_pow_from_position r d a (i + 1)

/-- Every cofacial source has an actual in-range coordinate on the boundary. -/
theorem exists_position_of_sameFace (r : G.RotationSystem) (base d : G.Dart)
    (hface : r.SameFace base d) :
    ∃ i < (r.faceBoundaryWalk base).length, (r.faceBoundaryWalk base).getVert i = d.fst := by
  obtain ⟨k, hk⟩ := hface.exists_nat_pow_eq
  have hpos : 0 < (r.faceBoundaryWalk base).length := by
    rw [r.faceBoundaryWalk_length]
    exact r.faceDegree_pos base
  refine ⟨k % (r.faceBoundaryWalk base).length, Nat.mod_lt _ hpos, ?_⟩
  rw [getVert_faceBoundaryWalk_mod, hk]

/-- All boundary positions at vertices of a given attachment set. -/
noncomputable def facePositions (r : G.RotationSystem) (base : G.Dart) (X : Finset V) : Finset ℕ :=
  (Finset.range (r.faceBoundaryWalk base).length).filter
    (fun i => (r.faceBoundaryWalk base).getVert i ∈ X)

/-- Exact membership in the finite attachment-coordinate set. -/
@[simp] theorem mem_facePositions (r : G.RotationSystem) (base : G.Dart)
    (X : Finset V) (i : ℕ) :
    i ∈ facePositions r base X ↔
      i < (r.faceBoundaryWalk base).length ∧ (r.faceBoundaryWalk base).getVert i ∈ X := by
  simp [facePositions]

/-- A gap obtained in finite cyclic coordinates constructs the actual exact
two-apex graph. No new topological or orbit hypothesis is assumed. -/
theorem exists_twoFanPlaneMap_of_gap (M : ConnectedPlaneMap G) (base : G.Dart)
    (X Y : Finset V)
    (hX : ∀ x ∈ X, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace base e)
    (hY : ∀ y ∈ Y, ∃ e : G.Dart, e.fst = y ∧ M.rawRotation.SameFace base e)
    (a b : ℕ) (hgap : Consecutive (facePositions M.rawRotation base X) a b)
    (hclosed : ∀ j ∈ facePositions M.rawRotation base Y, closedArc a b j) :
    Nonempty (ConnectedPlaneMap (twoFanGraph G X Y)) := by
  classical
  let r := M.rawRotation
  let p := r.faceBoundaryWalk base
  have ha := (mem_facePositions r base X a).mp hgap.1
  have hb := (mem_facePositions r base X b).mp hgap.2.1
  let d := (r.facePerm ^ a) base
  have hd : d.fst = p.getVert a := (getVert_faceBoundaryWalk r base a ha.1).symm
  have hdface : r.SameFace base d := (SameCycle.refl r.facePerm base).pow_right
  refine exists_twoFanPlaneMap G M X Y (p.getVert a) ha.2 d hd ?_
    (distance p.length a b - 1) ?_ ?_
  · intro x hx
    obtain ⟨e, he, hface⟩ := hX x hx
    exact ⟨e, he, hdface.symm.trans hface⟩
  · intro i hi hmem
    have hnot := not_mem_of_consecutive ha.1 hb.1 hgap hi
    apply hnot
    rw [mem_facePositions]
    have hpos : 0 < p.length := by
      change 0 < (r.faceBoundaryWalk base).length
      omega
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    change ((r.facePerm ^ i) ((r.facePerm ^ a) base)).snd ∈ X at hmem
    rw [target_pow_from_position] at hmem
    exact hmem
  · intro y hy
    obtain ⟨e, he, hface⟩ := hY y hy
    obtain ⟨j, hj, hje⟩ := exists_position_of_sameFace r base e hface
    have hjy : p.getVert j = y := hje.trans he
    have hjY : j ∈ facePositions r base Y := (mem_facePositions r base Y j).mpr
      ⟨hj, hjy ▸ hy⟩
    obtain ⟨i, hi, hij⟩ := exists_edge_offset_of_closedArc ha.1 hb.1 hj hgap.2.2.1
      (hclosed j hjY)
    refine ⟨i, hi, ?_⟩
    rcases hij with hij | hij
    · left
      rw [source_pow_from_position]
      exact hjy.symm.trans (congrArg p.getVert hij)
    · right
      rw [target_pow_from_position]
      exact hjy.symm.trans (congrArg p.getVert hij)

#print axioms getVert_faceBoundaryWalk
#print axioms exists_twoFanPlaneMap_of_gap

end PlaneTopology.PlaneFaceArc
