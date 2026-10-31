import GraphTheory.Faces.FaithfulPlaneMap
import GraphTheory.Plane.PlanePermutationSurgery
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Actual darts and rotations after inserting a missing edge

The two fresh darts are identified explicitly with the two orientations of
the added edge. This file does not assume an embedding-existence provider.
-/

namespace PlaneTopology.PlaneEdgeInsertion

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap

variable {V : Type*} (G : SimpleGraph V) (u v : V)

/-- The actual dart map after adding the edge `uv`; `false` is `uv` and
`true` is its reversal. -/
def augmentedDart (hne : u ≠ v) : G.Dart ⊕ Bool → (G ⊔ edge u v).Dart
  | Sum.inl d => ⟨d.toProd, Or.inl d.adj⟩
  | Sum.inr false => ⟨(u, v), Or.inr ((edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)⟩
  | Sum.inr true => ⟨(v, u), Or.inr ((edge_adj u v v u).mpr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩)⟩

/-- No preexisting dart is identified with a fresh dart because the inserted
edge is absent from the old graph. -/
theorem augmentedDart_injective (hne : u ≠ v) (hmiss : ¬G.Adj u v) :
    Function.Injective (augmentedDart G u v hne) := by
  intro x y h
  have hprod := congrArg (fun d : (G ⊔ edge u v).Dart => d.toProd) h
  cases x with
  | inl d =>
    cases y with
    | inl e => exact congrArg Sum.inl (Dart.ext d e hprod)
    | inr b =>
      cases b <;> simp only [augmentedDart] at hprod
      · exact (hmiss (by simpa only [hprod] using d.adj)).elim
      · exact (hmiss (by simpa only [hprod] using d.adj.symm)).elim
  | inr b =>
    cases y with
    | inl d =>
      cases b <;> simp only [augmentedDart] at hprod
      · exact (hmiss (by simpa only [← hprod] using d.adj)).elim
      · exact (hmiss (by simpa only [← hprod] using d.adj.symm)).elim
    | inr c =>
      cases b <;> cases c <;> simp_all [augmentedDart, Prod.mk.injEq]

/-- Every dart of the augmented graph is old or one of the two new darts. -/
theorem augmentedDart_surjective (hne : u ≠ v) :
    Function.Surjective (augmentedDart G u v hne) := by
  intro d
  rcases d.adj with hold | hnew
  · exact ⟨Sum.inl ⟨d.toProd, hold⟩, Dart.ext _ _ rfl⟩
  · rcases (edge_adj u v d.fst d.snd).mp hnew with ⟨h | h, _⟩
    · exact ⟨Sum.inr false, Dart.ext _ _ (Prod.ext h.1.symm h.2.symm)⟩
    · exact ⟨Sum.inr true, Dart.ext _ _ (Prod.ext h.1.symm h.2.symm)⟩

/-- Exact dart equivalence for one missing-edge insertion. -/
noncomputable def augmentedDartEquiv (hne : u ≠ v) (hmiss : ¬G.Adj u v) :
    G.Dart ⊕ Bool ≃ (G ⊔ edge u v).Dart :=
  Equiv.ofBijective (augmentedDart G u v hne)
    ⟨augmentedDart_injective G u v hne hmiss, augmentedDart_surjective G u v hne⟩

theorem augmentedDartEquiv_apply (hne : u ≠ v) (hmiss : ¬G.Adj u v)
    (d : G.Dart ⊕ Bool) :
    augmentedDartEquiv G u v hne hmiss d = augmentedDart G u v hne d := rfl

/-- Reversal on the old-plus-two dart type. -/
def augmentedReversal : Perm (G.Dart ⊕ Bool) :=
  Equiv.sumCongr (SimpleGraph.dartSymmPerm G) (Equiv.swap false true)

/-- The explicit dart equivalence respects the actual graph reversal. -/
theorem augmentedDart_reversal (hne : u ≠ v) (d : G.Dart ⊕ Bool) :
    augmentedDart G u v hne (augmentedReversal G d) =
      (augmentedDart G u v hne d).symm := by
  cases d with
  | inl d => rfl
  | inr b => cases b <;> rfl

#print axioms augmentedDartEquiv
#print axioms augmentedDart_reversal

section Rotation

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Old vertex rotation extended by two fixed fresh darts. -/
def baseRotation (r : G.RotationSystem) : Perm (G.Dart ⊕ Bool) :=
  Equiv.sumCongr r.σ (Equiv.refl Bool)

/-- Insert the new `uv` dart before `d`, and the new `vu` dart before `e`. -/
def augmentedRotation (r : G.RotationSystem) (d e : G.Dart) : Perm (G.Dart ⊕ Bool) :=
  swap (Sum.inl e) (Sum.inr true) *
    (swap (Sum.inl d) (Sum.inr false) * baseRotation G r)

/-- Every old rotation cycle survives both insertions. -/
theorem augmentedRotation_sameCycle_old (r : G.RotationSystem) (d e : G.Dart)
    {x y : G.Dart} (hxy : r.σ.SameCycle x y) :
    (augmentedRotation G r d e).SameCycle (Sum.inl x) (Sum.inl y) := by
  have hbase : (baseRotation G r).SameCycle (Sum.inl x) (Sum.inl y) :=
    PlaneTopology.PlanePermutationSurgery.sameCycle_map r.σ (baseRotation G r) Sum.inl
      (fun _ => rfl) hxy
  have hfirst := PlaneTopology.PlanePermutationSurgery.sameCycle_swap_mul_of_fixed
    (baseRotation G r) (Sum.inl d) (Sum.inr false) rfl hbase
  apply PlaneTopology.PlanePermutationSurgery.sameCycle_swap_mul_of_fixed _ _ _ _ hfirst
  simp [baseRotation, mul_apply, Equiv.swap_apply_def]

theorem augmentedRotation_sameCycle_false (r : G.RotationSystem) (d e : G.Dart) :
    (augmentedRotation G r d e).SameCycle (Sum.inr false) (Sum.inl d) := by
  have hfirst : (swap (Sum.inl d) (Sum.inr false) * baseRotation G r).SameCycle
      (Sum.inr false) (Sum.inl d) := ⟨1, by simp [baseRotation, mul_apply]⟩
  apply PlaneTopology.PlanePermutationSurgery.sameCycle_swap_mul_of_fixed _ _ _ _ hfirst
  simp [baseRotation, mul_apply, Equiv.swap_apply_def]

omit [Fintype V] [DecidableRel G.Adj] in
theorem augmentedRotation_sameCycle_true (r : G.RotationSystem) (d e : G.Dart) :
    (augmentedRotation G r d e).SameCycle (Sum.inr true) (Sum.inl e) :=
  ⟨1, by simp [augmentedRotation, baseRotation, mul_apply, Equiv.swap_apply_def]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The constructed permutation preserves actual dart sources. -/
theorem augmentedRotation_source (r : G.RotationSystem) (d e : G.Dart)
    (hne : u ≠ v) (hd : d.fst = u) (he : e.fst = v) (x : G.Dart ⊕ Bool) :
    (augmentedDart G u v hne (augmentedRotation G r d e x)).fst =
      (augmentedDart G u v hne x).fst := by
  let s := fun z : G.Dart ⊕ Bool => (augmentedDart G u v hne z).fst
  have hsd : s (Sum.inl d) = s (Sum.inr false) := hd
  have hse : s (Sum.inl e) = s (Sum.inr true) := he
  change s (augmentedRotation G r d e x) = s x
  simp only [augmentedRotation, mul_apply]
  rw [PlaneTopology.PlanePermutationSurgery.map_swap_eq s _ _ _ hse,
    PlaneTopology.PlanePermutationSurgery.map_swap_eq s _ _ _ hsd]
  cases x with
  | inl x => exact r.σ_source x
  | inr b => rfl

/-- All darts with a common actual source stay in one vertex cycle. -/
theorem augmentedRotation_sameCycle_at_source (R : FaithfulRotationSystem G)
    (d e : G.Dart) (hne : u ≠ v) (hd : d.fst = u) (he : e.fst = v)
    (x y : G.Dart ⊕ Bool)
    (hsource : (augmentedDart G u v hne x).fst = (augmentedDart G u v hne y).fst) :
    (augmentedRotation G R.toRotationSystem d e).SameCycle x y := by
  let anchor : G.Dart ⊕ Bool → G.Dart
    | Sum.inl z => z
    | Sum.inr false => d
    | Sum.inr true => e
  have ha (z : G.Dart ⊕ Bool) :
      (augmentedRotation G R.toRotationSystem d e).SameCycle z (Sum.inl (anchor z)) := by
    cases z with
    | inl z => exact SameCycle.refl _ _
    | inr b =>
      cases b
      · exact augmentedRotation_sameCycle_false G R.toRotationSystem d e
      · exact augmentedRotation_sameCycle_true G R.toRotationSystem d e
  have hs (z : G.Dart ⊕ Bool) : (anchor z).fst = (augmentedDart G u v hne z).fst := by
    cases z with
    | inl z => rfl
    | inr b => cases b <;> assumption
  have hanchors := R.sameCycle_at_source ((hs x).trans (hsource.trans (hs y).symm))
  exact (ha x).trans ((augmentedRotation_sameCycle_old G R.toRotationSystem d e hanchors).trans
    (ha y).symm)

/-- The actual source-preserving rotation after adding a missing edge. -/
noncomputable def insertedRotation (r : G.RotationSystem) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v) :
    (G ⊔ edge u v).RotationSystem where
  σ := (augmentedDartEquiv G u v hne hmiss).permCongr (augmentedRotation G r d e)
  σ_source x := by
    obtain ⟨z, rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective x
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact augmentedRotation_source G u v r d e hne hd he z

/-- Faithfulness is proved from the actual inserted vertex cycles. -/
noncomputable def insertedFaithfulRotation (R : FaithfulRotationSystem G) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v) :
    FaithfulRotationSystem (G ⊔ edge u v) where
  toRotationSystem := insertedRotation G u v R.toRotationSystem d e hne hmiss hd he
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro w x hx y hy
    obtain ⟨x', rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective x
    obtain ⟨y', rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective y
    apply PlaneTopology.PlanePermutationSurgery.sameCycle_map (augmentedRotation G R.toRotationSystem d e)
      _ (augmentedDartEquiv G u v hne hmiss) (fun z => by simp [insertedRotation])
    apply augmentedRotation_sameCycle_at_source G u v R d e hne hd he
    exact hx.trans hy.symm

#print axioms insertedFaithfulRotation

omit [Fintype V] [DecidableRel G.Adj] in
/-- The actual new facial permutation is precisely the checked chord surgery,
transported through the actual graph-dart equivalence. -/
theorem insertedRotation_facePerm (r : G.RotationSystem) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v) :
    (insertedRotation G u v r d e hne hmiss hd he).facePerm =
      (augmentedDartEquiv G u v hne hmiss).permCongr
        (PlaneTopology.PlanePermutationSurgery.chordPerm r.facePerm d e) := by
  apply Equiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective x
  have hrev : (augmentedDartEquiv G u v hne hmiss z).symm =
      augmentedDartEquiv G u v hne hmiss (augmentedReversal G z) :=
    (augmentedDart_reversal G u v hne z).symm
  change (augmentedDartEquiv G u v hne hmiss)
      (augmentedRotation G r d e ((augmentedDartEquiv G u v hne hmiss).symm
        ((augmentedDartEquiv G u v hne hmiss z).symm))) = _
  rw [hrev, Equiv.symm_apply_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply congrArg (augmentedDartEquiv G u v hne hmiss)
  cases z <;> rfl

/-- Simple-graph face permutations have no fixed darts, so every face is
counted by one nontrivial permutation cycle. -/
theorem numFaces_eq_cycleType_card (r : G.RotationSystem) :
    r.numFaces = r.facePerm.cycleType.card := by
  have hsupp : r.facePerm.support = Finset.univ := Finset.eq_univ_iff_forall.mpr
    (fun d => Equiv.Perm.mem_support.mpr (r.facePerm_ne_self d))
  simp [SimpleGraph.RotationSystem.numFaces, hsupp]

/-- Inserting a missing edge at two corners of one actual face creates
exactly one additional actual face. -/
theorem insertedRotation_numFaces (r : G.RotationSystem) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v)
    (hface : r.SameFace d e) :
    (insertedRotation G u v r d e hne hmiss hd he).numFaces = r.numFaces + 1 := by
  have hde : d ≠ e := by
    intro h
    exact hne (hd.symm.trans ((congrArg (fun z : G.Dart => z.fst) h).trans he))
  rw [numFaces_eq_cycleType_card, insertedRotation_facePerm,
    PlaneTopology.PlanePermutationSurgery.cycleType_permCongr,
    PlaneTopology.PlanePermutationSurgery.cycleType_card_chordPerm r.facePerm d e hde hface
      (r.facePerm_ne_self d), numFaces_eq_cycleType_card]

/-- Adding a missing edge with arbitrary endpoint corners gives an actual
connected faithful cellular map; planarity is handled separately. -/
noncomputable def insertedCellularMap (M : ConnectedCellularMap G) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v) :
    ConnectedCellularMap (G ⊔ edge u v) where
  rotation := insertedFaithfulRotation G u v M.rotation d e hne hmiss hd he
  connected := M.connected.mono le_sup_left
  dartNonempty := ⟨augmentedDart G u v hne (Sum.inr false)⟩

/-- **Actual chord insertion in a plane map.** The missing edge is inserted
at two corners of one actual face; faithfulness, connectedness and Euler's
equation are all proved for the resulting graph. -/
noncomputable def insertedPlaneMap (M : ConnectedPlaneMap G) (d e : G.Dart)
    (hne : u ≠ v) (hmiss : ¬G.Adj u v) (hd : d.fst = u) (he : e.fst = v)
    (hface : M.rawRotation.SameFace d e) : ConnectedPlaneMap (G ⊔ edge u v) where
  toConnectedCellularMap := insertedCellularMap G u v M.toConnectedCellularMap d e
    hne hmiss hd he
  euler := by
    change Fintype.card V +
      (insertedRotation G u v M.rawRotation d e hne hmiss hd he).numFaces = _
    rw [insertedRotation_numFaces G u v M.rawRotation d e hne hmiss hd he hface]
    have hcard := G.card_edgeFinset_sup_edge hmiss hne
    have heuler := M.euler
    change Fintype.card V + M.rawRotation.numFaces = G.edgeFinset.card + 2 at heuler
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard heuler ⊢
    omega

#print axioms insertedRotation_numFaces
#print axioms insertedPlaneMap

end Rotation

end PlaneTopology.PlaneEdgeInsertion
