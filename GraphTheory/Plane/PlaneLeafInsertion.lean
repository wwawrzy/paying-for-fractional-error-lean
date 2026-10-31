import GraphTheory.Faces.FaithfulPlaneMap
import GraphTheory.Plane.PlanePermutationSurgery

/-!
# Adding a genuine fresh leaf to a connected plane map

The new graph lives on `Option V`: old vertices are `some v`, and `none`
is adjacent only to the specified attachment vertex. The two actual new darts
are added to the same old face, without changing the face count.
-/

namespace PlaneTopology.PlaneLeafInsertion

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlanePermutationSurgery

variable {V : Type*} (G : SimpleGraph V) (v : V)

/-- Add one fresh leaf, represented by `none`, adjacent to `some v`. -/
def leafGraph : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | some a, none => a = v
    | none, some b => v = b
    | none, none => False
  symm := by
    intro a b hab
    cases a <;> cases b
    · exact hab
    · exact hab.symm
    · exact hab.symm
    · exact hab.symm
  loopless := ⟨by intro a; cases a <;> simp⟩

/-- Adjacency of the leaf graph is decidable whenever old adjacency is. -/
instance leafGraphDecidableRel [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (leafGraph G v).Adj :=
  fun a b => by cases a <;> cases b <;> unfold leafGraph <;> infer_instance

/-- Old darts plus the orientations `some v → none` and `none → some v`. -/
def leafDart : G.Dart ⊕ Bool → (leafGraph G v).Dart
  | Sum.inl d => ⟨(some d.fst, some d.snd), d.adj⟩
  | Sum.inr false => ⟨(some v, none), rfl⟩
  | Sum.inr true => ⟨(none, some v), rfl⟩

/-- The two new darts are distinct from one another and every old dart. -/
theorem leafDart_injective : Function.Injective (leafDart G v) := by
  intro a b hab
  have h := congrArg (fun d : (leafGraph G v).Dart => d.toProd) hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [leafDart, Prod.mk.injEq, Option.some.injEq] at h
      exact congrArg Sum.inl (Dart.ext _ _ (Prod.ext h.1 h.2))
    | inr b => cases b <;> simp [leafDart] at h
  | inr a =>
    cases b with
    | inl b => cases a <;> simp [leafDart] at h
    | inr b => cases a <;> cases b <;> simp_all [leafDart]

/-- All actual darts of the new graph have been enumerated. -/
theorem leafDart_surjective : Function.Surjective (leafDart G v) := by
  rintro ⟨⟨a, b⟩, hab⟩
  cases a with
  | none =>
    cases b with
    | none => exact hab.elim
    | some b =>
      change v = b at hab
      subst b
      exact ⟨Sum.inr true, rfl⟩
  | some a =>
    cases b with
    | none =>
      change a = v at hab
      subst a
      exact ⟨Sum.inr false, rfl⟩
    | some b => exact ⟨Sum.inl ⟨(a, b), hab⟩, rfl⟩

/-- Exact equivalence with the actual dart type after adding the leaf. -/
noncomputable def leafDartEquiv : G.Dart ⊕ Bool ≃ (leafGraph G v).Dart :=
  Equiv.ofBijective (leafDart G v) ⟨leafDart_injective G v, leafDart_surjective G v⟩

/-- Reversal acts on old darts as before and exchanges the two fresh darts. -/
def leafReversal : Perm (G.Dart ⊕ Bool) :=
  Equiv.sumCongr (SimpleGraph.dartSymmPerm G) (swap false true)

/-- The explicit dart equivalence intertwines the real edge reversals. -/
theorem leafDart_reversal (a : G.Dart ⊕ Bool) :
    leafDart G v (leafReversal G a) = (leafDart G v a).symm := by
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

section Rotation

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- One new outgoing dart is inserted at the attachment vertex; the new leaf's
outgoing dart remains a singleton vertex cycle. -/
def leafVertexPerm (r : G.RotationSystem) (d : G.Dart) : Perm (G.Dart ⊕ Bool) :=
  swap (Sum.inl d) (Sum.inr false) * Equiv.sumCongr r.σ (Equiv.refl Bool)

/-- Existing vertex cycles survive insertion of the leaf dart. -/
theorem leafVertexPerm_sameCycle_old (r : G.RotationSystem) (d : G.Dart)
    {a b : G.Dart} (hab : r.σ.SameCycle a b) :
    (leafVertexPerm G r d).SameCycle (Sum.inl a) (Sum.inl b) := by
  apply sameCycle_swap_mul_of_fixed _ _ _ rfl
  exact sameCycle_map r.σ _ Sum.inl (fun _ => rfl) hab

omit [Fintype V] [DecidableRel G.Adj] in
/-- The outgoing attachment dart joins the old attachment vertex cycle. -/
theorem leafVertexPerm_sameCycle_false (r : G.RotationSystem) (d : G.Dart) :
    (leafVertexPerm G r d).SameCycle (Sum.inr false) (Sum.inl d) :=
  ⟨1, by simp [leafVertexPerm, mul_apply]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The new permutation preserves actual vertex sources. -/
theorem leafVertexPerm_source (r : G.RotationSystem) (d : G.Dart)
    (hd : d.fst = v) (a : G.Dart ⊕ Bool) :
    (leafDart G v (leafVertexPerm G r d a)).fst = (leafDart G v a).fst := by
  let s := fun a : G.Dart ⊕ Bool => (leafDart G v a).fst
  have hs : s (Sum.inl d) = s (Sum.inr false) := congrArg some hd
  change s (leafVertexPerm G r d a) = s a
  rw [leafVertexPerm, mul_apply, map_swap_eq s _ _ _ hs]
  cases a with
  | inl a => exact congrArg some (r.σ_source a)
  | inr a => rfl

/-- All darts with the same actual source lie in one constructed vertex cycle. -/
theorem leafVertexPerm_sameCycle_at_source (R : FaithfulRotationSystem G)
    (d : G.Dart) (hd : d.fst = v) (a b : G.Dart ⊕ Bool)
    (hab : (leafDart G v a).fst = (leafDart G v b).fst) :
    (leafVertexPerm G R.toRotationSystem d).SameCycle a b := by
  have hf := leafVertexPerm_sameCycle_false G R.toRotationSystem d
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact leafVertexPerm_sameCycle_old G R.toRotationSystem d
        (R.sameCycle_at_source (Option.some.inj hab))
    | inr b =>
      cases b
      · have ha : a.fst = d.fst := (Option.some.inj hab).trans hd.symm
        exact (leafVertexPerm_sameCycle_old G R.toRotationSystem d
          (R.sameCycle_at_source ha)).trans hf.symm
      · cases hab
  | inr a =>
    cases a
    · cases b with
      | inl b =>
        have hb : d.fst = b.fst := hd.trans (Option.some.inj hab)
        exact hf.trans (leafVertexPerm_sameCycle_old G R.toRotationSystem d
          (R.sameCycle_at_source hb))
      | inr b => cases b <;> first | exact SameCycle.refl _ _ | cases hab
    · cases b with
      | inl b => cases hab
      | inr b => cases b <;> first | exact SameCycle.refl _ _ | cases hab

/-- Actual source-preserving rotation of the graph with its new leaf. -/
noncomputable def leafRotation (r : G.RotationSystem) (d : G.Dart) (hd : d.fst = v) :
    (leafGraph G v).RotationSystem where
  σ := (leafDartEquiv G v).permCongr (leafVertexPerm G r d)
  σ_source a := by
    obtain ⟨b, rfl⟩ := (leafDartEquiv G v).surjective a
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact leafVertexPerm_source G v r d hd b

/-- Faithfulness follows from the explicit old and new vertex cycles. -/
noncomputable def leafFaithfulRotation (R : FaithfulRotationSystem G)
    (d : G.Dart) (hd : d.fst = v) : FaithfulRotationSystem (leafGraph G v) where
  toRotationSystem := leafRotation G v R.toRotationSystem d hd
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro w a ha b hb
    obtain ⟨a', rfl⟩ := (leafDartEquiv G v).surjective a
    obtain ⟨b', rfl⟩ := (leafDartEquiv G v).surjective b
    apply sameCycle_map (leafVertexPerm G R.toRotationSystem d) _ (leafDartEquiv G v)
      (fun c => by simp [leafRotation])
    exact leafVertexPerm_sameCycle_at_source G v R d hd a' b' (ha.trans hb.symm)

/-- The facial permutation inserts both new darts into one existing face. -/
def leafFacePerm (r : G.RotationSystem) (d : G.Dart) : Perm (G.Dart ⊕ Bool) :=
  swap (Sum.inl d) (Sum.inr false) *
    Equiv.sumCongr r.facePerm (swap false true)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Leaf insertion factors into two insertions of a formerly fixed dart. -/
theorem leafFacePerm_factorization (r : G.RotationSystem) (d : G.Dart) :
    leafFacePerm G r d =
      swap (Sum.inr true) (Sum.inr false) *
        (swap (Sum.inl d) (Sum.inr true) *
          Equiv.sumCongr r.facePerm (Equiv.refl Bool)) := by
  ext a
  cases a with
  | inl a =>
    by_cases ha : r.σ a.symm = d <;>
      simp [leafFacePerm, mul_apply, Equiv.swap_apply_def, RotationSystem.facePerm_apply, ha]
  | inr a => cases a <;> simp [leafFacePerm, mul_apply, Equiv.swap_apply_def]

/-- Adding a leaf does not change the number of nontrivial facial cycles. -/
theorem leafFacePerm_cycleType_card (r : G.RotationSystem) (d : G.Dart) :
    (leafFacePerm G r d).cycleType.card = r.facePerm.cycleType.card := by
  let p₀ : Perm (G.Dart ⊕ Bool) := Equiv.sumCongr r.facePerm (Equiv.refl Bool)
  let p₁ : Perm (G.Dart ⊕ Bool) := swap (Sum.inl d) (Sum.inr true) * p₀
  have h₀ : p₀ (Sum.inl d) ≠ Sum.inl d := by
    intro h
    exact r.facePerm_ne_self d (Sum.inl.inj h)
  have h₁ := cycleType_card_swap_mul_of_fixed p₀ (Sum.inl d) (Sum.inr true) h₀ rfl
  have h₂ := cycleType_card_swap_mul_of_fixed p₁ (Sum.inr true) (Sum.inr false)
    (by simp [p₁, p₀, mul_apply])
    (by simp [p₁, p₀, mul_apply, Equiv.swap_apply_def])
  rw [leafFacePerm_factorization]
  change (swap (Sum.inr true) (Sum.inr false) * p₁).cycleType.card = _
  rw [h₂, h₁]
  exact congrArg Multiset.card (cycleType_sumCongr_refl r.facePerm)

/-- Old face incidences survive the two fixed-dart insertions. -/
theorem leafFacePerm_sameCycle_old (r : G.RotationSystem) (d : G.Dart)
    {a b : G.Dart} (hab : r.facePerm.SameCycle a b) :
    (leafFacePerm G r d).SameCycle (Sum.inl a) (Sum.inl b) := by
  let p₀ : Perm (G.Dart ⊕ Bool) := Equiv.sumCongr r.facePerm (Equiv.refl Bool)
  have h₀ : p₀.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_map r.facePerm p₀ Sum.inl (fun _ => rfl) hab
  have h₁ := sameCycle_swap_mul_of_fixed p₀ (Sum.inl d) (Sum.inr true) rfl h₀
  rw [leafFacePerm_factorization]
  apply sameCycle_swap_mul_of_fixed _ _ _ _ h₁
  simp [p₀, mul_apply, Equiv.swap_apply_def]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The dart leaving the new leaf belongs to the old chosen face. -/
theorem leafFacePerm_sameCycle_true (r : G.RotationSystem) (d : G.Dart) :
    (leafFacePerm G r d).SameCycle (Sum.inr true) (Sum.inl d) :=
  ⟨1, by simp [leafFacePerm, mul_apply]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The permutation calculation agrees with the actual graph face permutation. -/
theorem leafRotation_facePerm (r : G.RotationSystem) (d : G.Dart) (hd : d.fst = v) :
    (leafRotation G v r d hd).facePerm =
      (leafDartEquiv G v).permCongr (leafFacePerm G r d) := by
  apply Equiv.ext
  intro a
  obtain ⟨b, rfl⟩ := (leafDartEquiv G v).surjective a
  rw [RotationSystem.facePerm_apply]
  have hrev : (leafDartEquiv G v b).symm =
      leafDartEquiv G v (leafReversal G b) := (leafDart_reversal G v b).symm
  rw [hrev]
  change (leafDartEquiv G v).permCongr (leafVertexPerm G r d)
    (leafDartEquiv G v (leafReversal G b)) =
      (leafDartEquiv G v).permCongr (leafFacePerm G r d) (leafDartEquiv G v b)
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  congr 1
  cases b with
  | inl b => rfl
  | inr b => cases b <;> rfl

/-- The fresh leaf is on the same actual face as every old dart on the chosen
face. This is the interface needed to continue with fan-edge insertions. -/
theorem leafRotation_sameFace_leaf (r : G.RotationSystem) (d : G.Dart) (hd : d.fst = v)
    (a : G.Dart) (ha : r.SameFace d a) :
    (leafRotation G v r d hd).SameFace
      (leafDart G v (Sum.inr true)) (leafDart G v (Sum.inl a)) := by
  change (leafRotation G v r d hd).facePerm.SameCycle
    (leafDartEquiv G v (Sum.inr true)) (leafDartEquiv G v (Sum.inl a))
  rw [leafRotation_facePerm]
  apply sameCycle_map (leafFacePerm G r d) _ (leafDartEquiv G v)
    (fun b => by simp)
  exact (leafFacePerm_sameCycle_true G r d).trans (leafFacePerm_sameCycle_old G r d ha)

/-- A source-preserving graph rotation has no fixed facial darts, so its face
count equals the cardinality of the ordinary permutation cycle type. -/
theorem numFaces_eq_cycleType_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r : H.RotationSystem) :
    r.numFaces = r.facePerm.cycleType.card := by
  have hs : r.facePerm.support = Finset.univ := by
    ext a
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact r.facePerm_ne_self a
  simp [RotationSystem.numFaces, hs]

/-- The constructed leaf rotation has exactly the old number of faces. -/
theorem leafRotation_numFaces (r : G.RotationSystem) (d : G.Dart) (hd : d.fst = v) :
    (leafRotation G v r d hd).numFaces = r.numFaces := by
  rw [numFaces_eq_cycleType_card, numFaces_eq_cycleType_card,
    leafRotation_facePerm, cycleType_permCongr, leafFacePerm_cycleType_card]

/-- Adding the fresh leaf adds exactly one edge. -/
theorem card_edges_leafGraph : (leafGraph G v).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hc := Fintype.card_congr (leafDartEquiv G v)
  rw [Fintype.card_sum, Fintype.card_bool, G.dart_card_eq_twice_card_edges,
    (leafGraph G v).dart_card_eq_twice_card_edges] at hc
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The fresh leaf and old connected graph together remain connected. -/
theorem connected_leafGraph (hG : G.Connected) : (leafGraph G v).Connected := by
  let f : G →g leafGraph G v := ⟨some, fun h => h⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨some v, ?_⟩
  intro a
  cases a with
  | none => exact Adj.reachable rfl
  | some a => exact (hG.preconnected v a).map f

/-- Every vertex of an edgeful connected map has an outgoing anchor dart. -/
theorem exists_dart_at_vertex (M : ConnectedPlaneMap G) : ∃ d : G.Dart, d.fst = v := by
  obtain ⟨e⟩ := M.dartNonempty
  haveI : Nontrivial V := ⟨⟨e.fst, e.snd, G.ne_of_adj e.adj⟩⟩
  obtain ⟨w, hvw⟩ := M.connected.preconnected.exists_adj_of_nontrivial v
  exact ⟨⟨(v, w), hvw⟩, rfl⟩

/-- Construct the actual connected sphere map with its fresh leaf at a chosen
old outgoing dart. No face-count or embedding-existence hypothesis is added. -/
noncomputable def leafPlaneMapAt (M : ConnectedPlaneMap G) (d : G.Dart) (hd : d.fst = v) :
    ConnectedPlaneMap (leafGraph G v) where
  rotation := leafFaithfulRotation G v M.rotation d hd
  connected := connected_leafGraph G v M.connected
  dartNonempty := ⟨leafDart G v (Sum.inr false)⟩
  euler := by
    change Fintype.card (Option V) + (leafRotation G v M.rawRotation d hd).numFaces = _
    rw [Fintype.card_option, leafRotation_numFaces, card_edges_leafGraph]
    have h := M.euler
    change Fintype.card V + M.rawRotation.numFaces = G.edgeFinset.card + 2 at h
    omega

/-- Add a genuine fresh leaf at any specified vertex of a connected plane map. -/
noncomputable def leafPlaneMap (M : ConnectedPlaneMap G) :
    ConnectedPlaneMap (leafGraph G v) :=
  leafPlaneMapAt G v M (exists_dart_at_vertex G v M).choose
    (exists_dart_at_vertex G v M).choose_spec

end Rotation

end PlaneTopology.PlaneLeafInsertion

#print axioms PlaneTopology.PlaneLeafInsertion.leafFaithfulRotation
#print axioms PlaneTopology.PlaneLeafInsertion.leafPlaneMap
