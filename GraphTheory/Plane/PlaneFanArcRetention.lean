import GraphTheory.Plane.PlaneFanInsertion

/-!
# A fan construction retaining literal old face arcs

The construction strengthens single-fan insertion by recording actual old
dart incidences and exact facial steps away from the attachment vertices.
These facts keep an attachment-free old boundary gap on one face with the
apex, which is the interface required by a second, noncrossing fan.
-/

namespace PlaneTopology.PlaneFanArcRetention

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneChordFaces PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneFanInsertion

variable {V : Type*} {G H K : SimpleGraph V}

/-- Every old dart on a face incident with the apex keeps an actual new
apex-face witness; its old ordered endpoint pair is retained literally. -/
def PreservesApexDarts (r : G.RotationSystem) (s : H.RotationSystem) (u : V) : Prop :=
  ∀ c x : G.Dart, c.fst = u → r.SameFace c x →
    ∃ a b : H.Dart, a.fst = u ∧ b.toProd = x.toProd ∧ s.SameFace a b

/-- All facial steps entering vertices outside the fan endpoints retain
their exact old ordered endpoint pair. -/
def FaceStepsAgreeOff (r : G.RotationSystem) (s : H.RotationSystem)
    (u : V) (S : Finset V) : Prop :=
  ∀ d : G.Dart, ∀ e : H.Dart, e.toProd = d.toProd → d.snd ≠ u → d.snd ∉ S →
    (s.facePerm e).toProd = (r.facePerm d).toProd

/-- The dartwise invariant implies the ordinary vertex cofacial invariant. -/
theorem PreservesApexDarts.coFacial {r : G.RotationSystem} {s : H.RotationSystem}
    {u x : V} (h : PreservesApexDarts r s u) (hx : CoFacial G r u x) :
    CoFacial H s u x := by
  obtain ⟨c, d, hc, hd, hcd⟩ := hx
  obtain ⟨a, b, ha, hb, hab⟩ := h c d hc hcd
  exact ⟨a, b, ha, (congrArg Prod.fst hb).trans hd, hab⟩

variable [Fintype V] [DecidableEq V]

/-- Graph equality transports an actual dart without changing its endpoints. -/
def castDart (h : H = K) (d : H.Dart) : K.Dart := by
  subst K
  exact d

omit [Fintype V] [DecidableEq V] in
theorem castDart_toProd (h : H = K) (d : H.Dart) : (castDart h d).toProd = d.toProd := by
  subst K
  rfl

/-- The equality-transported map and darts retain their actual facial orbit. -/
theorem castPlaneMap_sameFace [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (h : H = K) (N : ConnectedPlaneMap H) (d e : H.Dart)
    (hde : N.rawRotation.SameFace d e) :
    (castPlaneMap h N).rawRotation.SameFace (castDart h d) (castDart h e) := by
  subst K
  cases Subsingleton.elim dK dH
  exact hde

/-- Graph-equality transport preserves the full literal-dart invariant. -/
theorem preservesApexDarts_cast [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (r : G.RotationSystem) (N : ConnectedPlaneMap H) (u : V)
    (h : H = K) (hN : PreservesApexDarts r N.rawRotation u) :
    PreservesApexDarts r (castPlaneMap h N).rawRotation u := by
  subst K
  cases Subsingleton.elim dK dH
  exact hN

/-- Graph-equality transport preserves exact old facial steps. -/
theorem faceStepsAgreeOff_cast [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (r : G.RotationSystem) (N : ConnectedPlaneMap H) (u : V) (S : Finset V)
    (h : H = K) (hN : FaceStepsAgreeOff r N.rawRotation u S) :
    FaceStepsAgreeOff r (castPlaneMap h N).rawRotation u S := by
  subst K
  cases Subsingleton.elim dK dH
  exact hN

/-- The literal-dart apex invariant survives a real chord insertion. -/
theorem preservesApexDarts_inserted [DecidableRel H.Adj]
    (r : G.RotationSystem) (N : ConnectedPlaneMap H) (u v : V)
    (d e : H.Dart) (hne : u ≠ v) (hmiss : ¬H.Adj u v)
    (hd : d.fst = u) (he : e.fst = v) (hface : N.rawRotation.SameFace d e)
    (hN : PreservesApexDarts r N.rawRotation u) :
    PreservesApexDarts r
      (insertedPlaneMap H u v N d e hne hmiss hd he hface).rawRotation u := by
  intro c x hc hcx
  obtain ⟨a, b, ha, hb, hab⟩ := hN c x hc hcx
  rcases insertedRotation_sameFace_cover H N.rawRotation u v d e hne hmiss hd he a b hab
      with h | h | h
  · exact ⟨augmentedDart H u v hne (Sum.inl a),
      augmentedDart H u v hne (Sum.inl b), ha, hb, h⟩
  · exact ⟨augmentedDart H u v hne (Sum.inl d),
      augmentedDart H u v hne (Sum.inl b), hd, hb, h⟩
  · exact ⟨augmentedDart H u v hne (Sum.inr false),
      augmentedDart H u v hne (Sum.inl b), rfl, hb, h⟩

variable (G) [DecidableRel G.Adj]

/-- A strengthened, actual fan construction: old apex-face darts and all
facial steps outside the attachment set are retained simultaneously. -/
theorem exists_retainedFanPlaneMap (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) :
    ∃ N : ConnectedPlaneMap (fanGraph G u S),
      PreservesApexDarts M.rawRotation N.rawRotation u ∧
        FaceStepsAgreeOff M.rawRotation N.rawRotation u S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨castPlaneMap (fanGraph_empty G u).symm M, ?_, ?_⟩
    · apply preservesApexDarts_cast M.rawRotation M u (fanGraph_empty G u).symm
      exact fun c x hc hcx => ⟨c, x, hc, rfl, hcx⟩
    · apply faceStepsAgreeOff_cast M.rawRotation M u ∅ (fanGraph_empty G u).symm
      intro d e hde _ _
      exact congrArg (fun x : G.Dart => (M.rawRotation.facePerm x).toProd)
        (Dart.ext e d hde)
  | @insert a S ha ih =>
    obtain ⟨N, hN, hsteps⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hca := hN.coFacial (hS a (Finset.mem_insert_self _ _))
    suffices ∃ N' : ConnectedPlaneMap (fanGraph G u S ⊔ edge u a),
        PreservesApexDarts M.rawRotation N'.rawRotation u ∧
          FaceStepsAgreeOff M.rawRotation N'.rawRotation u (insert a S) by
      obtain ⟨N', hN', hs'⟩ := this
      exact ⟨castPlaneMap (fanGraph_insert G u a S).symm N',
        preservesApexDarts_cast M.rawRotation N' u (fanGraph_insert G u a S).symm hN',
        faceStepsAgreeOff_cast M.rawRotation N' u (insert a S)
          (fanGraph_insert G u a S).symm hs'⟩
    have hsinsert : FaceStepsAgreeOff M.rawRotation N.rawRotation u (insert a S) := by
      intro d e hde hdu hdS
      exact hsteps d e hde hdu (fun hx => hdS (Finset.mem_insert_of_mem hx))
    by_cases hua : u = a
    · subst a
      have heq : fanGraph G u S ⊔ edge u u = fanGraph G u S := by simp
      exact ⟨castPlaneMap heq.symm N,
        preservesApexDarts_cast M.rawRotation N u heq.symm hN,
        faceStepsAgreeOff_cast M.rawRotation N u (insert u S) heq.symm hsinsert⟩
    · by_cases hadj : (fanGraph G u S).Adj u a
      · have heq : fanGraph G u S ⊔ edge u a = fanGraph G u S :=
          sup_eq_left.mpr ((edge_le_iff (fanGraph G u S)).mpr (Or.inr hadj))
        exact ⟨castPlaneMap heq.symm N,
          preservesApexDarts_cast M.rawRotation N u heq.symm hN,
          faceStepsAgreeOff_cast M.rawRotation N u (insert a S) heq.symm hsinsert⟩
      · obtain ⟨d, e, hd, he, hface⟩ := hca
        refine ⟨insertedPlaneMap (fanGraph G u S) u a N d e hua hadj hd he hface,
          preservesApexDarts_inserted M.rawRotation N u a d e hua hadj hd he hface hN, ?_⟩
        intro x y hy hxu hxS
        let z : (fanGraph G u S).Dart := ⟨x.toProd, Or.inl x.adj⟩
        have hyz : y = augmentedDart (fanGraph G u S) u a hua (Sum.inl z) :=
          Dart.ext _ _ hy
        have hxa : x.snd ≠ a := fun hx => hxS (Finset.mem_insert.mpr (Or.inl hx))
        subst y
        change ((insertedRotation (fanGraph G u S) u a N.rawRotation d e hua hadj hd he).facePerm
          (augmentedDart (fanGraph G u S) u a hua (Sum.inl z))).toProd = _
        rw [insertedRotation_facePerm_old_of_target_ne (fanGraph G u S) N.rawRotation u a
          d e hua hadj hd he z hxu hxa]
        exact hsteps x z rfl hxu (fun hx => hxS (Finset.mem_insert_of_mem hx))

/-- The actual fan map selected together with its retained-arc certificate. -/
noncomputable def retainedFanPlaneMap (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) : ConnectedPlaneMap (fanGraph G u S) :=
  (exists_retainedFanPlaneMap G M u S hS).choose

/-- Actual old darts embedded into the exact fan graph. -/
def oldFanDart (u : V) (S : Finset V) (d : G.Dart) : (fanGraph G u S).Dart :=
  ⟨d.toProd, Or.inl d.adj⟩

/-- The retained fan agrees exactly with each old facial step outside its
endpoint set. -/
theorem retainedFanPlaneMap_facePerm_old (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) (d : G.Dart)
    (hdu : d.snd ≠ u) (hdS : d.snd ∉ S) :
    (retainedFanPlaneMap G M u S hS).rawRotation.facePerm (oldFanDart G u S d) =
      oldFanDart G u S (M.rawRotation.facePerm d) := by
  apply Dart.ext
  exact (exists_retainedFanPlaneMap G M u S hS).choose_spec.2 d (oldFanDart G u S d)
    rfl hdu hdS

/-- Literal old facial iterates are retained along an attachment-free arc. -/
theorem retainedFanPlaneMap_facePerm_pow_old (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) (d : G.Dart) (n : ℕ)
    (havoid : ∀ i < n, ((M.rawRotation.facePerm ^ i) d).snd ≠ u ∧
      ((M.rawRotation.facePerm ^ i) d).snd ∉ S) :
    ((retainedFanPlaneMap G M u S hS).rawRotation.facePerm ^ n) (oldFanDart G u S d) =
      oldFanDart G u S ((M.rawRotation.facePerm ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply, ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))]
    have hn := havoid n (Nat.lt_succ_self n)
    simpa only [pow_succ', mul_apply] using
      retainedFanPlaneMap_facePerm_old G M u S hS ((M.rawRotation.facePerm ^ n) d) hn.1 hn.2

/-- Every retained old apex-face dart has a literal same-face apex witness
in the constructed fan. -/
theorem retainedFanPlaneMap_apex_dart (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) (c d : G.Dart)
    (hc : c.fst = u) (hcd : M.rawRotation.SameFace c d) :
    ∃ a : (fanGraph G u S).Dart, a.fst = u ∧
      (retainedFanPlaneMap G M u S hS).rawRotation.SameFace a (oldFanDart G u S d) := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (exists_retainedFanPlaneMap G M u S hS).choose_spec.1 c d hc hcd
  exact ⟨a, ha, (Dart.ext b (oldFanDart G u S d) hb) ▸ hab⟩

/-- One and the same new apex-face contains every vertex of a guarded old
arc, including the final target vertex even if that target is an attachment.
This is the retained-gap certificate for inserting a second fan. -/
theorem retainedFanPlaneMap_commonFace_arc (M : ConnectedPlaneMap G) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) (c d : G.Dart)
    (hc : c.fst = u) (hcd : M.rawRotation.SameFace c d) (n : ℕ)
    (havoid : ∀ i < n, ((M.rawRotation.facePerm ^ i) d).snd ≠ u ∧
      ((M.rawRotation.facePerm ^ i) d).snd ∉ S) :
    ∃ a : (fanGraph G u S).Dart, a.fst = u ∧
      ∀ i ≤ n, ∃ b t : (fanGraph G u S).Dart,
        b.fst = ((M.rawRotation.facePerm ^ i) d).fst ∧
        t.fst = ((M.rawRotation.facePerm ^ i) d).snd ∧
        (retainedFanPlaneMap G M u S hS).rawRotation.SameFace a b ∧
        (retainedFanPlaneMap G M u S hS).rawRotation.SameFace a t := by
  obtain ⟨a, ha, had⟩ := retainedFanPlaneMap_apex_dart G M u S hS c d hc hcd
  refine ⟨a, ha, ?_⟩
  intro i hi
  let r := (retainedFanPlaneMap G M u S hS).rawRotation
  let b := oldFanDart G u S ((M.rawRotation.facePerm ^ i) d)
  have hab : r.SameFace a b := by
    have hpow := retainedFanPlaneMap_facePerm_pow_old G M u S hS d i
      (fun j hj => havoid j (Nat.lt_of_lt_of_le hj hi))
    change r.facePerm.SameCycle a (oldFanDart G u S ((M.rawRotation.facePerm ^ i) d))
    rw [← hpow]
    exact Equiv.Perm.SameCycle.pow_right had
  exact ⟨b, r.facePerm b, rfl, r.facePerm_source b, hab,
    Equiv.Perm.SameCycle.apply_right hab⟩

#print axioms exists_retainedFanPlaneMap
#print axioms retainedFanPlaneMap_commonFace_arc

end PlaneTopology.PlaneFanArcRetention
