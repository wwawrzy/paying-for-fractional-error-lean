import GraphTheory.Plane.PlaneChordFaces

/-!
# Actual fan insertion into a connected plane map

Each missing edge from an apex is inserted inside an actual face. The face
may split, but both resulting faces contain the apex, so all remaining
target vertices retain a real cofacial witness. No ordering hypothesis or
assumed embedding provider is needed for a single fan.
-/

namespace PlaneTopology.PlaneFanInsertion

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneChordFaces
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneLeafInsertion

variable {V : Type*} (G : SimpleGraph V) (u : V)

/-- Add all edges from `u` to the specified finite target set. -/
def fanGraph (S : Finset V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b ∈ S)

instance fanGraphDecidableRel [DecidableEq V] [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (fanGraph G u S).Adj := by
  unfold fanGraph
  infer_instance

/-- The empty fan changes no edge. -/
theorem fanGraph_empty : fanGraph G u ∅ = G := by
  ext a b
  simp [fanGraph, SimpleGraph.fromRel_adj]

/-- A fan grows by adding exactly one endpoint edge. -/
theorem fanGraph_insert [DecidableEq V] (a : V) (S : Finset V) :
    fanGraph G u (insert a S) = fanGraph G u S ⊔ edge u a := by
  ext x y
  simp only [fanGraph, sup_adj, fromRel_adj, edge_adj, Finset.mem_insert]
  tauto

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Transport an actual map across graph equality, explicitly identifying
the subsingleton adjacency-decision instances. -/
noncomputable def castPlaneMap {H K : SimpleGraph V}
    [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (h : H = K) (M : ConnectedPlaneMap H) : ConnectedPlaneMap K := by
  subst K
  cases Subsingleton.elim dK dH
  exact M

/-- Equality transport preserves actual cofacial vertex witnesses. -/
theorem castPlaneMap_coFacial {H K : SimpleGraph V}
    [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (h : H = K) (M : ConnectedPlaneMap H) (a b : V)
    (hab : CoFacial H M.rawRotation a b) :
    CoFacial K (castPlaneMap h M).rawRotation a b := by
  subst K
  cases Subsingleton.elim dK dH
  exact hab

/-- Construct the actual plane map with all fan edges, preserving every
old cofacial incidence with the apex for later insertions. -/
theorem exists_fanPlaneMap (M : ConnectedPlaneMap G) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) :
    ∃ M' : ConnectedPlaneMap (fanGraph G u S),
      ∀ x, CoFacial G M.rawRotation u x →
        CoFacial (fanGraph G u S) M'.rawRotation u x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨castPlaneMap (fanGraph_empty G u).symm M,
      fun x hx => castPlaneMap_coFacial (fanGraph_empty G u).symm M u x hx⟩
  | @insert a S ha ih =>
    obtain ⟨N, hN⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hca := hN a (hS a (Finset.mem_insert_self _ _))
    suffices ∃ N' : ConnectedPlaneMap (fanGraph G u S ⊔ edge u a),
        ∀ x, CoFacial G M.rawRotation u x →
          CoFacial (fanGraph G u S ⊔ edge u a) N'.rawRotation u x by
      obtain ⟨N', hN'⟩ := this
      exact ⟨castPlaneMap (fanGraph_insert G u a S).symm N',
        fun x hx => castPlaneMap_coFacial (fanGraph_insert G u a S).symm N' u x (hN' x hx)⟩
    by_cases hua : u = a
    · subst a
      have heq : fanGraph G u S ⊔ edge u u = fanGraph G u S := by simp
      exact ⟨castPlaneMap heq.symm N,
        fun x hx => castPlaneMap_coFacial heq.symm N u x (hN x hx)⟩
    · by_cases hadj : (fanGraph G u S).Adj u a
      · have heq : fanGraph G u S ⊔ edge u a = fanGraph G u S := by
          apply sup_eq_left.mpr
          intro x y hxy
          rcases (edge_adj u a x y).mp hxy with ⟨h | h, _⟩
          · simpa only [h.1, h.2] using hadj
          · simpa only [h.1, h.2] using hadj.symm
        exact ⟨castPlaneMap heq.symm N,
          fun x hx => castPlaneMap_coFacial heq.symm N u x (hN x hx)⟩
      · obtain ⟨d, e, hd, he, hface⟩ := hca
        refine ⟨insertedPlaneMap (fanGraph G u S) u a N d e hua hadj hd he hface, ?_⟩
        intro x hx
        exact coFacial_insertedRotation (fanGraph G u S) N.rawRotation u a d e
          hua hadj hd he x (hN x hx)

/-- The chosen fan map is constructed by the verified finite edge induction. -/
noncomputable def fanPlaneMap (M : ConnectedPlaneMap G) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) :
    ConnectedPlaneMap (fanGraph G u S) :=
  (exists_fanPlaneMap G u M S hS).choose

/-- The chosen fan map retains each old cofacial incidence with its apex. -/
theorem fanPlaneMap_coFacial (M : ConnectedPlaneMap G) (S : Finset V)
    (hS : ∀ x ∈ S, CoFacial G M.rawRotation u x) (x : V)
    (hx : CoFacial G M.rawRotation u x) :
    CoFacial (fanGraph G u S) (fanPlaneMap G u M S hS).rawRotation u x :=
  (exists_fanPlaneMap G u M S hS).choose_spec x hx

/-- Add a fresh apex on `Option V` adjacent to exactly the targets `S`. -/
def apexGraph (S : Finset V) : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False
  symm := by intro a b hab; cases a <;> cases b <;> first | exact hab | exact hab.symm
  loopless := ⟨by intro a; cases a <;> simp⟩

instance apexGraphDecidableRel (S : Finset V) :
    DecidableRel (apexGraph G S).Adj :=
  fun a b => by cases a <;> cases b <;> unfold apexGraph <;> infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- Leaf insertion followed by all apex spokes is exactly the desired apex
graph, with no auxiliary edge left over. -/
theorem fan_leafGraph_eq_apexGraph (S : Finset V) (v : V) (hv : v ∈ S) :
    fanGraph (leafGraph G v) none (S.image some) = apexGraph G S := by
  ext a b
  cases a <;> cases b <;>
    simp [fanGraph, apexGraph, leafGraph, fromRel_adj] <;> aesop

/-- Insert a fresh apex adjacent to any nonempty finite set of vertices on
one actual face. The old face need not have a simple boundary. -/
theorem exists_apexPlaneMap (M : ConnectedPlaneMap G) (S : Finset V)
    (v : V) (hv : v ∈ S) (d : G.Dart) (hd : d.fst = v)
    (hS : ∀ x ∈ S, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace d e) :
    Nonempty (ConnectedPlaneMap (apexGraph G S)) := by
  classical
  let L := leafPlaneMapAt G v M d hd
  have hco (x : Option V) (hx : x ∈ S.image some) :
      CoFacial (leafGraph G v) L.rawRotation none x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he, hface⟩ := hS y hy
    refine ⟨leafDart G v (Sum.inr true), leafDart G v (Sum.inl e), rfl, ?_, ?_⟩
    · exact congrArg some he
    · exact leafRotation_sameFace_leaf G v M.rawRotation d hd e hface
  have h := (exists_fanPlaneMap (leafGraph G v) none L (S.image some) hco).choose
  exact ⟨castPlaneMap (fan_leafGraph_eq_apexGraph G S v hv) h⟩

/-- A chosen actual plane map with the fresh apex and precisely its requested
spokes. This is a construction, not an assumed fan provider. -/
noncomputable def apexPlaneMap (M : ConnectedPlaneMap G) (S : Finset V)
    (v : V) (hv : v ∈ S) (d : G.Dart) (hd : d.fst = v)
    (hS : ∀ x ∈ S, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace d e) :
    ConnectedPlaneMap (apexGraph G S) :=
  (exists_apexPlaneMap G M S v hv d hd hS).some

#print axioms exists_fanPlaneMap
#print axioms apexPlaneMap

end PlaneTopology.PlaneFanInsertion
