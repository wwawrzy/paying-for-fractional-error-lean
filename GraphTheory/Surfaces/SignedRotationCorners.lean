import GraphTheory.Surfaces.SignedRotationVertices

/-! At vertices of degree at least two, a corner joins distinct graph edges.
The two endpoint corners of an edge meet two further distinct edges. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)
  (hdeg : ∀ v, 2 ≤ G.degree v)

include hdeg

theorem rotation_ne_self (d : G.Dart) : r.σ d ≠ d := by
  intro hd
  have hc : 1 < (G.neighborFinset d.fst).card := by
    change 1 < G.degree d.fst
    have := hdeg d.fst
    omega
  obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne hc d.snd
  let e : G.Dart := ⟨(d.fst, w), (G.mem_neighborFinset d.fst w).mp hw⟩
  have he : d = e := (r.cyclic d e rfl).eq_of_left hd
  exact hne (congrArg (fun q : G.Dart => q.snd) he).symm

theorem inverse_rotation_ne_self (d : G.Dart) : r.σ.symm d ≠ d := by
  intro hd
  have he := congrArg r.σ hd
  simp only [Equiv.apply_symm_apply] at he
  exact r.rotation_ne_self hdeg d he.symm

theorem cornerFlip_dart_ne (x : Flag G) : (r.cornerFlip x).1 ≠ x.1 := by
  cases hb : x.2 <;> simp only [cornerFlip, hb, Bool.false_eq_true, if_false, if_true]
  · exact r.rotation_ne_self hdeg x.1
  · exact r.inverse_rotation_ne_self hdeg x.1

theorem cornerFlip_edge_ne (x : Flag G) : (r.cornerFlip x).1.edge ≠ x.1.edge := by
  intro h
  rcases (dart_edge_eq_iff _ _).mp h with hd | hd
  · exact r.cornerFlip_dart_ne hdeg x hd
  · exact x.1.fst_ne_snd ((r.cornerFlip_source x).symm.trans (congrArg (fun q : G.Dart => q.fst) hd))

theorem endpoint_corner_edges_ne (x : Flag G) :
    (r.cornerFlip x).1.edge ≠ (r.cornerFlip (r.edgeFlip x)).1.edge := by
  intro h
  have hu : (r.cornerFlip x).1.fst = x.1.fst := r.cornerFlip_source x
  have hv : (r.cornerFlip (r.edgeFlip x)).1.fst = x.1.snd :=
    r.cornerFlip_source (r.edgeFlip x)
  rcases (dart_edge_eq_iff _ _).mp h with he | he
  · exact x.1.fst_ne_snd (hu.symm.trans ((congrArg (fun q : G.Dart => q.fst) he).trans hv))
  · have hu' : (r.cornerFlip x).1.snd = x.1.snd := (congrArg (fun q : G.Dart => q.snd) he).trans hv
    apply r.cornerFlip_dart_ne hdeg x
    exact Dart.ext _ _ (Prod.ext hu hu')

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.rotation_ne_self
#print axioms SimpleGraph.SignedRotation.cornerFlip_edge_ne
#print axioms SimpleGraph.SignedRotation.endpoint_corner_edges_ne
