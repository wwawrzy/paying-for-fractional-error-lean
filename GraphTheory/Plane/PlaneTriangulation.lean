import GraphTheory.Plane.PlaneTriangulationCrossing
import GraphTheory.Plane.TriangularFaces

/-!
# Triangulating an actual connected sphere map on the same vertices

Finite maximal extension adds actual cofacial edges. Triangle face potentials
exclude faces longer than three, and faithfulness plus connectedness excludes
two-dart faces once there are at least three vertices. Thus no saturation or
geometric-existence premise is added to the supplied map.
-/

namespace PlaneTopology.PlaneTriangulation

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap TriangularFaces
open PlaneTopology.PlaneTriangulationMaximal PlaneTopology.PlaneTriangulationCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A fixed dart in a faithful vertex rotation is the only outgoing dart there. -/
theorem eq_of_source_eq_of_sigma_fixed (M : ConnectedPlaneMap G) (d : G.Dart)
    (hfixed : M.rawRotation.σ d = d) (e : G.Dart) (hsource : e.fst = d.fst) : e = d := by
  obtain ⟨n, hn⟩ := M.vertexDarts_sameCycle hsource.symm
  have hfix : (M.rawRotation.σ ^ n) d = d := Function.IsFixedPt.perm_zpow hfixed n
  exact hn.symm.trans hfix

/-- A two-dart face in a connected faithful sphere map forces the whole graph
to consist of the two endpoints of that edge. -/
theorem card_le_two_of_facePerm_twice (M : ConnectedPlaneMap G) (d : G.Dart)
    (htwo : M.rawRotation.facePerm (M.rawRotation.facePerm d) = d) :
    Fintype.card V ≤ 2 := by
  have hreverse : M.rawRotation.facePerm d = d.symm := by
    apply Dart.ext
    apply Prod.ext
    · exact M.rawRotation.facePerm_source d
    · have h := congrArg (fun x : G.Dart ↦ x.fst) htwo
      simpa only [SimpleGraph.RotationSystem.facePerm_source] using h
  have hfixed : M.rawRotation.σ d = d := by
    have h := htwo
    rw [hreverse] at h
    simpa only [SimpleGraph.RotationSystem.facePerm_apply, Dart.symm_symm] using h
  have hfixed' : M.rawRotation.σ d.symm = d.symm := by
    simpa only [SimpleGraph.RotationSystem.facePerm_apply] using hreverse
  have ha : ∀ x, G.Adj d.fst x → x = d.snd := by
    intro x hx
    exact congrArg (fun e : G.Dart ↦ e.snd)
      (eq_of_source_eq_of_sigma_fixed M d hfixed ⟨(d.fst, x), hx⟩ rfl)
  have hb : ∀ x, G.Adj d.snd x → x = d.fst := by
    intro x hx
    exact congrArg (fun e : G.Dart ↦ e.snd)
      (eq_of_source_eq_of_sigma_fixed M d.symm hfixed' ⟨(d.snd, x), hx⟩ rfl)
  have hwalk : ∀ {u v : V} (p : G.Walk u v),
      u = d.fst ∨ u = d.snd → v = d.fst ∨ v = d.snd := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      rcases hu with rfl | rfl
      · exact Or.inr (ha v huv)
      · exact Or.inl (hb v huv)
  have hall : ∀ v : V, v = d.fst ∨ v = d.snd := by
    intro v
    obtain ⟨p⟩ := M.connected.preconnected d.fst v
    exact hwalk p (Or.inl rfl)
  have hsub : (Finset.univ : Finset V) ⊆ {d.fst, d.snd} := by
    intro v _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hall v
  have hcard := Finset.card_le_card hsub
  simpa [d.fst_ne_snd] using hcard

/-- Maximal actual plane maps have no face orbit longer than three. -/
theorem facePerm_twice_or_thrice_of_maximal (hmax : Maximal HasPlaneMap G)
    (M : ConnectedPlaneMap G) (d : G.Dart) :
    M.rawRotation.facePerm (M.rawRotation.facePerm d) = d ∨
      M.rawRotation.facePerm (M.rawRotation.facePerm (M.rawRotation.facePerm d)) = d := by
  let e := M.rawRotation.facePerm d
  let f := M.rawRotation.facePerm e
  let g := M.rawRotation.facePerm f
  have hde : M.rawRotation.SameFace d e :=
    Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl _ d)
  have hef : M.rawRotation.SameFace e f :=
    Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl _ e)
  have hfg : M.rawRotation.SameFace f g :=
    Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl _ f)
  have hdf := M.rawRotation.sameFace_equivalence.trans hde hef
  have heg := M.rawRotation.sameFace_equivalence.trans hef hfg
  have hdg := M.rawRotation.sameFace_equivalence.trans hde heg
  by_cases htwo : f = d
  · exact Or.inl htwo
  right
  by_contra hthree
  have hac : d.fst ≠ f.fst := by
    intro h
    exact htwo (eq_of_sameFace_of_source_eq_of_maximal hmax M d f hdf h).symm
  have hwa : g.fst ≠ d.fst := by
    intro h
    exact hthree (eq_of_sameFace_of_source_eq_of_maximal hmax M g d
      (M.rawRotation.sameFace_equivalence.symm hdg) h)
  have hwb : g.fst ≠ e.fst := by
    intro h
    have hge := eq_of_sameFace_of_source_eq_of_maximal hmax M g e
      (M.rawRotation.sameFace_equivalence.symm heg) h
    exact htwo (M.rawRotation.facePerm.injective hge)
  have hwc : g.fst ≠ f.fst := by
    change (M.rawRotation.facePerm f).fst ≠ f.fst
    rw [SimpleGraph.RotationSystem.facePerm_source]
    exact f.fst_ne_snd.symm
  have hab : G.Adj d.fst e.fst := by
    change G.Adj d.fst (M.rawRotation.facePerm d).fst
    rw [SimpleGraph.RotationSystem.facePerm_source]
    exact d.adj
  have hbc : G.Adj e.fst f.fst := by
    change G.Adj e.fst (M.rawRotation.facePerm e).fst
    rw [M.rawRotation.facePerm_source e]
    exact e.adj
  have hca : G.Adj f.fst d.fst :=
    adjacent_of_sameFace_of_maximal hmax M f d hac.symm
      (M.rawRotation.sameFace_equivalence.symm hdf)
  have hbw : G.Adj e.fst g.fst :=
    adjacent_of_sameFace_of_maximal hmax M e g hwb.symm heg
  have hdcanonical : (⟨(d.fst, e.fst), hab⟩ : G.Dart) = d := by
    apply Dart.ext
    exact Prod.ext rfl (M.rawRotation.facePerm_source d)
  have hecanonical : (⟨(e.fst, f.fst), hbc⟩ : G.Dart) = e := by
    apply Dart.ext
    exact Prod.ext rfl (M.rawRotation.facePerm_source e)
  apply no_fourth_neighbor_at_triangle_corner M hab hbc hca hbw hwa hwc
    (dw := g) (hdw := rfl)
  · have hrev : (⟨(e.fst, d.fst), hab.symm⟩ : G.Dart) = d.symm :=
      congrArg Dart.symm hdcanonical
    rw [hrev, hecanonical]
    rfl
  · rw [hecanonical]
    exact heg

/-- Every face in a maximal actual plane map is triangular once there are
at least three vertices. -/
theorem triangular_of_maximal (hmax : Maximal HasPlaneMap G)
    (M : ConnectedPlaneMap G) (hcard : 3 ≤ Fintype.card V) : Triangular M.rawRotation := by
  intro d
  rcases facePerm_twice_or_thrice_of_maximal hmax M d with htwo | hthree
  · have hle := card_le_two_of_facePerm_twice M d htwo
    omega
  · exact hthree

/-- An actual connected sphere map extends to an actual triangular sphere
map on the same vertex type, without saturation assumptions. -/
theorem hasTriangulatedSupergraph_of_connectedPlaneMap
    (M : ConnectedPlaneMap G) (hcard : 3 ≤ Fintype.card V) :
    TriangularFaces.HasTriangulatedSupergraph G := by
  classical
  obtain ⟨T, hGT, hmax⟩ := exists_maximal_plane_supergraph M
  obtain ⟨N⟩ := hmax.1
  exact ⟨T, hGT, N, triangular_of_maximal hmax N hcard⟩

#print axioms card_le_two_of_facePerm_twice
#print axioms triangular_of_maximal
#print axioms hasTriangulatedSupergraph_of_connectedPlaneMap

end PlaneTopology.PlaneTriangulation
