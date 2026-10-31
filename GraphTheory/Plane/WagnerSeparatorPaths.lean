import GraphTheory.Plane.WagnerSeparatorMinor
import GraphTheory.SimpleGraph.Connectivity.Whitney

/-!
# Actual paths through the other side of a two-vertex separator

Connectivity after deleting either separator vertex forces every nonempty
closed outside branch to touch the other separator vertex. A connected such
branch then gives a genuine path with no retained-side internal vertex.
-/

namespace PlaneTopology.WagnerSeparatorPaths

open SimpleGraph PlaneTopology.WagnerSeparatorMinor

variable {V : Type*} (G : SimpleGraph V)

/-- Any actual outside walk can first be shortened to a simple path without
introducing any new vertex, then contracted to the filled-side minor. -/
theorem filledSide_minor_of_outsideWalk (A : Set V) (u v : A) (hne : u ≠ v)
    (p : G.Walk u.val v.val)
    (hout : ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val) :
    ((G.induce A) ⊔ edge u v) ≤m G := by
  classical
  exact filledSide_minor_of_outsidePath G A u v hne p.toPath p.toPath.property
    (fun z hz hzA => hout z (p.support_toPath_subset hz) hzA)

/-- Two actual attachment edges joined by a walk in the complement of A
produce a genuine simple u-v path whose internal vertices avoid A. -/
theorem exists_outsidePath_of_reachable (A : Set V) (u v : A) (x y : (Aᶜ : Set V))
    (hux : G.Adj u.val x.val) (hyv : G.Adj y.val v.val)
    (hxy : (G.induce Aᶜ).Reachable x y) :
    ∃ p : G.Walk u.val v.val, p.IsPath ∧
      ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val := by
  classical
  obtain ⟨q⟩ := hxy
  let f : (G.induce Aᶜ) →g G :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let p : G.Walk u.val v.val := (Walk.cons hux (q.map f)).concat hyv
  have hmapout (z : V) (hz : z ∈ (q.map f).support) : z ∉ A := by
    rw [Walk.support_map] at hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact w.property
  refine ⟨p.toPath, p.toPath.property, ?_⟩
  intro z hz hzA
  have hz' := p.support_toPath_subset hz
  simp only [p, Walk.support_concat, List.concat_eq_append, List.mem_append,
    Walk.support_cons, List.mem_cons, List.not_mem_nil, or_false] at hz'
  rcases hz' with (hzu | hzq) | hzv
  · exact Or.inl hzu
  · exact (hmapout z hzq hzA).elim
  · exact Or.inr hzv

/-- A connected nonempty outside set touching both separator vertices
supplies the exact outside path needed by the branch-set minor constructor. -/
theorem exists_outsidePath_of_connected_branch (A : Set V) (u v : A) (S : Set V)
    (hSA : S ⊆ Aᶜ) (hconn : (G.induce S).Connected)
    (hu : ∃ x ∈ S, G.Adj u.val x) (hv : ∃ y ∈ S, G.Adj v.val y) :
    ∃ p : G.Walk u.val v.val, p.IsPath ∧
      ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val := by
  obtain ⟨x, hxS, hux⟩ := hu
  obtain ⟨y, hyS, hvy⟩ := hv
  let f : (G.induce S) →g (G.induce Aᶜ) :=
    { toFun := fun z => ⟨z.val, hSA z.property⟩, map_rel' := fun h => h }
  exact exists_outsidePath_of_reachable G A u v ⟨x, hSA hxS⟩ ⟨y, hSA hyS⟩
    hux hvy.symm ((hconn.preconnected ⟨x, hxS⟩ ⟨y, hyS⟩).map f)

/-- The actual vertex set in G of a component after deleting u and v. -/
def separatorComponentSet (u v : V)
    (C : (G.induce {w | w ≠ u ∧ w ≠ v}).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

/-- The actual component's vertex set really induces a connected graph in G. -/
theorem separatorComponentSet_connected (u v : V)
    (C : (G.induce {w | w ≠ u ∧ w ≠ v}).ConnectedComponent) :
    (G.induce (separatorComponentSet G u v C)).Connected := by
  let f : C.toSimpleGraph →g (G.induce (separatorComponentSet G u v C)) :=
    { toFun := fun z => ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
      map_rel' := fun h => h }
  have hf : Function.Surjective f := by
    rintro ⟨z, w, hwC, rfl⟩
    exact ⟨⟨w, hwC⟩, rfl⟩
  exact Connected.map f hf C.connected_toSimpleGraph

/-- No edge leaves a component of G-{u,v} except through u or v. -/
theorem separatorComponentSet_boundary (u v : V)
    (C : (G.induce {w | w ≠ u ∧ w ≠ v}).ConnectedComponent) :
    ∀ x ∈ separatorComponentSet G u v C,
      ∀ y ∉ separatorComponentSet G u v C, G.Adj x y → y = u ∨ y = v := by
  intro x hx y hy hadj
  obtain ⟨w, hwC, rfl⟩ := hx
  by_cases hyu : y = u
  · exact Or.inl hyu
  · by_cases hyv : y = v
    · exact Or.inr hyv
    · exfalso
      apply hy
      exact ⟨⟨y, hyu, hyv⟩, C.mem_supp_of_adj_mem_supp hwC hadj, rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a two-connected graph a nonempty branch whose external neighborhood
is contained in {u,v} must really have a neighbor at u. Delete v and inspect
the first dart of an actual walk leaving the branch. -/
theorem two_connected_neighbor_in_branch (h2 : G.IsKConnected 2)
    (u v : V) (hne : u ≠ v) (S : Set V) (hS : S.Nonempty)
    (huS : u ∉ S) (hvS : v ∉ S)
    (hboundary : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → y = u ∨ y = v) :
    ∃ x ∈ S, G.Adj u x := by
  haveI : Nontrivial V := ⟨⟨u, v, hne⟩⟩
  have hconn := SimpleGraph.IsKConnected.no_cut_vertex G h2 v
  have heq : ((Finset.univ \ {v} : Finset V) : Set V) = {z | z ≠ v} := by
    ext z
    simp
  rw [heq] at hconn
  obtain ⟨w, hwS⟩ := hS
  have hwv : w ≠ v := fun h => hvS (h ▸ hwS)
  obtain ⟨p⟩ := hconn.preconnected ⟨w, hwv⟩ ⟨u, hne⟩
  obtain ⟨d, _, hdS, hdnot⟩ := p.exists_boundary_dart {z | z.val ∈ S} hwS huS
  have hadj : G.Adj d.fst.val d.snd.val := d.adj
  have hdu : d.snd.val = u := by
    rcases hboundary d.fst.val hdS d.snd.val hdnot hadj with h | h
    · exact h
    · exact (d.snd.property h).elim
  exact ⟨d.fst.val, hdS, hdu ▸ hadj.symm⟩

/-- A genuine connected outside branch of a two-vertex separator gives
an actual simple outside path in any two-connected graph. -/
theorem exists_outsidePath_of_two_connected_branch (h2 : G.IsKConnected 2)
    (A : Set V) (u v : A) (hne : u ≠ v) (S : Set V)
    (hSA : S ⊆ Aᶜ) (hconn : (G.induce S).Connected)
    (hboundary : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → y = u.val ∨ y = v.val) :
    ∃ p : G.Walk u.val v.val, p.IsPath ∧
      ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val := by
  have hS : S.Nonempty := by
    obtain ⟨w⟩ := hconn.nonempty
    exact ⟨w.val, w.property⟩
  have huv : u.val ≠ v.val := fun h => hne (Subtype.ext h)
  have huS : u.val ∉ S := fun h => hSA h u.property
  have hvS : v.val ∉ S := fun h => hSA h v.property
  have hu := two_connected_neighbor_in_branch G h2 u.val v.val huv S hS huS hvS hboundary
  have hv := two_connected_neighbor_in_branch G h2 v.val u.val huv.symm S hS hvS huS
    (fun x hx y hy hadj => (hboundary x hx y hy hadj).symm)
  exact exists_outsidePath_of_connected_branch G A u v S hSA hconn hu hv

/-- The planar two-connected graph's genuinely filled separator side is
planar whenever the other side contains a connected separator branch. -/
theorem filledSide_isPlanar_of_two_connected_branch (hG : G.IsPlanar)
    (h2 : G.IsKConnected 2) (A : Set V) (u v : A) (hne : u ≠ v) (S : Set V)
    (hSA : S ⊆ Aᶜ) (hconn : (G.induce S).Connected)
    (hboundary : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → y = u.val ∨ y = v.val) :
    ((G.induce A) ⊔ edge u v).IsPlanar := by
  obtain ⟨p, hp, hout⟩ := exists_outsidePath_of_two_connected_branch G h2 A u v hne
    S hSA hconn hboundary
  exact filledSide_isPlanar_of_outsidePath G hG A u v hne p hp hout

/-- A real component on the other side of a two-vertex separator supplies
all branch hypotheses; hence the filled retained side is genuinely planar. -/
theorem filledSide_isPlanar_of_outside_component (hG : G.IsPlanar)
    (h2 : G.IsKConnected 2) (A : Set V) (u v : A) (hne : u ≠ v)
    (C : (G.induce {w | w ≠ u.val ∧ w ≠ v.val}).ConnectedComponent)
    (hCA : separatorComponentSet G u.val v.val C ⊆ Aᶜ) :
    ((G.induce A) ⊔ edge u v).IsPlanar :=
  filledSide_isPlanar_of_two_connected_branch G hG h2 A u v hne _ hCA
    (separatorComponentSet_connected G u.val v.val C)
    (separatorComponentSet_boundary G u.val v.val C)

#print axioms exists_outsidePath_of_reachable
#print axioms two_connected_neighbor_in_branch
#print axioms filledSide_isPlanar_of_two_connected_branch
#print axioms filledSide_isPlanar_of_outside_component

end PlaneTopology.WagnerSeparatorPaths
