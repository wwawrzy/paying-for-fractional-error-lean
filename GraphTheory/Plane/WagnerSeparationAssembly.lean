import GraphTheory.Plane.PlaneSupergraphBasics
import GraphTheory.Plane.WagnerSideUnion
import GraphTheory.Plane.PlaneEdgeGluingTransport
import GraphTheory.Plane.PlanePointCover
import GraphTheory.Plane.PlaneDisjointCover
import GraphTheory.Plane.PlaneSingletonExtension

/-!
# Actual plane-supergraph assembly across small separators

All conclusions carry a constructed actual connected plane map. The inputs
are genuine smaller-side map witnesses, suitable for strong induction.
-/

namespace PlaneTopology.WagnerSeparationAssembly

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneTriangulationMaximal
  PlaneTopology.PlaneSupergraphBasics PlaneTopology.WagnerSideUnion

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Glue plane supergraphs of the two filled sides of a two-vertex separator. -/
theorem hasPlaneSupergraph_of_filled_sides (A B : Set V) (u v : V)
    (huA : u ∈ A) (hvA : v ∈ A) (huB : u ∈ B) (hvB : v ∈ B)
    (hne : u ≠ v) (hcover : A ∪ B = Set.univ) (hinter : A ∩ B = {u, v})
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (hA : by classical exact HasPlaneSupergraph ((G.induce A) ⊔ edge ⟨u, huA⟩ ⟨v, hvA⟩))
    (hB : by classical exact HasPlaneSupergraph ((G.induce B) ⊔ edge ⟨u, huB⟩ ⟨v, hvB⟩)) :
    HasPlaneSupergraph G := by
  classical
  obtain ⟨L, hL, hLM⟩ := hA
  obtain ⟨R, hR, hRM⟩ := hB
  obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty L).mp hLM
  obtain ⟨N⟩ := (hasPlaneMap_iff_nonempty R).mp hRM
  have hLedge : L.Adj ⟨u, huA⟩ ⟨v, hvA⟩ := by
    apply hL
    exact Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩,
      fun h => hne (congrArg Subtype.val h)⟩)
  have hRedge : R.Adj ⟨u, huB⟩ ⟨v, hvB⟩ := by
    apply hR
    exact Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩,
      fun h => hne (congrArg Subtype.val h)⟩)
  let P := PlaneTopology.PlaneEdgeGluingTransport.gluedPlaneMap A B u v huA hvA huB hvB
    hne hcover hinter L R M N hLedge hRedge
  exact ⟨L.map Subtype.val ⊔ R.map Subtype.val,
    original_le_sideUnion G A B hcover hcross L R (le_sup_left.trans hL) (le_sup_left.trans hR),
    hasPlaneMap_of_map P⟩

/-- Glue the actual smaller-side supergraphs along their one common vertex. -/
theorem hasPlaneSupergraph_of_point_sides (A B : Set V) (v : V)
    (hvA : v ∈ A) (hvB : v ∈ B)
    (hcover : A ∪ B = Set.univ) (hinter : A ∩ B = {v})
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (hA : by classical exact HasPlaneSupergraph (G.induce A))
    (hB : by classical exact HasPlaneSupergraph (G.induce B)) : HasPlaneSupergraph G := by
  classical
  obtain ⟨L, hL, hLM⟩ := hA
  obtain ⟨R, hR, hRM⟩ := hB
  obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty L).mp hLM
  obtain ⟨N⟩ := (hasPlaneMap_iff_nonempty R).mp hRM
  let P := PlaneTopology.PlanePointCover.coverPlaneMap A B L R v hvA hvB hcover hinter M N
  exact ⟨PlaneTopology.PlanePointCover.coverGraph L R,
    original_le_sideUnion G A B hcover hcross L R hL hR, hasPlaneMap_of_map P⟩

/-- Join two nontrivial disjoint sides by an actual bridge. -/
theorem hasPlaneSupergraph_of_disjoint_sides (A B : Set V)
    (hcover : A ∪ B = Set.univ) (hinter : A ∩ B = ∅)
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (hA : by classical exact HasPlaneSupergraph (G.induce A))
    (hB : by classical exact HasPlaneSupergraph (G.induce B)) : HasPlaneSupergraph G := by
  classical
  obtain ⟨L, hL, hLM⟩ := hA
  obtain ⟨R, hR, hRM⟩ := hB
  obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty L).mp hLM
  obtain ⟨N⟩ := (hasPlaneMap_iff_nonempty R).mp hRM
  apply PlaneTopology.PlaneDisjointCover.exists_plane_supergraph G A B hcover hinter ?_ L R M N hL hR
  intro a ha b hb
  have haB : a ∉ B := fun haB => (show a ∈ (∅ : Set V) from hinter ▸ ⟨ha, haB⟩)
  have hbA : b ∉ A := fun hbA => (show b ∈ (∅ : Set V) from hinter ▸ ⟨hbA, hb⟩)
  exact hcross a ⟨ha, haB⟩ b ⟨hb, hbA⟩

/-- A disjoint singleton side is attached as a genuine leaf of the other
side's plane supergraph; no nonexistent singleton plane map is requested. -/
theorem hasPlaneSupergraph_of_singleton_right (A B : Set V)
    (hcover : A ∪ B = Set.univ) (hinter : A ∩ B = ∅)
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (hBcard : Nat.card B = 1)
    (hA : by classical exact HasPlaneSupergraph (G.induce A)) : HasPlaneSupergraph G := by
  classical
  obtain ⟨b, hb, hcov, hno⟩ := singleton_right_of_separation G A B hcover hinter hcross hBcard
  obtain ⟨L, hL, hLM⟩ := hA
  obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty L).mp hLM
  exact PlaneTopology.PlaneSingletonExtension.exists_plane_supergraph G A b hb hcov hno L M hL

#print axioms hasPlaneSupergraph_of_filled_sides
#print axioms hasPlaneSupergraph_of_point_sides
#print axioms hasPlaneSupergraph_of_disjoint_sides
#print axioms hasPlaneSupergraph_of_singleton_right

end PlaneTopology.WagnerSeparationAssembly
