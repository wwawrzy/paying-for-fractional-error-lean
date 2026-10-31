import GraphTheory.SimpleGraph.Treewidth.Defs
import GraphTheory.SimpleGraph.Minor.Defs

/-! Transport a physical walk through a tree decomposition. This proves
connectedness of all bag unions associated with an actual minor branch set. -/
namespace Paper.TreeDecompositionRoutes
open SimpleGraph
variable {V I : Type*} {G : SimpleGraph V} {T : SimpleGraph I}
variable (D : G.TreeDecomposition T)

theorem lift_walk {u v : V} (p : G.Walk u v) (i j : I) (hu : u ∈ D.bag i) (hv : v ∈ D.bag j) :
    ∃ q : T.Walk i j, ∀ r ∈ q.support, ∃ w ∈ p.support, w ∈ D.bag r := by
  classical
  induction p generalizing i j with
  | @nil u =>
    obtain ⟨q, hq, _⟩ := D.isTree.existsUnique_path i j
    refine ⟨q, fun r hr => ⟨u, by simp only [Walk.support_nil, List.mem_singleton], ?_⟩⟩
    exact D.bag_connected _ q hq hu hv hr
  | @cons u v w h p ih =>
    obtain ⟨b, hub, hvb⟩ := D.edge_mem h
    obtain ⟨q₁, hq₁, _⟩ := D.isTree.existsUnique_path i b
    obtain ⟨q₂, hq₂⟩ := ih b j hvb hv
    refine ⟨q₁.append q₂, ?_⟩
    intro r hr
    rw [Walk.mem_support_append_iff] at hr
    rcases hr with hr | hr
    · exact ⟨u, by simp only [Walk.support_cons, List.mem_cons, true_or],
        D.bag_connected u q₁ hq₁ hu hub hr⟩
    · obtain ⟨z, hz, hzr⟩ := hq₂ r hr
      exact ⟨z, by simpa only [Walk.support_cons, List.mem_cons] using Or.inr hz, hzr⟩

theorem connected_bag_union (S : Set V) (hS : (G.induce S).Connected) {i j : I}
    (hi : ∃ u ∈ S, u ∈ D.bag i) (hj : ∃ v ∈ S, v ∈ D.bag j)
    (p : T.Walk i j) (hp : p.IsPath) {r : I} (hr : r ∈ p.support) :
    ∃ w ∈ S, w ∈ D.bag r := by
  classical
  obtain ⟨u, huS, hui⟩ := hi
  obtain ⟨v, hvS, hvj⟩ := hj
  let e : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  let physical := (hS.preconnected ⟨u, huS⟩ ⟨v, hvS⟩).some
  obtain ⟨q, hq⟩ := lift_walk D (physical.map e) i j hui hvj
  have he : p = (q.toPath : T.Walk i j) :=
    congrArg Subtype.val (D.isTree.isAcyclic.path_unique ⟨p, hp⟩ q.toPath)
  have hrq : r ∈ q.support := q.support_toPath_subset (he ▸ hr)
  obtain ⟨w, hw, hwr⟩ := hq r hrq
  have hm : w ∈ physical.support.map e := by simpa only [Walk.support_map] using hw
  obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hm
  exact ⟨w, hzw ▸ z.property, hwr⟩

end Paper.TreeDecompositionRoutes
