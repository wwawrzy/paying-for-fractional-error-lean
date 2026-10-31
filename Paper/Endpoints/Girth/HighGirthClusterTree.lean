import Paper.Endpoints.Girth.HighGirthClusterSize
import Paper.Endpoints.Girth.HighGirthRadiusTree

/-! Genuine bounded-radius induced trees from the separated-center construction
of fv:hg:dilute. Contraction and uniqueness of edges between clusters remain
separate obligations. -/
namespace Paper.HighGirthClusterTree
open HighGirthVoronoi
variable {V : Type} [LinearOrder V]

set_option backward.isDefEq.respectTransparency false in
theorem induced_radius (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R) (c : V) (hc : c ∈ C)
    (v : {v | owner G C hC v = c}) :
    (G.induce {v | owner G C hC v = c}).dist v
      ⟨c,owner_center G hconn C hC c hc⟩ ≤ R := by
  obtain ⟨p,hp,hs⟩ := cluster_walk G hconn C hC c hc v.val v.property
  have hlen : (p.induce {v | owner G C hC v = c} hs).length = p.length := by
    have hh := congrArg SimpleGraph.Walk.length (p.map_induce hs)
    simpa only [SimpleGraph.Walk.length_map] using hh
  have hh := (G.induce {v | owner G C hC v = c}).dist_le
    (p.induce {v | owner G C hC v = c} hs)
  rw [hlen,hp] at hh
  have hr := owner_radius G C hC R hcover v.val
  rw [v.property] at hr
  exact hh.trans hr

set_option backward.isDefEq.respectTransparency false in
theorem induced_tree (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 2*R+1 < p.length)
    (c : V) (hc : c ∈ C) : (G.induce {v | owner G C hC v = c}).IsTree := by
  have hcluster := cluster_connected G hconn C hC c hc
  refine ⟨hcluster,?_⟩
  apply HighGirthRadiusTree.acyclic_of_radius_girth _ hcluster
    ⟨c,owner_center G hconn C hC c hc⟩ R
  · exact induced_radius G hconn C hC R hcover c hc
  · intro v p hp
    have hcycle := hp.map (f := (SimpleGraph.Embedding.induce _).toHom) Subtype.val_injective
    have hh := hgirth v.val (p.map (SimpleGraph.Embedding.induce _).toHom) hcycle
    simpa only [SimpleGraph.Walk.length_map] using hh

end Paper.HighGirthClusterTree
#print axioms Paper.HighGirthClusterTree.induced_radius
#print axioms Paper.HighGirthClusterTree.induced_tree
