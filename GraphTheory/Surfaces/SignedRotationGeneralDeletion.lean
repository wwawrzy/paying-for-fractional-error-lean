import GraphTheory.Surfaces.SignedRotationPartitionGenus
import GraphTheory.Surfaces.SignedRotationConnectedDeletion
import GraphTheory.Surfaces.SignedRotationRestriction
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem component_deletion_witness (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (c : (G ⊔ edge u v).ConnectedComponent)
    (hu : u ∈ c.supp) (hv : v ∈ c.supp) :
    ∃ s : SignedRotation (G.induce c.supp), s.eulerGenus ≤ (r.restrictComponent c).eulerGenus := by
  classical
  let u' : c.supp := ⟨u,hu⟩
  let v' : c.supp := ⟨v,hv⟩
  have he : (G ⊔ edge u v).induce c.supp = G.induce c.supp ⊔ edge u' v' := by
    ext x y
    change (G.Adj x.val y.val ∨ (edge u v).Adj x.val y.val) ↔
      (G.Adj x.val y.val ∨ (edge u' v').Adj x y)
    simp only [edge_adj, Subtype.ext_iff]
    change (G.Adj x.val y.val ∨ (x.val = u ∧ y.val = v ∨ x.val = v ∧ y.val = u) ∧ x.val ≠ y.val) ↔ _
    simp only [ne_eq, Subtype.ext_iff]
    rfl
  let r' : SignedRotation (G.induce c.supp ⊔ edge u' v') := he ▸ r.restrictComponent c
  have hg : r'.eulerGenus = (r.restrictComponent c).eulerGenus :=
    eulerGenus_transport he (r.restrictComponent c)
  have hc : (G.induce c.supp ⊔ edge u' v').Connected := he ▸ c.connected_toSimpleGraph
  have hn : u' ≠ v' := fun h => hne (congrArg Subtype.val h)
  obtain ⟨s,hs⟩ := exists_deletion_genus_le_of_connected (G.induce c.supp) u' v' hn hmiss r' hc
  exact ⟨s,hs.trans_eq hg⟩
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem exists_deletion_genus_le (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) :
    ∃ s : SignedRotation G, s.eulerGenus ≤ r.eulerGenus := by
  classical
  let H := G ⊔ edge u v
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have huv : H.Adj u v := by
    right
    simp [edge_adj,hne]
  have hl (c : H.ConnectedComponent) :
      ∃ s : SignedRotation (G.induce c.supp), s.eulerGenus ≤ (r.restrictComponent c).eulerGenus := by
    by_cases hu : u ∈ c.supp
    · have hv := c.mem_supp_of_adj_mem_supp hu huv
      exact component_deletion_witness G u v hne hmiss r c hu hv
    · have hv : v ∉ c.supp := fun hv => hu (c.mem_supp_of_adj_mem_supp hv huv.symm)
      have he : H.induce c.supp = G.induce c.supp := by
        ext x y
        change (G.Adj x.val y.val ∨ (edge u v).Adj x.val y.val) ↔ G.Adj x.val y.val
        have hxu : x.val ≠ u := fun h => hu (h ▸ x.property)
        have hxv : x.val ≠ v := fun h => hv (h ▸ x.property)
        simp only [edge_adj,hxu,hxv,false_and,false_or]
        simp
      let s : SignedRotation (G.induce c.supp) := he ▸ r.restrictComponent c
      exact ⟨s,le_of_eq (eulerGenus_transport he (r.restrictComponent c))⟩
  choose s hs using hl
  refine ⟨partition_assemble H (le_sup_left : G ≤ H) s, ?_⟩
  rw [partition_assemble_genus]
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hs c)
  have he := r.eulerGenus_sum
  exact hsum.trans_eq he.symm
end SimpleGraph.SignedRotation
