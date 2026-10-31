import GraphTheory.Surfaces.SignedRotationPartitionAssembly
import GraphTheory.Surfaces.SignedRotationPartitionFaces
import GraphTheory.Surfaces.SignedRotationPartitionComponents
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (hGH : G ≤ H)
variable (r : SignedRotation G) [Fintype H.ConnectedComponent]
theorem partition_eulerGenus_sum :
    r.eulerGenus = ∑ c : H.ConnectedComponent,
      (r.restrictClosed c.supp
        (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).eulerGenus := by
  unfold eulerGenus eulerCharacteristic
  rw [partition_component_card_sum H hGH r, partition_vertex_card_sum H hGH r,
    partition_edge_card_sum H hGH r, partition_face_card_sum H hGH r]
  simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem partition_assemble_restrict
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : H.ConnectedComponent) :
    (partition_assemble H hGH s).restrictClosed c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)) = s c := by
  classical
  exact ext_data (partition_assemble_restrict_sigma H hGH s c)
    (partition_assemble_restrict_twist H hGH s c)

theorem partition_assemble_genus
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    (partition_assemble H hGH s).eulerGenus = ∑ c : H.ConnectedComponent, (s c).eulerGenus := by
  rw [partition_eulerGenus_sum H hGH]
  simp only [partition_assemble_restrict]
end SimpleGraph.SignedRotation
