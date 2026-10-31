import Paper.Optimality.Treewidth.CliqueEightBranchSets

/-! Lift actual graph edges to adjacency witnesses between the six
branch sets of the two-contraction model. -/
namespace Paper.CliqueEightBranchEdges
open SimpleGraph CliqueFourMatchings CliqueEightLabels CliqueTwoContractions
  CliqueEightBranchSets
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

def Linked (k : Fin 3) (i j : Fin 6) : Prop :=
  ∃ u ∈ blocks (labeling S eS eR k) i,
    ∃ v ∈ blocks (labeling S eS eR k) j, G.Adj u v

theorem linked_symm {k : Fin 3} {i j : Fin 6}
    (h : Linked G S eS eR k i j) : Linked G S eS eR k j i := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨v, hv, u, hu, huv.symm⟩

theorem rows (k : Fin 3) (a b : Fin 4) (hab : a ≠ b)
    (hS : G.IsClique (S : Set V)) :
    Linked G S eS eR k (rowIndex a) (rowIndex b) := by
  refine ⟨(eS a).val, ?_, (eS b).val, ?_, ?_⟩
  · rw [row_block]; exact Set.mem_singleton _
  · rw [row_block]; exact Set.mem_singleton _
  · exact hS (eS a).property (eS b).property
      (fun heq => hab (eS.injective (Subtype.ext heq)))

theorem row_pair (k : Fin 3) (a : Fin 4) (side : Bool)
    (h : ∃ j ∈ part k side, G.Adj (eS a).val (eR j).val) :
    Linked G S eS eR k (rowIndex a) (pairIndex side) := by
  obtain ⟨j, hj, hadj⟩ := h
  refine ⟨(eS a).val, ?_, (eR j).val, pair_member S eS eR k side j hj, hadj⟩
  rw [row_block]; exact Set.mem_singleton _

theorem pairs (k : Fin 3)
    (h : ∃ i ∈ part k false, ∃ j ∈ part k true, G.Adj (eR i).val (eR j).val) :
    Linked G S eS eR k (pairIndex false) (pairIndex true) := by
  obtain ⟨i, hi, j, hj, hij⟩ := h
  exact ⟨(eR i).val, pair_member S eS eR k false i hi,
    (eR j).val, pair_member S eS eR k true j hj, hij⟩

end Paper.CliqueEightBranchEdges
#print axioms Paper.CliqueEightBranchEdges.linked_symm
#print axioms Paper.CliqueEightBranchEdges.rows
#print axioms Paper.CliqueEightBranchEdges.row_pair
#print axioms Paper.CliqueEightBranchEdges.pairs
