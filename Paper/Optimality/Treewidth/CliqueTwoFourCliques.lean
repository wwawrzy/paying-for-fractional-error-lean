import Paper.Optimality.Treewidth.CliqueBalancedFourRows
import Paper.Optimality.Treewidth.CliqueCompleteTwoContractions
import Paper.Optimality.Treewidth.CliqueEightBranchEdges
import Paper.Optimality.Treewidth.CliqueEightMatchingData
namespace Paper.CliqueTwoFourCliques
open SimpleGraph CliqueFourMatchings CliqueEightLabels CliqueTwoContractions CliqueEightBranchSets CliqueEightBranchEdges
private theorem index_cases : ∀ i : Fin 6,
    (∃ s : Bool, i = pairIndex s) ∨ ∃ a : Fin 4, i = rowIndex a := by decide
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (eS : Fin 4 ≃ (S : Set V)) (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))
theorem minor (hS : G.IsClique (S : Set V)) (hR : G.IsClique ((Sᶜ : Finset V) : Set V))
    (hrows : ∀ i, (CliqueEightMatchingData.neighbors G S eS eR i).card = 2)
    (hcols : ∀ j : Fin 4, (Finset.univ.filter (fun i => j ∈ CliqueEightMatchingData.neighbors G S eS eR i)).card = 2) :
    (completeGraph (Fin 6)).IsMinor G := by
  classical
  obtain ⟨k,hk⟩ := CliqueBalancedFourRows.choose (CliqueEightMatchingData.neighbors G S eS eR) hrows hcols
  have hneq1 : ∀ k : Fin 3, (ends k).1.1 ≠ (ends k).1.2 := by decide
  have hneq2 : ∀ k : Fin 3, (ends k).2.1 ≠ (ends k).2.2 := by decide
  have h06 := hR (eR (ends k).1.1).property (eR (ends k).1.2).property
    (fun hh => hneq1 k (eR.injective (Subtype.ext hh)))
  have h17 := hR (eR (ends k).2.1).property (eR (ends k).2.2).property
    (fun hh => hneq2 k (eR.injective (Subtype.ext hh)))
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < (part k false).card by rw [part_card]; decide)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (part k true).card by rw [part_card]; decide)
  have hij : i ≠ j := fun hh => (Finset.disjoint_left.mp (part_partition k).1) hi (hh ▸ hj)
  have hcross : ∃ i ∈ part k false, ∃ j ∈ part k true, G.Adj (eR i).val (eR j).val :=
    ⟨i,hi,j,hj,hR (eR i).property (eR j).property (fun hh => hij (eR.injective (Subtype.ext hh)))⟩
  have hatt : ∀ b : Fin 4, ∀ side : Bool, ∃ j ∈ part k side, G.Adj (eS b).val (eR j).val := by
    intro b side
    obtain ⟨j,hj⟩ := hk b side
    obtain ⟨hjN,hjP⟩ := Finset.mem_inter.mp hj
    exact ⟨j,hjP,(Finset.mem_filter.mp hjN).2⟩
  apply CliqueCompleteTwoContractions.complete_minor G (labeling S eS eR k)
  · simpa only [zero,six] using h06
  · simpa only [CliqueEightLabels.one,seven] using h17
  · intro i j hij
    change Linked G S eS eR k i j
    rcases index_cases i with ⟨s,rfl⟩ | ⟨b,rfl⟩ <;> rcases index_cases j with ⟨t,rfl⟩ | ⟨c,rfl⟩
    · cases s <;> cases t
      · exact False.elim (hij rfl)
      · exact pairs G S eS eR k hcross
      · exact linked_symm G S eS eR (pairs G S eS eR k hcross)
      · exact False.elim (hij rfl)
    · exact linked_symm G S eS eR (row_pair G S eS eR k c s (hatt c s))
    · exact row_pair G S eS eR k b t (hatt b t)
    · exact rows G S eS eR k b c (fun hbc => hij (congrArg rowIndex hbc)) hS
end Paper.CliqueTwoFourCliques
