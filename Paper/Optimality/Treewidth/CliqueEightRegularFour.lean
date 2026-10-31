import Paper.Optimality.Treewidth.CliqueTwoFourCliques
import Paper.Optimality.Treewidth.CliqueEightCrossCount
namespace Paper.CliqueEightRegularFour
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem clique_degree (T : Finset V) (hT : T.card = 4) (hc : G.IsClique (T : Set V))
    (x : V) (hx : x ∈ T) : G.inducedDegree x T = 3 := by
  classical
  have he : T.filter (G.Adj x) = T.erase x := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_erase]
    constructor
    · intro h; exact ⟨h.2.ne.symm,h.1⟩
    · intro h; exact ⟨h.2,hc hx h.2 h.1.symm⟩
  change (T.filter (G.Adj x)).card = 3
  rw [he,Finset.card_erase_of_mem hx,hT]

theorem minor (S : Finset V) (hV : Fintype.card V = 8) (hS : S.card = 4)
    (hreg : ∀ x, G.degree x = 5) (hcl : G.IsClique (S : Set V)) :
    (completeGraph (Fin 6)).IsMinor G := by
  classical
  have hRcard : Sᶜ.card = 4 := by rw [Finset.card_compl,hV,hS]
  have hs2 : ∀ x ∈ S, G.inducedDegree x Sᶜ = 2 := by
    intro x hx
    have hi := clique_degree G S hS hcl x hx
    have hp := CliquePartitionDegrees.partition G S x
    have hd := hreg x
    omega
  have hRcl : G.IsClique ((Sᶜ : Finset V) : Set V) := by
    by_contra hn
    have hh := CliqueEightCrossCount.noncomplete_support G hV (fun x => by rw [hreg x]) S hS hn
    have he : S.filter (fun x => G.inducedDegree x Sᶜ = 2) = S := Finset.filter_eq_self.mpr hs2
    rw [he,hS] at hh
    omega
  have hr2 : ∀ x ∈ Sᶜ, G.inducedDegree x S = 2 := by
    intro x hx
    have hi := clique_degree G Sᶜ hRcard hRcl x hx
    have hp := CliquePartitionDegrees.partition G S x
    have hd := hreg x
    omega
  have enum (T : Finset V) (hc : T.card = 4) : Nonempty (Fin 4 ≃ (T : Set V)) := by
    have ht : Fintype.card (T : Set V) = 4 := by
      simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hc
    exact ⟨Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using ht.symm)⟩
  obtain ⟨eS⟩ := enum S hS
  obtain ⟨eR⟩ := enum Sᶜ hRcard
  apply CliqueTwoFourCliques.minor G S eS eR hcl hRcl
  · intro i
    rw [CliqueEightMatchingData.neighbors_card]
    exact hs2 (eS i).val (eS i).property
  · intro j
    have he : Finset.univ.filter (fun i => j ∈ CliqueEightMatchingData.neighbors G S eS eR i) =
        Finset.univ.filter (fun i => G.Adj (eR j).val (eS i).val) := by
      ext i
      simp [CliqueEightMatchingData.neighbors,adj_comm]
    rw [he,CliqueEightMatchingData.filter_card S eS]
    exact hr2 (eR j).val (eR j).property
end Paper.CliqueEightRegularFour
