import Paper.Optimality.Treewidth.CliqueEightMatchingData
import Paper.Optimality.Treewidth.CliqueMatchingAttachments
import Paper.Optimality.Treewidth.CliqueMatchingCrossEdge

/-! Actual attachment witnesses for a four-plus-four partition of an
 eight-vertex graph of minimum degree five. -/
namespace Paper.CliqueEightAttachments

open SimpleGraph CliqueFourMatchings
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

theorem choose (hV : Fintype.card V = 8) (hS : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x)
    (hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y) :
    ∃ k ∈ available (CliqueEightMatchingData.outsideGraph G S eR),
      ∃ a : Fin 4, ∃ missing : Bool, ∀ b : Fin 4, ∀ side : Bool,
        b ≠ a ∨ side ≠ missing →
        ∃ j ∈ part k side, G.Adj (eS b).val (eR j).val := by
  classical
  obtain ⟨k, hk, hbad⟩ := CliqueEightMatchingData.choose G S eS eR hV hS hd hno
  have hN : ∀ b, 2 ≤ (CliqueEightMatchingData.neighbors G S eS eR b).card := by
    intro b
    rw [CliqueEightMatchingData.neighbors_card]
    exact CliqueEightCrossCount.inside_degree G S hS hd (eS b).val (eS b).property
  obtain ⟨a, missing, htouch⟩ := CliqueMatchingAttachments.single_missing
    (CliqueEightMatchingData.neighbors G S eS eR) hN k hbad
  refine ⟨k, hk, a, missing, ?_⟩
  intro b side hgood
  obtain ⟨j, hj⟩ := htouch b side hgood
  obtain ⟨hneighbors, hpart⟩ := Finset.mem_inter.mp hj
  exact ⟨j, hpart, (Finset.mem_filter.mp hneighbors).2⟩

/-- All edges needed between the two contracted pairs and the retained
vertices, with just one allowed missing retained-to-pair attachment. -/
theorem choose_edges (hV : Fintype.card V = 8) (hS : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x)
    (hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y) :
    ∃ k : Fin 3,
      G.Adj (eR (ends k).1.1).val (eR (ends k).1.2).val ∧
      G.Adj (eR (ends k).2.1).val (eR (ends k).2.2).val ∧
      (∃ i ∈ part k false, ∃ j ∈ part k true, G.Adj (eR i).val (eR j).val) ∧
      ∃ a : Fin 4, ∃ missing : Bool, ∀ b : Fin 4, ∀ side : Bool,
        b ≠ a ∨ side ≠ missing →
        ∃ j ∈ part k side, G.Adj (eS b).val (eR j).val := by
  classical
  obtain ⟨k, hk, a, missing, ha⟩ := choose G S eS eR hV hS hd hno
  have hdegree : ∀ i, 2 ≤ (CliqueEightMatchingData.outsideGraph G S eR).degree i := by
    intro i
    rw [CliqueEightMatchingData.outside_degree]
    exact CliqueEightCrossCount.outside_degree G S hS hd (eR i).val
      (hno (eR i).val (eR i).property)
  have hcross := CliqueMatchingCrossEdge.exists_edge
    (CliqueEightMatchingData.outsideGraph G S eR) hdegree k
  have hpairs := (Finset.mem_filter.mp hk).2
  exact ⟨k, hpairs.1, hpairs.2, hcross, a, missing, ha⟩

end Paper.CliqueEightAttachments

#print axioms Paper.CliqueEightAttachments.choose
#print axioms Paper.CliqueEightAttachments.choose_edges
