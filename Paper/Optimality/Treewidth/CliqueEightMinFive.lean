import Paper.Optimality.Treewidth.CliqueEightJoinWitness
import Paper.Optimality.Treewidth.CliqueEightComplementTriangle
import Paper.Optimality.Treewidth.CliqueEightFourClique
namespace Paper.CliqueEightMinFive
open SimpleGraph CliqueTwoContractions
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem minor (hV : Fintype.card V = 8) (hd : ∀ v, 5 ≤ G.degree v) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  by_cases hfour : ∃ S : Finset V, S.card = 4 ∧ G.IsClique (S : Set V)
  · obtain ⟨S,hS,hcl⟩ := hfour
    exact CliqueEightFourClique.unrestricted G S hV hS hd hcl
  have hcomp : ∀ v, Gᶜ.degree v ≤ 2 := by
    intro v
    rw [G.degree_compl,hV]
    have hh := hd v
    omega
  have hsmall : ∀ I : Finset V, Gᶜ.IsIndepSet (I : Set V) → I.card ≤ 3 := by
    intro I hI
    have hcl : G.IsClique (I : Set V) := (SimpleGraph.isIndepSet_compl G).mp hI
    by_contra hn
    obtain ⟨S,hSI,hS⟩ := Finset.exists_subset_card_eq (show 4 ≤ I.card by omega)
    exact hfour ⟨S,hS,(fun a ha b hb hab => hcl (hSI ha) (hSI hb) hab)⟩
  obtain ⟨S,hS,hcl⟩ := CliqueEightComplementTriangle.exists_triangle Gᶜ hV hcomp hsmall
  have hcross : ∀ s ∈ S, ∀ r ∈ Sᶜ, G.Adj s r := by
    intro s hs r hr
    have hne : s ≠ r := by intro he; exact (Finset.mem_compl.mp hr) (he ▸ hs)
    by_contra hnot
    have hh : Gᶜ.Adj s r := ⟨hne,hnot⟩
    exact (Finset.mem_compl.mp hr) (CliqueEightComplement.triangle_closed Gᶜ hcomp S hS hcl s hs r hh)
  exact ⟨4,5,by decide,CliqueEightJoinWitness.minor G hV hd S hS hcross⟩
end Paper.CliqueEightMinFive
#print axioms Paper.CliqueEightMinFive.minor
