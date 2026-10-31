import Paper.Optimality.Treewidth.SevenCliqueResidualDegreeDistribution
import Paper.Optimality.Treewidth.SevenCliqueForcedContacts
namespace Paper.CliqueContactDegree
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem cross_six (T : Finset V) (x p : V) (hx : x ∈ T)
    (h7 : G.inducedDegree x T = 7) (hp : G.Adj p x)
    (hcount : Fintype.card {z : (T : Set V) // (G.induce (T : Set V)).degree z = 5} = 5)
    (hforced : ∀ z ∈ T, G.inducedDegree z T = 5 → G.Adj p z) :
    6 ≤ G.inducedDegree p T := by
  classical
  let H := G.induce (T : Set V)
  let Q : Finset (T : Set V) := Finset.univ.filter (fun z => H.degree z = 5)
  let P : Finset V := Q.image Subtype.val
  have hQ : Q.card = 5 := by
    change (Finset.univ.filter (fun z => H.degree z = 5)).card = 5
    rw [← Fintype.card_subtype]
    exact hcount
  have hP : P.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective,hQ]
  have hmem : ∀ z ∈ P, z ∈ T ∧ G.inducedDegree z T = 5 := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have hw5 := (Finset.mem_filter.mp hw).2
    exact ⟨w.property,by rw [← InducedCounting.degree_induce_eq_inducedDegree G T w]; exact hw5⟩
  have hxP : x ∉ P := by intro hh; have hh5 := (hmem x hh).2; omega
  have hsub : insert x P ⊆ T.filter (G.Adj p) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_filter.mpr ⟨hx,hp⟩
    · obtain ⟨hzT,hz5⟩ := hmem z hz
      exact Finset.mem_filter.mpr ⟨hzT,hforced z hzT hz5⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxP,hP] at hh
  exact hh

theorem twelve (S T : Finset V) (hdis : Disjoint S T) (p : V)
    (hS : G.inducedDegree p S = 6) (hT : 6 ≤ G.inducedDegree p T) : 12 ≤ G.degree p := by
  classical
  have hu := CliqueRegionCount.degree_union G S T hdis p
  have hh : G.inducedDegree p (S ∪ T) ≤ G.degree p := by
    change ((S ∪ T).filter (G.Adj p)).card ≤ (G.neighborFinset p).card
    apply Finset.card_le_card
    intro z hz
    exact (G.mem_neighborFinset p z).mpr (Finset.mem_filter.mp hz).2
  omega
end Paper.CliqueContactDegree
