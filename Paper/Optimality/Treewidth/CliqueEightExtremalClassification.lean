import Paper.Optimality.Treewidth.CliqueEightFullFiveClique
import Paper.Optimality.Treewidth.CliqueResidualCanonical
import Paper.Optimality.Treewidth.CliqueSixExtremalGeneral
namespace Paper.CliqueEightExtremalClassification
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem neighborhood_matching (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (hd : ∀ x, 5 ≤ G.degree x) (u : V) (hu : G.degree u = 5) :
    ((G.induce (G.neighborSet u))ᶜ).edgeFinset.card = 2 := by
  classical
  let J := G.induce (G.neighborSet u)
  have hj : Fintype.card (G.neighborSet u) = 5 := by rw [G.card_neighborSet_eq_degree,hu]
  have hcomp := CliqueSixExtremalLocal.five_complement G hG hV he u hu
  apply CliqueFiveMissingMatching.two_edges J hj hcomp
  intro Q hQ hclQ
  let P := Q.image Subtype.val
  have hP : P.card = 4 := by rw [Finset.card_image_of_injective _ Subtype.val_injective,hQ]
  have hpN : ∀ x ∈ P, G.Adj u x := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    exact w.property
  have huP : u ∉ P := fun hh => G.irrefl (hpN u hh)
  have hclP : G.IsClique (P : Set V) := by
    intro a ha b hb hab
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact hclQ hx hy (fun hxy => hab (congrArg Subtype.val hxy))
  have hS : (insert u P).card = 5 := by rw [Finset.card_insert_of_notMem huP,hP]
  apply CliqueEightFullFiveClique.impossible G hG hV hd (insert u P) hS
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact hpN b hb
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (hpN a ha).symm
    · exact hclP ha hb hab

theorem canonical (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (hd : ∀ x, 5 ≤ G.degree x) :
    Nonempty (G ≃g CliqueEightResidualTemplates.graph 0 1) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  have hs := G.minDegree_mul_card_le_two_mul_card_edges
  rw [hV,he] at hs
  have hu5 : G.degree u = 5 := by have hl := hd u; omega
  have hm := neighborhood_matching G hG hV he hd u hu5
  have hc := CliqueSixExtremalLocal.five_complement G hG hV he u hu5
  obtain ⟨a,b,⟨e⟩,hp⟩ := CliqueEightActualTemplate.surviving G hV he hd u hu5 hc hm hG
  obtain ⟨f⟩ := CliqueResidualCanonical.canonical a b hp
  exact ⟨e.trans f⟩
end Paper.CliqueEightExtremalClassification
