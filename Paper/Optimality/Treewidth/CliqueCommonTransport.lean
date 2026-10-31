import Paper.Optimality.Treewidth.SevenCliqueTwentySixClassification
namespace Paper.CliqueCommonTransport
open SimpleGraph
variable {V W : Type} [Fintype V] [Fintype W]
theorem iso_card (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (u z : V) :
    Fintype.card (G.commonNeighbors u z) = Fintype.card (H.commonNeighbors (e u) (e z)) := by
  classical
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv e.toEquiv (fun y => by
    change (G.Adj u y ∧ G.Adj z y) ↔ (H.Adj (e u) (e y) ∧ H.Adj (e z) (e y))
    simp only [e.map_rel_iff])

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem induced_card (T : Finset V) (u z : (T : Set V)) :
    (T.filter (fun y => G.Adj u.val y ∧ G.Adj z.val y)).card =
      Fintype.card ((G.induce (T : Set V)).commonNeighbors u z) := by
  classical
  let e : ((G.induce (T : Set V)).commonNeighbors u z) ≃
      {y : V // y ∈ T ∧ G.Adj u.val y ∧ G.Adj z.val y} := {
    toFun := fun y => ⟨y.val.val,y.val.property,y.property⟩
    invFun := fun y => ⟨⟨y.val,y.property.1⟩,y.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := Fintype.card_congr e
  have hc := Fintype.card_of_subtype (p := fun y : V => y ∈ T ∧ G.Adj u.val y ∧ G.Adj z.val y)
    (T.filter (fun y => G.Adj u.val y ∧ G.Adj z.val y))
    (fun y => by simp only [Finset.mem_filter])
  exact (hh.trans hc).symm
end Paper.CliqueCommonTransport
