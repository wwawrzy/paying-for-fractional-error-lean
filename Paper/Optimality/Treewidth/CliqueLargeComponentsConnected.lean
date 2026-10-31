import Paper.Optimality.Treewidth.CliqueExteriorComplementConnected
namespace Paper.CliqueLargeComponentsConnected
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem connected (S R : Set V) (hR : (G.induce R).Connected) (hRS : R ⊆ S)
    (P : Finset V) (hP : P.card ≤ 7) (hcover : S ⊆ R ∪ (P : Set V))
    (hlarge : ∀ C : (G.induce S).ConnectedComponent,
      8 ≤ (vertices (Subtype.val '' C.supp)).card) : (G.induce S).Connected := by
  classical
  let v : R := Classical.choice hR.nonempty
  apply G.induce_connected_of_patches v.val (hRS v.property)
  intro y hy
  let C := (G.induce S).connectedComponentMk ⟨y,hy⟩
  let Y : Set V := Subtype.val '' C.supp
  have hyY : y ∈ Y := ⟨⟨y,hy⟩,ConnectedComponent.connectedComponentMk_mem,rfl⟩
  have hYS : Y ⊆ S := by rintro z ⟨w,hw,rfl⟩; exact w.property
  have hYconn : (G.induce Y).Connected := by
    let f : C.toSimpleGraph →g G.induce Y := {
      toFun := fun w => ⟨w.val.val,⟨w.val,w.property,rfl⟩⟩
      map_rel' := fun h => h }
    apply C.connected_toSimpleGraph.map f
    rintro ⟨z,w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  have hex : ∃ z ∈ Y, z ∈ R := by
    by_contra hn
    push Not at hn
    have hsub : vertices Y ⊆ P := by
      intro z hz
      have hzY := (mem_vertices Y z).mp hz
      exact (hcover (hYS hzY)).resolve_left (hn z hzY)
    have hh := Finset.card_le_card hsub
    have hl := hlarge C
    change 8 ≤ (vertices Y).card at hl
    omega
  obtain ⟨z,hzY,hzR⟩ := hex
  have hRY : (G.induce (R ∪ Y)).Connected :=
    G.induce_union_connected hR.preconnected hYconn.preconnected ⟨z,hzR,hzY⟩
  have hsub : R ∪ Y ⊆ S := Set.union_subset hRS hYS
  have hv : v.val ∈ R ∪ Y := Or.inl v.property
  have hy' : y ∈ R ∪ Y := Or.inr hyY
  exact ⟨R ∪ Y,hsub,hv,hy',hRY.preconnected ⟨v.val,hv⟩ ⟨y,hy'⟩⟩
end Paper.CliqueLargeComponentsConnected
