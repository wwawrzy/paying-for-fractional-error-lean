import Paper.Preliminaries.LatticeBlockSelection
namespace Paper.LatticeBlock
open LocalCyclesRamseyInput LocalCyclesRamseyReservoir

theorem selected_count {b q m s T : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (hT : P.rounds ≤ T)
    (hm : 2*(T+3)*s+1 ≤ m) (B : Blocks (b*m^q) (m^q))
    (hhom : ∀ j, Homogeneous (windowColor O P ((T+1)*s)) ((2*((T+1)*s)+1)^q) (B.sets j))
    (hdom : G.IsDominatingSetFinset (selected O G H P (blockIds B))) :
    B.k*(m-2*((T+2)*s))^q ≤ (selected O G H P (blockIds B)).card := by
  classical
  let A := {x : Position q m // Full ((T+2)*s) x}
  let f : Fin B.k × A → Vertex b q m := fun v=>(goodBlock (by omega) B v.1,v.2.val)
  have hf : Function.Injective f := by
    rintro ⟨j,x⟩ ⟨k,y⟩ he
    have hj := congrArg (fun v : Vertex b q m=>v.1.val) he
    have hxy := congrArg Prod.snd he
    have hj' : j=k := Fin.ext hj
    have hxy' : x=y := Subtype.ext hxy
    exact Prod.ext hj' hxy'
  have hcard : (Finset.univ.image f).card=B.k*(m-2*((T+2)*s))^q := by
    rw [Finset.card_image_of_injective _ hf]
    have he:=Fintype.card_congr (deepEquiv q m ((T+2)*s) (by nlinarith))
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    dsimp only [A]
    rw [he]
    simp
  rw [←hcard]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨⟨j,x⟩,_,rfl⟩:=Finset.mem_image.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    homogeneous_selected O G H P hT hm B j (hhom j) hdom x.val x.property⟩
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.selected_count
