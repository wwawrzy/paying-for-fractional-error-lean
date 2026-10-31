import Paper.Preliminaries.LatticeBlockLabels
import Paper.Preliminaries.LatticeWindowRule
namespace Paper.LatticeBlock
open LocalCyclesRamseyInput LocalCyclesRamseyReservoir

noncomputable def windowColor {q s : ℕ} (O : Offsets q s)
    (P : PortLocal.Program Unit Bool) (r : ℕ) (X : Finset ℕ) : Fin 2 :=
  if h : X.card=(2*r+1)^q then
    ⟨(windowRule O P r (fun z=>X.orderEmbOfFin h (positionRank q (2*r+1) z))).toNat,by
      cases windowRule O P r (fun z=>X.orderEmbOfFin h (positionRank q (2*r+1) z)) <;> decide⟩
  else 0

theorem homogeneous_output {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (T : ℕ) (hT : P.rounds ≤ T) (hm : 0 < m) (B : Blocks (b*m^q) (m^q))
    (j : Fin B.k) (col : Fin 2)
    (hhom : ∀ A ⊆ B.sets j, A.card=(2*((T+1)*s)+1)^q →
      windowColor O P ((T+1)*s) A=col)
    (x : Position q m) (hx : Full ((T+1)*s) x) :
    (P.run (network O G H) (blockIds B) (fun _=>()) (goodBlock hm B j,x)).toNat=col.val := by
  classical
  let r := (T+1)*s
  let f : Fin ((2*r+1)^q) → ℕ := fun i=>blockIds B
    (goodBlock hm B j,boxPosition x hx (ofLex (positionOrder q (2*r+1) i)))
  let A := Finset.univ.image f
  have hf : StrictMono f :=
    (blockIds_mono hm B j).comp ((boxPosition_strictMono x hx).comp (positionOrder q (2*r+1)).strictMono)
  have hcard : A.card=(2*r+1)^q := by
    rw [Finset.card_image_of_injective _ hf.injective]
    simp
  have hsub : A ⊆ B.sets j := by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    exact blockIds_mem hm B j _
  have he := Finset.orderEmbOfFin_unique hcard
    (f:=f) (fun i=>Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hf
  have hh := congrArg Fin.val (hhom A hsub hcard)
  change (windowColor O P r A).val=col.val at hh
  have hc : (windowRule O P r (fun z=>A.orderEmbOfFin hcard (positionRank q (2*r+1) z))).toNat=col.val := by
    simpa only [windowColor,dif_pos hcard] using hh
  rw [←he] at hc
  have heq : (fun z=>f (positionRank q (2*r+1) z))=
      (fun z=>blockIds B (goodBlock hm B j,boxPosition x hx z)) := by
    funext z
    dsimp only [f,positionRank]
    rw [(positionOrder q (2*r+1)).apply_symm_apply]
    rfl
  rw [heq] at hc
  rw [block_window_rule O G H P (goodBlock hm B j) (blockIds B) ((T+1)*s) (by nlinarith) x hx]
  exact hc
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.homogeneous_output
