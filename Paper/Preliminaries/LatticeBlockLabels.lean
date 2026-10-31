import Paper.Preliminaries.LexCube
import GraphTheory.Local.LocalCyclesRamseyInput
namespace Paper.LatticeBlock
open LocalCyclesRamseyInput

noncomputable def vertexIndex (b q m : ℕ) : Vertex b q m ≃ Fin (b*m^q) :=
  (Equiv.prodCongr (Equiv.refl (Fin b)) (positionEquiv q m)).trans finProdFinEquiv

noncomputable def blockIds {b q m : ℕ} (P : Blocks (b*m^q) (m^q)) : Vertex b q m  →  ℕ :=
  fun v=>P.input.ident (vertexIndex b q m v)

theorem blockIds_injective {b q m : ℕ} (P : Blocks (b*m^q) (m^q)) :
    Function.Injective (blockIds P) := P.input.unique.comp (vertexIndex b q m).injective

theorem blockIds_bounds {b q m : ℕ} (P : Blocks (b*m^q) (m^q)) (v : Vertex b q m) :
    1 ≤ blockIds P v ∧ blockIds P v ≤ b*m^q := P.input_bounds _

theorem goodBlocks_le {b q m : ℕ} (hm : 0 < m) (P : Blocks (b*m^q) (m^q)) : P.k ≤ b := by
  have hp : 0 < m^q := pow_pos hm q
  have hh := P.count
  nlinarith

def goodBlock {b q m : ℕ} (hm : 0 < m) (P : Blocks (b*m^q) (m^q)) (j : Fin P.k) : Fin b :=
  ⟨j.val,lt_of_lt_of_le j.isLt (goodBlocks_le hm P)⟩

theorem blockIds_good {b q m : ℕ} (hm : 0 < m) (P : Blocks (b*m^q) (m^q))
    (j : Fin P.k) (x : Position q m) :
    blockIds P (goodBlock hm P j,x)=(P.sets j).orderEmbOfFin (P.card j) (positionRank q m x) := by
  have he : vertexIndex b q m (goodBlock hm P j,x)=
      LocalCyclesRamseyViews.blockIndex (j.val*m^q) (m^q) (P.block_fits j) (positionRank q m x) := by
    apply Fin.ext
    simp [vertexIndex,goodBlock,positionEquiv,finProdFinEquiv,LocalCyclesRamseyViews.blockIndex,Nat.mul_comm,Nat.add_comm]
  change P.input.ident (vertexIndex b q m (goodBlock hm P j,x))=_
  rw [he,P.input_block]

theorem blockIds_mono {b q m : ℕ} (hm : 0 < m) (P : Blocks (b*m^q) (m^q)) (j : Fin P.k) :
    StrictMono (fun x : LexPosition q m=>blockIds P (goodBlock hm P j,ofLex x)) := by
  intro x y hxy
  change blockIds P (goodBlock hm P j,ofLex x) < blockIds P (goodBlock hm P j,ofLex y)
  rw [blockIds_good hm P j,blockIds_good hm P j]
  apply (P.sets j).orderEmbOfFin (P.card j) |>.strictMono
  exact (positionOrder q m).symm.strictMono hxy

theorem blockIds_mem {b q m : ℕ} (hm : 0 < m) (P : Blocks (b*m^q) (m^q))
    (j : Fin P.k) (x : Position q m) : blockIds P (goodBlock hm P j,x) ∈ P.sets j := by
  rw [blockIds_good hm P j]
  exact Finset.orderEmbOfFin_mem _ _ _
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.blockIds_mono
