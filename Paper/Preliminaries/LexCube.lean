import Paper.Preliminaries.LatticeBlockGeometry
namespace Paper.LatticeBlock
abbrev LexPosition (q m : ℕ) := Lex (Position q m)

noncomputable def positionOrder (q m : ℕ) : Fin (m^q) ≃o LexPosition q m :=
  Fintype.orderIsoFinOfCardEq _ (by simp [LexPosition,Position])

noncomputable def positionRank (q m : ℕ) (x : Position q m) : Fin (m^q) :=
  (positionOrder q m).symm (toLex x)

noncomputable def positionEquiv (q m : ℕ) : Position q m ≃ Fin (m^q) where
  toFun := positionRank q m
  invFun i := ofLex (positionOrder q m i)
  left_inv x := (positionOrder q m).apply_symm_apply (toLex x)
  right_inv i := (positionOrder q m).symm_apply_apply i

def boxOffset {q r : ℕ} (z : Position q (2*r+1)) : Delta q :=
  fun i=>(z i).val-(r:ℤ)

def boxPosition {q m r : ℕ} (x : Position q m) (hx : Full r x)
    (z : Position q (2*r+1)) : Position q m :=
  fun i=>⟨(x i).val-r+(z i).val,by
    have hh:=hx i
    have hz:=(z i).isLt
    omega⟩

theorem box_coordinate {q m r : ℕ} (x : Position q m) (hx : Full r x)
    (z : Position q (2*r+1)) :
    (fun i=>((boxPosition x hx z i).val:ℤ))=
      fun i=>((x i).val:ℤ)+boxOffset z i := by
  funext i
  have hh:=hx i
  dsimp only [boxPosition,boxOffset]
  omega

theorem boxPosition_strictMono {q m r : ℕ} (x : Position q m) (hx : Full r x) :
    StrictMono (fun z : LexPosition q (2*r+1)=>toLex (boxPosition x hx (ofLex z))) := by
  intro z w hzw
  obtain ⟨i,he,hi⟩:=hzw
  refine ⟨i,?_,?_⟩
  · intro j hj
    have hh : ofLex z j=ofLex w j := he j hj
    change boxPosition x hx (ofLex z) j=boxPosition x hx (ofLex w) j
    apply Fin.ext
    simp only [boxPosition,hh]
  · change (boxPosition x hx (ofLex z) i).val<(boxPosition x hx (ofLex w) i).val
    change (ofLex z i).val<(ofLex w i).val at hi
    dsimp only [boxPosition]
    omega
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.boxPosition_strictMono
