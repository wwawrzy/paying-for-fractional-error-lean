import Paper.Preliminaries.LatticeBlockGeometry
namespace Paper.LatticeBlock

def deepPositions (q m r : ℕ) : Finset (Position q m) := Finset.univ.filter (Full r)

def deepEquiv (q m r : ℕ) (hm : 2*r ≤ m) : {x : Position q m // Full r x} ≃ (Fin q → Fin (m-2*r)) where
  toFun x i := ⟨(x.val i).val-r,by have h:=x.property i;omega⟩
  invFun f := ⟨fun i => ⟨(f i).val+r,by have h:=(f i).isLt;omega⟩,by
    intro i
    have h:=(f i).isLt
    dsimp only
    omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have h:=x.property i
    dsimp only
    omega
  right_inv f := by
    funext i
    apply Fin.ext
    dsimp only
    omega

theorem deep_card (q m r : ℕ) (hm : 2*r ≤ m) : (deepPositions q m r).card=(m-2*r)^q := by
  have h:=Fintype.card_congr (deepEquiv q m r hm)
  simpa only [Fintype.card_subtype,Fintype.card_fun,Fintype.card_fin,deepPositions] using h

def center (q m T s : ℕ) (hm : 2*(T+3)*s+1 ≤ m) : Position q m :=
  fun _ => ⟨(T+3)*s,by nlinarith⟩

theorem center_full (q m T s : ℕ) (hm : 2*(T+3)*s+1 ≤ m) :
    Full ((T+3)*s) (center q m T s hm) := by
  intro i
  dsimp only [center]
  constructor
  · rfl
  · nlinarith

theorem center_closed_deep {b q m T s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) (H : IsBlockGraph O G)
    (hm : 2*(T+3)*s+1 ≤ m) (j : Fin b) (v : Vertex b q m)
    (hv : v=(j,center q m T s hm) ∨ G.Adj (j,center q m T s hm) v) :
    v.1=j ∧ Full ((T+2)*s) v.2 := by
  have hc:=center_full q m T s hm
  have hcs : Full s (center q m T s hm) := full_mono (by nlinarith) hc
  rcases hv with he | ha
  · subst v
    exact ⟨rfl,full_mono (by nlinarith) hc⟩
  · obtain ⟨k,y⟩:=v
    have hk:=same_block O G H hcs ha
    subst k
    let σ : O.values := ⟨difference (center q m T s hm) y,(H.inside _ _ _).mp ha⟩
    have hs:=shift_full (r:=T+2) O (center q m T s hm) hc σ
    have he:=shift_unique O (center q m T s hm) hcs σ y rfl
    exact ⟨rfl,by simpa only [he] using hs⟩
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.deep_card
#print axioms Paper.LatticeBlock.center_closed_deep
