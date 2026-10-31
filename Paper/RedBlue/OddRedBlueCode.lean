import Paper.Preliminaries.OddPathGeometry
import Paper.RedBlue.IncidenceDensity
import Paper.TotalDomination.HighGirthBudget
namespace Paper.OddRedBlue
open scoped BigOperators
open OddPathPower

def codeVertex (m : ℕ) (p : Fin 2) (j : Fin m) : Fin (8*m) := ⟨8*j.val+3+p.val,by have hp:=p.isLt;have hj:=j.isLt;omega⟩
def packVertex (m : ℕ) (p : Fin 2) (j : Fin m) : Fin (8*m) := ⟨8*j.val+3*p.val,by have hp:=p.isLt;have hj:=j.isLt;omega⟩
def code (m : ℕ) (p : Fin 2) : Finset (Fin (8*m)) := Finset.univ.image (codeVertex m p)
def packing (m : ℕ) (p : Fin 2) : Finset (Fin (8*m)) := Finset.univ.image (packVertex m p)
def red (m : ℕ) (p : Fin 2) : Finset (Fin (8*m)) := Finset.univ.filter (fun v => v.val%2=p.val)
def blue (m : ℕ) (p : Fin 2) : Finset (Fin (8*m)) := Finset.univ \ red m p

theorem code_card (m : ℕ) (p : Fin 2) : (code m p).card=m := by
  have hi : Function.Injective (codeVertex m p) := by
    intro i j he
    have h := congrArg Fin.val he
    dsimp only [codeVertex] at h
    apply Fin.ext;omega
  simp only [code,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
theorem packing_card (m : ℕ) (p : Fin 2) : (packing m p).card=m := by
  have hi : Function.Injective (packVertex m p) := by
    intro i j he
    have h := congrArg Fin.val he
    dsimp only [packVertex] at h
    apply Fin.ext;omega
  simp only [packing,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

theorem code_blue (m : ℕ) (p : Fin 2) : code m p ⊆ blue m p := by
  intro u hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  simp only [red,Finset.mem_filter,Finset.mem_univ,true_and,codeVertex]
  have hp:=p.isLt
  omega

theorem packing_red (m : ℕ) (p : Fin 2) : packing m p ⊆ red m p := by
  intro u hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  dsimp only [packVertex]
  have hp:=p.isLt
  omega

theorem covers (m : ℕ) (p : Fin 2) : ∀ r ∈ red m p,
    ∃ u ∈ code m p, (graph (8*m) 3).Adj r u := by
  intro r hr
  have hpar := (Finset.mem_filter.mp hr).2
  let j : Fin m := ⟨r.val/8,by have hn:=r.isLt;omega⟩
  refine ⟨codeVertex m p j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
  have hp:=p.isLt
  change (r ≠ codeVertex m p j ∧ r.val ≤ (codeVertex m p j).val+3 ∧
    (codeVertex m p j).val ≤ r.val+3) ∧ r.val%2 ≠ (codeVertex m p j).val%2
  dsimp only [codeVertex,j]
  refine ⟨⟨?_,by omega,by omega⟩,by omega⟩
  intro he;have hh:=congrArg Fin.val he;dsimp only [codeVertex,j] at hh;omega

theorem packing_neighbor_unique (m : ℕ) (p : Fin 2) (v u w : Fin (8*m))
    (hu : u ∈ packing m p) (hw : w ∈ packing m p)
    (ha : (graph (8*m) 3).Adj v u) (hb : (graph (8*m) 3).Adj v w) : u=w := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
  have ha1:=ha.1.2
  have hb1:=hb.1.2
  apply Fin.ext
  dsimp only [packVertex] at ha1 hb1 ⊢
  omega

theorem packing_neighbor_count (m : ℕ) (p : Fin 2) (v : Fin (8*m)) :
    ((graph (8*m) 3).neighborFinset v ∩ packing m p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu w hw
  exact packing_neighbor_unique m p v u w (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hw).2
    (((graph (8*m) 3).mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1)
    (((graph (8*m) 3).mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1)

end Paper.OddRedBlue
#print axioms Paper.OddRedBlue.covers
#print axioms Paper.OddRedBlue.packing_neighbor_count
