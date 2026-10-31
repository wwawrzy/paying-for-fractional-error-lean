import Paper.Preliminaries.LexCube
import Paper.Preliminaries.LatticeBlockSimulation
namespace Paper.LatticeBlock

def boxCenter (q r : ℕ) : Position q (2*r+1) := fun _=>⟨r,by omega⟩

noncomputable def windowRule {q s : ℕ} (O : Offsets q s)
    (P : PortLocal.Program Unit Bool) (r : ℕ) (labels : Position q (2*r+1) → ℕ) : Bool :=
  P.run (latticeNetwork O) (extendIds (0 : Fin 1) (fun v=>labels v.2)) (fun _=>())
    (coordinate (boxCenter q r))

theorem block_window_rule {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (j : Fin b) (ids : Vertex b q m → ℕ)
    (r : ℕ) (hr : (P.rounds+1)*s ≤ r) (x : Position q m) (hx : Full r x) :
    P.run (network O G H) ids (fun _=>()) (j,x)=
      windowRule O P r (fun z=>ids (j,boxPosition x hx z)) := by
  rw [block_run_unit O G H P j ids x (full_mono hr hx)]
  apply lattice_run_unit O P
  intro d hd
  have hd' : ∀ i, -(r:ℤ) ≤ d i ∧ d i ≤ r := by
    intro i
    have hh:=hd i
    have hr' : s*(P.rounds+1) ≤ r := by nlinarith
    omega
  let z : Position q (2*r+1) := fun i=>⟨(d i+r).toNat,by have hh:=hd' i;omega⟩
  have hz : boxOffset z=d := by
    funext i
    have hh:=hd' i
    dsimp only [boxOffset,z]
    omega
  have hleft : (fun i=>coordinate x i+d i)=coordinate (boxPosition x hx z) := by
    rw [←hz]
    exact (box_coordinate x hx z).symm
  have hright : (fun i=>coordinate (boxCenter q r) i+d i)=coordinate z := by
    funext i
    have hh:=hd' i
    dsimp only [coordinate,boxCenter,z]
    omega
  rw [hleft,hright,extendIds_coordinate,extendIds_coordinate]
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.block_window_rule
