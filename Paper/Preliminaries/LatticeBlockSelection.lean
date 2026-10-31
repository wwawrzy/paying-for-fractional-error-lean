import Paper.Preliminaries.LatticeBlockHomogeneous
import Paper.Preliminaries.LatticeBlockCounting
import GraphTheory.SimpleGraph.Domination.Bounds
namespace Paper.LatticeBlock
open LocalCyclesRamseyInput LocalCyclesRamseyReservoir

noncomputable def selected {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (ids : Vertex b q m → ℕ) : Finset (Vertex b q m) :=
  Finset.univ.filter (fun v=>P.run (network O G H) ids (fun _=>()) v=true)

theorem homogeneous_selected {b q m s T : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (hT : P.rounds ≤ T)
    (hm : 2*(T+3)*s+1 ≤ m) (B : Blocks (b*m^q) (m^q))
    (j : Fin B.k)
    (hhom : Homogeneous (windowColor O P ((T+1)*s)) ((2*((T+1)*s)+1)^q) (B.sets j))
    (hdom : G.IsDominatingSetFinset (selected O G H P (blockIds B)))
    (x : Position q m) (hx : Full ((T+2)*s) x) :
    P.run (network O G H) (blockIds B) (fun _=>()) (goodBlock (by omega) B j,x)=true := by
  classical
  obtain ⟨col,hcol⟩:=hhom
  let u : Vertex b q m := (goodBlock (by omega) B j,center q m T s hm)
  have hw : ∃ w ∈ selected O G H P (blockIds B), w=u ∨ G.Adj u w := by
    rcases hdom u with hu|⟨w,hw,ha⟩
    · exact ⟨u,hu,Or.inl rfl⟩
    · exact ⟨w,hw,Or.inr ha⟩
  obtain ⟨w,hw,ha⟩:=hw
  obtain ⟨hwj,hwd⟩:=center_closed_deep O G H hm (goodBlock (by omega) B j) w ha
  have hws : Full ((T+1)*s) w.2 := full_mono (by nlinarith) hwd
  have hc:=homogeneous_output O G H P T hT (by omega) B j col hcol w.2 hws
  have hb : P.run (network O G H) (blockIds B) (fun _=>()) w=true := (Finset.mem_filter.mp hw).2
  have he : (goodBlock (by omega) B j,w.2)=w := by
    apply Prod.ext
    · exact hwj.symm
    · rfl
  rw [he,hb] at hc
  have hx' : Full ((T+1)*s) x := full_mono (by nlinarith) hx
  have hc' := homogeneous_output O G H P T hT (by omega) B j col hcol x hx'
  rw [←hc] at hc'
  cases hh : P.run (network O G H) (blockIds B) (fun _=>()) (goodBlock (by omega) B j,x) <;> simp_all <;> omega
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.homogeneous_selected
