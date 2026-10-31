import Paper.Preliminaries.LatticeBlockGeometry
import Paper.Optimality.LowerBounds.PortLocal
namespace Paper.LatticeBlock
noncomputable def enumeration {q s : ℕ} (O : Offsets q s) : Fin O.values.card ≃ O.values :=
  (Finset.equivFinOfCardEq (s:=O.values) rfl).symm

noncomputable def reversePort {q s : ℕ} (O : Offsets q s) (p : Fin O.values.card) : Fin O.values.card :=
  (enumeration O).symm ⟨fun i => -(enumeration O p).val i,O.symmetric _ (enumeration O p).property⟩

theorem reverse_offset {q s : ℕ} (O : Offsets q s) (p : Fin O.values.card) :
    (enumeration O (reversePort O p)).val=(fun i => -(enumeration O p).val i) := by
  simp only [reversePort,Equiv.apply_symm_apply]

theorem reverse_involutive {q s : ℕ} (O : Offsets q s) : Function.Involutive (reversePort O) := by
  intro p
  apply (enumeration O).injective
  apply Subtype.ext
  rw [reverse_offset,reverse_offset]
  funext i
  simp

noncomputable def latticeNetwork {q s : ℕ} (O : Offsets q s) : PortLocal.Network (Delta q) where
  degree _ := O.values.card
  neighbor x p := fun i => x i+(enumeration O p).val i
  back _ p := reversePort O p
  reverse_neighbor x p := by
    funext i
    dsimp only
    rw [show (enumeration O (reversePort O p)).val i= -(enumeration O p).val i by rw [reverse_offset]]
    omega

noncomputable def numbering {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G) :
    PortBroadcastModel.Numbering G := by
  classical
  intro v
  exact if hv : Full s v.2 then
    ((Fin.castOrderIso (full_degree O G H v.1 v.2 hv)).toEquiv.trans (enumeration O)).trans
      (fullNeighborEquiv O G H v.1 v.2 hv)
  else
    (Finset.equivFinOfCardEq (s:=G.neighborFinset v) (G.card_neighborFinset_eq_degree v)).symm

noncomputable def network {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G) :
    PortLocal.Network (Vertex b q m) := PortLocal.Network.ofNumbering G (numbering O G H)

theorem compatible {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G) :
    (network O G H).Compatible G := PortLocal.Network.ofNumbering_compatible G _

theorem neighbor_full {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (j : Fin b) (x : Position q m) (hx : Full s x) (p : Fin (G.degree (j,x))) :
    (network O G H).neighbor (j,x) p =
      (j,shift O x hx (enumeration O (Fin.cast (full_degree O G H j x hx) p))) := by
  classical
  simp only [network,PortLocal.Network.ofNumbering,numbering,dif_pos hx]
  rfl
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.compatible
#print axioms Paper.LatticeBlock.neighbor_full
