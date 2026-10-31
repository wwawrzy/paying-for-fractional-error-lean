import Paper.Preliminaries.LatticeBlockTransport
import Paper.Optimality.LowerBounds.PortContextTransport
namespace Paper.LatticeBlock

theorem block_context {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (j : Fin b) (x : Position q m) (hx : Full s x) (ids : Vertex b q m → ℕ) :
    ((network O G H).context ids (j,x)).transport (full_degree O G H j x hx)=
      (latticeNetwork O).context (extendIds j ids) (coordinate x) := by
  change PortLocal.Context.mk _ _ = PortLocal.Context.mk _ _
  congr 1
  · exact (extendIds_coordinate j ids x).symm
  · funext p
    change ids ((network O G H).neighbor (j,x) (Fin.cast (full_degree O G H j x hx).symm p)) =
      extendIds j ids (fun i=>coordinate x i+(enumeration O p).val i)
    rw [neighbor_full O G H j x hx]
    change ids (j,shift O x hx (enumeration O p)) =
      extendIds j ids (fun i=>coordinate x i+(enumeration O p).val i)
    have he : coordinate (shift O x hx (enumeration O p)) =
        fun i=>coordinate x i+(enumeration O p).val i := by
      funext i
      have hh:=congrFun (shift_difference O x hx (enumeration O p)) i
      dsimp only [coordinate,difference] at *
      omega
    rw [←he,extendIds_coordinate]
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.block_context
