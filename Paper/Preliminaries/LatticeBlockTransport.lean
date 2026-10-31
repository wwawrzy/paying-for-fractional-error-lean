import Paper.Preliminaries.LatticeBlockPorts
namespace Paper.LatticeBlock

def coordinate {q m : ℕ} (x : Position q m) : Delta q := fun i => (x i).val

theorem neighbor_coordinate {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (v : Vertex b q m) (hv : Full s v.2) (p : Fin ((network O G H).degree v)) :
    coordinate ((network O G H).neighbor v p).2 =
      fun i=>coordinate v.2 i+(enumeration O (Fin.cast (full_degree O G H v.1 v.2 hv) p)).val i := by
  obtain ⟨j,x⟩:=v
  rw [neighbor_full O G H j x hv p]
  funext i
  have hh:=congrFun (shift_difference O x hv (enumeration O (Fin.cast (full_degree O G H j x hv) p))) i
  dsimp only [coordinate,difference] at *
  omega

theorem back_index {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (v : Vertex b q m) (hv : Full s v.2) (p : Fin ((network O G H).degree v))
    (hw : Full s ((network O G H).neighbor v p).2) :
    Fin.cast (full_degree O G H _ _ hw) ((network O G H).back v p)=
      reversePort O (Fin.cast (full_degree O G H _ _ hv) p) := by
  apply (enumeration O).injective
  apply Subtype.ext
  rw [reverse_offset]
  funext i
  have h1:=congrFun (neighbor_coordinate O G H v hv p) i
  have h2:=congrFun (neighbor_coordinate O G H ((network O G H).neighbor v p) hw ((network O G H).back v p)) i
  rw [(network O G H).reverse_neighbor] at h2
  change coordinate v.2 i = coordinate ((network O G H).neighbor v p).2 i +
    (enumeration O (Fin.cast (full_degree O G H _ _ hw) ((network O G H).back v p))).val i at h2
  omega

noncomputable def extendIds {b q m : ℕ} (j : Fin b) (ids : Vertex b q m→ℕ) (z : Delta q) : ℕ :=
  if hz : ∀ i, 0 ≤ z i ∧ z i < m then ids (j,fun i=>⟨(z i).toNat,by have h:=hz i;omega⟩) else 0

theorem extendIds_coordinate {b q m : ℕ} (j : Fin b) (ids : Vertex b q m→ℕ) (x : Position q m) :
    extendIds j ids (coordinate x)=ids (j,x) := by
  have hh : ∀ i, 0 ≤ coordinate x i ∧ coordinate x i < m := by
    intro i
    have hh:=(x i).isLt
    dsimp only [coordinate]
    omega
  rw [extendIds,dif_pos hh]
  congr 1
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.back_index
