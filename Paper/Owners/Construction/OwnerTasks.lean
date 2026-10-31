import Paper.Owners.Construction.BoundaryOwners
import Paper.Owners.Construction.OwnerInteraction
import Paper.Preliminaries.PartMembership

/-! Actual task demands and useful physical candidates after owner repairs.
Distinct interior owner parts have disjoint useful candidate sets, even
though their communication graphs may overlap. -/
namespace Paper.OwnerTasks
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Low (D : Finset V) (Q : Finset D) := {d : D // d ∉ Q}

noncomputable def graph (D R : Finset V) (L : ℕ) (Q : Finset D) : SimpleGraph (Low D Q) :=
  (OwnerInteraction.graph G D R L).induce {d | d ∉ Q}

noncomputable def demands (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I B : Finset (Low D Q)) : Finset V :=
  (OwnerInteraction.remaining G D R L).filter (fun r =>
    ∃ d : Low D Q, d.val.val = OwnerSupport.owner G D r ∧ d ∈ I ∧ d ∉ B)

noncomputable def service (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I B : Finset (Low D Q)) : Finset V :=
  Finset.univ.filter (fun v => ∃ r ∈ demands G D R L Q I B, v ∈ closed G r)

theorem served_owner (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I B : Finset (Low D Q)) {v : V} (hv : v ∈ service G D R L Q I B) :
    ∃ d : Low D Q, d ∈ I ∧ d ∉ B ∧ d.val.val ∈ OwnerInteraction.actualSupport G D R L v := by
  obtain ⟨r, hr, hvr⟩ := (Finset.mem_filter.mp hv).2
  have hh := Finset.mem_filter.mp hr
  obtain ⟨d, hd, hdI, hdB⟩ := hh.2
  refine ⟨d, hdI, hdB, ?_⟩
  exact Finset.mem_image.mpr ⟨r, Finset.mem_inter.mpr ⟨(closed_symm G v r).mp hvr, hh.1⟩, hd.symm⟩

theorem light (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I B : Finset (Low D Q)) {v : V} (hv : v ∈ service G D R L Q I B) :
    v ∉ HeavyRepair.heavy G D R L := by
  obtain ⟨d, _, _, hd⟩ := served_owner G D R L Q I B hv
  intro hvh
  rw [OwnerInteraction.heavy_empty G D R L hvh] at hd
  exact Finset.notMem_empty _ hd

set_option maxHeartbeats 1000000 in
theorem service_disjoint (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (graph G D R L Q) Finset.univ k)
    (I J : Finset (Low D Q)) (hI : I ∈ P.parts) (hJ : J ∈ P.parts) (hne : I ≠ J) :
    let B := BoundaryOwners.vertices (graph G D R L Q) Finset.univ P.parts
    Disjoint (service G D R L Q I B) (service G D R L Q J B) := by
  classical
  dsimp only
  let B := BoundaryOwners.vertices (graph G D R L Q) Finset.univ P.parts
  apply Finset.disjoint_left.mpr
  intro v hvI hvJ
  obtain ⟨i, hiI, hiB, his⟩ := served_owner G D R L Q I B hvI
  obtain ⟨j, hjJ, _, hjs⟩ := served_owner G D R L Q J B hvJ
  by_cases hij : i = j
  · exact hne (PartMembership.unique _ P hI hJ hiI (hij ▸ hjJ))
  · have ha : (graph G D R L Q).Adj i j :=
      ⟨fun he => hij (Subtype.ext he), v, his, hjs⟩
    obtain ⟨U, hU, hiU, hjU⟩ := BoundaryOwners.same_part (graph G D R L Q) Finset.univ P.parts
      (Finset.mem_univ i) (Finset.mem_univ j) ha hiB
    exact hne ((PartMembership.unique _ P hI hU hiI hiU).trans
      (PartMembership.unique _ P hU hJ hjU hjJ))
end Paper.OwnerTasks
