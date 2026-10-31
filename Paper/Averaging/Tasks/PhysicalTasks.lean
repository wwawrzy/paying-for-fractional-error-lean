import Paper.Owners.Construction.OwnerTasks
import Paper.Owners.Construction.OwnerExperiment

/-! Actual physical task graphs contain every useful candidate and every
task demand. Selecting the task owners covers all its demands. -/
namespace Paper.PhysicalTasks
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def centers (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) : Finset V :=
  I.image (fun d => d.val.val)

theorem centers_subset (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) : centers D Q I ⊆ D := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  exact i.val.property

theorem centers_card (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) : (centers D Q I).card = I.card :=
  Finset.card_image_of_injective _ (fun _ _ he => Subtype.ext (Subtype.ext he))

noncomputable def vertices (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q)) : Finset V :=
  Finset.univ.filter (fun v => OwnerSupport.owner G D v ∈ centers D Q I ∨
    v ∉ HeavyRepair.heavy G D R L ∧ (OwnerInteraction.actualSupport G D R L v ∩ centers D Q I).Nonempty)

noncomputable def graph (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q)) :
    SimpleGraph ↥(vertices G D R L Q I : Set V) := G.induce (vertices G D R L Q I : Set V)

theorem root_mem (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (d : Low D Q) (hd : d ∈ I) : d.val.val ∈ vertices G D R L Q I := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Or.inl ?_⟩
  rw [OwnerSupport.owner_center G D d.val.property]
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

theorem star_mem (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    {v : V} (hv : OwnerSupport.owner G D v ∈ centers D Q I) : v ∈ vertices G D R L Q I :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hv⟩

theorem demands_subset (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q)) :
    OwnerTasks.demands G D R L Q I B ⊆ vertices G D R L Q I := by
  intro r hr
  obtain ⟨d, hd, hdI, _⟩ := (Finset.mem_filter.mp hr).2
  apply star_mem G D R L Q I
  exact Finset.mem_image.mpr ⟨d, hdI, hd⟩

theorem service_subset (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q)) :
    OwnerTasks.service G D R L Q I B ⊆ vertices G D R L Q I := by
  intro v hv
  obtain ⟨d, hdI, _, hds⟩ := OwnerTasks.served_owner G D R L Q I B hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr
    ⟨OwnerTasks.light G D R L Q I B hv,
      ⟨d.val.val, Finset.mem_inter.mpr ⟨hds, Finset.mem_image.mpr ⟨d, hdI, rfl⟩⟩⟩⟩⟩

theorem candidates_complete (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    {r v : V} (hr : r ∈ OwnerTasks.demands G D R L Q I B) (hv : v ∈ closed G r) :
    v ∈ vertices G D R L Q I :=
  service_subset G D R L Q I B (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hv⟩)

theorem owner_cover (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q)) :
    OwnerTasks.demands G D R L Q I B ⊆ covered G (centers D Q I) := by
  intro r hr
  obtain ⟨d, hd, hdI, _⟩ := (Finset.mem_filter.mp hr).2
  have hs := OwnerExperiment.owner_star G D r
  rw [← hd] at hs
  refine Finset.mem_biUnion.mpr ⟨d.val.val, Finset.mem_image.mpr ⟨d, hdI, rfl⟩, ?_⟩
  exact (mem_closed G r d.val.val).mpr (hs.elim (fun he => Or.inl he.symm) Or.inr)
end Paper.PhysicalTasks
