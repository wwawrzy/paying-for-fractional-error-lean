import Paper.Averaging.Tasks.PhysicalTasks

/-! Every actual original demand is covered by a repair or belongs to an
interior physical task. All three repair cases are explicit. -/
namespace Paper.TaskDecomposition
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def highCenters (D : Finset V) (Q : Finset D) : Finset V := Q.image Subtype.val

theorem covers (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (Q : Finset D)
    (B : Finset (Low D Q)) (k : ℕ) (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    {r : V} (hr : r ∈ R) :
    r ∈ covered G (HeavyRepair.heavy G D R L) ∨
      r ∈ covered G (highCenters D Q) ∨
      r ∈ covered G (PhysicalTasks.centers D Q B) ∨
      ∃ I ∈ P.parts, r ∈ OwnerTasks.demands G D R L Q I B := by
  classical
  by_cases hheavy : r ∈ covered G (HeavyRepair.heavy G D R L)
  · exact Or.inl hheavy
  · right
    have hrem : r ∈ OwnerInteraction.remaining G D R L := Finset.mem_sdiff.mpr ⟨hr, hheavy⟩
    have ho := OwnerSupport.owner_of_covered G D (hcover hr)
    let d : D := ⟨OwnerSupport.owner G D r, ho.1⟩
    have hrd : r ∈ closed G d.val := (mem_closed G r d.val).mpr
      (ho.2.elim (fun he => Or.inl he.symm) Or.inr)
    by_cases hd : d ∈ Q
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨d.val, Finset.mem_image.mpr ⟨d, hd, rfl⟩, hrd⟩)
    · right
      let i : Low D Q := ⟨d, hd⟩
      by_cases hi : i ∈ B
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨d.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hrd⟩)
      · right
        obtain ⟨I, hI, hiI⟩ := P.covers i (Finset.mem_univ _)
        exact ⟨I, hI, Finset.mem_filter.mpr ⟨hrem, i, rfl, hiI, hi⟩⟩
end Paper.TaskDecomposition
