import Paper.Owners.Construction.OwnerPublicTasks
import Paper.Owners.Construction.OwnerRoleTaskData
import Paper.Owners.Construction.OwnerMetadataCorrect

/-! The literal local role input is exactly the original physical task
input, after public parts/boundary are pulled back to the low-owner graph. -/
namespace Paper.RoleInputSemantics
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem active (D R : Finset V) (L : ℕ) (Q : Finset D) (d : OwnerRoleTaskData.Task V)
    (hvalid : d.valid = true) (hI : d.owners ⊆ PublicOwners.image D Q)
    {B : ℕ} (c : V → Fin (B + 1)) (v : V) :
    (OwnerRoleTaskData.input d (OwnerMetadataCorrect.expected G D R L v) (c v)).active =
      decide (v ∈ PhysicalTasks.vertices G D R L Q (OwnerPublicTasks.pull D Q d.owners)) := by
  simp only [OwnerRoleTaskData.input, hvalid, Bool.true_and, OwnerMetadataCorrect.expected]
  rw [decide_eq_decide, OwnerPublicTasks.mem_vertices G D R L Q d.owners hI v]
  have hh : (decide (L < (OwnerSupport.support G D R v).card) = false) ↔
      v ∉ HeavyRepair.heavy G D R L := by
    simp only [decide_eq_false_iff_not, HeavyRepair.heavy, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hh]

theorem demand (D R : Finset V) (L : ℕ) (Q : Finset D) (d : OwnerRoleTaskData.Task V)
    (hvalid : d.valid = true) (hI : d.owners ⊆ PublicOwners.image D Q)
    (boundary : Finset V) (hb : ∀ u ∈ d.owners, d.boundary u = decide (u ∈ boundary))
    {B : ℕ} (c : V → Fin (B + 1)) (v : V) :
    (OwnerRoleTaskData.input d (OwnerMetadataCorrect.expected G D R L v) (c v)).demand =
      decide (v ∈ OwnerTasks.demands G D R L Q (OwnerPublicTasks.pull D Q d.owners)
        (OwnerPublicTasks.pull D Q boundary)) := by
  simp only [OwnerRoleTaskData.input, hvalid, Bool.true_and, OwnerMetadataCorrect.expected]
  simp only [OwnerPublicTasks.mem_demands G D R L Q d.owners boundary hI v]
  by_cases ho : OwnerSupport.owner G D v ∈ d.owners
  · rw [hb _ ho]
    simp only [Bool.decide_and, decide_not, Bool.and_assoc]
    rfl
  · simp [ho]

theorem cost (D R : Finset V) (L : ℕ) (d : OwnerRoleTaskData.Task V)
    {B : ℕ} (c : V → Fin (B + 1)) (v : V) :
    (OwnerRoleTaskData.input d (OwnerMetadataCorrect.expected G D R L v) (c v)).cost = c v := rfl

end Paper.RoleInputSemantics
