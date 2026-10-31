import Paper.Owners.Construction.OwnerVirtualCorrect
import Paper.Averaging.Tasks.TaskDecomposition

namespace Paper.OwnerRepairFlags
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem heavy {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) (v : V) :
    (OwnerVirtualCorrect.learned G C D R L Δ v).metadata.heavy =
      decide (v ∈ HeavyRepair.heavy G D R L) := by
  rw [OwnerVirtualCorrect.metadata_correct]
  change decide (L < (OwnerSupport.support G D R v).card) = _
  rw [decide_eq_decide]
  simp only [HeavyRepair.heavy, Finset.mem_filter, Finset.mem_univ, true_and]

theorem high_member (D : Finset V) (Q : Finset D) (v : V) (hv : v ∈ D) :
    v ∈ TaskDecomposition.highCenters D Q ↔ (⟨v, hv⟩ : D) ∈ Q := by
  unfold TaskDecomposition.highCenters
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, he⟩
    have hh : d = (⟨v, hv⟩ : D) := Subtype.ext he
    exact hh ▸ hd
  · intro hd
    exact ⟨⟨v, hv⟩, hd, rfl⟩

theorem high_subset (D : Finset V) (Q : Finset D) : TaskDecomposition.highCenters D Q ⊆ D := by
  intro v hv
  unfold TaskDecomposition.highCenters at hv
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hv
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hv
  exact d.property

theorem high {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (v : V) :
    ((OwnerVirtualCorrect.learned G C D R L Δ v).metadata.center &&
      (OwnerVirtualCorrect.learned G C D R L Δ v).high) =
      decide (v ∈ TaskDecomposition.highCenters D (OwnerVirtualFacts.high G D R L Δ)) := by
  rw [OwnerVirtualCorrect.metadata_correct]
  change (decide (v ∈ D) && _) = _
  by_cases hv : v ∈ D
  · rw [decide_eq_true hv, Bool.true_and, OwnerVirtualCorrect.high_correct G C D R hcover L Δ ⟨v, hv⟩]
    rw [decide_eq_decide, high_member D _ v hv]
  · have hh : v ∉ TaskDecomposition.highCenters D (OwnerVirtualFacts.high G D R L Δ) :=
      fun h => hv (high_subset D _ h)
    rw [decide_eq_false hv, Bool.false_and, decide_eq_false hh]

end Paper.OwnerRepairFlags
