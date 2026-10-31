import Paper.Averaging.Tasks.TaskRoleId

namespace Paper.TaskRoleSum
open scoped BigOperators
variable {V A : Type} [LinearOrder V] [AddCommMonoid A]

theorem space (anchors : Finset V) (M : ℕ) (f : TaskRoleId.Id V M → A) :
    (∑ r ∈ TaskRoleId.space anchors M, f r) =
      ∑ a ∈ anchors, ∑ i : Fin M, f (TaskRoleId.make a i) := by
  unfold TaskRoleId.space
  have hi : Function.Injective (toLex : V × Fin M → TaskRoleId.Id V M) :=
    fun _ _ h => congrArg (ofLex : TaskRoleId.Id V M → V × Fin M) h
  have hs : (∑ r ∈ (anchors ×ˢ (Finset.univ : Finset (Fin M))).image
      (toLex : V × Fin M → TaskRoleId.Id V M), f r) =
      ∑ p ∈ anchors ×ˢ (Finset.univ : Finset (Fin M)), f (toLex p) :=
    Finset.sum_image (fun _ _ _ _ h => hi h)
  rw [hs, Finset.sum_product]
  rfl

end Paper.TaskRoleSum
