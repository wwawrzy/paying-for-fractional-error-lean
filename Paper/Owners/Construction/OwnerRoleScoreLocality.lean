import Paper.Owners.Construction.OwnerRoleNumerator
import Paper.Owners.Construction.OwnerRoleZero
import Paper.Averaging.Tasks.RoleTaskConfigurationLocality

/-! Different padded metadata numbers representing the same task have
identical real physical solver output. Same-anchor communication masks
are proved equal from the actual all-metadata role lists. -/
namespace Paper.OwnerRoleScoreLocality
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def score {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v : V)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s)) : ℕ :=
  ((TaggedDictionary.lookup (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
    (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) role).getD 0).val

theorem same_task {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V)
    (r₁ r₂ : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (ha : (ofLex r₁).1 = (ofLex r₂).1)
    (hd : OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ r₁ =
      OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ r₂) :
    score G C D R L Δ r k t Q T s a B q M hQ c v r₁ =
      score G C D R L Δ r k t Q T s a B q M hQ c v r₂ := by
  let xs := (OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
    (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u))
  have hk : ∀ u, r₁ ∈ TaggedDictionary.keys (xs u) ↔ r₂ ∈ TaggedDictionary.keys (xs u) := by
    intro u
    dsimp only [xs]
    rw [OwnerRoleInputs.keys, TaskRoleId.mem_space, TaskRoleId.mem_space, ha]
  have hf : SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r₁ =
      SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r₂ := by
    ext u
    rw [SparseRolePrepare.mem_vertices, SparseRolePrepare.mem_vertices]
    exact hk u
  have hi : (fun u => OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c u r₁) =
      (fun u => OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c u r₂) := by
    funext u
    unfold OwnerRoleInputsCorrect.expected
    rw [hd]
  by_cases hr₁ : r₁ ∈ TaggedDictionary.keys (xs v)
  · have hr₂ := (hk v).mp hr₁
    unfold score
    rw [OwnerRoleSolver.role_run G C D R hcover L Δ r k t Q T s a B q M hQ hks c v r₁ hr₁,
      OwnerRoleSolver.role_run G C D R hcover L Δ r k t Q T s a B q M hQ hks c v r₂ hr₂]
    change ((FractionalSearch.program C (4 * k) a B q M).run
      (MaskedTaskGraph.graph G (SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r₁))
      (fun u => OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c u r₁) v).val =
      ((FractionalSearch.program C (4 * k) a B q M).run
      (MaskedTaskGraph.graph G (SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r₂))
      (fun u => OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c u r₂) v).val
    rw [hf, hi]
  · have hr₂ : r₂ ∉ TaggedDictionary.keys (xs v) := fun h => hr₁ ((hk v).mpr h)
    have hkeys : TaggedDictionary.keys (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
        (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) = TaggedDictionary.keys (xs v) := by
      rw [OwnerRoleNumerator.keys G C D R L Δ r k t Q T s a B q M hQ c v]
      exact (OwnerRoleInputs.keys G C D R L Δ r k t Q T s B hQ c v).symm
    unfold score
    rw [SparseFractionalZero.lookup_none _ r₁ (by rwa [hkeys]),
      SparseFractionalZero.lookup_none _ r₂ (by rwa [hkeys])]

end Paper.OwnerRoleScoreLocality
