import Paper.Owners.Construction.OwnerRoleInputsCorrect
import Paper.Solver.LocalSearch.SparseFractional

/-! Actual physical role-input construction followed by the real sparse
parallel fractional solver. No role lists or solver certificates are inputs. -/
namespace Paper.OwnerRoleSolver
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :=
  Program.seq (OwnerRoleInputs.program C L Δ r k t Q T s B hQ)
    (SparseFractional.program C (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
      (OwnerRoleInputs.capacity L Δ k Q T s) (4 * k) a B q M)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem role_run {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (hr : role ∈ TaggedDictionary.keys ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v)) :
    TaggedDictionary.lookup (((program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v).1) role =
      some ((FractionalSearch.program C (4 * k) a B q M).run
        (MaskedTaskGraph.graph G (SparseRolePrepare.vertices (fun u => TaggedDictionary.keys
          ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
            (fun w => ((decide (w ∈ D), decide (w ∈ S)), c w)) u)) role))
        (fun u => OwnerRoleInputsCorrect.expected G C D S L Δ k t Q T s B hQ c u role) v) := by
  apply SparseFractional.key_run G C (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
    (OwnerRoleInputs.capacity L Δ k Q T s) (4 * k) a B q M _
    (fun u => OwnerRoleInputs.key_bound G C D S hcover L Δ r k t Q T s B hQ (by omega) c u)
    (OwnerRoleInputsCorrect.expected G C D S L Δ k t Q T s B hQ c)
    (fun u => OwnerRoleInputsCorrect.consistent G C D S hcover L Δ r k t Q T s B hQ hks c u) v role hr

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).rounds =
      14 + 4 * r + RecursiveSearch.roundBound (4 * k) a M := by
  simp only [program, Program.rounds, OwnerRoleInputs.rounds, SparseFractional.rounds,
    FractionalSearch.rounds]
  omega

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).maxBits ≤
      max (OwnerRoleFrames.program C L Δ r k).maxBits
        (OwnerRoleInputs.capacity L Δ k Q T s *
          ((b + OwnerRoleInputs.metadataCount Δ k Q T s) +
            (FractionalSearch.program C (4 * k) a B q M).maxBits + 1)) := by
  simp only [program, Program.maxBits, OwnerRoleInputs.maxBits]
  exact max_le_max (le_refl _) (SparseFractional.maxBits C _ _ _ _ _ _ _)

end Paper.OwnerRoleSolver
