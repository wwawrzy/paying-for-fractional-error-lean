import Paper.Partitions.Local.SparsePriority
import Paper.Endpoints.Rounding.FiniteZeroSelection

/-! The actual local priority rule accepts each set with frequency at least
1/(2Q), by exact finite counting. This weaker constant is sufficient. -/
namespace Paper.PriorityAcceptance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def conflicts (F : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  F.filter (fun T => T ≠ S ∧ ¬ Disjoint S T)

theorem frequency (F : Finset (Finset V)) (S : Finset V) (hS : S ∈ F)
    (Q : ℕ) (hQ : 0 < Q) (hconf : 2 * (conflicts F S).card ≤ Q) :
    Fintype.card (Finset V → Fin Q) ≤
      2 * Q * (Finset.univ.filter (fun ω : Finset V → Fin Q => SparsePriority.Accepted F ω S)).card := by
  have hs : S ∉ conflicts F S := by simp [conflicts]
  have he : FiniteZeroSelection.good Q S (conflicts F S) =
      Finset.univ.filter (fun ω : Finset V → Fin Q => SparsePriority.Accepted F ω S) := by
    ext ω
    simp only [FiniteZeroSelection.good, Finset.mem_filter, Finset.mem_univ, true_and,
      SparsePriority.Accepted, hS, conflicts]
    constructor
    · rintro ⟨hzero, hrest⟩
      refine ⟨hzero, ?_⟩
      intro T hT hne hd
      exact hrest T ⟨hT, hne, hd⟩
    · rintro ⟨hzero, hrest⟩
      refine ⟨hzero, ?_⟩
      intro T hT
      exact hrest T hT.1 hT.2.1 hT.2.2
  rw [← he]
  exact FiniteZeroSelection.count Q hQ S (conflicts F S) hs hconf
end Paper.PriorityAcceptance
