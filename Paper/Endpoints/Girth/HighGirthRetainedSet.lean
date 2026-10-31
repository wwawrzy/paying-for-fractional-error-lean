import Paper.Endpoints.Girth.HighGirthRetainedParts

/-! The actual retained parts, chosen from the proved construction, and their
union in the original vertex type. No size or density bound is assumed. -/
namespace Paper.HighGirthRetainedSet
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def parts := Classical.choose (HighGirthRetainedParts.retained_component_parts_exist G x)

theorem parts_spec :
    ∀ K, (parts G x K).Nonempty ∧ (parts G x K) ⊆ Paper.HighGirthFreePaths.members G x K ∧
      (G.induce (↑(parts G x K) : Set V)).Connected ∧
      (∀ u ∈ Paper.HighGirthFreePaths.members G x K, u ∈ Paper.HighGirthAttachments.vertices G x → u ∈ (parts G x K)) ∧
      (¬ Paper.HighGirthFreePaths.isFreePath G x K → (parts G x K) = Paper.HighGirthFreePaths.members G x K) ∧
      (Paper.HighGirthFreePaths.isFreePath G x K →
        (parts G x K).card + 4 ≤ 5 * Paper.HighGirthComponentAttachments.count G x K ∧
        (Paper.HighGirthComponentAttachments.count G x K = 2 →
          K ∉ Paper.HighGirthFewAttachments.twoFamily G x → (parts G x K).card ≤ 5)) := Classical.choose_spec (HighGirthRetainedParts.retained_component_parts_exist G x)

noncomputable def vertices : Finset V := by
  classical
  exact Finset.univ.biUnion (parts G x)

end Paper.HighGirthRetainedSet
#print axioms Paper.HighGirthRetainedSet.parts
#print axioms Paper.HighGirthRetainedSet.parts_spec
#print axioms Paper.HighGirthRetainedSet.vertices
