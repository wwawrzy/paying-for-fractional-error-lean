import Mathlib

/-! A finite local priority rule. A set is accepted when its priority is
zero and every intersecting competing set has a nonzero priority.
Accepted sets are disjoint; no global partition oracle is used. -/
namespace Paper.SparsePriority
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [DecidableEq V]

def Accepted {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) (S : Finset V) : Prop :=
  S ∈ F ∧ (ω S).val = 0 ∧ ∀ T ∈ F, T ≠ S → ¬ Disjoint S T → (ω T).val ≠ 0

noncomputable def accepted {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) : Finset (Finset V) :=
  F.filter (Accepted F ω)

noncomputable def removed {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) : Finset V :=
  (accepted F ω).biUnion id

theorem disjoint {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) :
    (accepted F ω : Set (Finset V)).Pairwise Disjoint := by
  intro S hS T hT hne
  by_contra hd
  have hs := (Finset.mem_filter.mp hS).2
  have ht := (Finset.mem_filter.mp hT).2
  exact hs.2.2 T ht.1 hne.symm hd ht.2.1

theorem subset {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) (S : Finset V)
    (hF : ∀ U ∈ F, U ⊆ S) : removed F ω ⊆ S := by
  intro v hv
  obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
  exact hF U (Finset.mem_filter.mp hU).1 hv

theorem removed_card {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) :
    (removed F ω).card = ∑ U ∈ accepted F ω, U.card :=
  Finset.card_biUnion (disjoint F ω)
end Paper.SparsePriority
