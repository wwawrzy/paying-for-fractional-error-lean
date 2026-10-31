import Paper.Preliminaries.PartAssembly
import Paper.Partitions.Local.PriorityCost

/-! The actual output partition of the finite priority iteration. Accepted
sets become parts, and final surviving vertices become singleton parts. -/
namespace Paper.PriorityPartition
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def partition (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V) :
    (n : ℕ) → FiniteIteration.Seeds (Finset V → Fin Q) n → SmallParts.Data G S k
  | 0, _ => PartAssembly.singletons G S k hk
  | n + 1, ω => by
    let F := EligibleSets.family G S k ε
    let A := SparsePriority.accepted F ω.1
    have hF : ∀ U ∈ A, U ∈ EligibleSets.family G S k ε :=
      fun U hU => (Finset.mem_filter.mp hU).1
    let P := partition k hk ε (PriorityStage.next G S k ε ω.1) n ω.2
    exact PartAssembly.merge G S k A
      (fun U hU => ((EligibleSets.mem_family G S U k ε).mp (hF U hU)).1)
      (fun U hU => by
        have hc := ((EligibleSets.mem_family G S U k ε).mp (hF U hU)).2.1
        obtain ⟨v⟩ := hc.nonempty
        exact ⟨v.val, v.property⟩)
      (fun U hU => ((EligibleSets.mem_family G S U k ε).mp (hF U hU)).2.1)
      (fun U hU => ((EligibleSets.mem_family G S U k ε).mp (hF U hU)).2.2.1)
      (SparsePriority.disjoint F ω.1) P

theorem parts_zero (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) 0) :
    (partition G k hk ε S 0 ω).parts = S.image (fun v => {v}) := rfl

theorem parts_succ (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) (n + 1)) :
    (partition G k hk ε S (n + 1) ω).parts =
      SparsePriority.accepted (EligibleSets.family G S k ε) ω.1 ∪
      (partition G k hk ε (PriorityStage.next G S k ε ω.1) n ω.2).parts := rfl
end Paper.PriorityPartition
