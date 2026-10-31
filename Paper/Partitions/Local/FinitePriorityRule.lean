import Paper.Preliminaries.FiniteEligibility
import Paper.Partitions.Local.FinitePriorityIndex
import Paper.Partitions.Local.SparsePriority
import Paper.Partitions.Local.PriorityStage

/-! Computable finite zero-priority acceptance. Only the supplied finite
candidate family is traversed; no real comparisons or choice of a part. -/
namespace Paper.FinitePriorityRule
variable {V : Type} [LinearOrder V]

def accepted {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) : Finset (Finset V) :=
  F.filter (fun S => (ω S).val = 0 ∧ ∀ T ∈ F, T ≠ S → ¬ Disjoint S T → (ω T).val ≠ 0)

def removed {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) : Finset V :=
  (accepted F ω).biUnion id

def part {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) (v : V) : Finset V :=
  (accepted F ω).biUnion (fun U => if v ∈ U then U else ∅)

def next {Q : ℕ} (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (ω : Finset V → Fin Q) : Finset V := S \ removed (FiniteEligibility.family N S k t) ω

theorem accepted_eq {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) :
    accepted F ω = SparsePriority.accepted F ω := by
  ext S
  simp only [accepted, SparsePriority.accepted, SparsePriority.Accepted, Finset.mem_filter]
  tauto

theorem removed_eq {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q) :
    removed F ω = SparsePriority.removed F ω := by
  rw [removed, SparsePriority.removed, accepted_eq]

theorem part_eq {Q : ℕ} (F : Finset (Finset V)) (ω : Finset V → Fin Q)
    (U : Finset V) (hU : U ∈ accepted F ω) (v : V) (hv : v ∈ U) : part F ω v = U := by
  ext u
  constructor
  · intro hu
    obtain ⟨T, hT, hu⟩ := Finset.mem_biUnion.mp hu
    split_ifs at hu with hvt
    · have he : T = U := by
        by_contra hne
        have hd := SparsePriority.disjoint F ω (accepted_eq F ω ▸ hT) (accepted_eq F ω ▸ hU) hne
        exact Finset.disjoint_left.mp hd hvt hv
      exact he ▸ hu
    · exact False.elim (Finset.notMem_empty u hu)
  · intro hu
    apply Finset.mem_biUnion.mpr
    exact ⟨U, hU, by simpa only [if_pos hv] using hu⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem next_correct (S : Finset V) (k t : ℕ) (ht : 0 < t) {Q : ℕ}
    (ω : Finset V → Fin Q) :
    next (fun u => G.neighborFinset u) S k t ω = PriorityStage.next G S k (1 / (t : ℝ)) ω := by
  rw [next, FiniteEligibility.correct G S k t ht, removed_eq]
  rfl
end Paper.FinitePriorityRule
