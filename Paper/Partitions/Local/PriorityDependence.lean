import Paper.Partitions.Local.PriorityPartition
import Paper.Partitions.Local.LocalPriorityIndex

/-! The actual partition depends only on priorities of original connected
sets of size at most k. All other coordinates can be normalized away. -/
namespace Paper.PriorityDependence
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem accepted_congr {Q : ℕ} (F : Finset (Finset V)) (ω τ : Finset V → Fin Q)
    (he : ∀ U ∈ F, ω U = τ U) : SparsePriority.accepted F ω = SparsePriority.accepted F τ := by
  ext U
  simp only [SparsePriority.accepted, Finset.mem_filter]
  constructor <;> rintro ⟨hUF, hU⟩
  · refine ⟨hUF, hU.1, ?_, ?_⟩
    · simpa only [he U hUF] using hU.2.1
    · intro T hT hne hd
      simpa only [he T hT] using hU.2.2 T hT hne hd
  · refine ⟨hUF, hU.1, ?_, ?_⟩
    · simpa only [he U hUF] using hU.2.1
    · intro T hT hne hd
      simpa only [he T hT] using hU.2.2 T hT hne hd

def Agree (k : ℕ) {Q : ℕ} (ω τ : Finset V → Fin Q) : Prop :=
  ∀ U : LocalPriorityIndex.Domain G k, ω U.val = τ U.val

def SeedAgree (k : ℕ) {Q : ℕ} :
    (n : ℕ) → FiniteIteration.Seeds (Finset V → Fin Q) n →
      FiniteIteration.Seeds (Finset V → Fin Q) n → Prop
  | 0, _, _ => True
  | n + 1, ω, τ => Agree G k ω.1 τ.1 ∧ SeedAgree k n ω.2 τ.2

theorem stage_congr (k : ℕ) (ε : ℝ) {Q : ℕ} (ω τ : Finset V → Fin Q) (he : Agree G k ω τ)
    (S : Finset V) : SparsePriority.accepted (EligibleSets.family G S k ε) ω =
      SparsePriority.accepted (EligibleSets.family G S k ε) τ := by
  apply accepted_congr
  intro U hU
  have hh := (EligibleSets.mem_family G S U k ε).mp hU
  exact he ⟨U, hh.2.1, hh.2.2.1⟩

theorem parts_congr (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω τ : FiniteIteration.Seeds (Finset V → Fin Q) n) (he : SeedAgree G k n ω τ) :
    (PriorityPartition.partition G k hk ε S n ω).parts =
      (PriorityPartition.partition G k hk ε S n τ).parts := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    have hstage := stage_congr G k ε ω.1 τ.1 he.1 S
    have hnext : PriorityStage.next G S k ε ω.1 = PriorityStage.next G S k ε τ.1 :=
      congrArg (fun A : Finset (Finset V) => S \ A.biUnion id) hstage
    simp only [PriorityPartition.parts_succ]
    rw [hstage, hnext]
    exact congrArg (fun A => SparsePriority.accepted (EligibleSets.family G S k ε) τ.1 ∪ A)
      (ih (PriorityStage.next G S k ε τ.1) ω.2 τ.2 he.2)
end Paper.PriorityDependence
