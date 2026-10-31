import Paper.RedBlue.IncidenceDensity
import Paper.Solver.LocalSearch.GeneralCoveringFractionalEndpoint

/-! Local red-blue incidence input for the executed general covering solver. -/
namespace Paper.RedBlue
open SevenFoundation
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def targets (R B : Finset V) (v : V) : Finset V :=
  if v ∈ B then G.neighborFinset v ∩ R else ∅

theorem targets_incidence (R B : Finset V) (v r : V) :
    r ∈ targets G R B v ↔ v ∈ rows G R B r := by
  rw [mem_rows]
  by_cases hv : v ∈ B <;>
    simp [targets, hv, G.adj_comm, and_comm, and_left_comm]

noncomputable def solverInput {M : ℕ} (R B : Finset V)
    (c : V → Fin (M + 1)) (v : V) : GeneralCoveringFractionalEndpoint.Input V M :=
  (⟨decide (v ∈ R), rows G R B v, targets G R B v⟩, c v)

noncomputable def solverOriginal {M : ℕ} (R B : Finset V)
    (c : V → Fin (M + 1)) (hne : ∀ r ∈ R, (rows G R B r).Nonempty) :
    GeneralCoveringInitializedFrameAverage.Original G (solverInput G R B c) where
  cover := rows G R B
  targets := targets G R B
  R := R
  incidence := targets_incidence G R B
  local_rows := fun r _ => rows_local G R B r
  rows := hne
  residual := fun _ => rfl
  candidates := fun _ => rfl
  inverse := fun _ => rfl

theorem admissible_subset_blue (R B : Finset V) :
    CoveringSupport.admissible (rows G R B) R ⊆ B := by
  intro v hv
  obtain ⟨r, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact ((mem_rows G R B r v).mp hv).2.2

theorem feasible_blue_support {M : ℕ} (R B : Finset V)
    (c : V → Fin (M + 1)) (x : V → ℝ)
    (hx : feasible (GeneralCoveringFractionalCorrect.coverInstance R (rows G R B) c) x) :
    ∀ v ∉ B, x v = 0 := by
  intro v hv
  exact hx.2.1 v (fun h => hv (admissible_subset_blue G R B h))

end Paper.RedBlue
#print axioms Paper.RedBlue.targets_incidence
#print axioms Paper.RedBlue.solverOriginal
#print axioms Paper.RedBlue.admissible_subset_blue
#print axioms Paper.RedBlue.feasible_blue_support
