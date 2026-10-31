import Paper.Partitions.Separators.WeightedSeparator

/-! Uniform half-balanced separators of all actual induced subgraphs. -/
namespace Paper.SeparatorProfile
attribute [local instance] Classical.propDecidable
open DeletionComponents
variable {A : Type*} [Fintype A] [DecidableEq A]

def Bound (J : SimpleGraph A) [DecidableRel J.Adj] (C : ℝ) : Prop :=
  ∀ I : Finset A, ∃ X : Finset ↥(I : Set A), (X.card : ℝ) ≤ C * Real.sqrt I.card ∧
    ∀ D : (deleted (J.induce (I : Set A)) X).ConnectedComponent,
      ((physical (J.induce (I : Set A)) X D).card : ℝ) ≤ (I.card : ℝ) / 2
end Paper.SeparatorProfile
