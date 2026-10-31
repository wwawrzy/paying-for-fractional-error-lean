import Paper.Owners.Construction.HeavyComponent

/-! Failure of a weighted half-balanced separator constructs an actual
monotone haven, using heavy connected components after deletion. -/
namespace Paper.WeightedHaven
attribute [local instance] Classical.propDecidable
open DeletionComponents HeavyComponent
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Haven (k : ℕ) where
  region : Finset V → Finset V
  nonempty : ∀ X, X.card ≤ k → (region X).Nonempty
  connected : ∀ X, X.card ≤ k → (G.induce (region X : Set V)).Connected
  avoids : ∀ X, X.card ≤ k → Disjoint (region X) X
  closed : ∀ X, X.card ≤ k → ∀ u ∈ region X, ∀ v, v ∉ X → G.Adj u v → v ∈ region X
  monotone : ∀ X Y, X.card ≤ k → Y.card ≤ k → X ⊆ Y → region Y ⊆ region X

def Balanced (w : V → ℝ) (k : ℕ) : Prop :=
  ∃ X : Finset V, X.card ≤ k ∧ ∀ C : (deleted G X).ConnectedComponent,
    mass w (physical G X C) ≤ (∑ v, w v) / 2

theorem haven_of_not_balanced (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ)
    (hn : ¬ Balanced G w k) : Nonempty (Haven G k) := by
  classical
  have hex : ∀ X : Finset V, X.card ≤ k →
      ∃ C : (deleted G X).ConnectedComponent, (∑ v, w v) / 2 < mass w (physical G X C) := by
    intro X hX
    by_contra hc
    have hall : ∀ C : (deleted G X).ConnectedComponent, mass w (physical G X C) ≤ (∑ v, w v) / 2 := by
      intro C
      by_contra! hC
      exact hc ⟨C, hC⟩
    exact hn ⟨X, hX, hall⟩
  let region := fun X : Finset V => if h : X.card ≤ k then physical G X (hex X h).choose else ∅
  refine ⟨{
    region := region
    nonempty := ?_
    connected := ?_
    avoids := ?_
    closed := ?_
    monotone := ?_ }⟩
  · intro X hX
    simpa only [region, dif_pos hX] using DeletionComponents.nonempty G X (hex X hX).choose
  · intro X hX
    have he : region X = physical G X (hex X hX).choose := by
      dsimp only [region]
      exact dif_pos hX
    rw [he]
    exact DeletionComponents.connected G X (hex X hX).choose
  · intro X hX
    simpa only [region, dif_pos hX] using DeletionComponents.avoids G X (hex X hX).choose
  · intro X hX u hu v hv ha
    simp only [region, dif_pos hX] at hu ⊢
    exact DeletionComponents.closed G X (hex X hX).choose hu hv ha
  · intro X Y hX hY hXY
    simp only [region, dif_pos hX, dif_pos hY]
    exact HeavyComponent.nested G w hw X Y hXY _ _ (hex X hX).choose_spec (hex Y hY).choose_spec
end Paper.WeightedHaven
