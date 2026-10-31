import Paper.Owners.Construction.OwnerGraphCount

/-! Induced density of both actual owner graphs from physical minor density.
The sufficient constant a*(L+1)^4 is larger than the paper's sharper
2aL. It remains a fixed structural constant and does not affect exact 7. -/
namespace Paper.OwnerDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem augmented_density (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    Incidence.InducedDensityBound (OwnerInteraction.augmentedGraph G D R L)
      (a * ((L + 1 : ℕ) : ℝ) ^ 4) := by
  classical
  intro S
  let J := (OwnerInteraction.augmentedGraph G D R L).induce (S : Set D)
  let e : ↥(S : Set D) → V := fun x => x.val.val
  have hinj : Function.Injective e := by
    intro x y he
    exact Subtype.ext (Subtype.ext he)
  have heD : ∀ x : (S : Set D), e x ∈ D := fun x => x.val.property
  have hedge : ∀ x y : (S : Set D), J.Adj x y →
      (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩ := fun _ _ h => h
  have hh := OwnerGraphCount.count G D R L hL J e hinj heD hedge hden ha
  change (J.edgeFinset.card : ℝ) ≤ _
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh

theorem actual_density (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    Incidence.InducedDensityBound (OwnerInteraction.graph G D R L)
      (a * ((L + 1 : ℕ) : ℝ) ^ 4) := by
  classical
  intro S
  have hle : (OwnerInteraction.graph G D R L).induce (S : Set D) ≤
      (OwnerInteraction.augmentedGraph G D R L).induce (S : Set D) :=
    fun _ _ h => OwnerInteraction.graph_le_augmented G D R L h
  have hc := Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  have hc' : (((OwnerInteraction.graph G D R L).induce (S : Set D)).edgeFinset.card : ℝ) ≤
      ((OwnerInteraction.augmentedGraph G D R L).induce (S : Set D)).edgeFinset.card := by exact_mod_cast hc
  exact hc'.trans (augmented_density G D R L hL hden ha S)
end Paper.OwnerDensity
