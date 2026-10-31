import Paper.Owners.Separators.OwnerSeparator
import Paper.Owners.Construction.OwnerHighRepair

/-! The actual owner graph after the second repair has bounded degree and
uniform sublinear half-balanced separators of all induced subgraphs. -/
namespace Paper.PrunedOwnerStructure
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    let K := HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ
    0 < OwnerSeparator.constant a h L ∧
      SeparatorProfile.Bound K (OwnerSeparator.constant a h L) ∧ ∀ v, K.degree v ≤ Δ := by
  classical
  dsimp only
  let K := HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ
  let e : {v : D // v ∉ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ} → V := fun x => x.val.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have heD : ∀ x, e x ∈ D := fun x => x.val.property
  have hedge : ∀ x y, K.Adj x y →
      (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩ :=
    fun _ _ h => OwnerInteraction.graph_le_augmented G D R L h
  have hp : (0 : ℝ) < h := by linarith
  have hnat : 1 ≤ h := by
    have hpos : 0 < h := by exact_mod_cast hp
    omega
  exact ⟨OwnerSeparator.constant_pos a ha h L hnat hL,
    OwnerSeparator.represented_profile G D R L hL K e hinj heD hedge hden ha h hh,
    fun v => HighDegreeCut.degree_bound _ Δ v⟩
end Paper.PrunedOwnerStructure
