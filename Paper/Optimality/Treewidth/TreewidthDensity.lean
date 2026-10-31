import Paper.Optimality.Treewidth.TreewidthLowDegree
import Paper.Optimality.Treewidth.TreewidthMinor
import Paper.Preliminaries.MinorDensity
import GraphTheory.SimpleGraph.Degeneracy

/-! The actual classical treewidth-to-minor-density implication. The
minor decomposition, low-degree elimination and edge count are proved. -/
namespace Paper.TreewidthDensity
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem induced_degree (S : Finset V) (v : ↥(S : Set V)) :
    (G.induce (S : Set V)).degree v = G.inducedDegree v.val S := by
  classical
  have he : ((G.induce (S : Set V)).neighborFinset v).image Subtype.val = S.filter (G.Adj v.val) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, (SimpleGraph.mem_neighborFinset _ v z).mp hz⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨w, hw⟩, (SimpleGraph.mem_neighborFinset _ v ⟨w, hw⟩).mpr ha, rfl⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

theorem degeneracy (t : ℕ) (ht : G.treeWidth ≤ t) : G.IsKDegenerate t := by
  classical
  intro S hS
  letI : Nonempty ↥(S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hminor : (G.induce (S : Set V)).IsMinor G := IsMinor.of_induce G _
  have hw : (G.induce (S : Set V)).treeWidth ≤ t := (TreewidthMinor.treeWidth_mono hminor).trans ht
  obtain ⟨v, hv⟩ := TreewidthLowDegree.of_treeWidth t hw
  exact ⟨v.val, v.property, (induced_degree G S v) ▸ hv⟩

theorem edge_bound (t : ℕ) (ht : G.treeWidth ≤ t) : G.edgeFinset.card ≤ t * Fintype.card V :=
  IsKDegenerate.edgeFinset_card_le_mul_card G (degeneracy G t ht)

theorem minor_density (t : ℕ) (ht : G.treeWidth ≤ t) : MinorDensity.Bound G (t : ℝ) := by
  intro A _ _ J _ hm
  have hw : J.treeWidth ≤ t := (TreewidthMinor.treeWidth_mono hm).trans ht
  exact_mod_cast edge_bound J t hw

end Paper.TreewidthDensity
