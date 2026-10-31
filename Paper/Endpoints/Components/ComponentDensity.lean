import Paper.Preliminaries.Incidence

/-! Induced density passes to a logical spanning subgraph and to a larger
public parameter. The natural ceiling supplies the integer search parameter.
These are structural proofs, with no runtime graph constructor. -/

namespace Paper.ComponentDensity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting edges cannot increase any induced edge count. -/
theorem subgraph_density (G I : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel I.Adj]
    (hle : I ≤ G) {a : ℝ} (hden : Incidence.InducedDensityBound G a) :
    Incidence.InducedDensityBound I a := by
  classical
  intro S
  have hi : I.induce (S : Set V) ≤ G.induce (S : Set V) := by
    intro u v huv
    exact hle huv
  have he : I.inducedEdgeCount S ≤ G.inducedEdgeCount S :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hi)
  have heR : (I.inducedEdgeCount S : ℝ) ≤ (G.inducedEdgeCount S : ℝ) := by
    exact_mod_cast he
  exact heR.trans (hden S)

/-- Increasing the density parameter preserves every induced estimate. -/
theorem density_mono (I : SimpleGraph V) [DecidableRel I.Adj] {a t : ℝ}
    (hat : a ≤ t) (hden : Incidence.InducedDensityBound I a) :
    Incidence.InducedDensityBound I t := by
  intro S
  exact (hden S).trans (mul_le_mul_of_nonneg_right hat (Nat.cast_nonneg S.card))

/-- Any natural parameter above the original real bound works on the subgraph. -/
theorem nat_bound (G I : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel I.Adj]
    (hle : I ≤ G) {a : ℝ} (hden : Incidence.InducedDensityBound G a)
    (p : ℕ) (hap : a ≤ (p : ℝ)) : Incidence.InducedDensityBound I (p : ℝ) :=
  density_mono I hap (subgraph_density G I hle hden)

/-- The public ceiling is positive and is a valid integer density parameter. -/
theorem ceil_bound (G I : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel I.Adj]
    (hle : I ≤ G) (a : ℝ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a) :
    1 ≤ Nat.ceil a ∧ Incidence.InducedDensityBound I (Nat.ceil a : ℝ) := by
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), ?_⟩
  exact nat_bound G I hle hden (Nat.ceil a) (Nat.le_ceil a)

end Paper.ComponentDensity

#print axioms Paper.ComponentDensity.subgraph_density
#print axioms Paper.ComponentDensity.density_mono
#print axioms Paper.ComponentDensity.nat_bound
#print axioms Paper.ComponentDensity.ceil_bound
