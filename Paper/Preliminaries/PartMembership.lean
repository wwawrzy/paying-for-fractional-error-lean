import Paper.Preliminaries.SmallParts

/-! Uniqueness of the part containing a physical vertex. -/
namespace Paper.PartMembership
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem unique {S : Finset V} {k : ℕ} (P : SmallParts.Data G S k)
    {U W : Finset V} (hU : U ∈ P.parts) (hW : W ∈ P.parts) {v : V}
    (hvU : v ∈ U) (hvW : v ∈ W) : U = W := by
  by_contra hn
  exact Finset.disjoint_left.mp (P.disjoint hU hW hn) hvU hvW
end Paper.PartMembership
