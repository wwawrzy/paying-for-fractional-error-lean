import Paper.TotalDomination.ExactEndpoint
import Paper.Optimality.Treewidth.TreewidthDensity

/-! The actual algorithmic upper bound in fv:total:treewidth. The separate
optimality assertion requires the total-domination LOCAL lower bound. -/
namespace Paper.TotalDomination.TreewidthEndpoint
open BroadcastModel ExactEndpoint

theorem parameters (t : ℕ) (ht : 1 ≤ t) :
    ∃ A : Algorithm, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.treeWidth ≤ t → (∀ v, (G.neighborFinset v).Nonempty) →
      ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G A (t:ℚ) codec := by
  obtain ⟨A,hA⟩ := ExactEndpoint.minor_parameters (t:ℚ) (by exact_mod_cast ht)
  refine ⟨A,?_⟩
  intro V _ _ G _ htw hfree ids codec
  have hminor := TreewidthDensity.minor_density G t htw
  exact hA G (by simpa only [Rat.cast_natCast] using hminor) hfree codec

end Paper.TotalDomination.TreewidthEndpoint
#print axioms Paper.TotalDomination.TreewidthEndpoint.parameters
