import Paper.Optimality.Treewidth.CliqueEightCanonical

/-! Transfer the two verified configurations to arbitrary vertex labels.
Only their edges need to be preserved; additional target edges are allowed. -/
namespace Paper.CliqueEightCanonicalTransfer
open SimpleGraph CliqueTwoContractions

theorem minor {V : Type} (G : SimpleGraph V) (five : Bool) (e : Fin 8 ↪ V)
    (hedge : ∀ i j, (CliqueEightCanonical.graph five).Adj i j → G.Adj (e i) (e j)) :
    (punctured 4 5).IsMinor G := by
  have hcopy : (CliqueEightCanonical.graph five).IsMinor G := by
    refine ⟨{
      branchSet := fun i => {e i}
      nonempty := fun _ => Set.singleton_nonempty _
      disjoint := fun i j hij => by
        rw [Set.disjoint_singleton]
        exact fun heq => hij (e.injective heq)
      connected := fun i => (MinorModel.refl G).connected (e i)
      adjacent := fun i j hij => ⟨e i, rfl, e j, rfl, hedge i j hij⟩ }⟩
  exact (CliqueEightCanonical.minor five).trans hcopy

end Paper.CliqueEightCanonicalTransfer
#print axioms Paper.CliqueEightCanonicalTransfer.minor
