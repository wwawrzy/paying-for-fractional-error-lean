import Paper.Preliminaries.SevenFoundation
import GraphTheory.SimpleGraph.Domination.Total

namespace Paper.IntegralFractionalOptima
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem dominates_iff (D : Finset V) : dominates G D ↔ G.IsDominatingSetFinset D := by
  constructor
  · intro h v
    obtain ⟨w, hw, hv⟩ := Finset.mem_biUnion.mp (h v)
    rcases (mem_closed G _ _).mp hv with he | ha
    · exact Or.inl (he ▸ hw)
    · exact Or.inr ⟨w, hw, ha.symm⟩
  · intro h v
    rcases h v with hv | ⟨w, hw, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv, (mem_closed G _ _).mpr (Or.inl rfl)⟩
    · exact Finset.mem_biUnion.mpr ⟨w, hw, (mem_closed G _ _).mpr (Or.inr ha.symm)⟩

theorem fractional_nonneg : 0 ≤ fractionalNumber G := by
  apply le_csInf (feasibleCosts_nonempty G)
  rintro _ ⟨x, hx, rfl⟩
  exact cost_nonneg_of_feasible _ _ hx

theorem fractional_le_domination : fractionalNumber G ≤ (G.dominationNumber : ℝ) := by
  obtain ⟨D, hD, he⟩ := SimpleGraph.exists_isDominatingSetFinset_card_eq_dominationNumber (G := G)
  have hh := fractionalNumber_le_integral G D ((dominates_iff G D).mpr hD)
  simpa only [he] using hh

end Paper.IntegralFractionalOptima
