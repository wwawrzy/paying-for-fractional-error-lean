import Paper.Preliminaries.FiniteEligibility
import Paper.Preliminaries.FiniteConnectivityLocality

/-! Local membership in the candidate family depends only on the candidate
and the residual membership of its actual neighbors. -/
namespace Paper.FiniteEligibilityLocality
variable {V : Type} [LinearOrder V]

theorem boundary_eq (N M : V → Finset V) (S T U : Finset V)
    (hn : ∀ u ∈ U, N u = M u)
    (hs : ∀ u ∈ U, ∀ w ∈ N u, w ∈ S ↔ w ∈ T) :
    FiniteEligibility.boundary N S U = FiniteEligibility.boundary M T U := by
  apply Finset.sum_congr rfl
  intro u hu
  apply congrArg Finset.card
  rw [← hn u hu]
  ext w
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hw, hws, hwu⟩
    exact ⟨hw, (hs u hu w hw).mp hws, hwu⟩
  · rintro ⟨hw, hwt, hwu⟩
    exact ⟨hw, (hs u hu w hw).mpr hwt, hwu⟩

theorem mem_iff (N M : V → Finset V) (S T U : Finset V) (k t : ℕ)
    (hn : ∀ u ∈ U, N u = M u)
    (hu : ∀ u ∈ U, u ∈ S ↔ u ∈ T)
    (hs : ∀ u ∈ U, ∀ w ∈ N u, w ∈ S ↔ w ∈ T) :
    U ∈ FiniteEligibility.family N S k t ↔ U ∈ FiniteEligibility.family M T k t := by
  rw [FiniteEligibility.mem_family, FiniteEligibility.mem_family,
    FiniteConnectivityLocality.connected_eq N M U hn, boundary_eq N M S T U hn hs]
  have hh : U ⊆ S ↔ U ⊆ T := by
    constructor
    · intro h u huU
      exact (hu u huU).mp (h huU)
    · intro h u huU
      exact (hu u huU).mpr (h huU)
  rw [hh]
end Paper.FiniteEligibilityLocality
