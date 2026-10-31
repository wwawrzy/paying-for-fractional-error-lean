import Paper.Preliminaries.PathPowerThreePlanar
import Paper.Optimality.LowerBounds.TreewidthLocalLower

namespace Paper.PlanarLocalLower
open PathPowerTreewidth SevenFoundation TreewidthLocalLower

/-- Exact deterministic LOCAL planar lower bound, with ordinary numbered
ports, arbitrary separate messages, KT1 and known n. The identifiers are
exactly1,...,n. This is a new formal witness proof, not the anonymous torus
bound and not an assumed external lower theorem. -/
theorem integral (T : ℕ) (c : ℝ) (hc : c < 7) :
    ∃ n : ℕ, 0 < n ∧ (graph n 3).IsPlanar ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n 3) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*(graph n 3).dominationNumber < (output N P ids).card := by
  obtain ⟨n, hn, _, hbad⟩ := TreewidthLocalLower.exact_lower 3 T c (by norm_num; exact hc)
  exact ⟨n, hn, PathPowerThreePlanar.isPlanar n, hbad⟩

theorem fractional (T : ℕ) (c : ℝ) (hc : c < 7) :
    ∃ n : ℕ, 0 < n ∧ (graph n 3).IsPlanar ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n 3) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*fractionalNumber (graph n 3) < (output N P ids).card := by
  obtain ⟨n, hn, _, hbad⟩ := TreewidthLocalLower.fractional_lower 3 T c (by norm_num; exact hc)
  exact ⟨n, hn, PathPowerThreePlanar.isPlanar n, hbad⟩

end Paper.PlanarLocalLower
