import Paper.Endpoints.Girth.HighGirthMinorPaths
namespace Paper.HighGirthMinorLower
theorem minor_density_large_girth_lower
    (rho : Real) (hrho : 1 ≤ rho) (g T : Nat) (c : Real) (hc : c < 3) :
    ∃ n : Nat, 0 < n ∧ Paper.MinorDensity.Bound (Paper.PathPowerTreewidth.graph n 1) rho ∧
      (Paper.PathPowerTreewidth.graph n 1).IsPlanar ∧
      (∀ (v : Fin n) (w : (Paper.PathPowerTreewidth.graph n 1).Walk v v), w.IsCycle → g ≤ w.length) ∧
      ∀ P : Paper.PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : Paper.PortLocal.Network (Fin n)), N.Compatible (Paper.PathPowerTreewidth.graph n 1) →
          ∀ ids : Fin n → Nat, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          Paper.SevenFoundation.dominates (Paper.PathPowerTreewidth.graph n 1)
            (Paper.TreewidthLocalLower.output N P ids)) →
        ∃ (N : Paper.PortLocal.Network (Fin n)) (ids : Fin n → Nat),
          N.Compatible (Paper.PathPowerTreewidth.graph n 1) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c * (Paper.PathPowerTreewidth.graph n 1).dominationNumber <
            (Paper.TreewidthLocalLower.output N P ids).card := by
  rcases Paper.TreewidthLocalLower.exact_lower 1 T c (by norm_num; exact hc) with ⟨n,hn,htw,hbad⟩
  refine ⟨n,hn,Paper.HighGirthMinorPaths.density n rho hrho,Paper.HighGirthPathFamily.planar n,?_,hbad⟩
  intro v w hw
  exact Paper.HighGirthPathFamily.girth n g v w hw
end Paper.HighGirthMinorLower
#print axioms Paper.HighGirthMinorLower.minor_density_large_girth_lower
