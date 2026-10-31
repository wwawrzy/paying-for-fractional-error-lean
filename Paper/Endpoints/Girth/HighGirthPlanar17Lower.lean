import Paper.Endpoints.Girth.HighGirthPathFamily
set_option maxHeartbeats 200000
namespace Paper.HighGirthPlanar17Lower

theorem planar_girth_seventeen_lower
    (T : Nat) (c : Real) (hc : c < 3) :
    ∃ n : Nat, 0 < n ∧ (Paper.PathPowerTreewidth.graph n 1).IsPlanar ∧
      (∀ (v : Fin n) (w : (Paper.PathPowerTreewidth.graph n 1).Walk v v), w.IsCycle → 17 ≤ w.length) ∧
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
  refine ⟨n,hn,Paper.HighGirthPathFamily.planar n,?_,hbad⟩
  intro v w hw
  exact Paper.HighGirthPathFamily.girth n 17 v w hw

end Paper.HighGirthPlanar17Lower

#print axioms Paper.HighGirthPlanar17Lower.planar_girth_seventeen_lower
