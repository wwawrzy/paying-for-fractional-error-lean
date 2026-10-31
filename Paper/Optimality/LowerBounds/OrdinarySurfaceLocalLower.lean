import Paper.External.Planarity
import Paper.Optimality.LowerBounds.PlanarLocalLower
namespace Paper.OrdinarySurfaceLocalLower
open PathPowerTreewidth SevenFoundation TreewidthLocalLower
theorem integral (T : ℕ) (c : ℝ) (hc : c < 7) :
    ∃ n : ℕ, 0 < n ∧ SimpleGraph.OrdinarySurface.HasEulerGenusAtMost (graph n 3) 2 ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n 3) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*(graph n 3).dominationNumber < (output N P ids).card := by
  obtain ⟨n,hn,hplanar,hbad⟩ := PlanarLocalLower.integral T c hc
  have hzero := External.Planarity.planar_euler_zero (graph n 3) hplanar
  have htwo : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost (graph n 3) 2 := by
    obtain ⟨S,topo,s,hemb,hgen⟩ := hzero
    exact ⟨S,topo,s,hemb,hgen.trans (by norm_num)⟩
  exact ⟨n,hn,htwo,hbad⟩
end Paper.OrdinarySurfaceLocalLower
#print axioms Paper.OrdinarySurfaceLocalLower.integral
