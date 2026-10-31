import Paper.External.Planarity
import Paper.RedBlue.OddRedBlueLower
/-! The unnumbered sharpness statement following fv:rb:surface-opt, with
ordinary Euler-genus membership for every fixed nonnegative genus bound. -/
namespace Paper.RedBlueOrdinarySurfaceLower
open SevenFoundation OddRedBlue
theorem lower (g T : ℕ) (c : ℝ) (hc : c < 4) :
    ∃ m : ℕ, 0 < m ∧ (OddPathPower.graph (8*m) 3).Connected ∧
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost (OddPathPower.graph (8*m) 3) g ∧
      (∀ v, (OddPathPower.graph (8*m) 3).degree v ≤ 4) ∧
      (∀ p, CoveringOptimum.number
        (RedBlue.rows (OddPathPower.graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ))=m) ∧
      ∀ P : PortLocal.Program Bool Bool, P.rounds ≤ T →
        (∀ (p : Fin 2) (N : PortLocal.Network (Fin (8*m))), N.Compatible (OddPathPower.graph (8*m) 3) →
          ∀ ids : Fin (8*m) → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ 8*m) → Feasible N P ids p) →
        ∃ (N : PortLocal.Network (Fin (8*m))) (ids : Fin (8*m) → ℕ) (p : Fin 2),
          N.Compatible (OddPathPower.graph (8*m) 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids=Finset.Icc 1 (8*m) ∧ Feasible N P ids p ∧
          c*CoveringOptimum.number
            (RedBlue.rows (OddPathPower.graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ)) <
            (output N P ids p).card := by
  obtain ⟨m,hm,hconn,hplanar,rest⟩ := OddRedBlue.lower T c hc
  have hzero := External.Planarity.planar_euler_zero (OddPathPower.graph (8*m) 3) hplanar
  have hgen : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost (OddPathPower.graph (8*m) 3) g := by
    obtain ⟨S,topo,s,hemb,hs⟩ := hzero
    exact ⟨S,topo,s,hemb,hs.trans (by exact_mod_cast Nat.zero_le g)⟩
  exact ⟨m,hm,hconn,hgen,rest⟩
end Paper.RedBlueOrdinarySurfaceLower
#print axioms Paper.RedBlueOrdinarySurfaceLower.lower
