import Paper.TotalDomination.TreewidthIntegralLower
import Paper.Endpoints.Girth.HighGirthMinorPaths
namespace Paper.TotalDomination.HighGirthOptimality
open PathPowerTreewidth
/-- Exact size-aware standard-port LOCAL lower bound, with isolate-free
planar path witnesses of every girth in every minor-density class rho>=1. -/
theorem lower (rho : ℝ) (hrho : 1 ≤ rho) (g T : ℕ) (c : ℝ) (hc : c < 2) :
    ∃ n : ℕ, 2 ≤ n ∧ graph n 1 = SimpleGraph.pathGraph n ∧
      MinorDensity.Bound (graph n 1) rho ∧ (graph n 1).IsPlanar ∧
      (∀ v, ((graph n 1).neighborFinset v).Nonempty) ∧
      (∀ (v : Fin n) (p : (graph n 1).Walk v v), p.IsCycle → g ≤ p.length) ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 1) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (graph n 1).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 1) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*((graph n 1).totalDominationNumber:ℝ) < (TreewidthLocalLower.output N P ids).card := by
  obtain ⟨n,hn,hconn,hpath,htw,hbad⟩ := TreewidthIntegralLower.lower T c hc
  exact ⟨n,hn,hpath,HighGirthMinorPaths.density n rho hrho,HighGirthPathFamily.planar n,
    PathPowerTotal.isolate_free n 1 hn (by decide),HighGirthPathFamily.girth n g,hbad⟩

/-- Every graph class containing all finite paths inherits the same lower bound;
minor closure is not needed once this explicit containment is known. -/
theorem class_lower (Class : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (hpaths : ∀ n, Class n (SimpleGraph.pathGraph n)) (g T : ℕ) (c : ℝ) (hc : c < 2) :
    ∃ n : ℕ, 2 ≤ n ∧ Class n (graph n 1) ∧
      (∀ v, ((graph n 1).neighborFinset v).Nonempty) ∧
      (∀ (v : Fin n) (p : (graph n 1).Walk v v), p.IsCycle → g ≤ p.length) ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 1) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (graph n 1).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 1) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*((graph n 1).totalDominationNumber:ℝ) < (TreewidthLocalLower.output N P ids).card := by
  obtain ⟨n,hn,hpath,hm,hp,hf,hg,hbad⟩ := lower 1 (by norm_num) g T c hc
  exact ⟨n,hn,hpath ▸ hpaths n,hf,hg,hbad⟩
end Paper.TotalDomination.HighGirthOptimality
#print axioms Paper.TotalDomination.HighGirthOptimality.lower
#print axioms Paper.TotalDomination.HighGirthOptimality.class_lower
