import Paper.Preliminaries.LatticeForcedSelection
import GraphTheory.SimpleGraph.Domination.Total
namespace Paper.LatticeBlock

theorem total_forced_parameters {q m s T : ℕ} (O : Offsets q s)
    (hm : 2*(T+3)*s+1 ≤ m) :
    ∃ ell : ℕ, ∀ (b : ℕ), ell < b →
      ∀ (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
        (P : PortLocal.Program Unit Bool), P.rounds ≤ T →
      ∃ ids : Vertex b q m → ℕ, Function.Injective ids ∧
        (Finset.univ.image ids=Finset.Icc 1 (b*m^q)) ∧
        (network O G H).Compatible G ∧
        (G.IsTotalDominatingSetFinset (selected O G H P ids) →
          (b-ell)*(m-2*((T+2)*s))^q ≤ (selected O G H P ids).card) := by
  obtain ⟨ell,hell⟩:=forced_parameters O hm
  refine ⟨ell,?_⟩
  intro b hb G inst H P hT
  obtain ⟨ids,hinj,hexact,hports,hcount⟩:=hell b hb G H P hT
  exact ⟨ids,hinj,hexact,hports,fun hdom=>hcount hdom.isDominatingSetFinset⟩
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.total_forced_parameters
