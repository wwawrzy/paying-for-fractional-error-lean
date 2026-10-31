import Paper.Endpoints.Girth.HighGirthInducedPaths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option maxHeartbeats 200000
namespace Paper.HighGirthExteriorComponent

theorem exterior_path_component
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u l : V) (hu : u ∈ S) (hl : l ∉ S)
    (w : G.Walk u l) (hw : w.IsPath)
    (hs : ∀ a ∈ w.support, a ∈ insert l S) :
    ∀ a ∈ w.support, a ≠ l → ∃ ha : a ∈ S,
      (G.induce (↑S : Set V)).connectedComponentMk ⟨a, ha⟩ =
        (G.induce (↑S : Set V)).connectedComponentMk ⟨u, hu⟩ := by
  classical
  intro a ha hal
  have haS : a ∈ S := (Finset.mem_insert.mp (hs a ha)).resolve_left hal
  refine ⟨haS, ?_⟩
  have hpS : ∀ v ∈ (w.takeUntil a ha).support, v ∈ S := by
    intro v hv
    have hvw := w.support_takeUntil_subset ha hv
    have hvl : v ≠ l := by
      intro heq
      subst v
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hw ha hal.symm hv
    exact (Finset.mem_insert.mp (hs v hvw)).resolve_left hvl
  obtain ⟨q, hq, hlen, hmap⟩ := Paper.HighGirthInducedPaths.lift_internal_path G S u a hu haS
    (w.takeUntil a ha) (hw.takeUntil ha) hpS
  exact (SimpleGraph.ConnectedComponent.sound q.reachable).symm

end Paper.HighGirthExteriorComponent

#print axioms Paper.HighGirthExteriorComponent.exterior_path_component
