import Paper.Preliminaries.StarCounting
import Paper.Endpoints.Girth.CurrentPlanarFaceBound

namespace Paper.StarMinorGirth
open SimpleGraph SevenFoundation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (W R T : Finset V)

def graph : SimpleGraph {v // v ∈ W∪R} where
  Adj u v := (StarMinor.graph G W R).Adj u v ∧ (u.val ∈ T ∨ v.val ∈ T)
  symm := by rintro u v ⟨ha,h⟩;exact ⟨ha.symm,h.symm⟩
  loopless := ⟨fun _ h => (StarMinor.graph G W R).irrefl h.1⟩

theorem le_star : graph G W R T ≤ StarMinor.graph G W R := fun _ _ h => h.1

theorem planar (hR : Disjoint R (covered G W)) (hp : G.IsPlanar) :
    (graph G W R T).IsPlanar := by
  have hm := (IsMinor.of_subgraph (le_star G W R T)).trans (StarMinor.isMinor G W R hR)
  exact ⟨IsHMinorFree.minor hp.1 hm,IsHMinorFree.minor hp.2 hm⟩

def marked : Finset {v // v ∈ W∪R} := W.subtype (fun v => v ∈ W∪R)

theorem fiber (hR : Disjoint R (covered G W)) (r : {v // v ∈ W∪R}) (hr : r ∉ marked W R) :
    {u | StarMinor.owner G W u = r.val} = {r.val} := by
  ext u
  constructor
  · intro hu
    by_cases hc : u ∈ covered G W
    · have hw := StarMinor.owner_covered G W hc
      rw [hu] at hw
      exact False.elim (hr (Finset.mem_subtype.mpr hw))
    · have he := StarMinor.owner_uncovered G W hc
      exact he.symm.trans hu
  · intro hu
    have he := StarMinor.owner_retained G W R hR r
    simpa only [Set.mem_singleton_iff.mp hu] using he

noncomputable def unmarkedHom (hR : Disjoint R (covered G W)) :
    ((graph G W R T).induce {r | r ∉ marked W R}) →g G where
  toFun r := r.val.val
  map_rel' := by
    intro r s hrs
    obtain ⟨_,u,v,hu,hv,ha⟩ := hrs.1
    have hu' : u = r.val.val := by
      have hh : u ∈ ({r.val.val}:Set V) := by
        rw [← fiber G W R hR r.val r.property]
        exact hu
      exact hh
    have hv' : v = s.val.val := by
      have hh : v ∈ ({s.val.val}:Set V) := by
        rw [← fiber G W R hR s.val s.property]
        exact hv
      exact hh
    simpa only [hu',hv'] using ha

theorem girth (hR : Disjoint R (covered G W)) (g : ℕ)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ∀ (r : {r : {v // v ∈ W∪R} // r ∉ marked W R})
      (c : ((graph G W R T).induce {r | r ∉ marked W R}).Walk r r),
      c.IsCycle → g ≤ c.length := by
  intro r c hc
  have hinj : Function.Injective (unmarkedHom G W R T hR) := by
    intro u v h
    exact Subtype.ext (Subtype.ext h)
  have hm := (Walk.map_isCycle_iff_of_injective
    (f := unmarkedHom G W R T hR) hinj).mpr hc
  simpa only [Walk.length_map] using hg _ (c.map (unmarkedHom G W R T hR)) hm

theorem marked_independent (hTW : Disjoint T W) :
    ∀ u ∈ marked W R, ∀ v ∈ marked W R, ¬ (graph G W R T).Adj u v := by
  intro u hu v hv ha
  rcases ha.2 with h | h
  · exact Finset.disjoint_left.mp hTW h (Finset.mem_subtype.mp hu)
  · exact Finset.disjoint_left.mp hTW h (Finset.mem_subtype.mp hv)

end Paper.StarMinorGirth
#print axioms Paper.StarMinorGirth.girth
