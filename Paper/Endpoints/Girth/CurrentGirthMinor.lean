import Paper.Endpoints.Girth.CurrentPlanarFaceBound
import Paper.Endpoints.Rounding.ComponentMinor

/-!
# The marked face bound on the actual component minor

Every uncontracted vertex has a singleton branch set. Thus deleting precisely
the contracted vertices leaves a graph which maps injectively into the
original graph, preserving its girth. The short-face estimate can therefore
be applied to the actual component minor used by the current rounding.
-/

namespace Paper.CurrentGirthMinor

open SimpleGraph

attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R W : Finset V)

local notation "K" => ComponentMinor.graph G R W
local notation "A" => ComponentMinor.contracted G R W

/-- Outside the actual contracted set, every original branch set is a singleton. -/
theorem uncontracted_fiber (r : ComponentMinor.retained G R W) (hr : r ∉ A) :
    {v | ComponentMinor.label G R W v = r.val} = {r.val} := by
  apply ComponentMinor.fiber_unmarked G R W r.val
    (ComponentMinor.retained_fixed G R W r.property)
  intro hm
  exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)

/-- Uncontracted adjacency is an original adjacency on the same two vertices. -/
theorem uncontracted_adj
    (r s : ComponentMinor.retained G R W) (hr : r ∉ A) (hs : s ∉ A)
    (hrs : (K).Adj r s) : G.Adj r.val s.val := by
  obtain ⟨_, u, v, hu, hv, huv⟩ := hrs
  have hu' : u ∈ ({r.val} : Set V) := by
    rw [← uncontracted_fiber G R W r hr]
    exact hu
  have hv' : v ∈ ({s.val} : Set V) := by
    rw [← uncontracted_fiber G R W s hs]
    exact hv
  simpa only [Set.mem_singleton_iff.mp hu', Set.mem_singleton_iff.mp hv'] using huv

/-- Deleting the contracted vertices gives an injective homomorphism into G. -/
noncomputable def uncontractedHom : ((K).induce {r | r ∉ A}) →g G where
  toFun r := r.val.val
  map_rel' := by
    intro r s hrs
    exact uncontracted_adj G R W r.val s.val r.property s.property hrs

theorem uncontractedHom_injective : Function.Injective (uncontractedHom G R W) := by
  intro r s h
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The girth of the original graph is preserved outside exactly A. -/
theorem girth_outside_contracted (g : ℕ)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (r : {r : ComponentMinor.retained G R W // r ∉ A})
    (c : ((K).induce {r | r ∉ A}).Walk r r) (hc : c.IsCycle) :
    g ≤ c.length := by
  have hcycle : (c.map (uncontractedHom G R W)).IsCycle :=
    (Walk.map_isCycle_iff_of_injective
      (f := uncontractedHom G R W) (uncontractedHom_injective G R W)).mpr hc
  simpa only [Walk.length_map] using
    hgirth _ (c.map (uncontractedHom G R W)) hcycle

/-- The minor used by the current rounding satisfies the marked face estimate
with exactly its contracted set and exactly its incident marked edges. -/
theorem edge_bound
    (hplanar : G.IsPlanar) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ((K).edgeFinset.card : ℝ) ≤
      (g : ℝ) / ((g : ℝ) - 2) * Fintype.card (ComponentMinor.retained G R W) +
        ((g : ℝ) - 3) / ((g : ℝ) - 2) *
          (CurrentFaceBound.incidentMarkedEdges (G := K) A).card := by
  have hminor := ComponentMinor.isMinor G R W
  have hK : (K).IsPlanar :=
    ⟨IsHMinorFree.minor hplanar.1 hminor, IsHMinorFree.minor hplanar.2 hminor⟩
  exact CurrentPlanarFaceBound.real_edge_bound hK A g hg
    (girth_outside_contracted G R W g hgirth)

end Paper.CurrentGirthMinor

#print axioms Paper.CurrentGirthMinor.uncontracted_fiber
#print axioms Paper.CurrentGirthMinor.uncontracted_adj
#print axioms Paper.CurrentGirthMinor.uncontractedHom_injective
#print axioms Paper.CurrentGirthMinor.girth_outside_contracted
#print axioms Paper.CurrentGirthMinor.edge_bound
