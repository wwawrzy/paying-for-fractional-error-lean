import Paper.Endpoints.Components.OriginalComponentSearch
import Paper.Endpoints.Components.ComponentContext

/-! Componentwise guarantees for the actual raw normalized search. Other
components may remain active. Restriction is used only in the correctness
proof; the executable has no component argument and retains optional failure. -/

namespace Paper.ParallelComponentSearch

open BroadcastModel SevenFoundation GeneralCoveringIntegral
open scoped BigOperators

variable {V : Type} [Fintype V] [LinearOrder V]
  (cover targets : V → Finset V) (R : Finset V)
  (X : (CoveringIncidence.graph cover R).ConnectedComponent)
  (d : ℕ)
  (hdiam : ∀ u ∈ X.supp, ∀ v ∈ X.supp,
    ∃ p : (CoveringIncidence.graph cover R).Walk u v, p.length ≤ d)
  (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
  (a : ℕ) (ha : 1 ≤ a)
  (hden : Incidence.InducedDensityBound (CoveringIncidence.graph cover R) (a : ℝ))
  (B K : ℕ) (hB : 1 ≤ B) {bits : ℕ} (C : BitCode V bits)
  (s : V → NormalizedComponentSearch.Input V B)
  (hactive : ∀ v ∈ X.supp, (s v).active = true)
  (hd : ∀ v, (s v).demand = decide (v ∈ R))
  (hC : ∀ v, (s v).candidates = cover v)
  (ht : ∀ v, (s v).targets = targets v)
  (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (s v).cost.val)

local notation "I" => CoveringIncidence.graph cover R
local notation "H" => IncidenceComponent.vertices I X
local notation "L" => R ∩ H
local notation "ctx" => IncidenceComponent.context I X d hdiam
local notation "rs" => IncidenceComponent.restrict H s
local notation "ans" => Program.runEncoded I (NormalizedComponentSearch.program C d a B K hB) s

private theorem local_rows : ∀ r ∈ L, cover r ⊆ closed I r := by
  intro r hr v hv
  exact CoveringIncidence.candidate_mem_closed cover R (Finset.mem_inter.mp hr).1 hv

include hc in
private theorem local_positive :
    ∀ v ∈ CoveringSupport.admissible cover L, 1 ≤ (rs v).cost.val := by
  intro v hv
  apply hc v
  obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨r, (Finset.mem_inter.mp hr).1, hvr⟩

include hactive in
private theorem restricted_active : ∀ v, (rs v).active =
    decide (v ∈ ActiveTask.Context.vertices ctx) := by
  apply IncidenceComponent.restrict_active
  intro v hv
  exact hactive v ((IncidenceComponent.mem_vertices I X v).mp hv)

include hdiam hinc ha hden hactive hd hC ht in
/-- The raw optional outputs agree throughout the component, even with active
vertices in other components. No affordable feasible witness is assumed. -/
theorem uniform (v u : V) (hv : v ∈ X.supp) (hu : u ∈ X.supp) :
    ans v = ans u := by
  rw [IncidenceComponent.encoded_restriction I _ X s v hv,
    IncidenceComponent.encoded_restriction I _ X s u hu]
  exact OriginalComponentSearch.uniform I ctx L Finset.inter_subset_right cover targets hinc
    (local_rows cover R X) a ha hden B K hB C rs
    (restricted_active cover R X d hdiam B s hactive)
    (IncidenceComponent.restrict_demand H R s hd) hC ht v u
    ((IncidenceComponent.mem_vertices I X v).mpr hv)
    ((IncidenceComponent.mem_vertices I X u).mpr hu)

include hdiam hinc ha hden hactive hd hC ht hc in
/-- Affordable actual success is equivalent to an original local admissible
cover of affordable original cost. Failure is preserved as `none`. -/
theorem solved_iff_original_set (v : V) (hv : v ∈ X.supp) :
    SmallComponentSearchDecision.Solved (ans v) K ↔
      ∃ O : Finset V, O ⊆ CoveringSupport.admissible cover L ∧ Covers cover L O ∧
        (∑ u ∈ O, (s u).cost.val) ≤ K := by
  rw [IncidenceComponent.encoded_restriction I _ X s v hv]
  exact OriginalComponentSearch.solved_iff_original_set I ctx L Finset.inter_subset_right
    cover targets hinc (local_rows cover R X) (IncidenceComponent.rows_stay cover R X)
    a ha hden B K hB C rs (restricted_active cover R X d hdiam B s hactive)
    (IncidenceComponent.restrict_demand H R s hd) hC ht
    (local_positive cover R X B s hc) v ((IncidenceComponent.mem_vertices I X v).mpr hv)

include hdiam hinc ha hden hactive hd hC ht hc in
/-- An affordable actual word yields an original local feasible set optimal
against every local admissible cover, without a competitor budget bound. -/
theorem returned_original_optimal (v : V) (hv : v ∈ X.supp)
    (w : SolutionWord.Word V B) (hw : ans v = some w) (hcost : SolutionWord.cost w ≤ K) :
    SmallComponentSetDecision.support w ⊆ H ∧
      SmallComponentSetDecision.support w ⊆ CoveringSupport.admissible cover L ∧
      Covers cover L (SmallComponentSetDecision.support w) ∧
      (∑ u ∈ SmallComponentSetDecision.support w, (s u).cost.val) ≤ SolutionWord.cost w ∧
      ∀ O : Finset V, O ⊆ CoveringSupport.admissible cover L → Covers cover L O →
        (∑ u ∈ SmallComponentSetDecision.support w, (s u).cost.val) ≤ ∑ u ∈ O, (s u).cost.val := by
  rw [IncidenceComponent.encoded_restriction I _ X s v hv] at hw
  exact OriginalComponentSearch.returned_original_optimal I ctx L Finset.inter_subset_right
    cover targets hinc (local_rows cover R X) (IncidenceComponent.rows_stay cover R X)
    a ha hden B K hB C rs (restricted_active cover R X d hdiam B s hactive)
    (IncidenceComponent.restrict_demand H R s hd) hC ht
    (local_positive cover R X B s hc) v ((IncidenceComponent.mem_vertices I X v).mpr hv)
    w hw hcost

end Paper.ParallelComponentSearch

#print axioms Paper.ParallelComponentSearch.uniform
#print axioms Paper.ParallelComponentSearch.solved_iff_original_set
#print axioms Paper.ParallelComponentSearch.returned_original_optimal
