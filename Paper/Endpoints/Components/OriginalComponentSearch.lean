import Paper.Endpoints.Components.NormalizedComponentSearch

/-! Original-input guarantees for the unchanged normalized raw search.
Affordable success is characterized using original admissible covers and
original costs. A successful affordable word gives an original optimal set.
Failure remains an optional result, and no cheap feasible witness is assumed. -/

namespace Paper.OriginalComponentSearch

open BroadcastModel SevenFoundation GeneralCoveringIntegral
open scoped BigOperators

variable {V : Type} [Fintype V] [LinearOrder V]
  (I : SimpleGraph V) [DecidableRel I.Adj]
  (H : ActiveTask.Context I) (R : Finset V) (hR : R ⊆ H.vertices)
  (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
  (hlocal : ∀ r ∈ R, cover r ⊆ closed I r)
  (htask : ∀ r ∈ R, cover r ⊆ H.vertices)
  (a : ℕ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound I (a : ℝ))
  (B K : ℕ) (hB : 1 ≤ B) {bits : ℕ} (C : BitCode V bits)
  (s : V → NormalizedComponentSearch.Input V B)
  (hactive : ∀ v, (s v).active = decide (v ∈ H.vertices))
  (hd : ∀ v, (s v).demand = decide (v ∈ R))
  (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
  (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (s v).cost.val)

local notation "ns" => Program.runEncoded I (GeneralCoveringInputNormalization.program B hB) s
local notation "rows" => (fun r => GeneralCoveringFractional.Input.candidates (ns r))
local notation "nc" => (fun u => GeneralCoveringFractional.Input.cost (ns u))
local notation "raw" => GeneralCoveringSearch.program C (ActiveTask.Context.diameter H) a B 1 K
local notation "input" => (fun u => GeneralCoveringFractional.searchInput 1 (ns u))
local notation "ans" => Program.runEncoded I
  (NormalizedComponentSearch.program C (ActiveTask.Context.diameter H) a B K hB) s

include hR hinc hlocal ha hden hactive hd hC ht

include htask hc in
/-- Affordable actual success is equivalent to an affordable original
admissible feasible set. Original costs need positivity only on admissibles. -/
theorem solved_iff_original_set (v : V) (hv : v ∈ H.vertices) :
    SmallComponentSearchDecision.Solved (ans v) K ↔
      ∃ O : Finset V, O ⊆ CoveringSupport.admissible cover R ∧ Covers cover R O ∧
        (∑ u ∈ O, (s u).cost.val) ≤ K := by
  have hsol := NormalizedComponentSearch.solved_iff_normalized_set I H R hR cover targets hinc hlocal
    htask a ha hden B K hB C s hactive hd hC ht hc v hv
  dsimp only at hsol
  rw [hsol]
  have hadm := GeneralCoveringInputNormalization.admissibility I cover R hB s hd hC
  constructor
  · rintro ⟨O, hOadm, hO, hcost⟩
    have hOadm' : O ⊆ CoveringSupport.admissible cover R := by
      simpa only [hadm] using hOadm
    have hO' := (GeneralCoveringInputNormalization.integral_covers I cover R hB s hd hC O).mp hO
    have hcostEq := GeneralCoveringInputNormalization.supported_cost I cover targets R hinc hlocal
      s hd ht hB O hOadm'
    exact ⟨O, hOadm', hO', by simpa only [hcostEq] using hcost⟩
  · rintro ⟨O, hOadm, hO, hcost⟩
    refine ⟨O, ?_, ?_, ?_⟩
    · simpa only [hadm] using hOadm
    · exact (GeneralCoveringInputNormalization.integral_covers I cover R hB s hd hC O).mpr hO
    · rw [GeneralCoveringInputNormalization.supported_cost I cover targets R hinc hlocal
        s hd ht hB O hOadm]
      exact hcost

include htask hc in
/-- The support of any affordable returned word is an original feasible set,
costs at most that word, and compares with every original admissible cover.
The competitor has no cost or cardinality budget restriction. -/
theorem returned_original_optimal (v : V) (hv : v ∈ H.vertices)
    (w : SolutionWord.Word V B) (hw : ans v = some w) (hcost : SolutionWord.cost w ≤ K) :
    SmallComponentSetDecision.support w ⊆ H.vertices ∧
      SmallComponentSetDecision.support w ⊆ CoveringSupport.admissible cover R ∧
      Covers cover R (SmallComponentSetDecision.support w) ∧
      (∑ u ∈ SmallComponentSetDecision.support w, (s u).cost.val) ≤ SolutionWord.cost w ∧
      ∀ O : Finset V, O ⊆ CoveringSupport.admissible cover R → Covers cover R O →
        (∑ u ∈ SmallComponentSetDecision.support w, (s u).cost.val) ≤ ∑ u ∈ O, (s u).cost.val := by
  have hspec := NormalizedComponentSearch.normalized_spec I H R hR cover targets hinc hlocal
    a ha hden B K hB C s hactive hd hC ht
  have hp := NormalizedComponentSearch.normalized_positive I cover targets R hinc hlocal hB s hd ht hc
  have hwraw : Program.run I raw input v = some w := by
    simpa only [NormalizedComponentSearch.run_program_eq_run] using hw
  have hs := SmallComponentSetDecision.support_properties rows I raw H.vertices R nc K input
    hspec hp v hv w hwraw
  have hadm := GeneralCoveringInputNormalization.admissibility I cover R hB s hd hC
  have houtadm : SmallComponentSetDecision.support w ⊆ CoveringSupport.admissible cover R := by
    simpa only [hadm] using hs.2.1
  have houtcover := (GeneralCoveringInputNormalization.integral_covers I cover R hB s hd hC
    (SmallComponentSetDecision.support w)).mp hs.2.2.1
  have houtcost := GeneralCoveringInputNormalization.supported_cost I cover targets R hinc hlocal
    s hd ht hB (SmallComponentSetDecision.support w) houtadm
  have hntask : ∀ r ∈ R, rows r ⊆ H.vertices := by
    intro r hr
    change (ns r).candidates ⊆ H.vertices
    rw [GeneralCoveringInputNormalization.candidates_eq I cover R hB s hd hC r]
    simpa only [GeneralCoveringInputNormalization.trimmed, if_pos hr] using htask r hr
  refine ⟨hs.1, houtadm, houtcover, ?_, ?_⟩
  · rw [← houtcost]
    exact hs.2.2.2
  · intro O hOadm hO
    have hOadm' : O ⊆ CoveringSupport.admissible rows R := by
      simpa only [hadm] using hOadm
    have hO' := (GeneralCoveringInputNormalization.integral_covers I cover R hB s hd hC O).mpr hO
    have hopt := SmallComponentSetDecision.optimal_against_set rows I raw H.vertices R nc K input
      hspec hp hntask v hv w hwraw hcost O hOadm' hO'
    calc
      _ = ∑ u ∈ SmallComponentSetDecision.support w, (nc u).val := houtcost.symm
      _ ≤ ∑ u ∈ O, (nc u).val := hopt.2
      _ = _ := GeneralCoveringInputNormalization.supported_cost I cover targets R hinc hlocal
        s hd ht hB O hOadm

/-- The actual optional output is uniform throughout the active context.
This does not assert success or require a feasible cost-budget witness. -/
theorem uniform (v u : V) (hv : v ∈ H.vertices) (hu : u ∈ H.vertices) : ans v = ans u := by
  have hspec := NormalizedComponentSearch.normalized_spec I H R hR cover targets hinc hlocal
    a ha hden B K hB C s hactive hd hC ht
  simpa only [NormalizedComponentSearch.run_program_eq_run] using hspec.uniform v u hv hu

end Paper.OriginalComponentSearch

#print axioms Paper.OriginalComponentSearch.solved_iff_original_set
#print axioms Paper.OriginalComponentSearch.returned_original_optimal
#print axioms Paper.OriginalComponentSearch.uniform
