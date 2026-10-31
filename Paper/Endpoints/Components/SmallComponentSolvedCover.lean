import Paper.Endpoints.Components.SmallComponentAcceptedContext
import Paper.Endpoints.Components.SmallComponentDecode
import Paper.Endpoints.Components.ParallelComponentSearch

namespace Paper.SmallComponentSolvedCover

theorem logical_solved_iff_cover
    {V : Type} [Fintype V] [LinearOrder V]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (v : V) (hv : v ∈ X.supp) :
    ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 = true ↔
    (Paper.SmallComponentProgram.acceptedInput (Paper.CoveringIncidence.graph cover R) ids K s v).active = true ∧
      ∃ O : Finset V,
        O ⊆ Paper.CoveringSupport.admissible cover
          (R ∩ Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X) ∧
        Paper.GeneralCoveringIntegral.Covers cover
          (R ∩ Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X) O ∧
        (O.sum (fun x => (s x).cost.val)) ≤ K := by
  let I := Paper.CoveringIncidence.graph cover R
  let t := Paper.SmallComponentProgram.acceptedInput I ids K s
  let ans := (Paper.NormalizedComponentSearch.program ids
    (2 * Paper.SmallComponentProgram.radius K) a B K hB).runEncoded I t
  rw [Paper.SmallComponentProgram.logical_run]
  change (Paper.SmallComponentProgram.decode K v (ans v, (t v).active)).1 = true ↔ _
  rw [Paper.SmallComponentDecode.decode_solved_iff]
  by_cases hactive : (t v).active = true
  · obtain ⟨hall, hdiam⟩ :=
      Paper.SmallComponentAcceptedContext.accepted_component_context I ids K s X v hv hactive
    have hsearch := Paper.ParallelComponentSearch.solved_iff_original_set cover targets R X
      (2 * Paper.SmallComponentProgram.radius K) hdiam hinc a ha hden B K hB ids t hall
      (fun x => hd x) (fun x => hC x) (fun x => ht x) (fun x hx => hc x hx) v hv
    change ((t v).active = true ∧ Paper.SmallComponentSearchDecision.Solved (ans v) K) ↔ _
    exact and_congr_right (fun _ => hsearch)
  · change ((t v).active = true ∧ _) ↔ ((t v).active = true ∧ _)
    simp [hactive]

end Paper.SmallComponentSolvedCover

#print axioms Paper.SmallComponentSolvedCover.logical_solved_iff_cover
