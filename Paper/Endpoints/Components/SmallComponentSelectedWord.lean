import Paper.Endpoints.Components.SmallComponentAcceptedContext
import Paper.Endpoints.Components.SmallComponentDecode
import Paper.Endpoints.Components.ParallelComponentSearch

namespace Paper.SmallComponentSelectedWord

theorem logical_selected_word
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
    (v : V) (hv : v ∈ X.supp)
    (hsolved : ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 = true) :
    ∃ w : Paper.SolutionWord.Word V B,
      (Paper.NormalizedComponentSearch.program ids (2 * Paper.SmallComponentProgram.radius K) a B K hB).runEncoded
        (Paper.CoveringIncidence.graph cover R)
        (Paper.SmallComponentProgram.acceptedInput (Paper.CoveringIncidence.graph cover R) ids K s) v = some w ∧
      Paper.SolutionWord.cost w ≤ K ∧
      ∀ u ∈ X.supp,
        (((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
          (Paper.CoveringIncidence.graph cover R) s u).2 = true ↔
          0 < Paper.SolutionWord.copies w u) := by
  let I := Paper.CoveringIncidence.graph cover R
  let t := Paper.SmallComponentProgram.acceptedInput I ids K s
  let ans := (Paper.NormalizedComponentSearch.program ids
    (2 * Paper.SmallComponentProgram.radius K) a B K hB).runEncoded I t
  rw [Paper.SmallComponentProgram.logical_run] at hsolved
  obtain ⟨hactive, w, hw, hcost⟩ :=
    (Paper.SmallComponentDecode.decode_solved_iff K v (ans v, (t v).active)).mp hsolved
  obtain ⟨hall, hdiam⟩ :=
    Paper.SmallComponentAcceptedContext.accepted_component_context I ids K s X v hv hactive
  refine ⟨w, hw, hcost, ?_⟩
  intro u hu
  have hword : ans v = ans u :=
    Paper.ParallelComponentSearch.uniform cover targets R X
      (2 * Paper.SmallComponentProgram.radius K) hdiam hinc a ha hden B K hB ids t hall
      (fun x => hd x) (fun x => hC x) (fun x => ht x) v u hv hu
  have hwu : ans u = some w := hword.symm.trans hw
  rw [Paper.SmallComponentProgram.logical_run]
  change (Paper.SmallComponentProgram.decode K u (ans u, (t u).active)).2 = true ↔ _
  rw [Paper.SmallComponentDecode.decode_selected_iff]
  have hau : (t u).active = true := hall u hu
  simp [hwu, hau, hcost]

end Paper.SmallComponentSelectedWord

#print axioms Paper.SmallComponentSelectedWord.logical_selected_word
