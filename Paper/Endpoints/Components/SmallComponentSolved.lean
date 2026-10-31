import Paper.Endpoints.Components.SmallComponentAcceptedContext
import Paper.Endpoints.Components.SmallComponentDecode
import Paper.Endpoints.Components.ParallelComponentSearch

namespace Paper.SmallComponentSolved

theorem logical_solved_uniform
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
    (v u : V) (hv : v ∈ X.supp) (hu : u ∈ X.supp) :
    ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 =
    ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s u).1 := by
  let I := Paper.CoveringIncidence.graph cover R
  let t := Paper.SmallComponentProgram.acceptedInput I ids K s
  let ans := (Paper.NormalizedComponentSearch.program ids
    (2 * Paper.SmallComponentProgram.radius K) a B K hB).runEncoded I t
  obtain ⟨p⟩ := X.reachable_of_mem_supp hv hu
  have hbits : (t v).active = (t u).active :=
    Paper.SmallComponentAcceptedInput.accepted_input_active_uniform I ids K s p
  simp only [Paper.SmallComponentProgram.logical_run]
  apply Bool.eq_iff_iff.mpr
  change (Paper.SmallComponentProgram.decode K v (ans v, (t v).active)).1 = true ↔
    (Paper.SmallComponentProgram.decode K u (ans u, (t u).active)).1 = true
  simp only [Paper.SmallComponentDecode.decode_solved_iff]
  by_cases hactive : (t v).active = true
  · obtain ⟨hall, hdiam⟩ :=
      Paper.SmallComponentAcceptedContext.accepted_component_context I ids K s X v hv hactive
    have hword : ans v = ans u :=
      Paper.ParallelComponentSearch.uniform cover targets R X
        (2 * Paper.SmallComponentProgram.radius K) hdiam hinc a ha hden B K hB ids t hall
        (fun x => hd x) (fun x => hC x) (fun x => ht x) v u hv hu
    change ((t v).active = true ∧ ∃ w, ans v = some w ∧ Paper.SolutionWord.cost w ≤ K) ↔
      ((t u).active = true ∧ ∃ w, ans u = some w ∧ Paper.SolutionWord.cost w ≤ K)
    rw [hbits, hword]
  · change ((t v).active = true ∧ ∃ w, ans v = some w ∧ Paper.SolutionWord.cost w ≤ K) ↔
      ((t u).active = true ∧ ∃ w, ans u = some w ∧ Paper.SolutionWord.cost w ≤ K)
    rw [← hbits]
    simp [hactive]

end Paper.SmallComponentSolved

#print axioms Paper.SmallComponentSolved.logical_solved_uniform
