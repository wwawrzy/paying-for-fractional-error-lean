import Paper.Communication.CurrentZoneProgram
import Paper.Endpoints.Rounding.SurfaceResidualBudget
namespace Paper.SurfaceResidual
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

noncomputable def targets (v : V) : Finset V :=
  Finset.univ.filter (fun r => v ∈ cover G d r)

noncomputable def unitInput (v : V) : GeneralCoveringFractional.Input V 1 where
  active := decide (v ∈ CurrentBudget.candidates G d)
  cost := 1
  demand := decide (v ∈ CurrentBudget.demands G d)
  candidates := cover G d v
  targets := targets G d v

theorem incidence (v r : V) : r ∈ targets G d v ↔ v ∈ cover G d r := by
  simp [targets]

theorem cover_local (r : V) : cover G d r ⊆ closed G r :=
  Finset.inter_subset_left

theorem targets_local (v : V) : targets G d v ⊆ closed G v := by
  intro r hr
  have h := (incidence G d v r).mp hr
  exact (closed_symm G r v).mpr (cover_local G d r h)

theorem unitInput_cost (v : V) : (unitInput G d v).cost.val = 1 := rfl

open BroadcastModel

def unitPrepare (d : ℕ) : Program V Unit (GeneralCoveringFractional.Input V 1) :=
  .seq (CurrentZoneProgram.program d)
    (.seq (.local fun _ _ e => (e.candidate, e))
      (.seq (ProgramMemory.carry ClosedBitProgram.program)
        (.local fun v N st =>
          ⟨st.2.candidate, 1, st.2.demand, st.1,
            if st.2.candidate then insert v N else ∅⟩)))

theorem unitPrepare_rounds : (unitPrepare (V := V) d).rounds = 3 := by
  simp [unitPrepare, Program.rounds, ProgramMemory.rounds,
    CurrentZoneProgram.rounds, ClosedBitProgram.rounds]

theorem unitPrepare_bits : (unitPrepare (V := V) d).maxBits = 1 := by
  simp [unitPrepare, Program.maxBits, ProgramMemory.maxBits,
    CurrentZoneProgram.maxBits, ClosedBitProgram.maxBits]

theorem targets_eq (v : V) : targets G d v =
    if v ∈ CurrentBudget.candidates G d then closed G v else ∅ := by
  ext r
  simp only [targets, Finset.mem_filter, Finset.mem_univ, true_and,
    cover, CurrentBudget.auxiliary, Finset.mem_inter]
  by_cases hv : v ∈ CurrentBudget.candidates G d
  · simp only [if_pos hv, hv, and_true]
    exact (closed_symm G r v).symm
  · simp [hv]

theorem unitPrepare_correct : (unitPrepare (V := V) d).run G (fun _ => ()) = unitInput G d := by
  unfold unitPrepare
  simp only [Program.run]
  rw [CurrentZoneProgram.correct]
  simp only [ProgramMemory.run]
  change (fun v => (⟨decide (v ∈ CurrentBudget.candidates G d), 1,
    decide (v ∈ CurrentBudget.demands G d),
    ClosedBitProgram.program.run G (fun u => decide (u ∈ CurrentBudget.candidates G d)) v,
    if decide (v ∈ CurrentBudget.candidates G d) then insert v (G.neighborFinset v) else ∅⟩ :
    GeneralCoveringFractional.Input V 1)) = _
  rw [ClosedBitProgram.correct]
  funext v
  have ht := targets_eq G d v
  simp only [unitInput, ht, decide_eq_true_eq]
  have he : insert v (G.neighborFinset v) = closed G v := by
    ext u
    simp [mem_closed, eq_comm]
  rw [he]
  rfl

end Paper.SurfaceResidual
