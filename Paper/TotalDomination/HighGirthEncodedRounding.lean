import Paper.TotalDomination.HighGirthProtocol
import Paper.TotalDomination.EncodedRounding
namespace Paper.TotalDomination.HighGirthEncodedRounding
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
structure Input (V : Type) where
  startup : HighGirthStartup.Output V
  numerator : ℕ

def prepare (Q : ℕ) (N : Finset V) (s : Input V) : HighGirthProtocol.Input :=
  ⟨⟨decide (0 < s.startup.solver.2.val),!s.startup.selected,
    decide (0 < s.startup.solver.2.val) && decide (3 ≤ N.card) &&
      decide ((2:ℚ)/3 < EncodedRounding.capped Q s.numerator)⟩,s.startup.linked⟩
def program {ids : ℕ} (codec : BitCode V ids) (Q : ℕ) : Program V (Input V) Bool :=
  .seq (.local fun _ N s => (prepare Q N s,s.startup.selected))
    (.seq (ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec))
      (.local fun _ _ s => s.1 || s.2))
theorem rounds {ids : ℕ} (codec : BitCode V ids) (Q : ℕ) :
    (program codec Q).rounds=4 := by
  simp only [program,Program.rounds,ProgramMemory.rounds,HighGirthProtocol.rounds,Nat.zero_add,Nat.add_zero]
theorem maxBits {ids : ℕ} (codec : BitCode V ids) (Q : ℕ) :
    (program codec Q).maxBits ≤ ids+1 := by
  simp only [program,Program.maxBits,ProgramMemory.maxBits,Nat.zero_max,Nat.max_zero]
  exact HighGirthProtocol.maxBits codec
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Q : ℕ)
def localInput (numerator : V → ℕ) (v : V) : Input V :=
  ⟨⟨HighGirthStartup.input G v,decide (v ∈ HighGirthSetup.F G),decide (v ∈ HighGirthStartup.linked G)⟩,numerator v⟩
theorem candidate_correct (numerator : V → ℕ) (v : V) :
    (prepare Q (G.neighborFinset v) (localInput G numerator v)).base.candidate =
      decide (v ∈ HighGirthSetup.K G) := by
  simp only [prepare,localInput,HighGirthStartup.input,HighGirthSetup.K,HighGirthSelection.candidates,
    Finset.mem_filter,Finset.mem_univ,true_and]
theorem demand_correct (numerator : V → ℕ) (v : V) :
    (prepare Q (G.neighborFinset v) (localInput G numerator v)).base.demand =
      decide (v ∈ HighGirthSetup.Z G) := by
  simp only [prepare,localInput,HighGirthSetup.Z,HighGirthSelection.remaining,
    Finset.mem_sdiff,Finset.mem_univ,true_and,decide_not]
theorem linked_correct (numerator : V → ℕ) (v : V) :
    (prepare Q (G.neighborFinset v) (localInput G numerator v)).linked =
      decide (v ∈ HighGirthStartup.linked G) := rfl
theorem first_correct (numerator : V → ℕ) (labels : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) (v : V) :
    (prepare Q (G.neighborFinset v) (localInput G numerator v)).base.first =
      decide (v ∈ first G (HighGirthSetup.I G
        (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q)) labels hfree)) := by
  have ht : (2:ℚ)/3 < EncodedRounding.capped Q (numerator v) ↔
      (2:ℝ)/3 < min 1 ((numerator v : ℝ)/Q) := by
    have hcast : (((2:ℚ)/3:ℚ):ℝ)=(2:ℝ)/3 := by norm_num
    rw [←hcast,←EncodedRounding.capped_cast Q (numerator v)]
    exact Rat.cast_lt.symm
  rw [show (prepare Q (G.neighborFinset v) (localInput G numerator v)).base.first =
      (decide (v ∈ HighGirthSetup.K G) && decide (v ∈ HighGirthSetup.B G) &&
        decide ((2:ℝ)/3 < min 1 ((numerator v : ℝ)/Q))) by
      simp only [prepare,localInput,HighGirthStartup.input,HighGirthSetup.K,HighGirthSelection.candidates,
        HighGirthSetup.c,HighGirthSetup.B,HighGirthSelection.branch,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.card_neighborFinset_eq_degree,ht]
      rfl]
  rw [←Bool.decide_and,←Bool.decide_and]
  apply Bool.decide_congr
  have hk : v ∈ HighGirthSetup.B G → v ∈ HighGirthSetup.K G := fun hv => HighGirthSetup.branch_candidates G hv
  simp only [first,HighGirthSetup.I,HighGirthSetup.input,Finset.mem_filter,CoveringOptimum.cap]
  tauto

theorem run_eq {ids : ℕ} (codec : BitCode V ids) (numerator : V → ℕ)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (program codec Q).runEncoded G (localInput G numerator) = fun v =>
      decide (v ∈ HighGirthSetup.F G ∪ HighGirthSetup.selected G
        (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q)) labels hfree) := by
  let s := fun v => prepare Q (G.neighborFinset v) (localInput G numerator v)
  have hr := HighGirthProtocol.run_eq G (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q))
    labels hfree s codec (candidate_correct G Q numerator) (demand_correct G Q numerator)
    (first_correct G Q numerator labels hfree) (linked_correct G Q numerator) hmono
  simp only [Program.runEncoded_eq_run] at hr ⊢
  change (fun v => ((ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec)).run G
    (fun u => (s u,decide (u ∈ HighGirthSetup.F G))) v).1 ||
      ((ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec)).run G
    (fun u => (s u,decide (u ∈ HighGirthSetup.F G))) v).2) = _
  rw [ProgramMemory.run]
  change (fun v => (HighGirthProtocol.program codec).run G s v || decide (v ∈ HighGirthSetup.F G)) = _
  change (HighGirthProtocol.program codec).run G s = _ at hr
  rw [hr]
  funext v
  simp only [Finset.mem_union,Bool.decide_or]
  exact Bool.or_comm _ _
end Paper.TotalDomination.HighGirthEncodedRounding
#print axioms Paper.TotalDomination.HighGirthEncodedRounding.run_eq
