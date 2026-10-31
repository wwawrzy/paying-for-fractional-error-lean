import Paper.TotalDomination.IntegerStartup
import Paper.TotalDomination.IntegerMathematicalEndpoint
import Paper.TotalDomination.EncodedRounding

/-! Four-round integer rounding from private startup flags and one private
natural numerator. All scalar tests are rational and local. -/
namespace Paper.TotalDomination.IntegerEncodedRounding
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (d : ℕ) where
  startup : IntegerStartup.Output V d
  numerator : ℕ

def prepare (d Q : ℕ) (N : Finset V) (s : Input V d) : Protocol.Input :=
  ⟨decide (0 < s.startup.solver.2.val),!s.startup.selected && !s.startup.linked,
    decide (0 < s.startup.solver.2.val) && decide (d < N.card) &&
      decide ((3:ℚ)/(2*(d:ℚ)) < EncodedRounding.capped Q s.numerator)⟩

def program {ids : ℕ} (codec : BitCode V ids) (d Q : ℕ) : Program V (Input V d) Bool :=
  .seq (.local fun _ N s => (prepare d Q N s,s.startup.selected))
    (.seq (ProgramMemory.carry (X := Bool) (Protocol.program codec d))
      (.local fun _ _ s => s.1 || s.2))

theorem rounds {ids : ℕ} (codec : BitCode V ids) (d Q : ℕ) :
    (program codec d Q).rounds = 4 := by
  simp only [program,Program.rounds,ProgramMemory.rounds,Protocol.rounds,Nat.zero_add,Nat.add_zero]

theorem maxBits {ids : ℕ} (codec : BitCode V ids) (d Q : ℕ) :
    (program codec d Q).maxBits ≤ ids+1 := by
  simp only [program,Program.maxBits,ProgramMemory.maxBits,Nat.zero_max,Nat.max_zero]
  exact Protocol.maxBits codec d

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d Q : ℕ)

def localInput (numerator : V → ℕ) (v : V) : Input V d :=
  ⟨⟨IntegerStartup.input G d v,decide (v ∈ IntegerSetup.F G d),decide (v ∈ IntegerSetup.linked G d)⟩,
    numerator v⟩

theorem candidate_correct (numerator : V → ℕ) (v : V) :
    (prepare d Q (G.neighborFinset v) (localInput G d numerator v)).candidate =
      decide (v ∈ IntegerSetup.K G d) := by
  simp only [prepare,localInput,IntegerStartup.input,IntegerSetup.K,InitialSelection.candidates,
    Finset.mem_filter,Finset.mem_univ,true_and]

theorem demand_correct (numerator : V → ℕ) (v : V) :
    (prepare d Q (G.neighborFinset v) (localInput G d numerator v)).demand =
      decide (v ∈ IntegerSetup.demands G d) := by
  simp only [prepare,localInput,IntegerSetup.demands,Finset.mem_sdiff,IntegerSetup.Z,
    InitialSelection.remaining,Finset.mem_univ,true_and,decide_not,Bool.decide_and]

theorem first_correct (numerator : V → ℕ) (labels : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) (v : V) :
    (prepare d Q (G.neighborFinset v) (localInput G d numerator v)).first =
      decide (v ∈ first G (IntegerSetup.I G d
        (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q)) labels hfree)) := by
  have ht : ((3:ℚ)/(2*(d:ℚ)) < EncodedRounding.capped Q (numerator v)) ↔
      (3:ℝ)/(2*(d:ℝ)) < min 1 ((numerator v : ℝ)/Q) := by
    have hcast : (((3:ℚ)/(2*(d:ℚ)) : ℚ) : ℝ) = (3:ℝ)/(2*(d:ℝ)) := by
      simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    rw [← hcast,← EncodedRounding.capped_cast Q (numerator v)]
    exact Rat.cast_lt.symm
  simp only [prepare,localInput,IntegerStartup.input,first,IntegerSetup.I,IntegerSetup.input,
    IntegerSetup.eligible,Finset.mem_filter,IntegerSetup.K,InitialSelection.candidates,
    Finset.mem_univ,true_and,CoveringOptimum.cap,SimpleGraph.card_neighborFinset_eq_degree,
    Bool.decide_and,ht]
  rfl

theorem run_eq {ids : ℕ} (codec : BitCode V ids) (numerator : V → ℕ)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (program codec d Q).runEncoded G (localInput G d numerator) =
      fun v => decide (v ∈ IntegerSetup.finalSelection G d
        (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q)) labels hfree) := by
  let s := fun v => prepare d Q (G.neighborFinset v) (localInput G d numerator v)
  let I := IntegerSetup.I G d (CoveringOptimum.cap (fun u => (numerator u : ℝ)/Q)) labels hfree
  have hr := Protocol.run_eq G I s codec
    (candidate_correct G d Q numerator) (demand_correct G d Q numerator)
    (first_correct G d Q numerator labels hfree) hmono
  simp only [Program.runEncoded_eq_run] at hr ⊢
  change (fun v => ((ProgramMemory.carry (X := Bool) (Protocol.program codec d)).run G
    (fun u => (s u,decide (u ∈ IntegerSetup.F G d))) v).1 ||
      ((ProgramMemory.carry (X := Bool) (Protocol.program codec d)).run G
    (fun u => (s u,decide (u ∈ IntegerSetup.F G d))) v).2) = _
  rw [ProgramMemory.run]
  change (fun v => (Protocol.program codec d).run G s v || decide (v ∈ IntegerSetup.F G d)) = _
  change (Protocol.program codec d).run G s = _ at hr
  rw [hr]
  funext v
  simp only [IntegerSetup.finalSelection,Finset.mem_union,Bool.decide_or]
  exact Bool.or_comm _ _

end Paper.TotalDomination.IntegerEncodedRounding
#print axioms Paper.TotalDomination.IntegerEncodedRounding.run_eq
