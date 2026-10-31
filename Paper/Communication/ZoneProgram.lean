import Paper.Communication.ClosedBitProgram
import Paper.Communication.ProgramMemory
import Paper.Endpoints.Rounding.WeightedBudget

/-! Three one-bit broadcasts compute actual defect-zone participation,
initial demands, and bounded integer boundary weights. No graph oracle. -/
namespace Paper.ZoneProgram
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

@[ext] structure Env (d : ℕ) where
  zone : Bool
  demand : Bool
  cost : Fin (d + 2)

def weight (d : ℕ) (z : Bool) (n : ℕ) : Fin (d + 2) :=
  ⟨if z then d + 1 - min n d else 1, by split <;> omega⟩

theorem weight_pos (d : ℕ) (z : Bool) (n : ℕ) : 1 ≤ (weight d z n).val := by
  dsimp only [weight]
  split <;> omega

def near (d : ℕ) : Program V Unit Bool :=
  .seq (.local fun _ N _ => decide (N.card ≠ d)) ClosedBitProgram.closure

def zone (d : ℕ) : Program V Unit Bool := .seq (near d) ClosedBitProgram.closure

def program (d : ℕ) : Program V Unit (Env d) :=
  .seq (zone d)
    (.seq (.local fun _ _ z => (!z, z))
      (.seq (ProgramMemory.carry ClosedBitProgram.program)
        (.local fun _ _ st => ⟨st.2, st.2 && !decide st.1.Nonempty, weight d st.2 st.1.card⟩)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def expected (d : ℕ) (v : V) : Env d :=
  ⟨decide (v ∈ WeightedBudget.zone G d), decide (v ∈ WeightedBudget.initialDemands G d),
    weight d (decide (v ∈ WeightedBudget.zone G d)) (closed G v ∩ WeightedBudget.far G d).card⟩

theorem near_correct (d : ℕ) :
    (near d).run G (fun _ => ()) = fun v => decide (v ∈ covered G (WeightedBudget.defects G d)) := by
  have he : (fun v => decide ((G.neighborFinset v).card ≠ d)) =
      (fun v => decide (v ∈ WeightedBudget.defects G d)) := by
    funext v
    simp only [WeightedBudget.defects, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  change ClosedBitProgram.closure.run G (fun v => decide ((G.neighborFinset v).card ≠ d)) = _
  rw [he, ClosedBitProgram.closure_correct]

theorem zone_correct (d : ℕ) :
    (zone d).run G (fun _ => ()) = fun v => decide (v ∈ WeightedBudget.zone G d) := by
  change ClosedBitProgram.closure.run G ((near d).run G (fun _ => ())) = _
  rw [near_correct, ClosedBitProgram.closure_correct]
  rfl

theorem correct (d : ℕ) : (program d).run G (fun _ => ()) = expected G d := by
  have hf : (fun v => !(decide (v ∈ WeightedBudget.zone G d))) =
      (fun v => decide (v ∈ WeightedBudget.far G d)) := by
    funext v
    simp only [WeightedBudget.far, Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not]
  change (fun v => let z := ((ProgramMemory.carry ClosedBitProgram.program).run G
    (fun u => (!((zone d).run G (fun _ => ()) u), (zone d).run G (fun _ => ()) u)) v);
    (⟨z.2, z.2 && !decide z.1.Nonempty, weight d z.2 z.1.card⟩ : Env d)) = _
  rw [zone_correct, ProgramMemory.run G ClosedBitProgram.program, hf, ClosedBitProgram.correct]
  funext v
  apply Env.ext
  · rfl
  · change (decide (v ∈ WeightedBudget.zone G d) &&
      !(decide (closed G v ∩ WeightedBudget.far G d).Nonempty)) =
        decide (v ∈ WeightedBudget.initialDemands G d)
    apply Bool.eq_iff_iff.mpr
    simp [ClosedBitProgram.covered_iff, WeightedBudget.initialDemands]
  · rfl

theorem cost_correct (d : ℕ) {v : V} (hv : v ∈ WeightedBudget.zone G d) :
    (((expected G d v).cost).val : ℝ) = WeightedBudget.boundaryCost G d v := by
  have hn := WeightedBudget.boundary_card_le G d hv
  change ((if decide (v ∈ WeightedBudget.zone G d) then
    d + 1 - min (closed G v ∩ WeightedBudget.far G d).card d else 1 : ℕ) : ℝ) = _
  rw [if_pos (by simpa using hv), min_eq_left hn, Nat.cast_sub (by omega)]
  rfl

theorem rounds (d : ℕ) : (program (V := V) d).rounds = 3 := rfl
theorem maxBits (d : ℕ) : (program (V := V) d).maxBits = 1 := rfl

end Paper.ZoneProgram
