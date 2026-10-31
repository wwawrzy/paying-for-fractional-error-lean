import Paper.Communication.ZoneProgram
import Paper.Communication.EncodedProgram
import Paper.Endpoints.Rounding.CurrentBudget

/-!
Actual preprocessing for the current F = V \ N[B]. Two one-bit broadcast
rounds compute F, C = V\F, R₀ = V\N[F], and the bounded integer costs.

The degree comparison is purely local. The number of selected neighbors
is also counted locally from received bits, never transmitted. `weight`
saturates at d so every output has a fixed finite type; the current budget
lemma proves that this saturation is exact at every candidate.
-/

namespace Paper.CurrentZoneProgram

open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

@[ext] structure Env (d : ℕ) where
  selected : Bool
  candidate : Bool
  demand : Bool
  cost : Fin (d + 2)

def program (d : ℕ) : Program V Unit (Env d) :=
  .seq (ZoneProgram.near d)
    (.seq (.local fun _ _ c => (!c, c))
      (.seq (ProgramMemory.carry ClosedBitProgram.program)
        (.local fun _ _ st =>
          ⟨!st.2, st.2, !decide st.1.Nonempty, ZoneProgram.weight d st.2 st.1.card⟩)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def expected (d : ℕ) (v : V) : Env d :=
  ⟨decide (v ∈ CurrentBudget.selected G d),
    decide (v ∈ CurrentBudget.candidates G d),
    decide (v ∈ CurrentBudget.demands G d),
    ZoneProgram.weight d (decide (v ∈ CurrentBudget.candidates G d))
      (closed G v ∩ CurrentBudget.selected G d).card⟩

theorem candidates_correct (d : ℕ) :
    (ZoneProgram.near d).run G (fun _ => ()) =
      fun v => decide (v ∈ CurrentBudget.candidates G d) :=
  ZoneProgram.near_correct G d

theorem correct (d : ℕ) : (program d).run G (fun _ => ()) = expected G d := by
  have hf : (fun v => !(decide (v ∈ CurrentBudget.candidates G d))) =
      (fun v => decide (v ∈ CurrentBudget.selected G d)) := by
    funext v
    simp only [CurrentBudget.selected, Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not]
  change (fun v => let st := ((ProgramMemory.carry ClosedBitProgram.program).run G
    (fun u => (!((ZoneProgram.near d).run G (fun _ => ()) u),
      (ZoneProgram.near d).run G (fun _ => ()) u)) v);
    (⟨!st.2, st.2, !decide st.1.Nonempty, ZoneProgram.weight d st.2 st.1.card⟩ : Env d)) = _
  rw [candidates_correct, ProgramMemory.run G ClosedBitProgram.program, hf, ClosedBitProgram.correct]
  funext v
  apply Env.ext
  · change (!decide (v ∈ CurrentBudget.candidates G d)) = decide (v ∈ CurrentBudget.selected G d)
    simp only [CurrentBudget.selected, Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not]
  · rfl
  · change (!(decide (closed G v ∩ CurrentBudget.selected G d).Nonempty)) =
      decide (v ∈ CurrentBudget.demands G d)
    apply Bool.eq_iff_iff.mpr
    simp [ClosedBitProgram.covered_iff, CurrentBudget.demands]
  · rfl

theorem encoded_correct (d : ℕ) :
    (program d).runEncoded G (fun _ => ()) = expected G d := by
  rw [Program.runEncoded_eq_run]
  exact correct G d

/-- Every encoded local output gives the exact three current membership bits. -/
theorem membership_correct (d : ℕ) (v : V) :
    (((program d).runEncoded G (fun _ => ()) v).selected = true ↔
      v ∈ CurrentBudget.selected G d) ∧
    (((program d).runEncoded G (fun _ => ()) v).candidate = true ↔
      v ∈ CurrentBudget.candidates G d) ∧
    (((program d).runEncoded G (fun _ => ()) v).demand = true ↔
      v ∈ CurrentBudget.demands G d) := by
  rw [encoded_correct]
  simp [expected]

theorem cost_positive (d : ℕ) (v : V) : 1 ≤ ((expected G d v).cost).val :=
  ZoneProgram.weight_pos d _ _

theorem cost_bounded (d : ℕ) (v : V) : ((expected G d v).cost).val ≤ d + 1 := by
  have hh := ((expected G d v).cost).isLt
  omega

theorem cost_correct (d : ℕ) {v : V} (hv : v ∈ CurrentBudget.candidates G d) :
    (((expected G d v).cost).val : ℝ) = CurrentBudget.boundaryCost G d v := by
  have hn := CurrentBudget.boundary_card_le G d hv
  change ((if decide (v ∈ CurrentBudget.candidates G d) then
    d + 1 - min (closed G v ∩ CurrentBudget.selected G d).card d else 1 : ℕ) : ℝ) = _
  rw [if_pos (by simpa using hv), min_eq_left hn, Nat.cast_sub (by omega)]
  rfl

/-- On candidates this is exactly the open-neighborhood cost in the TeX,
with no assumption on the physical degree. -/
theorem encoded_cost_correct (d : ℕ) {v : V} (hv : v ∈ CurrentBudget.candidates G d) :
    ((((program d).runEncoded G (fun _ => ()) v).cost).val : ℝ) =
      (d + 1 : ℕ) - ((G.neighborFinset v ∩ CurrentBudget.selected G d).card : ℝ) := by
  rw [encoded_correct, cost_correct G d hv]
  exact CurrentBudget.cost_eq_open G d v hv

theorem rounds (d : ℕ) : (program (V := V) d).rounds = 2 := rfl

theorem maxBits (d : ℕ) : (program (V := V) d).maxBits = 1 := rfl

theorem logarithmic_bits (d n : ℕ) :
    (program (V := V) d).maxBits ≤ Nat.clog 2 (n + 2) := by
  rw [maxBits]
  have hp : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  omega

end Paper.CurrentZoneProgram
