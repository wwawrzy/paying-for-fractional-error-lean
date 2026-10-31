import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairObserver
import Paper.Solver.LocalSearch.GeneralCoveringRandomFractionalPhysical

/-! Literal physical randomized repair equals the observer's union event.
The original producer computes both Env and boundary fields. No supplied
mark, interior, request list or observer correctness premise is used. -/
namespace Paper.GeneralCoveringOwnerRepairPhysical
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj :=
  fun _ _ => Classical.propDecidable _

private theorem mark_core {ids : ℕ} (I : BitCode V ids)
    (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (boundary : V → Bool) :
    (GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
      ⟨E u, (E u).metadata.owned.input.center &&
        ((E u).high || ((E u).low && !((E u).low && !boundary u)))⟩) =
      (GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
        ⟨E u, (E u).high || ((E u).low && boundary u)⟩) := by
  simp only [Program.runEncoded_eq_run, GeneralCoveringOwnerRepair.run_core]
  apply congrArg ((GeneralCoveringOwnerRepair.requestProgram I).run G)
  funext u
  congr 1
  cases (E u).metadata.owned.input.center <;> cases (E u).high <;>
    cases (E u).low <;> cases boundary u <;> rfl

private theorem core_repair {ids B : ℕ} (I : BitCode V ids) (L a k q : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringTaskFractionalRepair.Input V B) (v : V) :
    ((GeneralCoveringTaskFractionalRepair.core I L a B k q hB).runEncoded G s v).2.1 =
      (GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
        ⟨(s u).1, (s u).1.metadata.owned.input.center &&
          ((s u).1.high || ((s u).1.low && !(s u).2.interior))⟩) v := by
  rw [GeneralCoveringTaskFractionalRepair.run_core, GeneralCoveringTaskFractionalRepair.beforeProgram_run]
  rfl

theorem selected {ids B : ℕ} (I : BitCode V ids) (L Δ a k q t b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input)
    (c : V → Fin (B + 1)) (β : V → ActiveFiniteBitPartition.Bits Δ k b n) (v : V) :
    ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
      (fun u => (input u, (c u, β u))) v).1.2.1.selected =
      GeneralCoveringOwnerRepairObserver.evaluate
        ((GeneralCoveringOwnerRepairObserver.core I).runEncoded G
          (GeneralCoveringOwnerSimulation.learned G I L Δ input) v).fixed
        ((GeneralCoveringOwnerRepairObserver.core I).runEncoded G
          (GeneralCoveringOwnerSimulation.learned G I L Δ input) v).roots
        (fun u => ((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded
          (GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L
            (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
          (fun w => (decide (w ∈ GeneralCoveringOwnerVirtualPrepare.image d.D
            (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)), β w)) u).2) := by
  have hp := GeneralCoveringTaskRandomPhysicalMarks.correct G I L Δ k t b n B input d c β
  change GeneralCoveringRandomFractionalPhysical.produced G I L Δ k t b n B
    (fun u => (input u, (c u, β u))) = _ at hp
  have he : ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
      (fun u => (input u, (c u, β u))) v).1.2.1 =
      (GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
        let z := GeneralCoveringRandomFractionalPhysical.produced G I L Δ k t b n B
          (fun w => (input w, (c w, β w))) u
        ⟨z.env, z.env.metadata.owned.input.center &&
          (z.env.high || (z.env.low && !z.fields.interior))⟩) v := by
    rw [GeneralCoveringRandomFractionalPhysical.run_program]
    exact core_repair G I L a k q hB _ v
  rw [he, hp]
  change ((GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
    ⟨GeneralCoveringOwnerSimulation.learned G I L Δ input u,
      (GeneralCoveringOwnerSimulation.learned G I L Δ input u).metadata.owned.input.center &&
        ((GeneralCoveringOwnerSimulation.learned G I L Δ input u).high ||
          ((GeneralCoveringOwnerSimulation.learned G I L Δ input u).low &&
            !((GeneralCoveringOwnerSimulation.learned G I L Δ input u).low && !_)))⟩) v).selected = _
  rw [mark_core]
  exact GeneralCoveringOwnerRepairObserver.core_selected G I _ _ v

theorem numerator_decomposition {ids B : ℕ} (I : BitCode V ids) (L Δ a k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n) (v : V) :
    let out := (GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G s v
    out.1.1 = out.1.2.2.1 + if out.1.2.1.selected then q else 0 := by
  dsimp only
  rw [GeneralCoveringRandomFractionalPhysical.run_program, GeneralCoveringTaskFractionalRepair.run_core]

theorem quotient_decomposition {ids B : ℕ} (I : BitCode V ids) (L Δ a k q t b n : ℕ) (hB : 1 ≤ B)
    (hq : 0 < q) (s : V → GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n) (v : V) :
    let out := (GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G s v
    (out.1.1 : ℝ) / q = (out.1.2.2.1 : ℝ) / q +
      ((if out.1.2.1.selected then 1 else 0 : ℕ) : ℝ) := by
  dsimp only
  rw [numerator_decomposition]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  by_cases hs : ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G s v).1.2.1.selected = true <;>
    simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_zero, Nat.cast_one, add_div, div_self hqR, zero_div]


end Paper.GeneralCoveringOwnerRepairPhysical

#print axioms Paper.GeneralCoveringOwnerRepairPhysical.selected
#print axioms Paper.GeneralCoveringOwnerRepairPhysical.numerator_decomposition
#print axioms Paper.GeneralCoveringOwnerRepairPhysical.quotient_decomposition
