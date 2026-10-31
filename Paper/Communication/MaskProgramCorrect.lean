import Paper.Communication.MaskProgram

namespace Paper.MaskProgramCorrect
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def learned (H : Finset V) : V → MaskProgram.Env V :=
  MaskProgram.prepare.run G (fun v => decide (v ∈ H))

theorem active (H : Finset V) (v : V) : (learned G H v).active = decide (v ∈ H) := rfl

theorem neighbors (H : Finset V) (v : V) :
    (learned G H v).neighbors = (MaskedTaskGraph.graph G H).neighborFinset v := by
  by_cases hv : v ∈ H
  · rw [MaskedTaskGraph.neighbor_inside G H v hv]
    change (if decide (v ∈ H) then
      ((G.neighborFinset v).attach.filter (fun u => decide (u.val ∈ H) = true)).image Subtype.val else ∅) = _
    simp only [decide_eq_true hv, ↓reduceIte]
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, decide_eq_true_eq, Finset.mem_inter]
    constructor
    · rintro ⟨w, hw, he⟩
      exact ⟨he ▸ w.property, he ▸ hw⟩
    · rintro ⟨huN, huH⟩
      exact ⟨⟨u, huN⟩, huH, rfl⟩
  · rw [MaskedTaskGraph.neighbor_outside G H v hv]
    change (if decide (v ∈ H) then _ else ∅) = ∅
    simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte]

theorem inter_neighbors (H : Finset V) (v : V) :
    G.neighborFinset v ∩ (MaskedTaskGraph.graph G H).neighborFinset v =
      (MaskedTaskGraph.graph G H).neighborFinset v := by
  apply Finset.inter_eq_right.mpr
  intro u hu
  exact (G.mem_neighborFinset v u).mpr
    (MaskedTaskGraph.le G H ((SimpleGraph.mem_neighborFinset (MaskedTaskGraph.graph G H) v u).mp hu))

theorem round_correct {In Out Msg : Type} {w : ℕ} (P : BitCode Msg w) (R : Round V In Out Msg)
    (H : Finset V) (s : V → In) (v : V) :
    (MaskProgram.simulateRound P R).run G (fun u => (s u, learned G H u)) v =
      (eval (MaskedTaskGraph.graph G H) R s v, learned G H v) := by
  change (R.update v (G.neighborFinset v ∩ (learned G H v).neighbors) (s v)
    (fun u => R.send u.val (learned G H u.val).neighbors (s u.val)), learned G H v) = _
  rw [neighbors G H v, inter_neighbors G H v]
  simp only [neighbors G H]
  rfl

theorem translate_correct {In Out : Type} (P : Program V In Out) (H : Finset V) : ∀ s : V → In,
    (MaskProgram.translate P).run G (fun v => (s v, learned G H v)) =
      fun v => (P.run (MaskedTaskGraph.graph G H) s v, learned G H v) := by
  induction P with
  | «local» f =>
    intro s
    funext v
    change (f v (learned G H v).neighbors (s v), learned G H v) = _
    rw [neighbors G H v]
    rfl
  | broadcast w code R =>
    intro s
    funext v
    exact round_correct G code R H s v
  | seq P Q ihP ihQ =>
    intro s
    change (MaskProgram.translate Q).run G ((MaskProgram.translate P).run G
      (fun v => (s v, learned G H v))) = _
    rw [ihP s]
    exact ihQ _

theorem execute_correct {In Out : Type} (P : Program V In Out) (H : Finset V) (s : V → In) :
    (MaskProgram.execute P).run G (fun v => (decide (v ∈ H), s v)) =
      fun v => (P.run (MaskedTaskGraph.graph G H) s v, learned G H v) := by
  dsimp only [MaskProgram.execute, Program.run]
  rw [ProgramMemory.run G MaskProgram.prepare]
  exact translate_correct G P H s
end Paper.MaskProgramCorrect
