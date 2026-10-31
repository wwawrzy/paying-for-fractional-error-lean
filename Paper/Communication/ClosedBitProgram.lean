import Paper.Communication.BroadcastModel
import Paper.Preliminaries.SevenFoundation

/-! One physical bit broadcast identifies the selected vertices in each
closed neighborhood. The list is private local memory, never a message. -/
namespace Paper.ClosedBitProgram
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

def program : Program V Bool (Finset V) := .broadcast 1 BitCode.bool {
  send := fun _ _ s => s
  update := fun v N s incoming =>
    (if s then {v} else ∅) ∪
      (N.attach.filter (fun u => incoming u = true)).image Subtype.val }

def closure : Program V Bool Bool :=
  .seq program (.local fun _ _ s => decide s.Nonempty)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (S : Finset V) :
    program.run G (fun v => decide (v ∈ S)) = fun v => closed G v ∩ S := by
  funext v
  ext u
  simp only [program, Program.run, eval, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_attach, true_and, decide_eq_true_eq,
    Finset.mem_inter, mem_closed]
  by_cases hv : v ∈ S
  · simp only [if_pos hv, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact ⟨Or.inl rfl, hv⟩
      · exact ⟨Or.inr ((SimpleGraph.mem_neighborFinset G v w).mp w.property), hw⟩
    · rintro ⟨h, hu⟩
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr h⟩, hu, rfl⟩
  · simp only [if_neg hv, Finset.notMem_empty, false_or]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Or.inr ((SimpleGraph.mem_neighborFinset G v w).mp w.property), hw⟩
    · rintro ⟨h, hu⟩
      rcases h with rfl | h
      · exact False.elim (hv hu)
      · exact ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr h⟩, hu, rfl⟩

theorem covered_iff (S : Finset V) (v : V) :
    (closed G v ∩ S).Nonempty ↔ v ∈ covered G S := by
  simp only [Finset.Nonempty, Finset.mem_inter, covered, Finset.mem_biUnion]
  constructor
  · rintro ⟨u, hu, hs⟩
    exact ⟨u, hs, (closed_symm G v u).mpr hu⟩
  · rintro ⟨u, hs, hu⟩
    exact ⟨u, (closed_symm G v u).mp hu, hs⟩

theorem closure_correct (S : Finset V) :
    closure.run G (fun v => decide (v ∈ S)) = fun v => decide (v ∈ covered G S) := by
  change (fun v => decide ((program.run G (fun u => decide (u ∈ S)) v).Nonempty)) = _
  rw [correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using covered_iff G S v

theorem rounds : (program (V := V)).rounds = 1 := rfl
theorem maxBits : (program (V := V)).maxBits = 1 := rfl

end Paper.ClosedBitProgram
