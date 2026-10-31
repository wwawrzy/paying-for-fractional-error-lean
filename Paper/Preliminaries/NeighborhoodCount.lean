import Paper.Communication.BroadcastModel
import Paper.Preliminaries.SevenFoundation

/-! One actual one-bit broadcast counts selected demands in the original
closed neighborhood. Local memory and computation need no degree bound. -/
namespace Paper.NeighborhoodCount
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

def round : Round V Bool ℕ Bool where
  send _ _ s := s
  update _ N s incoming := (if s then 1 else 0) +
    (N.attach.filter (fun w => incoming w = true)).card

def program : Program V Bool ℕ := .broadcast 1 BitCode.bool round

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem eval_eq (A : Finset V) (v : V) :
    program.run G (fun u => decide (u ∈ A)) v = (closed G v ∩ A).card := by
  have he : (closed G v ∩ A) =
      (if v ∈ A then {v} else ∅) ∪ (G.neighborFinset v).filter (fun u => u ∈ A) := by
    ext u
    simp only [Finset.mem_inter, mem_closed, Finset.mem_union, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    by_cases hu : u = v
    · subst u; by_cases hv : v ∈ A <;> simp [hv]
    · by_cases hv : v ∈ A <;> simp [hv, hu]
  have hd : Disjoint (if v ∈ A then {v} else ∅)
      ((G.neighborFinset v).filter (fun u => u ∈ A)) := by
    by_cases hv : v ∈ A
    · simp [hv, SimpleGraph.mem_neighborFinset]
    · simp [hv]
  have hc : ((G.neighborFinset v).attach.filter (fun w : ↥(G.neighborFinset v) =>
      decide ((w : V) ∈ A) = true)).card =
      ((G.neighborFinset v).filter (fun u => u ∈ A)).card := by
    apply Finset.card_bij (fun (w : ↥(G.neighborFinset v)) _ => (w : V))
    · intro w hw
      exact Finset.mem_filter.mpr ⟨w.property, of_decide_eq_true (Finset.mem_filter.mp hw).2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro u hu
      refine ⟨⟨u, (Finset.mem_filter.mp hu).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
        decide_eq_true (Finset.mem_filter.mp hu).2⟩
  change (if decide (v ∈ A) then 1 else 0) +
    ((G.neighborFinset v).attach.filter (fun w : ↥(G.neighborFinset v) =>
      decide ((w : V) ∈ A) = true)).card = _
  rw [he, Finset.card_union_of_disjoint hd, hc]
  by_cases hv : v ∈ A <;> simp [hv]
end Paper.NeighborhoodCount
