import Paper.Communication.BroadcastModel
import Paper.Preliminaries.SevenFoundation

/-! A single bit broadcast reconstructs selected identifiers in one's
closed physical neighborhood. Large received sets remain private memory. -/
namespace Paper.FlagNeighborhood
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

def selected (v : V) (N : Finset V) (own : Bool) (msg : N → Bool) : Finset V :=
  (if own then {v} else ∅) ∪ (N.attach.filter (fun u => msg u)).image Subtype.val

def round : Round V Bool (Finset V) Bool where
  send _ _ s := s
  update v N s msg := selected v N s msg

def program : Program V Bool (Finset V) := .broadcast 1 BitCode.bool round

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (S : Finset V) (v : V) :
    program.run G (fun u => decide (u ∈ S)) v = closed G v ∩ S := by
  change selected v (G.neighborFinset v) (decide (v ∈ S)) (fun u => decide (u.val ∈ S)) = _
  ext u
  simp only [selected, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
    true_and, decide_eq_true_eq, Finset.mem_inter, mem_closed]
  constructor
  · rintro (h | ⟨w, hw, he⟩)
    · by_cases hv : v ∈ S
      · have hu : u = v := by simpa [hv] using h
        subst u
        exact ⟨Or.inl rfl, hv⟩
      · simp [hv] at h
    · subst u
      exact ⟨Or.inr ((SimpleGraph.mem_neighborFinset G v w.val).mp w.property), hw⟩
  · rintro ⟨he | ha, hs⟩
    · subst u
      exact Or.inl (by simp [hs])
    · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr ha⟩, hs, rfl⟩

theorem rounds : (program (V := V)).rounds = 1 := rfl

theorem maxBits : (program (V := V)).maxBits = 1 := rfl
end Paper.FlagNeighborhood
