import Paper.Preliminaries.FlagNeighborhood

/-! One true broadcast of (own label, own participation bit) reconstructs
the distinct labels of participating closed neighbors. No degree bound or
global vertex enumeration is used by the round constructor. -/
namespace Paper.LabelNeighborhood
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

def selected (N : Finset V) (own : V × Bool) (msg : N → V × Bool) : Finset V :=
  (if own.2 then {own.1} else ∅) ∪ (N.attach.filter (fun u => (msg u).2)).image (fun u => (msg u).1)

def round : Round V (V × Bool) (Finset V) (V × Bool) where
  send _ _ s := s
  update _ N s msg := selected N s msg

def program {b : ℕ} (C : BitCode V b) : Program V (V × Bool) (Finset V) :=
  .broadcast (b + 1) C.pairBool round

theorem mem_selected (N : Finset V) (own : V × Bool) (msg : N → V × Bool) (d : V) :
    d ∈ selected N own msg ↔ (own.2 = true ∧ own.1 = d) ∨
      ∃ u : N, (msg u).2 = true ∧ (msg u).1 = d := by
  simp only [selected, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  apply or_congr ?_ Iff.rfl
  cases h : own.2 with
  | false => simp [h]
  | true =>
    simp only [h, Bool.true_eq, ↓reduceIte, Finset.mem_singleton, true_and]
    exact eq_comm

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (label : V → V) (S : Finset V) (v : V) :
    (program C).run G (fun u => (label u, decide (u ∈ S))) v = (closed G v ∩ S).image label := by
  change selected (G.neighborFinset v) (label v, decide (v ∈ S)) (fun u => (label u.val, decide (u.val ∈ S))) = _
  ext d
  rw [mem_selected]
  simp only [decide_eq_true_eq, Finset.mem_image, Finset.mem_inter, mem_closed]
  constructor
  · rintro (⟨hv, hd⟩ | ⟨u, hu, hd⟩)
    · exact ⟨v, ⟨Or.inl rfl, hv⟩, hd⟩
    · exact ⟨u.val, ⟨Or.inr ((SimpleGraph.mem_neighborFinset G v u.val).mp u.property), hu⟩, hd⟩
  · rintro ⟨u, ⟨he | hadj, hu⟩, hd⟩
    · subst u
      exact Or.inl ⟨hu, hd⟩
    · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr hadj⟩, hu, hd⟩

theorem rounds {b : ℕ} (C : BitCode V b) : (program C).rounds = 1 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) : (program C).maxBits = b + 1 := rfl
end Paper.LabelNeighborhood
