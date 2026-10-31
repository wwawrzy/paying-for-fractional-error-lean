import Paper.Communication.ListIncidenceBroadcast

/-! One bounded-set broadcast reconstructs the union over one's closed
physical neighborhood. Received unions are private and need not be bounded. -/
namespace Paper.SetNeighborhood
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def round (f : ℕ) : Round V (Finset V) (Finset V) {l : List V // l.length ≤ f} where
  send _ _ s := ListIncidenceBroadcast.packet f s
  update _ N own msg := own ∪ N.attach.biUnion (fun u => (msg u).val.toFinset)

def program {b : ℕ} (C : BitCode V b) (f : ℕ) : Program V (Finset V) (Finset V) :=
  .broadcast (f * (b + 1)) (ListPacket.bounded C f) (round f)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (f : ℕ) (s : V → Finset V)
    (hs : ∀ u, (s u).card ≤ f) (v : V) :
    (program C f).run G s v = (closed G v).biUnion s := by
  change s v ∪ (G.neighborFinset v).attach.biUnion
    (fun u => (ListIncidenceBroadcast.packet f (s u.val)).val.toFinset) = _
  simp only [ListIncidenceBroadcast.packet_set f _ (hs _)]
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and, mem_closed]
  constructor
  · rintro (hv | ⟨u, hu⟩)
    · exact ⟨v, Or.inl rfl, hv⟩
    · exact ⟨u.val, Or.inr ((SimpleGraph.mem_neighborFinset G v u.val).mp u.property), hu⟩
  · rintro ⟨u, he | ha, hu⟩
    · subst u
      exact Or.inl hu
    · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr ha⟩, hu⟩

theorem rounds {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).rounds = 1 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).maxBits = f * (b + 1) := rfl
end Paper.SetNeighborhood
