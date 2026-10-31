import Paper.Preliminaries.SetNeighborhood

/-! One actual bounded owner-labelled report is sent to every physical
neighbor. The receiver retains only reports carrying its own identifier. -/
namespace Paper.OwnedReportNeighborhood
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure Report (V : Type) where
  owner : V
  active : Bool
  ids : Finset V

def accept (v : V) (r : Report V) : Finset V :=
  if r.active && decide (r.owner = v) then r.ids else ∅

def decode {f : ℕ} (m : (V × Bool) × {l : List V // l.length ≤ f}) : Report V :=
  ⟨m.1.1, m.1.2, m.2.val.toFinset⟩

def round (f : ℕ) : Round V (Report V) (Finset V) ((V × Bool) × {l : List V // l.length ≤ f}) where
  send _ _ s := ((s.owner, s.active), ListIncidenceBroadcast.packet f s.ids)
  update v N own msg := accept v own ∪ N.attach.biUnion (fun u => accept v (decode (msg u)))

def program {b : ℕ} (C : BitCode V b) (f : ℕ) : Program V (Report V) (Finset V) :=
  .broadcast ((b + 1) + f * (b + 1)) (PacketCode.product C.pairBool (ListPacket.bounded C f)) (round f)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (f : ℕ) (s : V → Report V)
    (hs : ∀ u, (s u).ids.card ≤ f) (v : V) :
    (program C f).run G s v = (closed G v).biUnion (fun u => accept v (s u)) := by
  have hd (u : V) : decode (((s u).owner, (s u).active),
      ListIncidenceBroadcast.packet f (s u).ids) = s u := by
    simp only [decode, ListIncidenceBroadcast.packet_set f _ (hs u)]
  change accept v (s v) ∪ (G.neighborFinset v).attach.biUnion
    (fun u => accept v (decode (((s u.val).owner, (s u.val).active), ListIncidenceBroadcast.packet f (s u.val).ids))) = _
  simp only [hd]
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

theorem maxBits {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).maxBits = (b + 1) + f * (b + 1) := rfl
end Paper.OwnedReportNeighborhood
