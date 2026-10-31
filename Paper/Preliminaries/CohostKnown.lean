import Paper.Communication.ListIncidenceBroadcast

/-! Two genuine broadcasts reveal exactly the selection bits of vertices
sharing an original short list. A host first receives one bit from every
neighbor, then broadcasts at most f selected identifiers from its own list.
This works at unbounded physical degrees with receiver-independent messages. -/
namespace Paper.CohostKnown
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def read (v : V) (N : Finset V) (own : Bool) (msg : N → Bool) (u : V) : Bool :=
  if u = v then own else if hu : u ∈ N then msg ⟨u, hu⟩ else false

def flags (f : ℕ) : Round V (Finset V × Bool) {l : List V // l.length ≤ f} Bool where
  send _ _ s := s.2
  update v N s msg := ListIncidenceBroadcast.packet f (s.1.filter (fun u => read v N s.2 msg u))

def reports (f : ℕ) : Round V {l : List V // l.length ≤ f} (Finset V) {l : List V // l.length ≤ f} where
  send _ _ own := own
  update _ N own msg := own.val.toFinset ∪ N.attach.biUnion (fun host => (msg host).val.toFinset)

def program {b : ℕ} (C : BitCode V b) (f : ℕ) :=
  Program.seq (.broadcast 1 BitCode.bool (flags f))
    (.broadcast (f * (b + 1)) (ListPacket.bounded C f) (reports f))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem read_correct (S : Finset V) (v u : V) (hu : u ∈ closed G v) :
    read v (G.neighborFinset v) (decide (v ∈ S)) (fun w => decide (w.val ∈ S)) u = decide (u ∈ S) := by
  by_cases he : u = v
  · subst u
    simp [read]
  · have hn : u ∈ G.neighborFinset v :=
      (SimpleGraph.mem_neighborFinset G v u).mpr (((mem_closed G u v).mp hu).resolve_left he)
    simp only [read, if_neg he, dif_pos hn]

theorem flags_correct (f : ℕ) (lists : V → Finset V)
    (hlocal : ∀ v, lists v ⊆ closed G v) (S : Finset V) (v : V) :
    eval G (flags f) (fun u => (lists u, decide (u ∈ S))) v =
      ListIncidenceBroadcast.packet f (lists v ∩ S) := by
  apply congrArg (ListIncidenceBroadcast.packet f)
  ext u
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hu, hr⟩
    exact ⟨hu, of_decide_eq_true (read_correct G S v u (hlocal v hu) ▸ hr)⟩
  · rintro ⟨hu, hs⟩
    exact ⟨hu, (read_correct G S v u (hlocal v hu)).trans (decide_eq_true hs)⟩

def known (lists : V → Finset V) (S : Finset V) (v : V) : Finset V :=
  (lists v ∩ S) ∪ (G.neighborFinset v).attach.biUnion (fun host => lists host.val ∩ S)

theorem correct {b : ℕ} (C : BitCode V b) (f : ℕ) (lists : V → Finset V)
    (hbound : ∀ u, (lists u).card ≤ f) (hlocal : ∀ u, lists u ⊆ closed G u) (S : Finset V) :
    (program C f).run G (fun u => (lists u, decide (u ∈ S))) = known G lists S := by
  have he : eval G (flags f) (fun u => (lists u, decide (u ∈ S))) =
      fun v => ListIncidenceBroadcast.packet f (lists v ∩ S) := funext (flags_correct G f lists hlocal S)
  change eval G (reports f) (eval G (flags f) (fun u => (lists u, decide (u ∈ S)))) = _
  rw [he]
  have hlen (u : V) : (lists u ∩ S).card ≤ f := (Finset.card_le_card Finset.inter_subset_left).trans (hbound u)
  funext v
  simp only [eval, reports, known, ListIncidenceBroadcast.packet_set f _ (hlen _)]

theorem mem_known (lists : V → Finset V) (S : Finset V) (v u : V) :
    u ∈ known G lists S v ↔ u ∈ S ∧ ∃ host ∈ closed G v, u ∈ lists host := by
  simp only [known, Finset.mem_union, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_attach, true_and]
  constructor
  · rintro (⟨hl, hs⟩ | ⟨host, hl, hs⟩)
    · exact ⟨hs, v, self_mem_closed G v, hl⟩
    · exact ⟨hs, host.val, (mem_closed G host.val v).mpr (Or.inr
        ((SimpleGraph.mem_neighborFinset G v host.val).mp host.property)), hl⟩
  · rintro ⟨hs, host, hhost, hl⟩
    rcases (mem_closed G host v).mp hhost with he | hadj
    · subst host
      exact Or.inl ⟨hl, hs⟩
    · exact Or.inr ⟨⟨host, (SimpleGraph.mem_neighborFinset G v host).mpr hadj⟩, hl, hs⟩

theorem cohost_agrees (lists : V → Finset V) (hlocal : ∀ u, lists u ⊆ closed G u)
    (S : Finset V) (v host u : V) (hv : v ∈ lists host) (hu : u ∈ lists host) :
    u ∈ known G lists S v ↔ u ∈ S := by
  rw [mem_known]
  exact ⟨And.left, fun hs => ⟨hs, host, (closed_symm G host v).mpr (hlocal host hv), hu⟩⟩

theorem rounds {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).rounds = 2 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).maxBits = max 1 (f * (b + 1)) := rfl
end Paper.CohostKnown
