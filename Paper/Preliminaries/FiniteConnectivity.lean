import Paper.Partitions.Local.NeighborBallGraph

/-! Executable connectivity of a finite candidate from local neighbor
records, by finite bounded-radius exploration entirely inside the candidate. -/
namespace Paper.FiniteConnectivity
variable {V : Type} [LinearOrder V]

def neighbors (N : V → Finset V) (S : Finset V) (v : V) : Finset V := N v ∩ S

def connected (N : V → Finset V) (S : Finset V) : Bool :=
  if h : S.Nonempty then decide (S ⊆ NeighborBalls.ball (neighbors N S) (S.min' h) S.card) else false

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem walk_mem (S : Finset V) {v u : S} (p : (G.induce (S : Set V)).Walk v u) :
    u.val ∈ NeighborBalls.ball (neighbors (fun w => G.neighborFinset w) S) v.val p.length := by
  induction p with
  | nil => exact NeighborBalls.self_mem _ _ _
  | @cons v w u ha p ih =>
    apply (NeighborBalls.mem_succ _ v.val u.val p.length).mpr
    exact Or.inr ⟨w.val, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v.val w.val).mpr ha, w.property⟩, ih⟩

theorem mem_walk (S : Finset V) (v : V) (hv : v ∈ S) (u : V) (r : ℕ)
    (hu : u ∈ NeighborBalls.ball (neighbors (fun w => G.neighborFinset w) S) v r) :
    ∃ hw : u ∈ S, Nonempty ((G.induce (S : Set V)).Walk ⟨v, hv⟩ ⟨u, hw⟩) := by
  induction r generalizing v u with
  | zero =>
    have he := (NeighborBalls.mem_zero _ v u).mp hu
    subst u
    exact ⟨hv, ⟨.nil⟩⟩
  | succ r ih =>
    rcases (NeighborBalls.mem_succ _ v u r).mp hu with he | ⟨w, hw, hu⟩
    · subst u
      exact ⟨hv, ⟨.nil⟩⟩
    · have hw' := Finset.mem_inter.mp hw
      obtain ⟨huS, ⟨p⟩⟩ := ih w hw'.2 u hu
      have ha : (G.induce (S : Set V)).Adj ⟨v, hv⟩ ⟨w, hw'.2⟩ :=
        (G.mem_neighborFinset v w).mp hw'.1
      exact ⟨huS, ⟨.cons ha p⟩⟩

theorem correct (S : Finset V) :
    connected (fun v => G.neighborFinset v) S = true ↔ (G.induce (S : Set V)).Connected := by
  by_cases hs : S.Nonempty
  · simp only [connected, dif_pos hs, decide_eq_true_eq]
    constructor
    · intro h
      apply (SimpleGraph.connected_iff_exists_forall_reachable (G.induce (S : Set V))).mpr
      refine ⟨⟨S.min' hs, Finset.min'_mem S hs⟩, ?_⟩
      intro u
      obtain ⟨hu, hp⟩ := mem_walk G S (S.min' hs) (Finset.min'_mem S hs) u.val S.card (h u.property)
      exact hp
    · intro h u hu
      obtain ⟨p, hp⟩ := (h ⟨S.min' hs, Finset.min'_mem S hs⟩ ⟨u, hu⟩).exists_isPath
      have hlen : p.length ≤ S.card := by
        have hh := hp.length_lt
        simpa only [Finset.coe_sort_coe, Fintype.card_coe] using Nat.le_of_lt hh
      exact NeighborBalls.monotone _ _ hlen (walk_mem G S p)
  · simp only [connected, dif_neg hs, Bool.false_eq_true, false_iff]
    intro h
    obtain ⟨u⟩ := h.nonempty
    exact hs ⟨u.val, u.property⟩
end Paper.FiniteConnectivity
