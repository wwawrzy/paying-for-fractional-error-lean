import Paper.Preliminaries.LabeledTopologyGather
import Paper.Preliminaries.FrameInterpreter

/-! Executable projections and lookup of labeled topology records. -/
namespace Paper.LabeledFrame
variable {V A : Type} [LinearOrder V] [DecidableEq A]

def topology {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) : List (TopologyGather.Record V Δ) :=
  xs.map (fun p => (p.1, p.2.1))

def labels {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) : List (V × A) :=
  xs.map (fun p => (p.1, p.2.2))

def neighbors {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) : V → Finset V :=
  FrameInterpreter.neighbors (topology xs)

def inputs {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) (fallback : A) : V → A :=
  FrameInterpreter.inputs (labels xs) fallback

theorem topology_keys {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) :
    TaggedDictionary.keys (topology xs) = TaggedDictionary.keys xs := by
  simp only [topology, TaggedDictionary.keys, List.map_map, Function.comp_def]

theorem labels_keys {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ)) :
    TaggedDictionary.keys (labels xs) = TaggedDictionary.keys xs := by
  simp only [labels, TaggedDictionary.keys, List.map_map, Function.comp_def]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem neighbors_correct {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ))
    (s : V → A) (hdeg : ∀ v, G.degree v ≤ Δ)
    (htrue : ∀ p ∈ xs, ∃ u, p = LabeledTopologyGather.localData G Δ s u)
    (u : V) (hu : u ∈ TaggedDictionary.keys xs) : neighbors xs u = G.neighborFinset u := by
  apply FrameInterpreter.neighbors_correct (topology xs) (fun u => G.neighborFinset u)
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, rfl⟩ := htrue a ha
    change ((LabeledTopologyGather.localData G Δ s v).2.1.val).toFinset = _
    rw [LabeledTopologyGather.true_neighbors G Δ hdeg s v, Finset.sort_toFinset]
    rfl
  · rw [topology_keys]
    exact hu

theorem inputs_correct {Δ : ℕ} (xs : List (LabeledTopologyGather.Record V A Δ))
    (s : V → A) (fallback : A)
    (htrue : ∀ p ∈ xs, ∃ u, p = LabeledTopologyGather.localData G Δ s u)
    (u : V) (hu : u ∈ TaggedDictionary.keys xs) : inputs xs fallback u = s u := by
  apply FrameInterpreter.inputs_correct (labels xs) fallback s
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, rfl⟩ := htrue a ha
    rfl
  · rw [labels_keys]
    exact hu


theorem gather_true {b w : ℕ} (C : BroadcastModel.BitCode V b) (P : BroadcastModel.BitCode A w)
    (Δ r : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (s : V → A) (v : V) :
    ∀ p ∈ (LabeledTopologyGather.program C P Δ r).run G s v,
      ∃ u, p = LabeledTopologyGather.localData G Δ s u := by
  intro p hp
  obtain ⟨u, _, _, he⟩ := (LabeledTopologyGather.records G C P Δ r hdeg s v p).mp hp
  exact ⟨u, he⟩

theorem gather_keys {b w : ℕ} (C : BroadcastModel.BitCode V b) (P : BroadcastModel.BitCode A w)
    (Δ r : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (s : V → A) (v : V) :
    TaggedDictionary.keys ((LabeledTopologyGather.program C P Δ r).run G s v) =
      NeighborBalls.ball (fun u => G.neighborFinset u) v r := by
  ext u
  rw [TaggedDictionary.mem_keys]
  constructor
  · rintro ⟨a, ha, hk⟩
    obtain ⟨z, p, hp, he⟩ := (LabeledTopologyGather.records G C P Δ r hdeg s v a).mp ha
    have hz : z = u := by rw [he] at hk; exact hk
    exact hz ▸ NeighborBallGraph.walk_mem G p r hp
  · intro hu
    obtain ⟨p, hp⟩ := NeighborBallGraph.exists_walk G v u r hu
    exact ⟨LabeledTopologyGather.localData G Δ s u,
      (LabeledTopologyGather.records G C P Δ r hdeg s v _).mpr ⟨u, p, hp, rfl⟩, rfl⟩
end Paper.LabeledFrame
