import Paper.Partitions.Local.NeighborBallGraph
import Paper.Preliminaries.TaggedDictionary
import Paper.Preliminaries.TopologyGather

/-! Actual local evaluation from finite received topology and seed records.
No global vertex enumeration, graph argument or external decoder occurs
in these executable definitions. -/
namespace Paper.FrameInterpreter
open BroadcastModel NeighborBalls
variable {V : Type} [LinearOrder V]

def neighbors {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) (u : V) : Finset V :=
  ((TaggedDictionary.lookup xs u).map (fun l => l.val.toFinset)).getD ∅

def inputs {In : Type} (ys : List (V × In)) (fallback : In) (u : V) : In :=
  (TaggedDictionary.lookup ys u).getD fallback

def evaluate {In Out : Type} {Δ : ℕ} (P : Program V In Out)
    (xs : List (TopologyGather.Record V Δ)) (ys : List (V × In)) (fallback : In) (v : V) : Out :=
  NeighborInterpreter.run (neighbors xs) P (inputs ys fallback) v

theorem neighbors_correct {Δ : ℕ} (xs : List (TopologyGather.Record V Δ))
    (N : V → Finset V) (hs : ∀ p ∈ xs, p.2.val.toFinset = N p.1)
    (u : V) (hu : u ∈ TaggedDictionary.keys xs) : neighbors xs u = N u := by
  rw [neighbors, TaggedDictionary.lookup, TaggedDictionary.find_entry xs u hu]
  simp only [Option.map_some, Option.getD_some]
  rw [hs _ (TaggedDictionary.entry_mem xs u hu), TaggedDictionary.entry_key xs u hu]

theorem inputs_correct {In : Type} (ys : List (V × In)) (fallback : In) (s : V → In)
    (hs : TaggedDictionary.Consistent s ys) (u : V) (hu : u ∈ TaggedDictionary.keys ys) :
    inputs ys fallback u = s u := by
  rw [inputs, TaggedDictionary.lookup_correct s ys hs u hu]
  rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {In Out : Type} {Δ : ℕ} (P : Program V In Out)
    (xs : List (TopologyGather.Record V Δ)) (ys : List (V × In)) (fallback : In)
    (s : V → In) (v : V)
    (hxs : ∀ p ∈ xs, p.2.val.toFinset = G.neighborFinset p.1)
    (hys : TaggedDictionary.Consistent s ys)
    (hx : ball (fun u => G.neighborFinset u) v P.rounds ⊆ TaggedDictionary.keys xs)
    (hy : ball (fun u => G.neighborFinset u) v P.rounds ⊆ TaggedDictionary.keys ys) :
    evaluate P xs ys fallback v = P.run G s v := by
  have hh := NeighborLocality.locality P (fun u => G.neighborFinset u) (neighbors xs)
    s (inputs ys fallback) v
    (fun u hu => (neighbors_correct xs (fun w => G.neighborFinset w) hxs u (hx hu)).symm)
    (fun u hu => (inputs_correct ys fallback s hys u (hy hu)).symm)
  rw [NeighborInterpreter.run_graph] at hh
  exact hh.symm
end Paper.FrameInterpreter
