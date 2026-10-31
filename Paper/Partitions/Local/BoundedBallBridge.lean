import Paper.Partitions.Local.NeighborBallGraph
import Paper.Partitions.Local.LocalPriorityIndex

/-! The executable first-step balls coincide with the existing mathematical
last-step balls. This connects local record computations to the proved law. -/
namespace Paper.BoundedBallBridge
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem old_exists_walk (v u : V) (r : ℕ) (hu : u ∈ BoundedBall.ball G v r) :
    ∃ p : G.Walk v u, p.length ≤ r := by
  induction r generalizing u with
  | zero =>
    have he : u = v := Finset.mem_singleton.mp hu
    subst u
    exact ⟨.nil, Nat.zero_le _⟩
  | succ r ih =>
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨p, hp⟩ := ih u hu
      exact ⟨p, hp.trans (Nat.le_succ r)⟩
    · obtain ⟨w, hw, hwu⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨p, hp⟩ := ih w hw
      exact ⟨p.concat ((G.mem_neighborFinset w u).mp hwu), by
        simpa only [SimpleGraph.Walk.length_concat] using Nat.succ_le_succ hp⟩

theorem balls_eq (v : V) (r : ℕ) :
    NeighborBalls.ball (fun u => G.neighborFinset u) v r = BoundedBall.ball G v r := by
  ext u
  constructor
  · intro hu
    obtain ⟨p, hp⟩ := NeighborBallGraph.exists_walk G v u r hu
    exact BoundedBall.mono G v hp (BoundedBall.walk_mem G p)
  · intro hu
    obtain ⟨p, hp⟩ := old_exists_walk G v u r hu
    exact NeighborBallGraph.walk_mem G p r hp
end Paper.BoundedBallBridge
