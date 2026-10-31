import Paper.Preliminaries.CandidateGeometry
import Paper.Partitions.Local.FinitePriorityIndex

namespace Paper.CandidateFrameAgreement
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem near_iff (M : V → Finset V) (F S U : Finset V) (x w : V) (r k t : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) ⊆ F)
    (hwU : w ∈ U) (hw : w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r) :
    U ∈ FiniteEligibility.family M (F ∩ S) k t ↔
      U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t := by
  constructor
  · intro hu
    have hU := CandidateGeometry.local_subset_ball G M F (F ∩ S) U hm Finset.inter_subset_left
      k t hu w hwU x r hw
    exact (CandidateGeometry.membership G M F S U x r k t hm hF hU).mp hu
  · intro hu
    have hh := (FiniteEligibility.mem_family _ S U k t).mp hu
    have hc := (FiniteConnectivity.correct G U).mp hh.2.1
    have hU := CandidateGeometry.connected_subset_ball G U hc k hh.2.2.1 w hwU x r hw
    exact (CandidateGeometry.membership G M F S U x r k t hm hF hU).mpr hu

theorem index_eq (M : V → Finset V) (F U : Finset V) (x : V) (r Δ k : ℕ) (fallback : V)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) ⊆ F)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x r) (hne : U.Nonempty) :
    FinitePriorityIndex.index M Δ k U fallback =
      FinitePriorityIndex.index (fun u => G.neighborFinset u) Δ k U fallback := by
  have hl : FinitePriorityIndex.leader U fallback ∈ U := by
    rw [FinitePriorityIndex.leader, dif_pos hne]
    exact Finset.min'_mem U hne
  have hb := FiniteBallAgreement.balls_eq (fun u => G.neighborFinset u) M
    (FinitePriorityIndex.leader U fallback) k (fun u hu =>
      (hm u (hF (NeighborBalls.subball _ r k x _ (hU hl) hu))).symm)
  unfold FinitePriorityIndex.index
  refine Prod.ext rfl ?_
  funext i
  simp only [FinitePriorityIndex.mask, ← hb]
end Paper.CandidateFrameAgreement
