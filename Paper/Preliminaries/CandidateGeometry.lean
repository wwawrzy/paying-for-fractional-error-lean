import Paper.Partitions.Local.FiniteBallAgreement
import Paper.Preliminaries.FiniteEligibilityLocality
import Paper.Partitions.Local.BoundedBallBridge

/-! Geometry discharges candidate-agreement premises from actual finite
frame coverage. No assumed partition locality is used. -/
namespace Paper.CandidateGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem connected_subset_ball (U : Finset V) (hc : (G.induce (U : Set V)).Connected)
    (k : ℕ) (hk : U.card ≤ k) (v : V) (hv : v ∈ U) (x : V) (r : ℕ)
    (hx : v ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r) :
    U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) := by
  have hh := BoundedBall.contains_connected G U hc k hk v hv
  intro u hu
  apply NeighborBalls.subball (fun u => G.neighborFinset u) r k x v hx
  rw [BoundedBallBridge.balls_eq G v k]
  exact hh hu

theorem local_connected (M : V → Finset V) (F S U : Finset V)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hs : S ⊆ F)
    (k t : ℕ) (hu : U ∈ FiniteEligibility.family M S k t) :
    (G.induce (U : Set V)).Connected := by
  have hh := (FiniteEligibility.mem_family M S U k t).mp hu
  apply (FiniteConnectivity.correct G U).mp
  rw [← FiniteConnectivityLocality.connected_eq M (fun u => G.neighborFinset u) U
    (fun u hu => hm u (hs (hh.1 hu)))]
  exact hh.2.1

theorem local_subset_ball (M : V → Finset V) (F S U : Finset V)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hs : S ⊆ F)
    (k t : ℕ) (hu : U ∈ FiniteEligibility.family M S k t)
    (v : V) (hv : v ∈ U) (x : V) (r : ℕ)
    (hx : v ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r) :
    U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) :=
  connected_subset_ball G U (local_connected G M F S U hm hs k t hu) k
    ((FiniteEligibility.mem_family M S U k t).mp hu).2.2.1 v hv x r hx

theorem membership (M : V → Finset V) (F S U : Finset V) (x : V) (r k t : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) ⊆ F)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k)) :
    U ∈ FiniteEligibility.family M (F ∩ S) k t ↔
      U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t := by
  have huF : ∀ u ∈ U, u ∈ F := fun u hu => hF (NeighborBalls.step_subset _ x (r + k) (hU hu))
  apply FiniteEligibilityLocality.mem_iff M (fun u => G.neighborFinset u) (F ∩ S) S U k t
  · exact fun u hu => hm u (huF u hu)
  · intro u hu
    exact ⟨fun h => (Finset.mem_inter.mp h).2, fun h => Finset.mem_inter.mpr ⟨huF u hu, h⟩⟩
  · intro u hu w hw
    have hwG : w ∈ G.neighborFinset u := by rw [← hm u (huF u hu)]; exact hw
    have hwF := hF (FiniteBallAgreement.neighbor_of_mem _ x u w (r + k) (hU hu) hwG)
    exact ⟨fun h => (Finset.mem_inter.mp h).2, fun h => Finset.mem_inter.mpr ⟨hwF, h⟩⟩
end Paper.CandidateGeometry
