import Paper.Preliminaries.FiniteConnectivity

/-! Connectivity uses neighbor records only at vertices in the candidate. -/
namespace Paper.FiniteConnectivityLocality
variable {V : Type} [LinearOrder V]

theorem balls_eq (N M : V → Finset V) (S : Finset V)
    (h : ∀ u ∈ S, N u = M u) (v : V) (hv : v ∈ S) (r : ℕ) :
    NeighborBalls.ball (FiniteConnectivity.neighbors N S) v r =
      NeighborBalls.ball (FiniteConnectivity.neighbors M S) v r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    change insert v ((N v ∩ S).biUnion (fun u => NeighborBalls.ball (FiniteConnectivity.neighbors N S) u r)) =
      insert v ((M v ∩ S).biUnion (fun u => NeighborBalls.ball (FiniteConnectivity.neighbors M S) u r))
    rw [h v hv]
    congr 1
    apply Finset.biUnion_congr rfl
    intro u hu
    exact ih u (Finset.mem_inter.mp hu).2

theorem connected_eq (N M : V → Finset V) (S : Finset V) (h : ∀ u ∈ S, N u = M u) :
    FiniteConnectivity.connected N S = FiniteConnectivity.connected M S := by
  by_cases hs : S.Nonempty
  · simp only [FiniteConnectivity.connected, dif_pos hs,
      balls_eq N M S h (S.min' hs) (Finset.min'_mem S hs) S.card]
  · simp only [FiniteConnectivity.connected, dif_neg hs]
end Paper.FiniteConnectivityLocality
