import Paper.Preliminaries.NeighborLocality

namespace Paper.FiniteBallAgreement
open NeighborBalls
variable {V : Type} [DecidableEq V]

theorem balls_eq (N M : V → Finset V) (v : V) (r : ℕ)
    (h : ∀ u ∈ ball N v r, N u = M u) : ball N v r = ball M v r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    have hv := h v (self_mem N v (r + 1))
    change insert v ((N v).biUnion (fun u => ball N u r)) =
      insert v ((M v).biUnion (fun u => ball M u r))
    rw [← hv]
    congr 1
    apply Finset.biUnion_congr rfl
    intro u hu
    apply ih u
    intro x hx
    apply h x
    have hh := subball N 1 r v u (neighbor_mem N v u hu) hx
    simpa only [Nat.add_comm] using hh

theorem neighbor_of_mem (N : V → Finset V) (v u w : V) (r : ℕ)
    (hu : u ∈ ball N v r) (hw : w ∈ N u) : w ∈ ball N v (r + 1) :=
  subball N r 1 v u hu (neighbor_mem N u w hw)
end Paper.FiniteBallAgreement
