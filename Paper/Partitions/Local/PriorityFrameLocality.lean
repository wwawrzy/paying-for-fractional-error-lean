import Paper.Preliminaries.CandidateFrameAgreement
import Paper.Preliminaries.FiniteAcceptanceLocality

/-! One priority stage has an explicit finite topology radius. Candidate
and conflict agreement follow from geometry, never from a locality oracle. -/
namespace Paper.PriorityFrameLocality
variable {V : Type} [LinearOrder V]

def priority (N : V → Finset V) (Δ k : ℕ) (fallback : V) {Q : ℕ}
    (seed : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q) (U : Finset V) : Fin Q :=
  let i := FinitePriorityIndex.index N Δ k U fallback
  seed i.1 i.2

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem priority_eq (M : V → Finset V) (F U : Finset V) (x : V) (r Δ k : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) ⊆ F)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x r) (hne : U.Nonempty)
    (hs : ∀ u ∈ F, η u = ζ u) :
    priority M Δ k x η U = priority (fun u => G.neighborFinset u) Δ k x ζ U := by
  unfold priority
  rw [CandidateFrameAgreement.index_eq G M F U x r Δ k x hm hF hU hne]
  have hl : FinitePriorityIndex.leader U x ∈ U := by
    rw [FinitePriorityIndex.leader, dif_pos hne]
    exact Finset.min'_mem U hne
  have hlF := hF (NeighborBalls.monotone _ x (Nat.le_add_right r k) (hU hl))
  exact congrFun (hs _ hlF) _

theorem accepted_iff (M : V → Finset V) (F S U : Finset V) (x : V) (Δ k t : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) ⊆ F)
    (hs : ∀ u ∈ F, η u = ζ u) (hx : x ∈ U) :
    U ∈ FinitePriorityRule.accepted (FiniteEligibility.family M (F ∩ S) k t) (priority M Δ k x η) ↔
      U ∈ FinitePriorityRule.accepted (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (priority (fun u => G.neighborFinset u) Δ k x ζ) := by
  have hrad : ∀ a, a ≤ 3 * k + 1 → NeighborBalls.ball (fun u => G.neighborFinset u) x a ⊆ F :=
    fun a ha => (NeighborBalls.monotone _ x ha).trans hF
  have he := CandidateFrameAgreement.near_iff G M F S U x x 0 k t hm
    (hrad _ (by omega)) hx (NeighborBalls.self_mem _ x 0)
  by_cases hu : U ∈ FiniteEligibility.family M (F ∩ S) k t
  · have hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x k := by
      simpa only [Nat.zero_add] using CandidateGeometry.local_subset_ball G M F (F ∩ S) U hm
        Finset.inter_subset_left k t hu x hx x 0 (NeighborBalls.self_mem _ x 0)
    apply FiniteAcceptanceLocality.accepted_iff _ _ _ _ U he
      (priority_eq G M F U x k Δ k η ζ hm (hrad _ (by omega)) hU ⟨x, hx⟩ hs)
    · intro T hd
      obtain ⟨w, hwU, hwT⟩ := Finset.not_disjoint_iff.mp hd
      exact CandidateFrameAgreement.near_iff G M F S T x w k k t hm
        (hrad _ (by omega)) hwT (hU hwU)
    · intro T ht hd
      obtain ⟨w, hwU, hwT⟩ := Finset.not_disjoint_iff.mp hd
      have hT := CandidateGeometry.local_subset_ball G M F (F ∩ S) T hm
        Finset.inter_subset_left k t ht w hwT x k (hU hwU)
      exact priority_eq G M F T x (k + k) Δ k η ζ hm (hrad _ (by omega)) hT ⟨w, hwT⟩ hs
  · have hu' : U ∉ FiniteEligibility.family (fun u => G.neighborFinset u) S k t := fun h => hu (he.mpr h)
    simp only [FinitePriorityRule.accepted, Finset.mem_filter, hu, hu', false_and]

theorem part_eq (M : V → Finset V) (F S : Finset V) (x : V) (Δ k t : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) ⊆ F)
    (hs : ∀ u ∈ F, η u = ζ u) :
    FinitePriorityRule.part (FiniteEligibility.family M (F ∩ S) k t) (priority M Δ k x η) x =
      FinitePriorityRule.part (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (priority (fun u => G.neighborFinset u) Δ k x ζ) x := by
  apply FiniteAcceptanceLocality.part_eq
  exact fun U hx => accepted_iff G M F S U x Δ k t η ζ hm hF hs hx
end Paper.PriorityFrameLocality
