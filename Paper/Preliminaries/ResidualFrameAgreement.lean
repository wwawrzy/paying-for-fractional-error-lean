import Paper.Partitions.Local.PriorityFrameLocality

/-! Residual regions may disagree near the received frame boundary.
Only equality on the specified inner ball is needed for the next stage. -/
namespace Paper.ResidualFrameAgreement
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem priority_eq_at (M : V → Finset V) (F U : Finset V) (x fallback : V) (r Δ k : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) ⊆ F)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x r) (hne : U.Nonempty)
    (hs : ∀ u ∈ F, η u = ζ u) :
    PriorityFrameLocality.priority M Δ k fallback η U =
      PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback ζ U := by
  unfold PriorityFrameLocality.priority
  rw [CandidateFrameAgreement.index_eq G M F U x r Δ k fallback hm hF hU hne]
  have hl : FinitePriorityIndex.leader U fallback ∈ U := by
    rw [FinitePriorityIndex.leader, dif_pos hne]
    exact Finset.min'_mem U hne
  have hlF := hF (NeighborBalls.monotone _ x (Nat.le_add_right r k) (hU hl))
  exact congrFun (hs _ hlF) _

theorem membership (M : V → Finset V) (F S T U : Finset V) (x : V) (r k t : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1), u ∈ S ↔ u ∈ T)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k)) :
    U ∈ FiniteEligibility.family M S k t ↔
      U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) T k t := by
  have huB : ∀ u ∈ U, u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) :=
    fun u hu => NeighborBalls.step_subset _ x (r + k) (hU hu)
  apply FiniteEligibilityLocality.mem_iff M (fun u => G.neighborFinset u) S T U k t
  · exact fun u hu => hm u (hF (huB u hu))
  · exact fun u hu => hS u (huB u hu)
  · intro u hu w hw
    have hwG : w ∈ G.neighborFinset u := by rw [← hm u (hF (huB u hu))]; exact hw
    exact hS w (FiniteBallAgreement.neighbor_of_mem _ x u w (r + k) (hU hu) hwG)

theorem near_iff (M : V → Finset V) (F S T U : Finset V) (x w : V) (r k t : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hSF : S ⊆ F)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1), u ∈ S ↔ u ∈ T)
    (hwU : w ∈ U) (hw : w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r) :
    U ∈ FiniteEligibility.family M S k t ↔
      U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) T k t := by
  constructor
  · intro hu
    have hU := CandidateGeometry.local_subset_ball G M F S U hm hSF k t hu w hwU x r hw
    exact (membership G M F S T U x r k t hm hF hS hU).mp hu
  · intro hu
    have hh := (FiniteEligibility.mem_family _ T U k t).mp hu
    have hc := (FiniteConnectivity.correct G U).mp hh.2.1
    have hU := CandidateGeometry.connected_subset_ball G U hc k hh.2.2.1 w hwU x r hw
    exact (membership G M F S T U x r k t hm hF hS hU).mpr hu

theorem accepted_iff (M : V → Finset V) (F S T U : Finset V) (x fallback : V) (Δ k t : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hSF : S ⊆ F)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1), u ∈ S ↔ u ∈ T)
    (hs : ∀ u ∈ F, η u = ζ u) (hx : x ∈ U) :
    U ∈ FinitePriorityRule.accepted (FiniteEligibility.family M S k t) (PriorityFrameLocality.priority M Δ k fallback η) ↔
      U ∈ FinitePriorityRule.accepted (FiniteEligibility.family (fun u => G.neighborFinset u) T k t)
        (PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback ζ) := by
  have hrad : ∀ a, a ≤ 3 * k + 1 → NeighborBalls.ball (fun u => G.neighborFinset u) x a ⊆
      NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) := fun _ ha => NeighborBalls.monotone _ x ha
  have he := near_iff G M F S T U x x 0 k t hm hSF
    ((hrad _ (by omega)).trans hF) (fun u hu => hS u (hrad _ (by omega) hu)) hx (NeighborBalls.self_mem _ x 0)
  by_cases hu : U ∈ FiniteEligibility.family M S k t
  · have hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x k := by
      simpa only [Nat.zero_add] using CandidateGeometry.local_subset_ball G M F S U hm hSF k t hu
        x hx x 0 (NeighborBalls.self_mem _ x 0)
    apply FiniteAcceptanceLocality.accepted_iff _ _ _ _ U he
      (priority_eq_at G M F U x fallback k Δ k η ζ hm ((hrad _ (by omega)).trans hF) hU ⟨x, hx⟩ hs)
    · intro W hd
      obtain ⟨w, hwU, hwW⟩ := Finset.not_disjoint_iff.mp hd
      exact near_iff G M F S T W x w k k t hm hSF ((hrad _ (by omega)).trans hF)
        (fun u hu => hS u (hrad _ (by omega) hu)) hwW (hU hwU)
    · intro W hW hd
      obtain ⟨w, hwU, hwW⟩ := Finset.not_disjoint_iff.mp hd
      have hB := CandidateGeometry.local_subset_ball G M F S W hm hSF k t hW w hwW x k (hU hwU)
      exact priority_eq_at G M F W x fallback (k + k) Δ k η ζ hm
        ((hrad _ (by omega)).trans hF) hB ⟨w, hwW⟩ hs
  · have hu' : U ∉ FiniteEligibility.family (fun u => G.neighborFinset u) T k t := fun h => hu (he.mpr h)
    simp only [FinitePriorityRule.accepted, Finset.mem_filter, hu, hu', false_and]

theorem part_eq (M : V → Finset V) (F S T : Finset V) (x fallback : V) (Δ k t : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hSF : S ⊆ F)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1), u ∈ S ↔ u ∈ T)
    (hs : ∀ u ∈ F, η u = ζ u) :
    FinitePriorityRule.part (FiniteEligibility.family M S k t) (PriorityFrameLocality.priority M Δ k fallback η) x =
      FinitePriorityRule.part (FiniteEligibility.family (fun u => G.neighborFinset u) T k t)
        (PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback ζ) x := by
  apply FiniteAcceptanceLocality.part_eq
  exact fun U hx => accepted_iff G M F S T U x fallback Δ k t η ζ hm hSF hF hS hs hx

theorem next_iff (M : V → Finset V) (F S T : Finset V) (x fallback : V) (Δ k t : ℕ) {Q : ℕ}
    (η ζ : V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hSF : S ⊆ F)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (3 * k + 1), u ∈ S ↔ u ∈ T)
    (hs : ∀ u ∈ F, η u = ζ u) :
    x ∈ FinitePriorityRule.next M S k t (PriorityFrameLocality.priority M Δ k fallback η) ↔
      x ∈ FinitePriorityRule.next (fun u => G.neighborFinset u) T k t
        (PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback ζ) := by
  have hr := FiniteAcceptanceLocality.removed_iff _ _ _ _ x
    (fun U hx => accepted_iff G M F S T U x fallback Δ k t η ζ hm hSF hF hS hs hx)
  simp only [FinitePriorityRule.next, Finset.mem_sdiff, hr, hS x (NeighborBalls.self_mem _ x _)]
end Paper.ResidualFrameAgreement
