import Paper.Preliminaries.NeighborLocality

namespace Paper.NeighborBallGraph
open NeighborBalls
variable {V : Type} [DecidableEq V]

theorem card_bound (N : V → Finset V) (Δ : ℕ) (hn : ∀ u, (N u).card ≤ Δ)
    (v : V) (r : ℕ) : (ball N v r).card ≤ (Δ + 1) ^ r := by
  induction r generalizing v with
  | zero => simp only [ball, Finset.card_singleton, pow_zero, le_refl]
  | succ r ih =>
    have hsum : ((N v).biUnion (fun u => ball N u r)).card ≤ Δ * (Δ + 1) ^ r := by
      calc
        _ ≤ ∑ u ∈ N v, (ball N u r).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ N v, (Δ + 1) ^ r := Finset.sum_le_sum (fun u _ => ih u)
        _ = (N v).card * (Δ + 1) ^ r := by simp only [Finset.sum_const_nat]
        _ ≤ _ := Nat.mul_le_mul_right _ (hn v)
    have hp : 1 ≤ (Δ + 1) ^ r := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ((N v).biUnion (fun u => ball N u r)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Δ * (Δ + 1) ^ r + 1 := Nat.add_le_add_right hsum 1
      _ ≤ (Δ + 1) ^ (r + 1) := by rw [pow_succ]; nlinarith

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem walk_mem {v u : V} (p : G.Walk v u) (r : ℕ) (hp : p.length ≤ r) :
    u ∈ ball (fun w => G.neighborFinset w) v r := by
  induction r generalizing v u with
  | zero =>
    cases p with
    | nil => exact self_mem _ _ _
    | cons ha p => simp only [SimpleGraph.Walk.length_cons] at hp; omega
  | succ r ih =>
    cases p with
    | nil => exact self_mem _ _ _
    | @cons _ w _ ha p =>
      apply (mem_succ _ v u r).mpr
      exact Or.inr ⟨w, (G.mem_neighborFinset v w).mpr ha, ih p (by simpa using hp)⟩

theorem exists_walk (v u : V) (r : ℕ)
    (hu : u ∈ ball (fun w => G.neighborFinset w) v r) :
    ∃ p : G.Walk v u, p.length ≤ r := by
  induction r generalizing v u with
  | zero =>
    have he := (mem_zero _ v u).mp hu
    subst u
    exact ⟨.nil, Nat.zero_le _⟩
  | succ r ih =>
    rcases (mem_succ _ v u r).mp hu with he | ⟨w, hw, hu⟩
    · subst u
      exact ⟨.nil, Nat.zero_le _⟩
    · obtain ⟨p, hp⟩ := ih w u hu
      exact ⟨.cons ((G.mem_neighborFinset v w).mp hw) p, Nat.succ_le_succ hp⟩

theorem mem_iff_walk (v u : V) (r : ℕ) :
    u ∈ ball (fun w => G.neighborFinset w) v r ↔ ∃ p : G.Walk v u, p.length ≤ r :=
  ⟨exists_walk G v u r, fun ⟨p, hp⟩ => walk_mem G p r hp⟩

theorem graph_card_bound (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) (r : ℕ) :
    (ball (fun u => G.neighborFinset u) v r).card ≤ (Δ + 1) ^ r :=
  card_bound _ Δ (fun u => by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg u) v r
end Paper.NeighborBallGraph
