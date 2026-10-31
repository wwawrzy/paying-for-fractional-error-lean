import Mathlib

/-! Finite knowledge sets after closed-neighborhood gossip. Their size is
bounded solely by radius, degree and the initial local payload count. -/
namespace Paper.GossipKnowledge
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def knowledge (initial : V → Finset A) : ℕ → V → Finset A
  | 0, v => initial v
  | r + 1, v => knowledge initial r v ∪ (G.neighborFinset v).biUnion (knowledge initial r)

theorem step (initial : V → Finset A) (r : ℕ) (v : V) :
    knowledge G initial r v ⊆ knowledge G initial (r + 1) v := Finset.subset_union_left

theorem mono (initial : V → Finset A) (v : V) {r s : ℕ} (hrs : r ≤ s) :
    knowledge G initial r v ⊆ knowledge G initial s v := by
  induction s, hrs using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ s _ ih => exact ih.trans (step G initial s v)

theorem card_bound (initial : V → Finset A) (Δ M : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hinit : ∀ v, (initial v).card ≤ M) (r : ℕ) :
    ∀ v, (knowledge G initial r v).card ≤ M * (Δ + 1) ^ r := by
  induction r with
  | zero => intro v; simpa only [knowledge, pow_zero, mul_one] using hinit v
  | succ r ih =>
    intro v
    have hn : ((G.neighborFinset v).biUnion (knowledge G initial r)).card ≤ Δ * (M * (Δ + 1) ^ r) := by
      calc
        _ ≤ ∑ u ∈ G.neighborFinset v, (knowledge G initial r u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ G.neighborFinset v, M * (Δ + 1) ^ r := Finset.sum_le_sum (fun u _ => ih u)
        _ = G.degree v * (M * (Δ + 1) ^ r) := by simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, Nat.cast_id]
        _ ≤ _ := Nat.mul_le_mul_right _ (hdeg v)
    calc
      _ ≤ (knowledge G initial r v).card + ((G.neighborFinset v).biUnion (knowledge G initial r)).card := Finset.card_union_le _ _
      _ ≤ M * (Δ + 1) ^ r + Δ * (M * (Δ + 1) ^ r) := Nat.add_le_add (ih v) hn
      _ = _ := by rw [pow_succ]; ring

theorem of_walk (initial : V → Finset A) {v u : V} (p : G.Walk v u) (r : ℕ) (hlen : p.length ≤ r)
    {a : A} (ha : a ∈ initial u) : a ∈ knowledge G initial r v := by
  induction p generalizing r with
  | nil => exact mono G initial _ (Nat.zero_le r) ha
  | @cons v w u hvw p ih =>
    cases r with
    | zero => simp only [SimpleGraph.Walk.length_cons] at hlen; omega
    | succ r =>
      have hp : p.length ≤ r := by simp only [SimpleGraph.Walk.length_cons] at hlen; omega
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨w, (G.mem_neighborFinset v w).mpr hvw, ih r hp ha⟩)

theorem exists_walk (initial : V → Finset A) (r : ℕ) (v : V) {a : A}
    (ha : a ∈ knowledge G initial r v) : ∃ u, ∃ p : G.Walk v u, p.length ≤ r ∧ a ∈ initial u := by
  induction r generalizing v with
  | zero => exact ⟨v, .nil, le_rfl, ha⟩
  | succ r ih =>
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨u, p, hp, hau⟩ := ih v ha
      exact ⟨u, p, hp.trans (Nat.le_succ _), hau⟩
    · obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨u, p, hp, hau⟩ := ih w ha
      refine ⟨u, SimpleGraph.Walk.cons ((G.mem_neighborFinset v w).mp hw) p, ?_, hau⟩
      simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hp 1
end Paper.GossipKnowledge
