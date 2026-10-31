import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Distance bounds in a connected graph covered by finitely many balls.
The shortest-walk argument is reused unchanged; fixed-radius corollaries
express the bounds in terms of an upper bound on the number of centers. -/
namespace SimpleGraph.DominationDiameter

variable {V : Type*} [DecidableEq V]

theorem shortest_prefix_distance (G : SimpleGraph V) {x y : V}
    (p : G.Walk x y) (hp : p.length = G.dist x y)
    (i : ℕ) (hi : i ≤ p.length) : G.dist x (p.getVert i) = i := by
  have h := G.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  simpa only [SimpleGraph.Walk.take_length, Nat.min_eq_left hi] using h.symm

theorem domination_bounds_distance
    (G : SimpleGraph V) (connected : G.Connected) (r : ℕ) (B : Finset V)
    (cover : ∀ v, ∃ b ∈ B, G.dist v b ≤ r) (x y : V) :
    G.dist x y < (2 * r + 1) * B.card := by
  by_contra hlt
  have hlong : (2 * r + 1) * B.card ≤ G.dist x y := by omega
  obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist x y
  let step := 2 * r + 1
  let sample : Fin (B.card + 1) → V := fun i => p.getVert (step * i.val)
  have sample_dist : ∀ i, G.dist x (sample i) = step * i.val := by
    intro i
    apply shortest_prefix_distance G p hp
    have hi : i.val ≤ B.card := by omega
    have hm := Nat.mul_le_mul_left step hi
    dsimp [step] at hm ⊢
    omega
  have witness : ∀ i, ∃ b : B, G.dist (sample i) b ≤ r := by
    intro i
    obtain ⟨b, hb, hdist⟩ := cover (sample i)
    exact ⟨⟨b, hb⟩, hdist⟩
  choose center hcenter using witness
  have increasing : ∀ i j, i.val < j.val → center i ≠ center j := by
    intro i j hij heq
    have htri₁ : G.dist x (sample j) ≤ G.dist x (sample i) + G.dist (sample i) (sample j) :=
      connected.dist_triangle
    have htri₂ : G.dist (sample i) (sample j) ≤
        G.dist (sample i) (center i) + G.dist (center i) (sample j) := connected.dist_triangle
    have hci := hcenter i
    have hcj := hcenter j
    rw [← heq] at hcj
    rw [G.dist_comm] at hcj
    rw [sample_dist i, sample_dist j] at htri₁
    have hmul := Nat.mul_le_mul_left step (Nat.succ_le_of_lt hij)
    rw [Nat.mul_succ] at hmul
    dsimp [step] at hmul htri₁
    omega
  have injective : Function.Injective center := by
    intro i j heq
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt | hequal | hgt
    · exact False.elim (increasing i j hlt heq)
    · exact hequal
    · exact False.elim (increasing j i hgt heq.symm)
  have hc := Fintype.card_le_of_injective center injective
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

/-- A radius-one cover with at most K centers bounds every distance by 3K-1. -/
theorem radius_one_distance_le
    (G : SimpleGraph V) (connected : G.Connected) (B : Finset V) (K : ℕ)
    (cover : ∀ v, ∃ b ∈ B, G.dist v b ≤ 1) (hcard : B.card ≤ K) (x y : V) :
    G.dist x y ≤ 3 * K - 1 := by
  have h := domination_bounds_distance G connected 1 B cover x y
  omega

/-- A radius-two cover with at most K centers bounds every distance by 5K-1. -/
theorem radius_two_distance_le
    (G : SimpleGraph V) (connected : G.Connected) (B : Finset V) (K : ℕ)
    (cover : ∀ v, ∃ b ∈ B, G.dist v b ≤ 2) (hcard : B.card ≤ K) (x y : V) :
    G.dist x y ≤ 5 * K - 1 := by
  have h := domination_bounds_distance G connected 2 B cover x y
  omega

#print axioms shortest_prefix_distance
#print axioms domination_bounds_distance
#print axioms radius_one_distance_le
#print axioms radius_two_distance_le

end SimpleGraph.DominationDiameter
