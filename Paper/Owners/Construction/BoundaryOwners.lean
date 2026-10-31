import Paper.Owners.Construction.OwnerPartitionDistribution

/-! Actual boundary vertices of the output partition. Their exact mean
number is at most twice the proved mean number of crossing edges. -/
namespace Paper.BoundaryOwners
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def vertices (S : Finset V) (P : Finset (Finset V)) : Finset V :=
  (PartCut.graph G S P).support.toFinset

theorem card_support (K : SimpleGraph V) [DecidableRel K.Adj] :
    K.support.toFinset.card ≤ 2 * K.edgeFinset.card := by
  calc
    _ = ∑ _v ∈ K.support.toFinset, 1 := by simp
    _ ≤ ∑ v ∈ K.support.toFinset, K.degree v := Finset.sum_le_sum (fun v hv =>
      (K.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv))
    _ ≤ ∑ v, K.degree v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := SimpleGraph.sum_degrees_eq_twice_card_edges K

theorem count (S : Finset V) (P : Finset (Finset V)) :
    (vertices G S P).card ≤ 2 * (PartCut.graph G S P).edgeFinset.card := card_support _

theorem subset (S : Finset V) (P : Finset (Finset V)) : vertices G S P ⊆ S := by
  intro v hv
  obtain ⟨u, hu⟩ := (SimpleGraph.mem_support _).mp (Set.mem_toFinset.mp hv)
  exact hu.2.1

theorem same_part (S : Finset V) (P : Finset (Finset V)) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (ha : G.Adj u v) (hboundary : u ∉ vertices G S P) :
    ∃ U ∈ P, u ∈ U ∧ v ∈ U := by
  by_contra hn
  have hcut : (PartCut.graph G S P).Adj u v := ⟨ha, hu, hv, hn⟩
  exact hboundary (Set.mem_toFinset.mpr ((SimpleGraph.mem_support _).mpr ⟨v, hcut⟩))

noncomputable def outcome (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V)
    (n : ℕ) (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) : Finset V :=
  vertices G S (PriorityPartition.partition G k hk ε S n ω).parts

theorem finite_mean (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V) (n : ℕ)
    {η : ℝ} (hcut : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      (PriorityCut.cut G k hk ε S n ω : ℝ)) ≤
      η * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card) :
    (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n, ((outcome G k hk ε S n ω).card : ℝ)) ≤
      2 * η * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card := by
  have hb : ∀ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      ((outcome G k hk ε S n ω).card : ℝ) ≤ 2 * (PriorityCut.cut G k hk ε S n ω : ℝ) := by
    intro ω
    exact_mod_cast count G S (PriorityPartition.partition G k hk ε S n ω).parts
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hb ω)
  rw [← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith
end Paper.BoundaryOwners
