import Paper.Preliminaries.BoundaryEdges
import Paper.Partitions.Local.PriorityPartition

/-! The actual cut of the output partition is bounded by the accumulated
boundary charges and half the degree times the final residual order. -/
namespace Paper.PriorityCut
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def cut (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V)
    (n : ℕ) (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) : ℕ :=
  (PartCut.graph G S (PriorityPartition.partition G k hk ε S n ω).parts).edgeFinset.card

theorem deterministic (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) (ε : ℝ) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) :
    (cut G k hk ε S n ω : ℝ) ≤ PriorityCost.total G k ε S n ω + (Δ : ℝ) / 2 *
      (FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card := by
  induction n generalizing S with
  | zero =>
    have hb := PartCut.singleton_bound G S Δ hdeg
    have hr : 2 * ((PartCut.graph G S (S.image (fun v => {v}))).edgeFinset.card : ℝ) ≤ (Δ : ℝ) * S.card := by exact_mod_cast hb
    simp only [cut, PriorityPartition.parts_zero, PriorityCost.total, FiniteIteration.run]
    rw [zero_add, div_mul_eq_mul_div]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [mul_comm] using hr
  | succ n ih =>
    let A := SparsePriority.accepted (EligibleSets.family G S k ε) ω.1
    let T := PriorityStage.next G S k ε ω.1
    let P := PriorityPartition.partition G k hk ε T n ω.2
    have hb := BoundaryEdges.cut_count G S A P.parts
    have hr' : ((PartCut.graph G S (A ∪ P.parts)).edgeFinset.card : ℝ) ≤
        (∑ U ∈ A, (PartBoundaries.boundary G S U : ℝ)) +
        ((PartCut.graph G (S \ A.biUnion id) P.parts).edgeFinset.card : ℝ) := by exact_mod_cast hb
    have hr : ((PartCut.graph G S (A ∪ P.parts)).edgeFinset.card : ℝ) ≤
        PriorityCost.stage G S k ε ω.1 + (cut G k hk ε T n ω.2 : ℝ) := hr'
    have hi := ih T ω.2
    simp only [cut, PriorityPartition.parts_succ, PriorityCost.total, FiniteIteration.run]
    change ((PartCut.graph G S (A ∪ P.parts)).edgeFinset.card : ℝ) ≤
      PriorityCost.stage G S k ε ω.1 + PriorityCost.total G k ε T n ω.2 +
        (Δ : ℝ) / 2 * (FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) T n ω.2).card
    linarith

theorem outcome_bound (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) :
    (cut G k hk ε S n ω : ℝ) ≤ 4 * ε * S.card + (Δ : ℝ) / 2 *
      (FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card :=
  (deterministic G Δ hdeg k hk ε S n ω).trans
    (add_le_add (PriorityCost.bound G k hε S n ω) le_rfl)

theorem finite_mean (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) {Q : ℕ} (S : Finset V) (n : ℕ)
    {δ : ℝ} (hremaining : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      ((FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card : ℝ)) ≤
      δ * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card) :
    (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n, (cut G k hk ε S n ω : ℝ)) ≤
      (4 * ε + (Δ : ℝ) / 2 * δ) * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card := by
  have hc : (Fintype.card (FiniteIteration.Seeds (Finset V → Fin Q) n) : ℝ) =
      (Fintype.card (Finset V → Fin Q) : ℝ) ^ n := by exact_mod_cast FiniteIteration.card_seeds (Finset V → Fin Q) n
  have hs := Finset.sum_le_sum (fun (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) (_ : ω ∈ Finset.univ) =>
    outcome_bound G Δ hdeg k hk hε S n ω)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hc] at hs
  have hr := mul_le_mul_of_nonneg_left hremaining (by positivity : (0 : ℝ) ≤ (Δ : ℝ) / 2)
  nlinarith
end Paper.PriorityCut
