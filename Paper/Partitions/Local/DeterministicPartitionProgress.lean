import Paper.Partitions.Local.DeterministicPartitionGreedy
import Paper.Preliminaries.FiniteEligibility
import Paper.Preliminaries.EligibleConflicts

/-! Executable deterministic stage and its graph-theoretic progress bound.
The coloring is an input to this stage; computing a small proper palette
and simulating its communication are separate obligations. -/
namespace Paper.DeterministicPartitionProgress
open scoped BigOperators
variable {V : Type} [LinearOrder V]

/-- The integer eligibility test is evaluated in the stage-start state. -/
def accepted (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) : Finset (Finset V) :=
  DeterministicPartitionGreedy.run (FiniteEligibility.family N S k t) color q

def removed (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) : Finset V :=
  (accepted N S k t color q).biUnion id

def next (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) : Finset V :=
  S \ removed N S k t color q

theorem accepted_subset (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) :
    accepted N S k t color q ⊆ FiniteEligibility.family N S k t :=
  DeterministicPartitionGreedy.subset _ _ _

theorem accepted_disjoint (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : DeterministicPartitionGreedy.Proper (FiniteEligibility.family N S k t) color) :
    (accepted N S k t color q : Set (Finset V)).Pairwise Disjoint :=
  DeterministicPartitionGreedy.disjoint _ _ hc q

theorem removed_subset (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) : removed N S k t color q ⊆ S :=
  DeterministicPartitionGreedy.removed_subset _ color q S
    (fun U hU => ((FiniteEligibility.mem_family N S U k t).mp hU).1)

theorem card_split (N : V → Finset V) (S : Finset V) (k t : ℕ)
    (color : Finset V → ℕ) (q : ℕ) :
    (next N S k t color q).card + (removed N S k t color q).card = S.card :=
  Finset.card_sdiff_add_card_eq_card (removed_subset N S k t color q)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Bound all intersecting candidates, including the accepted set itself. -/
theorem touching_bound (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (E : Finset (Finset V)) (k : ℕ)
    (hE : ∀ U ∈ E, (G.induce (U : Set V)).Connected ∧ U.card ≤ k)
    (U : Finset V) (hU : U ∈ E) :
    (DeterministicPartitionGreedy.touching E U).card ≤ k * 2 ^ ((Δ + 1) ^ k) := by
  have hsub : DeterministicPartitionGreedy.touching E U ⊆
      U.biUnion (fun v => BoundedBall.smallContaining G v k) := by
    intro W hW
    have hw := Finset.mem_filter.mp hW
    obtain ⟨v, hvW, hvU⟩ := Finset.not_disjoint_iff.mp hw.2
    exact Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvW, (hE W hw.1).1, (hE W hw.1).2⟩⟩
  calc
    _ ≤ (U.biUnion (fun v => BoundedBall.smallContaining G v k)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ U, (BoundedBall.smallContaining G v k).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ U, 2 ^ ((Δ + 1) ^ k) :=
      Finset.sum_le_sum (fun v _ => BoundedBall.small_count G Δ hdeg v k)
    _ = U.card * 2 ^ ((Δ + 1) ^ k) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (hE U hU).2

theorem eligible_nonempty (S : Finset V) (k t : ℕ) (ht : 0 < t)
    (U : Finset V) (hU : U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) S k t) :
    U.Nonempty := by
  rw [FiniteEligibility.correct G S k t ht] at hU
  have hh := (EligibleSets.mem_family G S U k (1 / (t : ℝ))).mp hU
  obtain ⟨v⟩ := hh.2.1.nonempty
  exact ⟨v.val, v.property⟩

theorem accepted_spec (S : Finset V) (k t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ) (U : Finset V)
    (hU : U ∈ accepted (fun v => G.neighborFinset v) S k t color q) :
    U ⊆ S ∧ (G.induce (U : Set V)).Connected ∧ U.card ≤ k ∧
      (PartBoundaries.boundary G S U : ℝ) ≤ 4 * (1 / (t : ℝ)) * U.card := by
  have hu := accepted_subset (fun v => G.neighborFinset v) S k t color q hU
  rw [FiniteEligibility.correct G S k t ht] at hu
  exact (EligibleSets.mem_family G S U k (1 / (t : ℝ))).mp hu

/-- The same eligibility budget used by the random construction holds for
this deterministic sweep. It charges actual current physical boundaries. -/
theorem boundary_budget (S : Finset V) (k t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) S k t) color) :
    (∑ U ∈ accepted (fun v => G.neighborFinset v) S k t color q,
        (PartBoundaries.boundary G S U : ℝ)) ≤
      4 * (1 / (t : ℝ)) * (removed (fun v => G.neighborFinset v) S k t color q).card := by
  have hcard := DeterministicPartitionGreedy.removed_card
    (FiniteEligibility.family (fun v => G.neighborFinset v) S k t) color hc q
  have hreal : ((removed (fun v => G.neighborFinset v) S k t color q).card : ℝ) =
      ∑ U ∈ accepted (fun v => G.neighborFinset v) S k t color q, (U.card : ℝ) := by
    exact_mod_cast hcard
  rw [hreal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U hU
  exact (accepted_spec G S k t ht color q U hU).2.2.2

/-- Each stage-start eligible set intersects an actually accepted set. -/
theorem dominates (S : Finset V) (k t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hpalette : ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) S k t,
      color U < q) :
    ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) S k t,
      ∃ W ∈ accepted (fun v => G.neighborFinset v) S k t color q, ¬ Disjoint U W := by
  intro U hU
  exact DeterministicPartitionGreedy.dominates _ color
    (eligible_nonempty G S k t ht) q U hU (hpalette U hU)

/-- Uniform deterministic progress; M = k * 2^((Δ+1)^k) counts touching candidates. -/
theorem half_progress {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (S : Finset V) (color : Finset V → ℕ) (q : ℕ)
    (hc : DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) S k t) color)
    (hpalette : ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) S k t,
      color U < q) :
    S.card ≤ (2 * k * (k * 2 ^ ((Δ + 1) ^ k))) *
      (removed (fun v => G.neighborFinset v) S k t color q).card := by
  let E := FiniteEligibility.family (fun v => G.neighborFinset v) S k t
  have hE : ∀ U ∈ E, (G.induce (U : Set V)).Connected ∧ U.card ≤ k := by
    intro U hU
    dsimp only [E] at hU
    rw [FiniteEligibility.correct G S k t ht] at hU
    have hh := (EligibleSets.mem_family G S U k (1 / (t : ℝ))).mp hU
    exact ⟨hh.2.1, hh.2.2.1⟩
  have hε : (0 : ℝ) < 1 / (t : ℝ) := by positivity
  have hhalf := EligibleSets.half_covered G hC hprofile Δ hdeg k hk hε hparam S
  have hhalfNat : S.card ≤ 2 * (E.biUnion id).card := by
    have he : E.biUnion id = EligibleSets.covered G S k (1 / (t : ℝ)) := by
      dsimp only [E, EligibleSets.covered]
      rw [FiniteEligibility.correct G S k t ht]
    rw [he]
    have hh : (S.card : ℝ) ≤ 2 * (EligibleSets.covered G S k (1 / (t : ℝ))).card := by
      linarith
    exact_mod_cast hh
  exact DeterministicPartitionGreedy.half_progress E color hc
    (eligible_nonempty G S k t ht) q k (k * 2 ^ ((Δ + 1) ^ k)) hpalette
    (fun U hU => (hE U hU).2) (touching_bound G Δ hdeg E k hE) S hhalfNat

theorem remaining_bound {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (S : Finset V) (color : Finset V → ℕ) (q : ℕ)
    (hc : DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) S k t) color)
    (hpalette : ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) S k t,
      color U < q) :
    (2 * k * (k * 2 ^ ((Δ + 1) ^ k))) *
        (next (fun v => G.neighborFinset v) S k t color q).card ≤
      (2 * k * (k * 2 ^ ((Δ + 1) ^ k)) - 1) * S.card := by
  have hp := half_progress G hC hprofile Δ hdeg k hk t ht hparam S color q hc hpalette
  have hs := card_split (fun v => G.neighborFinset v) S k t color q
  exact DeterministicPartitionGreedy.remaining_of_progress (by positivity) hs hp

end Paper.DeterministicPartitionProgress

#print axioms Paper.DeterministicPartitionProgress.accepted_disjoint
#print axioms Paper.DeterministicPartitionProgress.dominates
#print axioms Paper.DeterministicPartitionProgress.remaining_bound
#print axioms Paper.DeterministicPartitionProgress.boundary_budget
