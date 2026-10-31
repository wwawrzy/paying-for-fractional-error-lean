import Paper.Partitions.Local.DeterministicPartitionStage
import Paper.Preliminaries.PartAssembly

/-! Actual finite iteration of the deterministic greedy stage. The
executable state records the final residual and all previously accepted
parts. Only the terminal residual is split into singleton parts.

The certificate is proved separately from the executable data. A proper
candidate coloring is used at every residual; the supplied power-color
wrapper discharges this condition using the already proved mask colors.
There is no computation of a power coloring or log-star round claim. -/
namespace Paper.DeterministicPartitionIterationCore
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  remaining : Finset V
  accepted : Finset (Finset V)

/-- Execute the current stage, then iterate on its actual residual. -/
def run (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) :
    Finset V → ℕ → State V
  | S, 0 => ⟨S, ∅⟩
  | S, n + 1 =>
    let A := DeterministicPartitionProgress.accepted N S k t color q
    let R := DeterministicPartitionProgress.next N S k t color q
    let future := run N k t color q R n
    ⟨future.remaining, A ∪ future.accepted⟩

/-- All accepted parts, with a singleton for each terminal survivor. -/
def parts (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (n : ℕ) : Finset (Finset V) :=
  (run N k t color q S n).accepted ∪
    (run N k t color q S n).remaining.image (fun v => {v})

theorem remaining_zero (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (S : Finset V) : (run N k t color q S 0).remaining = S := rfl

theorem remaining_succ (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (S : Finset V) (n : ℕ) :
    (run N k t color q S (n + 1)).remaining =
      (run N k t color q (DeterministicPartitionProgress.next N S k t color q) n).remaining := rfl

theorem accepted_succ (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (S : Finset V) (n : ℕ) :
    (run N k t color q S (n + 1)).accepted =
      DeterministicPartitionProgress.accepted N S k t color q ∪
        (run N k t color q (DeterministicPartitionProgress.next N S k t color q) n).accepted := rfl

theorem parts_zero (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (S : Finset V) : parts N k t color q S 0 = S.image (fun v => {v}) := by
  simp only [parts, run, Finset.empty_union]

theorem parts_succ (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (S : Finset V) (n : ℕ) :
    parts N k t color q S (n + 1) =
      DeterministicPartitionProgress.accepted N S k t color q ∪
        parts N k t color q (DeterministicPartitionProgress.next N S k t color q) n := by
  dsimp only [parts, run]
  exact Finset.union_assoc _ _ _

theorem remaining_subset (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ)
    (q : ℕ) (n : ℕ) (S : Finset V) : (run N k t color q S n).remaining ⊆ S := by
  induction n generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    exact (ih (DeterministicPartitionProgress.next N S k t color q)).trans Finset.sdiff_subset

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Proof-only partition invariants for the executable finite family. -/
structure Valid (S : Finset V) (k : ℕ) (P : Finset (Finset V)) : Prop where
  nonempty : ∀ U ∈ P, U.Nonempty
  subset : ∀ U ∈ P, U ⊆ S
  connected : ∀ U ∈ P, (G.induce (U : Set V)).Connected
  size : ∀ U ∈ P, U.card ≤ k
  disjoint : (P : Set (Finset V)).Pairwise Disjoint
  covers : ∀ v ∈ S, ∃ U ∈ P, v ∈ U

def Valid.toData {S : Finset V} {k : ℕ} {P : Finset (Finset V)}
    (h : Valid G S k P) : SmallParts.Data G S k where
  parts := P
  nonempty := h.nonempty
  subset := h.subset
  connected := h.connected
  size := h.size
  disjoint := h.disjoint
  covers := h.covers

theorem valid_data {S : Finset V} {k : ℕ} (P : SmallParts.Data G S k) :
    Valid G S k P.parts :=
  ⟨P.nonempty, P.subset, P.connected, P.size, P.disjoint, P.covers⟩

/-- The actual accumulated parts form a disjoint connected small partition.
The hypothesis concerns only properness of the fixed input coloring. -/
theorem valid (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (n : ℕ) (S : Finset V) :
    Valid G S k (parts (fun v => G.neighborFinset v) k t color q S n) := by
  induction n generalizing S with
  | zero =>
    rw [parts_zero]
    exact valid_data G (PartAssembly.singletons G S k hk)
  | succ n ih =>
    let N := fun v => G.neighborFinset v
    let A := DeterministicPartitionProgress.accepted N S k t color q
    let R := DeterministicPartitionProgress.next N S k t color q
    have hA := fun U (hU : U ∈ A) =>
      DeterministicPartitionProgress.accepted_spec G S k t ht color q U hU
    let P := Valid.toData G (ih R)
    let Q := PartAssembly.merge G S k A
      (fun U hU => (hA U hU).1)
      (fun U hU => by
        obtain ⟨v⟩ := (hA U hU).2.1.nonempty
        exact ⟨v.val, v.property⟩)
      (fun U hU => (hA U hU).2.1)
      (fun U hU => (hA U hU).2.2.1)
      (DeterministicPartitionProgress.accepted_disjoint N S k t color q (hc S)) P
    rw [parts_succ]
    exact valid_data G Q

/-- Proof fields certify the computable output, without choosing a partition. -/
def partition (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (S : Finset V) (n : ℕ) : SmallParts.Data G S k :=
  Valid.toData G (valid G k hk t ht color q hc n S)

theorem partition_parts (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (S : Finset V) (n : ℕ) :
    (partition G k hk t ht color q hc S n).parts =
      parts (fun v => G.neighborFinset v) k t color q S n := rfl

/-- Instantiate the iteration with the existing explicit mask colors.
The distance-2k vertex coloring remains supplied input. -/
def powerPartition (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (Φ : ℕ) (χ : V → Fin Φ) (fallback : V)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (n : ℕ) : SmallParts.Data G S k :=
  partition G k hk t ht
    (DeterministicPartitionColors.color (fun v => G.neighborFinset v) Δ k fallback Φ χ)
    (Φ * 2 ^ ((Δ + 1) ^ k))
    (fun R => DeterministicPartitionColors.proper_eligible G Δ k hdeg fallback Φ χ hpower R t) S n

end Paper.DeterministicPartitionIterationCore

#print axioms Paper.DeterministicPartitionIterationCore.valid
#print axioms Paper.DeterministicPartitionIterationCore.partition_parts
#print axioms Paper.DeterministicPartitionIterationCore.powerPartition
