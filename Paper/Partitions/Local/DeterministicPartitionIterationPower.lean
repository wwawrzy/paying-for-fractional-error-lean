import Paper.Partitions.Local.DeterministicPartitionIterationBounds
import Paper.Partitions.Separators.SeparatorBalance

/-! Uniform parameters and the actual certified iteration with a supplied
power coloring. Nonempty candidates use their own minimum as the irrelevant
fallback of the received mask codec; the empty candidate has color zero.
Thus neither an inhabitant of V nor a global vertex choice is needed.
Computing the supplied vertex coloring remains a separate obligation. -/
namespace Paper.DeterministicPartitionIterationPower

private noncomputable local instance partCutDecidable {V : Type}
    [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (P : Finset (Finset V)) : DecidableRel (PartCut.graph G S P).Adj :=
  fun _ _ => Classical.propDecidable _

section Kernel
variable {V : Type} [LinearOrder V]

/-- Canonical executable mask color, also defined on an empty vertex type. -/
def color (N : V → Finset V) (Δ k Φ : ℕ) (χ : V → Fin Φ) (U : Finset V) : ℕ :=
  if hU : U.Nonempty then
    DeterministicPartitionColors.color N Δ k (U.min' hU) Φ χ U
  else 0

theorem color_eq_fallback (N : V → Finset V) (Δ k Φ : ℕ) (χ : V → Fin Φ)
    (U : Finset V) (fallback : V) (hU : U.Nonempty) :
    color N Δ k Φ χ U = DeterministicPartitionColors.color N Δ k fallback Φ χ U := by
  simp only [color, dif_pos hU]
  exact DeterministicPartitionColors.fallback_eq N Δ k (U.min' hU) fallback Φ χ U hU

theorem palette (N : V → Finset V) (Δ k Φ : ℕ) (χ : V → Fin Φ)
    (U : Finset V) (hU : U.Nonempty) :
    color N Δ k Φ χ U < Φ * 2 ^ ((Δ + 1) ^ k) := by
  simp only [color, dif_pos hU]
  exact DeterministicPartitionColors.palette N Δ k (U.min' hU) Φ χ U

theorem eligible_nonempty (N : V → Finset V) (S U : Finset V) (k t : ℕ)
    (hU : U ∈ FiniteEligibility.family N S k t) : U.Nonempty := by
  by_contra hn
  have hc := ((FiniteEligibility.mem_family N S U k t).mp hU).2.1
  simp only [FiniteConnectivity.connected, dif_neg hn, Bool.false_eq_true] at hc

/-- The actual sweep agrees with the received implementation on every
eligible candidate, independently of its fallback vertex. -/
theorem run_eq_fallback (N : V → Finset V) (S : Finset V) (Δ k t Φ : ℕ)
    (χ : V → Fin Φ) (fallback : V) (q : ℕ) :
    DeterministicPartitionGreedy.run (FiniteEligibility.family N S k t) (color N Δ k Φ χ) q =
      DeterministicPartitionGreedy.run (FiniteEligibility.family N S k t)
        (DeterministicPartitionColors.color N Δ k fallback Φ χ) q :=
  DeterministicPartitionGreedy.congr_colors _ _ _
    (fun U hU => color_eq_fallback N Δ k Φ χ U fallback (eligible_nonempty N S U k t hU)) q

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem proper (Δ k : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (t : ℕ) :
    DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) S k t)
      (color (fun v => G.neighborFinset v) Δ k Φ χ) := by
  intro U hU W hW he hn
  have hu := eligible_nonempty (fun v => G.neighborFinset v) S U k t hU
  have hw := eligible_nonempty (fun v => G.neighborFinset v) S W k t hW
  let v := U.min' hu
  have he' : DeterministicPartitionColors.color (fun v => G.neighborFinset v) Δ k v Φ χ U =
      DeterministicPartitionColors.color (fun v => G.neighborFinset v) Δ k v Φ χ W :=
    (color_eq_fallback _ Δ k Φ χ U v hu).symm.trans
      (he.trans (color_eq_fallback _ Δ k Φ χ W v hw))
  exact DeterministicPartitionColors.proper_eligible G Δ k hdeg v Φ χ hpower S t U hU W hW he' hn

/-- This is Core's actual iteration, with no fallback vertex parameter. -/
def partition (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (T : ℕ) : SmallParts.Data G S k :=
  DeterministicPartitionIterationCore.partition G k hk t ht
    (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k))
    (fun R => proper G Δ k hdeg Φ χ hpower R t) S T

theorem partition_parts (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (T : ℕ) :
    (partition G Δ hdeg k hk t ht Φ χ hpower S T).parts =
      DeterministicPartitionIterationCore.parts (fun v => G.neighborFinset v) k t
        (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k)) S T := rfl

theorem cut_partition (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (T : ℕ) :
    DeterministicPartitionIterationBounds.cut G k t (color (fun v => G.neighborFinset v) Δ k Φ χ)
        (Φ * 2 ^ ((Δ + 1) ^ k)) S T =
      (PartCut.graph G S (partition G Δ hdeg k hk t ht Φ χ hpower S T).parts).edgeFinset.card := by
  exact DeterministicPartitionIterationBounds.cut_partition G k hk t ht
    (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k))
    (fun R => proper G Δ k hdeg Φ χ hpower R t) S T

/-- Empty graphs are covered without manufacturing a vertex or an identifier. -/
theorem partition_empty [IsEmpty V] (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (T : ℕ) :
    (partition G Δ hdeg k hk t ht Φ χ hpower S T).parts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro U hU
  obtain ⟨v, _⟩ := (partition G Δ hdeg k hk t ht Φ χ hpower S T).nonempty U hU
  exact isEmptyElim v

/-- Bridge for the forthcoming sequential program: the received actual
stage already computes the canonical fallback-free candidate colors. -/
theorem stage_output {ids : ℕ} (C : BroadcastModel.BitCode V ids) (Δ k t Φ q : ℕ)
    (hΦ : 0 < Φ) (S : Finset V) (χ : V → Fin Φ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).runEncoded G
        (fun u => (decide (u ∈ S), χ u)) v =
      DeterministicPartitionLocality.part
        (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (color (fun u => G.neighborFinset u) Δ k Φ χ) q v := by
  rw [DeterministicPartitionBroadcast.correct G C Δ k t Φ q hΦ S χ hdeg v]
  unfold DeterministicPartitionLocality.part DeterministicPartitionLocality.atVertex
  rw [← run_eq_fallback (fun u => G.neighborFinset u) S Δ k t Φ χ v q]

end Graph
end Kernel

/-- A single graph-uniform contract. All t,k,T are chosen before V,G and
before the supplied power coloring; both budgets refer to the actual run. -/
theorem parameters (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k T : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C (2 / 3) → (hdeg : ∀ v, G.degree v ≤ Δ) →
        ∀ (Φ : ℕ) (χ : V → Fin Φ)
          (hpower : ∀ u v : V, u ≠ v →
            v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
          (S : Finset V),
          (DeterministicPartitionIterationBounds.totalCharge (fun v => G.neighborFinset v) k t
            (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k)) S T : ℝ) ≤
              (η / 2) * S.card ∧
          (Δ : ℝ) / 2 * (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t
            (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k)) S T).remaining.card ≤
              (η / 2) * S.card ∧
          ((PartCut.graph G S (partition G Δ hdeg k hk t ht Φ χ hpower S T).parts).edgeFinset.card : ℝ) ≤
            η * S.card := by
  obtain ⟨t, k, T, ht, hk, hb, hparam, hT⟩ :=
    DeterministicPartitionIterationBounds.uniform_parameters C Δ η hη
  refine ⟨t, k, T, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg Φ χ hpower S
  have hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t)
      (color (fun v => G.neighborFinset v) Δ k Φ χ) :=
    fun R => proper G Δ k hdeg Φ χ hpower R t
  have hp : ∀ R : Finset V, ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) R k t,
      color (fun v => G.neighborFinset v) Δ k Φ χ U < Φ * 2 ^ ((Δ + 1) ^ k) :=
    fun R U hU => palette _ Δ k Φ χ U (eligible_nonempty _ R U k t hU)
  have hhalf := SeparatorBalance.half_profile G hC hprofile
  have hAll := DeterministicPartitionIterationBounds.cut_after_stages G
    (show 0 ≤ 2 * C by positivity) hhalf Δ hdeg k hk t ht hparam
    (color (fun v => G.neighborFinset v) Δ k Φ χ) (Φ * 2 ^ ((Δ + 1) ^ k)) hc hp T S η hη hb hT
  refine ⟨hAll.1, hAll.2.1, ?_⟩
  have he := cut_partition G Δ hdeg k hk t ht Φ χ hpower S T
  exact (congrArg (fun m : ℕ => (m : ℝ) ≤ η * S.card) he).mp hAll.2.2

end Paper.DeterministicPartitionIterationPower

#print axioms Paper.DeterministicPartitionIterationPower.proper
#print axioms Paper.DeterministicPartitionIterationPower.partition_empty
#print axioms Paper.DeterministicPartitionIterationPower.stage_output
#print axioms Paper.DeterministicPartitionIterationPower.parameters
