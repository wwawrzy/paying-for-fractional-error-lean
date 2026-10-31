import Paper.Partitions.Local.DeterministicPartitionIterationCore
import Paper.Partitions.Local.PartitionParameters
import Paper.Preliminaries.BoundaryEdges

/-! Actual residual contraction and boundary accounting for the executable
iteration. The final cut is PartCut.graph of exactly Core.parts, with an
explicit bridge to the certified Core.partition. Numeric parameters are
chosen before any vertex type, graph, or supplied coloring is introduced. -/
namespace Paper.DeterministicPartitionIterationBounds
open scoped BigOperators

/-- Cast and divide a natural contraction using only three natural numbers.
No graph, finite-set enumeration or instance normalization enters this proof. -/
theorem nat_contraction_to_real (D a s : ℕ) (hD : 0 < D)
    (h : D * a ≤ (D - 1) * s) :
    (a : ℝ) ≤ (1 - 1 / (D : ℝ)) * s := by
  have hOne : 1 ≤ D := hD
  have hR : (D : ℝ) * a ≤ ((D : ℝ) - 1) * s := by exact_mod_cast h
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have he : (1 - 1 / (D : ℝ)) * (D : ℝ) = (D : ℝ) - 1 := by field_simp
  have he' := congrArg (fun x : ℝ => x * s) he
  apply (mul_le_mul_iff_right₀ hDR).mp
  nlinarith only [hR, he']

/-- Combine one physical cut split with the induction hypothesis over naturals. -/
theorem cut_step_arithmetic {c a b e r Δ : ℕ}
    (hsplit : c ≤ a + b) (hrest : 2 * b ≤ 2 * e + Δ * r) :
    2 * c ≤ 2 * (a + e) + Δ * r := by omega

/-- D = 2kM for the received touching-family bound M. -/
def denominator (Δ k : ℕ) : ℕ := 2 * k * (k * 2 ^ ((Δ + 1) ^ k))

noncomputable def rate (Δ k : ℕ) : ℝ := 1 - 1 / (denominator Δ k : ℝ)

theorem denominator_pos (Δ k : ℕ) (hk : 0 < k) : 0 < denominator Δ k := by
  unfold denominator
  positivity

theorem rate_bounds (Δ k : ℕ) (hk : 0 < k) : 0 ≤ rate Δ k ∧ rate Δ k < 1 := by
  have hD : (0 : ℝ) < denominator Δ k := by exact_mod_cast denominator_pos Δ k hk
  have hOne : (1 : ℝ) ≤ denominator Δ k := by exact_mod_cast denominator_pos Δ k hk
  unfold rate
  constructor
  · have hh := (div_le_one hD).mpr hOne
    linarith
  · have hh : (0 : ℝ) < 1 / (denominator Δ k : ℝ) := by positivity
    linarith

theorem exists_stages (Δ k : ℕ) (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, rate Δ k ^ T ≤ δ := by
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hδ (rate_bounds Δ k hk).2
  exact ⟨T, hT.le⟩

/-- All three numeric choices precede the graph. The half-balanced profile
will use constant 2*C. The two cut contributions have separate budgets. -/
theorem uniform_parameters (C : ℝ) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k T : ℕ, 0 < t ∧ 0 < k ∧
      4 * (1 / (t : ℝ)) ≤ η / 2 ∧
      4 * (Δ : ℝ) * (2 * C) / Real.sqrt k ≤ 1 / (t : ℝ) ∧
      rate Δ k ^ T ≤ η / ((Δ : ℝ) + 1) := by
  let t := Nat.ceil (8 / η) + 1
  have ht : 0 < t := by dsimp only [t]; omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hlarge : 8 / η ≤ (t : ℝ) :=
    (Nat.le_ceil (8 / η)).trans (by dsimp only [t]; push_cast; linarith)
  have hEight : 8 / (t : ℝ) ≤ η := by
    have hh := (div_le_iff₀ hη).mp hlarge
    exact (div_le_iff₀ htR).mpr (by nlinarith)
  have hbudget : 4 * (1 / (t : ℝ)) ≤ η / 2 := by
    have he : 4 * (1 / (t : ℝ)) = (8 / (t : ℝ)) / 2 := by ring
    rw [he]
    linarith
  have hε : (0 : ℝ) < 1 / (t : ℝ) := by positivity
  obtain ⟨k, hk, hparam⟩ := PartitionParameters.exists_size (2 * C) Δ hε
  have hδ : (0 : ℝ) < η / ((Δ : ℝ) + 1) := by positivity
  obtain ⟨T, hT⟩ := exists_stages Δ k hk hδ
  exact ⟨t, k, T, ht, hk, hbudget, hparam, hT⟩

variable {V : Type} [LinearOrder V]

/-- Current physical boundary charges, computed using integer neighbor lists. -/
def stageCharge (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) : ℕ :=
  ∑ U ∈ DeterministicPartitionProgress.accepted N S k t color q,
    FiniteEligibility.boundary N S U

def totalCharge (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) :
    Finset V → ℕ → ℕ
  | _, 0 => 0
  | S, n + 1 => stageCharge N k t color q S +
    totalCharge N k t color q (DeterministicPartitionProgress.next N S k t color q) n

/-- A generic induction on the actual executable residual, not a new process. -/
theorem geometric (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ S : Finset V,
      ((DeterministicPartitionProgress.next N S k t color q).card : ℝ) ≤ ρ * S.card)
    (n : ℕ) (S : Finset V) :
    ((DeterministicPartitionIterationCore.run N k t color q S n).remaining.card : ℝ) ≤
      ρ ^ n * S.card := by
  induction n generalizing S with
  | zero => simp only [DeterministicPartitionIterationCore.remaining_zero, pow_zero, one_mul, le_rfl]
  | succ n ih =>
    rw [DeterministicPartitionIterationCore.remaining_succ]
    calc
      _ ≤ ρ ^ n * (DeterministicPartitionProgress.next N S k t color q).card := ih _
      _ ≤ ρ ^ n * (ρ * S.card) := mul_le_mul_of_nonneg_left (hstep S) (pow_nonneg hρ n)
      _ = _ := by rw [pow_succ]; ring

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only the crossing graph uses a classical adjacency test. In particular,
this instance does not replace the supplied decidability of G.Adj or the
order-derived equality used by the executable stage and Core.parts. -/
private noncomputable local instance partCutDecidable (S : Finset V)
    (P : Finset (Finset V)) : DecidableRel (PartCut.graph G S P).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Bundle the dependent edge-set Fintype behind a plain function of P. -/
private noncomputable def edgeCount (S : Finset V) (P : Finset (Finset V)) : ℕ :=
  (PartCut.graph G S P).edgeFinset.card

/-- Cut edges of the actual finite output, including terminal singleton parts. -/
noncomputable def cut (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) (S : Finset V) (n : ℕ) : ℕ :=
  edgeCount G S (DeterministicPartitionIterationCore.parts
    (fun v => G.neighborFinset v) k t color q S n)

theorem cut_partition (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (S : Finset V) (n : ℕ) :
    cut G k t color q S n =
      (PartCut.graph G S (DeterministicPartitionIterationCore.partition G k hk t ht color q hc S n).parts).edgeFinset.card := rfl

theorem step_rate {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (hp : ∀ R : Finset V, ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) R k t,
      color U < q) (S : Finset V) :
    ((DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q).card : ℝ) ≤
      rate Δ k * S.card := by
  exact nat_contraction_to_real (denominator Δ k)
    (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q).card
    S.card (denominator_pos Δ k hk)
    (DeterministicPartitionProgress.remaining_bound G hC hprofile Δ hdeg k hk t ht hparam
      S color q (hc S) (hp S))

theorem remaining_geometric {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (hp : ∀ R : Finset V, ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) R k t,
      color U < q) (n : ℕ) (S : Finset V) :
    ((DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card : ℝ) ≤
      rate Δ k ^ n * S.card :=
  geometric _ k t color q (rate Δ k) (rate_bounds Δ k hk).1
    (step_rate G hC hprofile Δ hdeg k hk t ht hparam color q hc hp) n S

theorem stageCharge_bound (k t : ℕ) (ht : 0 < t) (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color) (S : Finset V) :
    (stageCharge (fun v => G.neighborFinset v) k t color q S : ℝ) ≤
      4 * (1 / (t : ℝ)) * (DeterministicPartitionProgress.removed (fun v => G.neighborFinset v) S k t color q).card := by
  simpa only [stageCharge, Nat.cast_sum, FiniteEligibility.boundary_eq] using
    DeterministicPartitionProgress.boundary_budget G S k t ht color q (hc S)

theorem telescoping (k t : ℕ) (ht : 0 < t) (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (n : ℕ) (S : Finset V) :
    (totalCharge (fun v => G.neighborFinset v) k t color q S n : ℝ) ≤
      4 * (1 / (t : ℝ)) * ((S.card : ℝ) -
        (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card) := by
  induction n generalizing S with
  | zero => simp only [totalCharge, Nat.cast_zero,
      DeterministicPartitionIterationCore.remaining_zero, sub_self, mul_zero, le_rfl]
  | succ n ih =>
    have hb := stageCharge_bound G k t ht color q hc S
    have hs := DeterministicPartitionProgress.card_split (fun v => G.neighborFinset v) S k t color q
    have hsR : ((DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q).card : ℝ) +
        (DeterministicPartitionProgress.removed (fun v => G.neighborFinset v) S k t color q).card = S.card := by
      exact_mod_cast hs
    have hi := ih (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q)
    have hsScaled := congrArg (fun x : ℝ => 4 * (1 / (t : ℝ)) * x) hsR
    simp only [totalCharge, Nat.cast_add, DeterministicPartitionIterationCore.remaining_succ]
    nlinarith only [hb, hsScaled, hi]

theorem totalCharge_bound (k t : ℕ) (ht : 0 < t) (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (n : ℕ) (S : Finset V) :
    (totalCharge (fun v => G.neighborFinset v) k t color q S n : ℝ) ≤
      4 * (1 / (t : ℝ)) * S.card := by
  apply (telescoping G k t ht color q hc n S).trans
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (by positivity)

private theorem edgeCount_singletons (S : Finset V) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    2 * edgeCount G S (S.image (fun v => {v})) ≤ Δ * S.card := by
  exact PartCut.singleton_bound G S Δ hdeg

private theorem edgeCount_split (S : Finset V) (A P : Finset (Finset V)) :
    edgeCount G S (A ∪ P) ≤
      (∑ U ∈ A, PartBoundaries.boundary G S U) + edgeCount G (S \ A.biUnion id) P := by
  exact BoundaryEdges.cut_count G S A P

private theorem stageCharge_eq (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) (S : Finset V) :
    stageCharge (fun v => G.neighborFinset v) k t color q S =
      ∑ U ∈ DeterministicPartitionProgress.accepted (fun v => G.neighborFinset v) S k t color q,
        PartBoundaries.boundary G S U := by
  unfold stageCharge
  apply Finset.sum_congr rfl
  intro U _
  exact FiniteEligibility.boundary_eq G S U

private theorem cut_zero (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) (S : Finset V) :
    cut G k t color q S 0 = edgeCount G S (S.image (fun v => {v})) := by
  unfold cut
  rw [DeterministicPartitionIterationCore.parts_zero]

private theorem cut_split (k t : ℕ) (color : Finset V → ℕ) (q : ℕ) (S : Finset V) (n : ℕ) :
    cut G k t color q S (n + 1) ≤ stageCharge (fun v => G.neighborFinset v) k t color q S +
      cut G k t color q (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q) n := by
  unfold cut
  rw [DeterministicPartitionIterationCore.parts_succ, stageCharge_eq]
  exact edgeCount_split G S
    (DeterministicPartitionProgress.accepted (fun v => G.neighborFinset v) S k t color q)
    (DeterministicPartitionIterationCore.parts (fun v => G.neighborFinset v) k t color q
      (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q) n)

/-- Natural-number accounting for actual crossing edges. The recursive
expressions use one explicit neighbor function throughout, without aliases. -/
theorem cut_decomposition (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k t : ℕ) (color : Finset V → ℕ) (q n : ℕ) (S : Finset V) :
    2 * cut G k t color q S n ≤
      2 * totalCharge (fun v => G.neighborFinset v) k t color q S n +
        Δ * (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card := by
  induction n generalizing S with
  | zero =>
    rw [cut_zero, totalCharge, DeterministicPartitionIterationCore.remaining_zero]
    simpa only [Nat.mul_zero, Nat.zero_add] using edgeCount_singletons G S Δ hdeg
  | succ n ih =>
    have hb := cut_split G k t color q S n
    have hi := ih (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t color q)
    simp only [totalCharge, DeterministicPartitionIterationCore.remaining_succ]
    exact cut_step_arithmetic hb hi

theorem cut_bound (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k t : ℕ) (color : Finset V → ℕ) (q n : ℕ) (S : Finset V) :
    (cut G k t color q S n : ℝ) ≤
      totalCharge (fun v => G.neighborFinset v) k t color q S n + (Δ : ℝ) / 2 *
        (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card := by
  have hn := cut_decomposition G Δ hdeg k t color q n S
  have hr : 2 * (cut G k t color q S n : ℝ) ≤
      2 * (totalCharge (fun v => G.neighborFinset v) k t color q S n : ℝ) + (Δ : ℝ) *
        (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card := by
    exact_mod_cast hn
  nlinarith only [hr]

/-- Both contributions are budgeted. The residual premise alone is not the
statement of this theorem; the boundary budget is an independent premise. -/
theorem cut_from_budgets (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k t : ℕ) (ht : 0 < t) (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (n : ℕ) (S : Finset V) (η : ℝ) (hη : 0 < η)
    (hb : 4 * (1 / (t : ℝ)) ≤ η / 2)
    (hr : ((DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card : ℝ) ≤
      (η / ((Δ : ℝ) + 1)) * S.card) :
    (totalCharge (fun v => G.neighborFinset v) k t color q S n : ℝ) ≤ (η / 2) * S.card ∧
      (Δ : ℝ) / 2 * (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card ≤
        (η / 2) * S.card ∧
      (cut G k t color q S n : ℝ) ≤ η * S.card := by
  have hb' := (totalCharge_bound G k t ht color q hc n S).trans
    (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg S.card))
  have hδ : (0 : ℝ) ≤ η / ((Δ : ℝ) + 1) := by positivity
  have he : ((Δ : ℝ) + 1) * (η / ((Δ : ℝ) + 1)) = η := by field_simp
  have hcoef : (Δ : ℝ) / 2 * (η / ((Δ : ℝ) + 1)) ≤ η / 2 := by nlinarith only [he, hδ]
  have hr' : (Δ : ℝ) / 2 *
      (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card ≤
        (η / 2) * S.card := by
    calc
      _ ≤ (Δ : ℝ) / 2 * ((η / ((Δ : ℝ) + 1)) * S.card) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = ((Δ : ℝ) / 2 * (η / ((Δ : ℝ) + 1))) * S.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg S.card)
  refine ⟨hb', hr', ?_⟩
  have hh := cut_bound G Δ hdeg k t color q n S
  nlinarith only [hh, hb', hr']

/-- Apply geometric contraction to the actual residual and discharge both
budgets for the actual iteration output. Input colors remain supplied. -/
theorem cut_after_stages {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (color : Finset V → ℕ) (q : ℕ)
    (hc : ∀ R : Finset V, DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) R k t) color)
    (hp : ∀ R : Finset V, ∀ U ∈ FiniteEligibility.family (fun v => G.neighborFinset v) R k t,
      color U < q) (n : ℕ) (S : Finset V) (η : ℝ) (hη : 0 < η)
    (hb : 4 * (1 / (t : ℝ)) ≤ η / 2)
    (hn : rate Δ k ^ n ≤ η / ((Δ : ℝ) + 1)) :
    (totalCharge (fun v => G.neighborFinset v) k t color q S n : ℝ) ≤ (η / 2) * S.card ∧
      (Δ : ℝ) / 2 * (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t color q S n).remaining.card ≤
        (η / 2) * S.card ∧
      (cut G k t color q S n : ℝ) ≤ η * S.card := by
  apply cut_from_budgets G Δ hdeg k t ht color q hc n S η hη hb
  exact (remaining_geometric G hC hprofile Δ hdeg k hk t ht hparam color q hc hp n S).trans
    (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg S.card))

end Paper.DeterministicPartitionIterationBounds

#print axioms Paper.DeterministicPartitionIterationBounds.uniform_parameters
#print axioms Paper.DeterministicPartitionIterationBounds.remaining_geometric
#print axioms Paper.DeterministicPartitionIterationBounds.telescoping
#print axioms Paper.DeterministicPartitionIterationBounds.cut_partition
#print axioms Paper.DeterministicPartitionIterationBounds.cut_after_stages
