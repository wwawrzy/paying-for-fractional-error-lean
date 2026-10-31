import Paper.Optimality.Treewidth.CliqueDenseCore

/-! Minimal minors for affine edge thresholds. This reuses the existing
finite threshold selection proof, keeping the additive term needed in the
small excluded-clique arguments. All resulting graphs are actual minors. -/
namespace Paper.CliqueAffineCore

open SimpleGraph

macro "existingThresholdCoreProof%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.exists_threshold_minimal_minor))

macro "existingContractEdgeCountProof%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.card_edgeFinset_contractAdj))

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem extract (k b B : ℕ) (hB : 0 < B) (hb : b ≤ k * B)
    (hboundary : B.choose 2 < k * B - b)
    (hV : B ≤ Fintype.card V) (hdense : k * Fintype.card V - b ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      B < Fintype.card W ∧ H.edgeFinset.card = k * Fintype.card W - b ∧
      (∀ v, 0 < H.degree v) ∧
      (∀ v w, H.Adj v w → k ≤ Fintype.card (H.commonNeighbors v w)) ∧ H.IsMinor G := by
  classical
  have hmono : ∀ n, B < n → k * (n - 1) - b ≤ k * n - b := by
    intro n _
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left k (Nat.sub_le n 1)) b
  obtain ⟨W, _, _, H, _, hW, he, hp, hc, hm⟩ :=
    existingThresholdCoreProof% (Fintype.card V + G.edgeFinset.card)
      B (fun n => k * n - b) hB hmono hboundary V G rfl hV hdense
  refine ⟨W, inferInstance, inferInstance, H, inferInstance, hW, he, hp, ?_, hm⟩
  intro v w hadj
  have hcon := hc v w hadj
  have hcount := existingContractEdgeCountProof% H v w hadj hadj.ne
  have hpred : k * (Fintype.card W - 1) + k = k * Fintype.card W := by
    calc
      _ = k * (Fintype.card W - 1 + 1) := by simp only [Nat.mul_add, Nat.mul_one]
      _ = _ := by congr 1; omega
  have hfloor : b ≤ k * (Fintype.card W - 1) :=
    hb.trans (Nat.mul_le_mul_left k (by omega))
  omega

end Paper.CliqueAffineCore

#print axioms Paper.CliqueAffineCore.extract
