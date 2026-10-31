import GraphTheory.SimpleGraph.Minor.AverageDegree

/-! Public proof bridges to the existing proved contraction core. The original
source keeps these general helpers private; its proof terms are reused here
without changing that source or postulating a sharp density theorem. -/
namespace Paper.CliqueDenseCore

open SimpleGraph

/- Private names have a numerical component. Construct their identifiers
with Lean's standard name function; the resulting terms are ordinary
references to the existing kernel-checked declarations. -/
macro "existingDenseCoreProof%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.exists_exact_dense_minor_with_cn_bound))

macro "existingNeighborhoodExtensionProof%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.extend_minor_from_neighborhood))

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem extract (k : ℕ) (hk : 0 < k) (hV : 0 < Fintype.card V)
    (hdense : k * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      0 < Fintype.card W ∧ k * Fintype.card W = H.edgeFinset.card ∧
      (∀ v, 0 < H.degree v) ∧
      (∀ v w, H.Adj v w → k ≤ Fintype.card (H.commonNeighbors v w)) ∧ H.IsMinor G := by
  exact existingDenseCoreProof%
    (Fintype.card V + G.edgeFinset.card) k hk V G rfl hV hdense

theorem neighborhood_excludes_four (hG : G.IsKMinorFree 5) (v : V) :
    (G.induce (G.neighborSet v)).IsKMinorFree 4 := by
  intro hm
  have hnot : ¬ (G.induce (G.neighborSet v)).IsKMinorFree (5 - 1) := fun hh => hh hm
  exact existingNeighborhoodExtensionProof%
    G v 5 (by decide) hnot hG

end Paper.CliqueDenseCore

#print axioms Paper.CliqueDenseCore.extract
#print axioms Paper.CliqueDenseCore.neighborhood_excludes_four
