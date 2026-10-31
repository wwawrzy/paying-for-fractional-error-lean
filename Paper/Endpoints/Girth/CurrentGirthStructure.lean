import Paper.Endpoints.Girth.CurrentGirthMinor

/-! # Contracted-neighbor structure and exact marked degree accounting -/

namespace Paper.CurrentGirthStructure

open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An independent marked set counts each incident edge exactly once. -/
theorem incident_card_eq_degree_sum (A : Finset V)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) :
    (CurrentFaceBound.incidentMarkedEdges (G := G) A).card =
      ∑ a ∈ A, G.degree a := by
  have hdis : (↑A : Set V).PairwiseDisjoint
      (GirthFaceOccurrenceBudget.incidentEdges (G := G)) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro e hea heb
    have hae := (GirthFaceOccurrenceBudget.mem_incidentEdges_iff a e).mp hea
    have hbe := (GirthFaceOccurrenceBudget.mem_incidentEdges_iff b e).mp heb
    apply hA a ha b hb
    exact (G.adj_iff_exists_edge).mpr
      ⟨hab, e.val, G.mem_edgeFinset.mp e.property, hae, hbe⟩
  unfold CurrentFaceBound.incidentMarkedEdges
    GirthFaceOccurrenceBudget.markedEdges
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro a ha
  exact GirthFaceOccurrenceBudget.incidentEdges_card_eq_degree a

variable (R W : Finset V)
local notation "K" => ComponentMinor.graph G R W
local notation "A" => ComponentMinor.contracted G R W

/-- Every neighbor of a contracted vertex is an original residual vertex.
An edge to another vertex outside R would join the same contracted component. -/
theorem contracted_neighbor_residual
    (r s : ComponentMinor.retained G R W) (hr : r ∈ A)
    (hrs : (K).Adj r s) : s.val ∈ R := by
  obtain ⟨hne, u, v, hu, hv, huv⟩ := hrs
  have hmr := (Finset.mem_filter.mp hr).2
  have hfix := ComponentMinor.retained_fixed G R W r.property
  have huC : u ∈ ComponentMinor.cluster G R r.val := by
    change u ∈ (ComponentMinor.cluster G R r.val : Set V)
    rw [← ComponentMinor.fiber_marked G R W r.val hfix hmr]
    exact hu
  have huR : u ∉ R :=
    (Finset.mem_sdiff.mp (ComponentMinor.cluster_subset G R r.val huC)).2
  by_contra hsR
  have hvR : v ∉ R := by
    intro hvR
    have he : v = s.val := (ComponentMinor.label_residual G R W hvR).symm.trans hv
    exact hsR (he ▸ hvR)
  have he : ComponentMinor.cluster G R u = ComponentMinor.cluster G R v :=
    ComponentMap.eq_of_adj G (Finset.univ \ R) u v
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huR⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvR⟩) huv
  have hmU : (ComponentMinor.marked G R W u).Nonempty := by
    unfold ComponentMinor.marked
    rw [ComponentMinor.cluster_eq_of_mem G R huC]
    exact hmr
  have hl := ComponentMinor.label_eq_of_cluster_eq G R W he.symm hmU
  exact hne (Subtype.ext (hu.symm.trans (hl.symm.trans hv)))

/-- Distinct contracted components are not adjacent in the actual minor. -/
theorem contracted_independent :
    ∀ r ∈ A, ∀ s ∈ A, ¬ (K).Adj r s := by
  intro r hr s hs hrs
  exact ComponentMinor.contracted_outside G R W hs
    (contracted_neighbor_residual G R W r s hr hrs)

/-- The p in the face estimate is the degree sum at exactly the actual
contracted vertices, with no double counting. -/
theorem contracted_incident_card_eq_degree_sum :
    (CurrentFaceBound.incidentMarkedEdges (G := K) A).card =
      ∑ r ∈ A, (K).degree r :=
  incident_card_eq_degree_sum K A (contracted_independent G R W)

end Paper.CurrentGirthStructure

#print axioms Paper.CurrentGirthStructure.incident_card_eq_degree_sum
#print axioms Paper.CurrentGirthStructure.contracted_neighbor_residual
#print axioms Paper.CurrentGirthStructure.contracted_independent
#print axioms Paper.CurrentGirthStructure.contracted_incident_card_eq_degree_sum
