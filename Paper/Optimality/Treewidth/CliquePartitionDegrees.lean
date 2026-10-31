import GraphTheory.SimpleGraph.InducedCounting

/-! Actual degree accounting across a vertex partition. These identities
support the bounded neighborhood-minor analysis on the original graph. -/
namespace Paper.CliquePartitionDegrees

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem partition (S : Finset V) (v : V) :
    G.degree v = G.inducedDegree v S + G.inducedDegree v Sᶜ := by
  classical
  have hleft : (G.neighborFinset v).filter (fun x => x ∈ S) = S.filter (G.Adj v) := by
    ext x
    simp only [Finset.mem_filter, G.mem_neighborFinset, and_comm]
  have hright : (G.neighborFinset v).filter (fun x => ¬x ∈ S) = Sᶜ.filter (G.Adj v) := by
    ext x
    simp only [Finset.mem_filter, G.mem_neighborFinset, Finset.mem_compl, and_comm]
  have hh := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (fun x => x ∈ S)
  rw [hleft, hright, G.card_neighborFinset_eq_degree] at hh
  exact hh.symm

theorem cross_sum (S T : Finset V) :
    ∑ v ∈ S, G.inducedDegree v T = ∑ w ∈ T, G.inducedDegree w S := by
  classical
  have hboole (v : V) (A : Finset V) :
      G.inducedDegree v A = ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
    exact (Finset.sum_boole (G.Adj v) A).symm
  simp_rw [hboole]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  by_cases hvw : G.Adj v w
  · rw [if_pos hvw, if_pos hvw.symm]
  · rw [if_neg hvw, if_neg (fun hh => hvw hh.symm)]

end Paper.CliquePartitionDegrees

#print axioms Paper.CliquePartitionDegrees.partition
#print axioms Paper.CliquePartitionDegrees.cross_sum
