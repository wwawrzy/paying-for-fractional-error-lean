import Paper.Preliminaries.Incidence

namespace Paper.DisjointIncidence
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem union_left (A B C : Finset V) (h : Disjoint A B) :
    (G.interedges (A∪B) C).card = (G.interedges A C).card+(G.interedges B C).card := by
  have heq : G.interedges (A∪B) C = G.interedges A C ∪ G.interedges B C := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff,Finset.mem_union]
    tauto
  have hd : Disjoint (G.interedges A C) (G.interedges B C) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [SimpleGraph.mem_interedges_iff] at hp hq
    exact Finset.disjoint_left.mp h hp.1 hq.1
  rw [heq,Finset.card_union_of_disjoint hd]

theorem union_right (A B C : Finset V) (h : Disjoint B C) :
    (G.interedges A (B∪C)).card = (G.interedges A B).card+(G.interedges A C).card := by
  rw [Incidence.card_interedges_comm G A (B∪C),union_left G B C A h,
    Incidence.card_interedges_comm G B A,Incidence.card_interedges_comm G C A]

theorem four_blocks (Q A L W : Finset V)
    (hQA : Disjoint Q A) (hQL : Disjoint Q L) (hQW : Disjoint Q W)
    (hAL : Disjoint A L) (hAW : Disjoint A W) (hLW : Disjoint L W) :
    (G.interedges (Q∪A) (Q∪L)).card + (G.interedges A (Q∪L)).card +
      (G.interedges Q L).card + 2*(G.interedges A W).card ≤
      2*G.inducedEdgeCount ((Q∪A)∪(L∪W)) := by
  have hbig : Disjoint (Q∪A) (L∪W) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hQL,hQW⟩,
      Finset.disjoint_union_right.mpr ⟨hAL,hAW⟩⟩
  rw [← Incidence.card_interedges_self]
  rw [union_left G _ _ _ hbig]
  simp only [union_right G _ _ _ hbig,union_left G _ _ _ hQA,
    union_left G _ _ _ hLW,union_right G _ _ _ hQA,
    union_right G _ _ _ hLW,union_right G _ _ _ hQL]
  rw [Incidence.card_interedges_comm G A Q,
    Incidence.card_interedges_comm G L Q,Incidence.card_interedges_comm G W Q,
    Incidence.card_interedges_comm G L A,Incidence.card_interedges_comm G W A,
    Incidence.card_interedges_comm G W L]
  omega

end Paper.DisjointIncidence
