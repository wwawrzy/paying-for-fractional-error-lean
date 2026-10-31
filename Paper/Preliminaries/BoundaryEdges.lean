import Paper.Preliminaries.PartCut
import Paper.Preliminaries.PartBoundaries

/-! Actual undirected boundary edges. Splitting off a family of parts
charges new cut edges to their current physical boundaries. -/
namespace Paper.BoundaryEdges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edges (S U : Finset V) : Finset (Sym2 V) :=
  U.biUnion (fun u => (G.neighborFinset u ∩ (S \ U)).image (fun v => s(u, v)))

theorem card_bound (S U : Finset V) : (edges G S U).card ≤ PartBoundaries.boundary G S U := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro u _
  exact Finset.card_image_le

theorem mem (S U : Finset V) {u v : V} (ha : G.Adj u v) (hu : u ∈ U) (hv : v ∈ S \ U) :
    s(u, v) ∈ edges G S U :=
  Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr
    ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr ha, hv⟩, rfl⟩⟩

theorem cut_subset (S : Finset V) (A P : Finset (Finset V)) :
    (PartCut.graph G S (A ∪ P)).edgeFinset ⊆
      A.biUnion (edges G S) ∪ (PartCut.graph G (S \ A.biUnion id) P).edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : (PartCut.graph G S (A ∪ P)).Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    by_cases hu : u ∈ A.biUnion id
    · obtain ⟨U, hU, huU⟩ := Finset.mem_biUnion.mp hu
      have hvU : v ∉ U := fun hvU => ha.2.2.2 ⟨U, Finset.mem_union_left _ hU, huU, hvU⟩
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨U, hU, mem G S U ha.1 huU (Finset.mem_sdiff.mpr ⟨ha.2.2.1, hvU⟩)⟩)
    by_cases hv : v ∈ A.biUnion id
    · obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
      have huU : u ∉ U := fun huU => ha.2.2.2 ⟨U, Finset.mem_union_left _ hU, huU, hvU⟩
      have hm := mem G S U ha.1.symm hvU (Finset.mem_sdiff.mpr ⟨ha.2.1, huU⟩)
      have hm' : s(u, v) ∈ edges G S U := by simpa only [Sym2.eq_swap] using hm
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨U, hU, hm'⟩)
    · apply Finset.mem_union_right
      apply SimpleGraph.mem_edgeFinset.mpr
      exact ⟨ha.1, Finset.mem_sdiff.mpr ⟨ha.2.1, hu⟩, Finset.mem_sdiff.mpr ⟨ha.2.2.1, hv⟩,
        fun ⟨U, hU, huU, hvU⟩ => ha.2.2.2 ⟨U, Finset.mem_union_right _ hU, huU, hvU⟩⟩

theorem cut_count (S : Finset V) (A P : Finset (Finset V)) :
    (PartCut.graph G S (A ∪ P)).edgeFinset.card ≤
      (∑ U ∈ A, PartBoundaries.boundary G S U) +
      (PartCut.graph G (S \ A.biUnion id) P).edgeFinset.card := by
  calc
    _ ≤ (A.biUnion (edges G S) ∪ (PartCut.graph G (S \ A.biUnion id) P).edgeFinset).card :=
      Finset.card_le_card (cut_subset G S A P)
    _ ≤ (A.biUnion (edges G S)).card + (PartCut.graph G (S \ A.biUnion id) P).edgeFinset.card :=
      Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun U _ => card_bound G S U))) _
end Paper.BoundaryEdges
