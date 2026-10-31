import Paper.Partitions.Local.SmallCutPartition

/-! Boundaries of actual parts count each crossing edge exactly twice. -/
namespace Paper.PartBoundaries
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundary (S U : Finset V) : ℕ := ∑ u ∈ U, (G.neighborFinset u ∩ (S \ U)).card

theorem degree_eq (S : Finset V) (p : V → Finset V)
    (hself : ∀ u ∈ S, u ∈ p u)
    (hconsistent : ∀ u v, u ∈ p v → p u = p v) (u : V) (hu : u ∈ S) :
    (CrossingEdges.graph G S p).degree u = (G.neighborFinset u ∩ (S \ p u)).card := by
  change ((CrossingEdges.graph G S p).neighborFinset u).card = _
  congr 1
  ext v
  simp only [SimpleGraph.mem_neighborFinset, CrossingEdges.graph, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨ha, _, hv, hn⟩
    exact ⟨ha, hv, fun hmem => hn (hconsistent v u hmem).symm⟩
  · rintro ⟨ha, hv, hn⟩
    exact ⟨ha, hu, hv, fun he => hn (he.symm ▸ hself v hv)⟩

theorem degree_zero (S : Finset V) (p : V → Finset V) (u : V) (hu : u ∉ S) :
    (CrossingEdges.graph G S p).degree u = 0 := by
  change ((CrossingEdges.graph G S p).neighborFinset u).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hu (((CrossingEdges.graph G S p).mem_neighborFinset u v).mp hv).2.1

theorem total (S : Finset V) (k : ℕ) (P : SmallParts.Data G S k)
    (p : V → Finset V) (he : P.parts = S.image p)
    (hself : ∀ u ∈ S, u ∈ p u)
    (hconsistent : ∀ u v, u ∈ p v → p u = p v) :
    ∑ U ∈ P.parts, boundary G S U = 2 * (CrossingEdges.graph G S p).edgeFinset.card := by
  have hcover : P.parts.biUnion id = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
      exact P.subset U hU hv
    · intro hv
      obtain ⟨U, hU, hv⟩ := P.covers v hv
      exact Finset.mem_biUnion.mpr ⟨U, hU, hv⟩
  have hinner : ∀ U ∈ P.parts, boundary G S U = ∑ u ∈ U, (CrossingEdges.graph G S p).degree u := by
    intro U hU
    apply Finset.sum_congr rfl
    intro u hu
    have huS := P.subset U hU hu
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (he ▸ hU)
    have hp : p u = U := (hconsistent u v (hv.symm ▸ hu)).trans hv
    rw [degree_eq G S p hself hconsistent u huS, hp]
  calc
    _ = ∑ U ∈ P.parts, ∑ u ∈ U, (CrossingEdges.graph G S p).degree u := Finset.sum_congr rfl hinner
    _ = ∑ u ∈ P.parts.biUnion id, (CrossingEdges.graph G S p).degree u := (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ u ∈ S, (CrossingEdges.graph G S p).degree u := by rw [hcover]
    _ = ∑ u, (CrossingEdges.graph G S p).degree u :=
      Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => degree_zero G S p u hu)
    _ = _ := SimpleGraph.sum_degrees_eq_twice_card_edges (CrossingEdges.graph G S p)
end Paper.PartBoundaries
