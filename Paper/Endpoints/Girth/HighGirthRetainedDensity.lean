import Paper.Endpoints.Girth.HighGirthRetainedEdgeCount
import Paper.Endpoints.Girth.MarkedRestriction
set_option maxHeartbeats 400000
namespace Paper.HighGirthRetainedDensity
theorem retained_density_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (a : Real) (hden : Paper.Incidence.InducedDensityBound G a) :
    ((Paper.HighGirthRetainedSet.vertices G x).card : Real) -
      (Paper.HighGirthComponentCounting.pathComponents G x).card +
      Paper.HighGirthAttachments.count G x + (Paper.HighGirthAttachments.connectors G x).card ≤
      a * ((Paper.HighGirthRetainedSet.vertices G x).card +
        (Paper.HighGirthAttachments.connectors G x).card + (Paper.HighGirthRounding.first G x).card) := by
  classical
  let U := Paper.HighGirthRetainedSet.vertices G x
  let T := Paper.HighGirthAttachments.connectors G x
  let W := Paper.HighGirthRounding.first G x
  have hp := Paper.HighGirthRetainedPartition.retained_set_partition G x
  have hUT : Disjoint U T :=
    (Paper.HighGirthAttachmentCounts.attachment_count_bounds G x).1.mono_left hp.1
  have hTW : Disjoint T W := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvW
    exact (Finset.mem_filter.mp hvT).2.1 hvW
  have hUW : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvW
    have hvLast := hp.1 hvU
    have hvR := (Finset.mem_sdiff.mp hvLast).1
    exact (Finset.mem_sdiff.mp hvR).2 (Paper.SevenFoundation.subset_covered G W hvW)
  have hUtw : Disjoint U (T ∪ W) := Finset.disjoint_union_right.mpr ⟨hUT,hUW⟩
  have hq : G.interedges U T = Paper.HighGirthAttachments.pairs G x := by
    ext p
    constructor
    · intro h
      obtain ⟨hu,ht,hadj⟩ := (SimpleGraph.mem_interedges_iff G).mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1 hu,ht⟩,hadj⟩
    · intro h
      obtain ⟨hprod,hadj⟩ := Finset.mem_filter.mp h
      obtain ⟨hu,ht⟩ := Finset.mem_product.mp hprod
      have huA : p.1 ∈ Paper.HighGirthAttachments.vertices G x := Finset.mem_filter.mpr ⟨hu,⟨p.2,ht,hadj⟩⟩
      exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hp.2.1 huA,ht,hadj⟩
  have hTWimage : (G.interedges T W).image Prod.fst = T := by
    ext t
    constructor
    · intro h
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact ((SimpleGraph.mem_interedges_iff G).mp hp).1
    · intro ht
      obtain ⟨w,hw,hadj⟩ := (Finset.mem_filter.mp ht).2.2.1
      exact Finset.mem_image.mpr ⟨(t,w),(SimpleGraph.mem_interedges_iff G).mpr ⟨ht,hw,hadj⟩,rfl⟩
  have hTcard : T.card ≤ (G.interedges T W).card := by
    calc
      T.card = ((G.interedges T W).image Prod.fst).card := congrArg Finset.card hTWimage.symm
      _ ≤ (G.interedges T W).card := Finset.card_image_le
  have hqcard : Paper.HighGirthAttachments.count G x ≤ (G.interedges U (T ∪ W)).card := by
    change (Paper.HighGirthAttachments.pairs G x).card ≤ _
    rw [←hq]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hu,ht,hadj⟩ := (SimpleGraph.mem_interedges_iff G).mp hp
    exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hu,Finset.mem_union_left _ ht,hadj⟩
  have he1 := Paper.MarkedRestriction.inducedEdgeCount_union G U (T ∪ W) hUtw
  have he2 := Paper.MarkedRestriction.inducedEdgeCount_union G T W hTW
  have hlower : G.inducedEdgeCount U + Paper.HighGirthAttachments.count G x + T.card ≤ G.inducedEdgeCount (U ∪ (T ∪ W)) := by omega
  have hcards : (U ∪ (T ∪ W)).card = U.card + T.card + W.card := by
    rw [Finset.card_union_of_disjoint hUtw,Finset.card_union_of_disjoint hTW]
    omega
  have heN : G.inducedEdgeCount U + (Paper.HighGirthComponentCounting.pathComponents G x).card = U.card := by
    have he := Paper.HighGirthRetainedEdgeCount.retained_edge_count G x
    change (G.induce (↑U : Set V)).edgeFinset.card + _ = _
    simp only [←SimpleGraph.card_edgeSet,←Nat.card_eq_fintype_card]
    exact he
  have heR : (G.inducedEdgeCount U : Real) + (Paper.HighGirthComponentCounting.pathComponents G x).card = U.card := by exact_mod_cast heN
  have hlowerR : (G.inducedEdgeCount U : Real) + Paper.HighGirthAttachments.count G x + T.card ≤ G.inducedEdgeCount (U ∪ (T ∪ W)) := by exact_mod_cast hlower
  have hd := hden (U ∪ (T ∪ W))
  rw [hcards] at hd
  push_cast at hd
  change (U.card : Real) - (Paper.HighGirthComponentCounting.pathComponents G x).card +
      Paper.HighGirthAttachments.count G x + T.card ≤ a * (U.card + T.card + W.card)
  linarith
end Paper.HighGirthRetainedDensity
#print axioms Paper.HighGirthRetainedDensity.retained_density_bound
