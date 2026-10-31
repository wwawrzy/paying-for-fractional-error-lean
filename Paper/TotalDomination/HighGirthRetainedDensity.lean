import Paper.TotalDomination.HighGirthRetainedEdges
import Paper.Endpoints.Girth.MarkedRestriction
namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
set_option maxHeartbeats 400000
theorem retained_density_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (a : Real) (hden : Paper.Incidence.InducedDensityBound G a) :
    ((retainedVertices G x identifier hfree).card : Real) -
      (pathComponents G x identifier hfree).card +
      (attachmentPairs G x identifier hfree).card + (connectors G x identifier hfree).card ≤
      a * ((retainedVertices G x identifier hfree).card +
        (connectors G x identifier hfree).card + (first G (I G x identifier hfree)).card) := by
  classical
  let U := retainedVertices G x identifier hfree
  let T := connectors G x identifier hfree
  let W := first G (I G x identifier hfree)
  have hp := retained_set_partition G x identifier hfree
  have hUT : Disjoint U T :=
    (core_connectors_disjoint G x identifier hfree).mono_left hp.1
  have hTW : Disjoint T W := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvW
    exact (Finset.mem_filter.mp hvT).2.1 hvW
  have hUW : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvW
    exact core_not_first G x identifier hfree (hp.1 hvU) hvW
  have hUtw : Disjoint U (T ∪ W) := Finset.disjoint_union_right.mpr ⟨hUT,hUW⟩
  have hq : G.interedges U T = attachmentPairs G x identifier hfree := by
    ext p
    constructor
    · intro h
      obtain ⟨hu,ht,hadj⟩ := (SimpleGraph.mem_interedges_iff G).mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1 hu,ht⟩,hadj⟩
    · intro h
      obtain ⟨hprod,hadj⟩ := Finset.mem_filter.mp h
      obtain ⟨hu,ht⟩ := Finset.mem_product.mp hprod
      have huA : p.1 ∈ attachments G x identifier hfree := Finset.mem_inter.mpr ⟨hu,(mem_neighbors G).mpr ⟨p.2,ht,hadj⟩⟩
      exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hp.2.1 huA,ht,hadj⟩
  have hTWimage : (G.interedges T W).image Prod.fst = T := by
    ext t
    constructor
    · intro h
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact ((SimpleGraph.mem_interedges_iff G).mp hp).1
    · intro ht
      obtain ⟨w,hw,hadj⟩ := (mem_neighbors G).mp (Finset.mem_filter.mp ht).2.2.1
      exact Finset.mem_image.mpr ⟨(t,w),(SimpleGraph.mem_interedges_iff G).mpr ⟨ht,hw,hadj⟩,rfl⟩
  have hTcard : T.card ≤ (G.interedges T W).card := by
    calc
      T.card = ((G.interedges T W).image Prod.fst).card := congrArg Finset.card hTWimage.symm
      _ ≤ (G.interedges T W).card := Finset.card_image_le
  have hqcard : (attachmentPairs G x identifier hfree).card ≤ (G.interedges U (T ∪ W)).card := by
    change (attachmentPairs G x identifier hfree).card ≤ _
    rw [←hq]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hu,ht,hadj⟩ := (SimpleGraph.mem_interedges_iff G).mp hp
    exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hu,Finset.mem_union_left _ ht,hadj⟩
  have he1 := Paper.MarkedRestriction.inducedEdgeCount_union G U (T ∪ W) hUtw
  have he2 := Paper.MarkedRestriction.inducedEdgeCount_union G T W hTW
  have hlower : G.inducedEdgeCount U + (attachmentPairs G x identifier hfree).card + T.card ≤ G.inducedEdgeCount (U ∪ (T ∪ W)) := by omega
  have hcards : (U ∪ (T ∪ W)).card = U.card + T.card + W.card := by
    rw [Finset.card_union_of_disjoint hUtw,Finset.card_union_of_disjoint hTW]
    omega
  have heN : G.inducedEdgeCount U + (pathComponents G x identifier hfree).card = U.card := by
    have he := retained_edge_count G x identifier hfree
    change (G.induce (↑U : Set V)).edgeFinset.card + _ = _
    simp only [←SimpleGraph.card_edgeSet,←Nat.card_eq_fintype_card]
    exact he
  have heR : (G.inducedEdgeCount U : Real) + (pathComponents G x identifier hfree).card = U.card := by exact_mod_cast heN
  have hlowerR : (G.inducedEdgeCount U : Real) + (attachmentPairs G x identifier hfree).card + T.card ≤ G.inducedEdgeCount (U ∪ (T ∪ W)) := by exact_mod_cast hlower
  have hd := hden (U ∪ (T ∪ W))
  rw [hcards] at hd
  push_cast at hd
  change (U.card : Real) - (pathComponents G x identifier hfree).card +
      (attachmentPairs G x identifier hfree).card + T.card ≤ a * (U.card + T.card + W.card)
  linarith
end Paper.TotalDomination.HighGirthSetup
