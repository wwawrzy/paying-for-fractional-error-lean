import Paper.TotalDomination.HighGirthPathMetric

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem component_neighbor_sum
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj]
    (z : C) :
    (∑ v ∈ G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree C, x v) =
      ∑ w ∈ C.toSimpleGraph.neighborFinset z, x w.val.val := by
  classical
  let e : C ↪ V := ⟨fun a => a.val.val,by intro a b hab; exact Subtype.ext (Subtype.ext hab)⟩
  have hmap : (C.toSimpleGraph.neighborFinset z).map e =
      G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree C := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
      have hadj : G.Adj z.val.val a.val.val := (C.toSimpleGraph.mem_neighborFinset z a).mp ha
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩⟩
    · intro hv
      obtain ⟨hvn,hvC⟩ := Finset.mem_inter.mp hv
      obtain ⟨hvU,hvComp⟩ := (Finset.mem_filter.mp hvC).2
      let a : C := ⟨⟨v,hvU⟩,hvComp⟩
      have hadj : C.toSimpleGraph.Adj z a := (G.mem_neighborFinset _ _).mp hvn
      exact Finset.mem_map.mpr ⟨a,(C.toSimpleGraph.mem_neighborFinset z a).mpr hadj,rfl⟩
  rw [← hmap,Finset.sum_map]
  rfl

theorem internal_neighbor_finset
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj]
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length) :
    C.toSimpleGraph.neighborFinset (p.getVert i) = {p.getVert (i-1),p.getVert (i+1)} := by
  classical
  ext w
  have he : C.toSimpleGraph.Adj (p.getVert i) w ↔ p.toSubgraph.Adj (p.getVert i) w :=
    Iff.of_eq (congrArg (fun H : SimpleGraph C => H.Adj (p.getVert i) w) hgraph)
  rw [SimpleGraph.mem_neighborFinset,he]
  change w ∈ p.toSubgraph.neighborSet (p.getVert i) ↔ _
  rw [hp.neighborSet_toSubgraph_internal hi hhi]
  simp

theorem internal_neighbor_sum
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj]
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length) :
    (∑ v ∈ G.neighborFinset (p.getVert i).val.val ∩ componentMembers G x identifier hfree C, x v) =
      x (p.getVert (i-1)).val.val + x (p.getVert (i+1)).val.val := by
  classical
  rw [component_neighbor_sum G x identifier hfree C]
  rw [internal_neighbor_finset G x identifier hfree C a b p hp hgraph i hi hhi]
  have hne : p.getVert (i-1) ≠ p.getVert (i+1) := by
    intro he
    have hh := hp.getVert_injOn (by change i-1 ≤ p.length; omega) (by change i+1 ≤ p.length; omega) he
    omega
  rw [Finset.sum_pair hne]

theorem internal_original_row
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length)
    (hn : (p.getVert i).val.val ∉ attachments G x identifier hfree) :
    (∑ v ∈ G.neighborFinset (p.getVert i).val.val, x v) =
      x (p.getVert (i-1)).val.val + x (p.getVert (i+1)).val.val := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hm : (p.getVert i).val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert i).val.property,(p.getVert i).property⟩
  have hs : G.neighborFinset (p.getVert i).val.val ⊆ componentMembers G x identifier hfree C := by
    intro v hv
    exact free_all_neighbors_internal G x identifier hfree C hC hm hn v
      ((G.mem_neighborFinset _ _).mp hv)
  rw [← Finset.inter_eq_left.mpr hs]
  exact internal_neighbor_sum G x identifier hfree C a b p hp hgraph i hi hhi

theorem internal_fractional_constraint
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length)
    (hn : (p.getVert i).val.val ∉ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    1 ≤ x (p.getVert (i-1)).val.val + x (p.getVert (i+1)).val.val := by
  classical
  have hm : (p.getVert i).val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert i).val.property,(p.getVert i).property⟩
  have hz := (Finset.mem_sdiff.mp (core_residual G x identifier hfree
    (component_subset_core G x identifier hfree C hm))).1
  have hrow := hx.2 _ hz
  change 1 ≤ ∑ v ∈ G.neighborFinset (p.getVert i).val.val, x v at hrow
  rw [internal_original_row G x identifier hfree C hC a b p hp hgraph i hi hhi hn] at hrow
  exact hrow

theorem internal_excess_constraint
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length) (hx : ∀ v, 0 ≤ x v) :
    x (p.getVert (i-1)).val.val + x (p.getVert (i+1)).val.val ≤
      1+((∑ v ∈ G.neighborFinset (p.getVert i).val.val, x v)-1) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hs := internal_neighbor_sum G x identifier hfree C a b p hp hgraph i hi hhi
  have hb : (∑ v ∈ G.neighborFinset (p.getVert i).val.val ∩ componentMembers G x identifier hfree C, x v) ≤
      ∑ v ∈ G.neighborFinset (p.getVert i).val.val, x v :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun v _ _ => hx v)
  linarith

end Paper.TotalDomination.HighGirthSetup
