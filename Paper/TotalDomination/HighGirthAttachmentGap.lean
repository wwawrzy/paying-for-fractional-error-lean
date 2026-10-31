import Paper.TotalDomination.HighGirthAttachmentPositions

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem attachment_gap_le_seven
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i j : ℕ) (hij : i < j) (hj : j ≤ p.length)
    (hbetween : ∀ k, i < k → k < j → (p.getVert k).val.val ∉ attachments G x identifier hfree) : j-i ≤ 7 := by
  classical
  by_contra hn
  let m := i+4
  have hm : m ≤ p.length := by dsimp [m]; omega
  have hpath : isPathComponent G x identifier hfree C := ⟨a,b,p,hp,hcover,hgraph⟩
  have hex : ∃ z : C, z.val.val ∈ attachments G x identifier hfree ∧ C.toSimpleGraph.dist (p.getVert m) z ≤ 3 := by
    rcases free_component_metric_access G x identifier hfree C hC (p.getVert m) with ⟨z,hB,hd⟩ | ⟨z,hA,hd⟩
    · exact ⟨z,branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,z.val.property⟩),hd⟩
    · exact ⟨z,hA,by omega⟩
  obtain ⟨z,hA,hd⟩ := hex
  obtain ⟨k,hzk,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
  have hd' : C.toSimpleGraph.dist (p.getVert m) (p.getVert k) ≤ 3 := by simpa only [hzk] using hd
  have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp m k 3 hm hk hd'
  exact hbetween k (by dsimp [m] at hbnd; omega) (by dsimp [m] at hbnd; omega)
    (by simpa only [hzk] using hA)

theorem first_gap_le_five_of_not_bad
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hnB : ¬Bad G x identifier hfree C)
    (hdistinct : Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C))
    (i j : ℕ) (hij : i < j) (hj : j ≤ p.length)
    (hiA : (p.getVert i).val.val ∈ attachments G x identifier hfree)
    (hjA : (p.getVert j).val.val ∈ attachments G x identifier hfree)
    (hbefore : ∀ k, k < i → (p.getVert k).val.val ∉ attachments G x identifier hfree)
    (hbetween : ∀ k, i < k → k < j → (p.getVert k).val.val ∉ attachments G x identifier hfree) : j-i ≤ 5 := by
  have hseven := attachment_gap_le_seven G x identifier hfree C hC a b p hp hcover hgraph i j hij hj hbetween
  by_contra hn
  have hgap : j-i = 6 ∨ j-i = 7 := by omega
  apply hnB
  exact ⟨hC,⟨a,b,p,hp,hcover,hgraph⟩,Or.inr ⟨hdistinct,a,b,p,hp,hcover,hgraph,i,j,hij,hj,hiA,hjA,hbefore,hbetween,hgap⟩⟩

end Paper.TotalDomination.HighGirthSetup
