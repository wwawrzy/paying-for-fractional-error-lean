import Paper.TotalDomination.HighGirthBadPaths

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

/-- The second, unconditional inequality in fv:hg:t-count. -/
theorem selected_vertex_bound :
    (selected G x identifier hfree).card ≤
      2*(first G (I G x identifier hfree)).card + 2*(high G (I G x identifier hfree)).card +
      6*(served G (I G x identifier hfree)).card + 7*(attachmentEdges G x identifier hfree).card := by
  have hD := Finset.card_union_le
    (first G (I G x identifier hfree) ∪ high G (I G x identifier hfree))
    ((requests G x identifier hfree).image (request G (I G x identifier hfree)))
  have hWH := Finset.card_union_le (first G (I G x identifier hfree)) (high G (I G x identifier hfree))
  have himg := Finset.card_image_le (s := requests G x identifier hfree) (f := request G (I G x identifier hfree))
  have hreq : (requests G x identifier hfree).card ≤ (last G (I G x identifier hfree)).card :=
    Finset.card_le_card Finset.sdiff_subset
  have hsplit := Finset.card_sdiff_add_card_inter (last G (I G x identifier hfree))
    (first G (I G x identifier hfree) ∪ high G (I G x identifier hfree))
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := last G (I G x identifier hfree))
    (s₂ := first G (I G x identifier hfree) ∪ high G (I G x identifier hfree)))
  have hcore := residual_size_edges G x identifier hfree
  change (selected G x identifier hfree).card ≤ _ at hD
  change (core G x identifier hfree).card + _ = _ at hsplit
  omega

end Paper.TotalDomination.HighGirthSetup
