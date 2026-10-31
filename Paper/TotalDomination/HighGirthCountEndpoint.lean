import Paper.TotalDomination.HighGirthRetainedDensity
import Paper.TotalDomination.HighGirthCountArithmetic
import Paper.TotalDomination.HighGirthSelectedCount

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem connectors_le_attachment_edges : (connectors G x identifier hfree).card ≤
    (attachmentEdges G x identifier hfree).card := by
  classical
  have him : (attachmentPairs G x identifier hfree).image Prod.snd = connectors G x identifier hfree := by
    ext v
    constructor
    · intro hv
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    · intro hv
      obtain ⟨u,hu,ha⟩ := (mem_neighbors G).mp (Finset.mem_filter.mp hv).2.2.2
      exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hu,hv⟩,ha.symm⟩,rfl⟩
  rw [attachment_edges_card G x identifier hfree,←him]
  exact Finset.card_image_le

/-- Both inequalities of fv:hg:t-count for the actual rounded total-dominating set. -/
theorem count_endpoint (a : ℝ) (ha : 1 ≤ a) (ha' : a < 9/8)
    (hden : Paper.Incidence.InducedDensityBound G a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (9-8*a)/2*((attachmentEdges G x identifier hfree).card : ℝ) ≤
      (5-2*a)/2*(first G (I G x identifier hfree)).card +
      (6*a-4)*(served G (I G x identifier hfree)).card +
      (linkedLast G x identifier hfree).card + (15-12*a)/2*
      (penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) + oversupply G (I G x identifier hfree)) ∧
    (selected G x identifier hfree).card ≤
      2*(first G (I G x identifier hfree)).card + 2*(high G (I G x identifier hfree)).card +
      6*(served G (I G x identifier hfree)).card + 7*(attachmentEdges G x identifier hfree).card := by
  constructor
  · have hd := retained_density_bound G x identifier hfree a hden
    rw [←attachment_edges_card G x identifier hfree] at hd
    have hs : ((connectors G x identifier hfree).card : ℝ) ≤ (attachmentEdges G x identifier hfree).card := by
      exact_mod_cast connectors_le_attachment_edges G x identifier hfree
    have hu : ((retainedVertices G x identifier hfree).card : ℝ)+8*(freeComponents G x identifier hfree).card ≤
        7*(attachmentEdges G x identifier hfree).card+6*(served G (I G x identifier hfree)).card+
        2*(badComponents G x identifier hfree).card := by
      exact_mod_cast retained_size_bound G x identifier hfree
    have hcp : ((pathComponents G x identifier hfree).card : ℝ) ≤ (freeComponents G x identifier hfree).card+
        2*(served G (I G x identifier hfree)).card+(linkedLast G x identifier hfree).card := by
      exact_mod_cast path_component_count G x identifier hfree
    have hc : 2*((freeComponents G x identifier hfree).card : ℝ) ≤
        (attachmentEdges G x identifier hfree).card+(badComponents G x identifier hfree).card := by
      exact_mod_cast free_component_attachment_bound G x identifier hfree
    exact Paper.TotalDomination.HighGirthCountArithmetic.eliminate a _ _ _ _ _ _ _ _ _ _ _ ha ha'
      hd hs hu hcp hc (bad_component_count G x identifier hfree hx hcap)
  · exact selected_vertex_bound G x identifier hfree
end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.count_endpoint
