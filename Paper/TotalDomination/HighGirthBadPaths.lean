import Paper.TotalDomination.HighGirthOneAttachmentCharge
import Paper.TotalDomination.HighGirthExceptionalCount

/-! The exact bad-path predicate and both conclusions of fv:hg:t-bad.
The path, attachments and exceptional singleton are actual graph objects. -/
namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def Bad
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Prop :=
  freeComponent G x identifier hfree C ∧ isPathComponent G x identifier hfree C ∧
    ((componentAttachmentPairs G x identifier hfree C).card = 1 ∨
      (Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C) ∧
        ∃ (a b : C) (p : C.toSimpleGraph.Walk a b), p.IsPath ∧
          (∀ z : C, z ∈ p.support) ∧ C.toSimpleGraph = p.toSubgraph.spanningCoe ∧
          ∃ i j : ℕ, i < j ∧ j ≤ p.length ∧
            (p.getVert i).val.val ∈ attachments G x identifier hfree ∧
            (p.getVert j).val.val ∈ attachments G x identifier hfree ∧
            (∀ k, k < i → (p.getVert k).val.val ∉ attachments G x identifier hfree) ∧
            (∀ k, i < k → k < j → (p.getVert k).val.val ∉ attachments G x identifier hfree) ∧
            (j-i = 6 ∨ j-i = 7)))

noncomputable def badComponents : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  letI := Fintype.ofFinite (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
  exact Finset.univ.filter (Bad G x identifier hfree)

theorem bad_nonexceptional_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hbad : Bad G x identifier hfree C) (hnE : ¬Exceptional G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  obtain ⟨hC,hpath,hcase⟩ := hbad
  rcases hcase with hone | ⟨hdistinct,a,b,p,hp,hcover,hgraph,i,j,hij,hj,hiA,hjA,hbefore,hbetween,hgap⟩
  · obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hpath
    exact one_attachment_nonexceptional_charge G x identifier hfree C hC a b p hp hcover hgraph hone hnE hx hcap
  · exact consecutive_gap_charge G x identifier hfree C hC a b p hp hcover hgraph hdistinct
      i j hij hj hiA hjA hbefore hbetween hgap hx hcap

theorem bad_component_count
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    ((badComponents G x identifier hfree).card : ℝ) ≤ (first G (I G x identifier hfree)).card +
      3*penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) + 3*oversupply G (I G x identifier hfree) := by
  classical
  have hb : ∀ C ∈ badComponents G x identifier hfree, Bad G x identifier hfree C := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  apply bad_family_bound G x identifier hfree (badComponents G x identifier hfree)
    (fun C hC => (hb C hC).1) hx hcap
  intro C hC hn
  exact bad_nonexceptional_charge G x identifier hfree C (hb C hC) hn hx hcap

/-- All local charges and the global count, with the exceptional case paid
through its actual degree-two neighbor and W-intersect-R constraints. -/
theorem bad_paths_endpoint
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (∀ C, Bad G x identifier hfree C → ¬Exceptional G x identifier hfree C →
      (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C) ∧
    ((badComponents G x identifier hfree).card : ℝ) ≤ (first G (I G x identifier hfree)).card +
      3*penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) + 3*oversupply G (I G x identifier hfree) := by
  exact ⟨fun C hC hn => bad_nonexceptional_charge G x identifier hfree C hC hn hx hcap,
    bad_component_count G x identifier hfree hx hcap⟩

end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.bad_paths_endpoint
