import Paper.Optimality.Treewidth.CliqueContactDegree
namespace Paper.SevenCliqueTwentySixClassification
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem high_degree_contact (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    ∃ p ∈ G.neighborFinset v, 12 ≤ G.degree p := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let T := vertices X
  let S := insert v (G.neighborFinset v)
  obtain ⟨x,hx,h7,h1⟩ := universal_contact G hG horder hmin hcn hsep v hv8 C hsize
  change G.inducedDegree x T = 7 at h7
  obtain ⟨p,hp,hxp,hunique⟩ := unique_outside G T x h1
  have hxX : x ∈ X := (mem_vertices X x).mp hx
  have hpX : p ∉ X := fun hh => hp ((mem_vertices X p).mpr hh)
  have hpA := outside_boundary G A C x hxX p hpX hxp
  have hxA := outside_subset G A C hxX
  have hpN : p ∈ G.neighborFinset v := by
    rcases hpA with heq | hpN
    · subst p
      exact False.elim (hxA (Or.inr hxp.symm))
    · exact (G.mem_neighborFinset v p).mpr hpN
  have hforced : ∀ z ∈ T, G.inducedDegree z T = 5 → G.Adj p z := by
    intro z hz hz5
    have hzx : z ≠ x := by intro heq; subst z; omega
    have hxz := CliqueForcedExteriorContact.universal_inside G T x hx hsize h7 z hz hzx
    exact CliqueForcedExteriorContact.forced G T x p z hx hxz hunique hz5 (hcn x z hxz)
  have hc := (degree_distribution G hG horder hmin hcn hsep v hv8 C hsize).1
  have hT := CliqueContactDegree.cross_six G T x p hx h7 hxp.symm hc hforced
  have hreg := SevenCliqueEightNeighborhood.neighborhood_regular G hG v hv8
    (fun z => by rw [hv8]; exact hmin z) (hcn v) C hsize p hpN
  have hpv : G.Adj p v := ((G.mem_neighborFinset v p).mp hpN).symm
  have hfilter : S.filter (G.Adj p) = insert v ((G.neighborFinset v).filter (G.Adj p)) := by
    ext z
    simp only [S,Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨h|h,hz⟩
      · exact Or.inl h
      · exact Or.inr ⟨h,hz⟩
    · rintro (rfl|h)
      · exact ⟨Or.inl rfl,hpv⟩
      · exact ⟨Or.inr h.1,h.2⟩
  have hvnot : v ∉ (G.neighborFinset v).filter (G.Adj p) :=
    fun hh => G.notMem_neighborFinset_self v (Finset.mem_filter.mp hh).1
  have hS : G.inducedDegree p S = 6 := by
    change (S.filter (G.Adj p)).card = 6
    rw [hfilter,Finset.card_insert_of_notMem hvnot]
    change G.inducedDegree p (G.neighborFinset v)+1 = 6
    omega
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro z hzS hzT
    have hzA := outside_subset G A C ((mem_vertices X z).mp hzT)
    apply hzA
    simpa only [S,A,Finset.mem_insert,Set.mem_insert_iff,G.mem_neighborFinset] using hzS
  exact ⟨p,hpN,CliqueContactDegree.twelve G S T hdis p hS hT⟩
end Paper.SevenCliqueTwentySixClassification
