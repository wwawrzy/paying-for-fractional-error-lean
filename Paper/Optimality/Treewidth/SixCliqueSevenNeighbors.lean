import Paper.Optimality.Treewidth.SixCliqueBoundaryMissing
import Paper.Optimality.Treewidth.CliqueSevenBoundary
import Paper.Optimality.Treewidth.CliqueProjectionSeparation

/-! The degree-seven global K6 case. A real outside component has a
boundary on at most five vertices with at most two missing edges. Two
actual projections, one from each side, contradict affine minimality. -/
namespace Paper.SixCliqueSevenNeighbors

open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem impossible (hG : G.IsKMinorFree 6) (horder : 10 ≤ Fintype.card V)
    (he : G.edgeFinset.card + 9 = 4 * Fintype.card V)
    (hd : ∀ z, 4 ≤ G.degree z) (hminimal : CliqueMinorMinimal.BelowThreshold G 4 9 4)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (v : V) (hv : G.degree v = 7)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) : False := by
  classical
  have heN := SixCliqueSevenRegular.edge_count G hG horder hsep v hv hcn
  have hregular := SixCliqueSevenRegular.regular_finset G v hv heN hcn
  obtain ⟨X, hX, hXne, hout, hBN⟩ :=
    CliqueNeighborhoodExterior.exists_exterior G v (by omega)
  let B := boundary G X
  have hunique : ∀ u ∈ B, ∀ a ∈ B, a ≠ u → ¬G.Adj u a →
      ∀ b ∈ B, b ≠ u → ¬G.Adj u b → a = b := by
    intro u hu a ha hau hna b hb hbu hnb
    exact SixCliqueBoundaryMissing.unique G hG v hv heN X hX hout hBN
      u hu a ha hau hna b hb hbu hnb
  have hBdegree : ∀ u ∈ B, B.card - 2 ≤ G.inducedDegree u B := by
    intro u hu
    exact CliqueMissingEdges.degree_lower G B u (hunique u hu)
  have hBsub : B ⊆ G.neighborFinset v := by
    intro u hu
    exact (G.mem_neighborFinset v u).mpr (hBN hu)
  have hNcard : (G.neighborFinset v).card = 7 := by
    rw [G.card_neighborFinset_eq_degree, hv]
  have hBcard : B.card ≤ 5 := CliqueSevenBoundary.within G (G.neighborFinset v) B
    hNcard hBsub hregular hBdegree
  have hBtype : Fintype.card (B : Set V) = B.card := by
    simp only [Fintype.card_eq_nat_card, Finset.coe_sort_coe, Nat.card_eq_finsetCard]
  have hmissing : B.card.choose 2 ≤ (G.induce (B : Set V)).edgeFinset.card + 2 := by
    have hh := CliqueMissingEdges.two (G.induce (B : Set V)) (by omega) (by
      intro z
      rw [hBtype, TreewidthDensity.induced_degree]
      exact hBdegree z.val z.property)
    simpa only [hBtype] using hh
  have hnot := CliqueNeighborhoodExterior.boundary_not_clique G v X hXne hout hsep
  change ¬(∀ u ∈ (B : Set V), ∀ w ∈ (B : Set V), u ≠ w → G.Adj u w) at hnot
  push Not at hnot
  obtain ⟨u, hu, w, hw, huw, hnuw⟩ := hnot
  have hvX : v ∉ X := fun hh => hout hh (Set.mem_insert _ _)
  have hno : ∀ z ∈ X, ¬G.Adj v z := by
    intro z hz hadj
    exact hout hz (Or.inr hadj)
  have hvB : v ∉ B := fun hh => G.loopless.irrefl v (hBN hh)
  have huX : u ∉ X := ((mem_boundary G X u).mp hu).1
  have hwX : w ∉ X := ((mem_boundary G X w).mp hw).1
  let s := separation G X hXne v hvX hno
  letI : Fintype s.left := Fintype.ofFinite _
  letI : Fintype s.right := Fintype.ofFinite _
  let uL : s.left := ⟨u, Or.inr hu⟩
  let wL : s.left := ⟨w, Or.inr hw⟩
  let uR : s.right := ⟨u, huX⟩
  let wR : s.right := ⟨w, hwX⟩
  let SL : Set V := insert u {v}
  let SR : Set V := insert u X
  have hvL : v ∉ s.left := by
    change v ∉ X ∪ (B : Set V)
    exact fun hh => hh.elim hvX hvB
  have hdisjL : Disjoint ({v} : Set V) s.left := by
    rw [Set.disjoint_left]
    intro z hz hzL
    have hzv : z = v := hz
    subst z
    exact hvL hzL
  have hminorL : (CliqueStarProjection.fill G s.left uL SL).IsMinor G :=
    CliqueStarProjection.outside G s.left {v} uL ((MinorModel.refl G).connected v)
      hdisjL ⟨v, rfl, (hBN hu).symm⟩
  have hdisjR : Disjoint X s.right := by
    rw [Set.disjoint_left]
    intro z hz hzR
    exact hzR hz
  have hminorR : (CliqueStarProjection.fill G s.right uR SR).IsMinor G :=
    CliqueStarProjection.outside G s.right X uR hX hdisjR ((mem_boundary G X u).mp hu).2
  have hgrowL := CliqueStarBound.growth G s.left uL wL SL
    (fun hh => huw (congrArg Subtype.val hh)) hnuw
    ⟨v, Or.inr rfl, hBN hw⟩
  have hgrowR := CliqueStarBound.growth G s.right uR wR SR
    (fun hh => huw (congrArg Subtype.val hh)) hnuw (by
      obtain ⟨z, hz, hwz⟩ := ((mem_boundary G X w).mp hw).2
      exact ⟨z, Or.inr hz, hwz.symm⟩)
  exact CliqueProjectionSeparation.impossible G he hd hminimal B s
    (CliqueStarProjection.fill G s.left uL SL) (CliqueStarProjection.fill G s.right uR SR)
    hminorL hminorR (by omega) (by omega) hmissing

end Paper.SixCliqueSevenNeighbors

#print axioms Paper.SixCliqueSevenNeighbors.impossible
