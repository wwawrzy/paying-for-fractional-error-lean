import Paper.Optimality.Treewidth.CliqueFiveConnectedAttachment

/-! A three-vertex set of minimum degree five with at most three boundary
vertices forms a six-clique whenever its boundary is a clique. -/
namespace Paper.CliqueThreeAttachment
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem six_clique (C T : Finset V) (hC : C.card = 3) (hT : T.card ≤ 3)
    (hclique : G.IsClique (T : Set V))
    (hd : ∀ x ∈ C, 5 ≤ G.degree x)
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∪ T) :
    (C ∪ T).card = 6 ∧ G.IsClique ((C ∪ T : Finset V) : Set V) := by
  classical
  have hupper : (C ∪ T).card ≤ 6 := by
    have := Finset.card_union_le C T
    omega
  have hfull : ∀ x ∈ C, G.neighborFinset x = (C ∪ T).erase x := by
    intro x hx
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have hxy : G.Adj x y := by simpa only [mem_neighborFinset] using hy
      exact Finset.mem_erase.mpr ⟨hxy.ne.symm, hclosed x hx y hxy⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_union_left T hx)]
      have hdeg := hd x hx
      change (C ∪ T).card - 1 ≤ G.degree x
      omega
  have hcard : (C ∪ T).card = 6 := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
    have hh := congrArg Finset.card (hfull x hx)
    rw [Finset.card_erase_of_mem (Finset.mem_union_left T hx)] at hh
    have hdeg := hd x hx
    change G.degree x = (C ∪ T).card - 1 at hh
    omega
  refine ⟨hcard, ?_⟩
  intro x hx y hy hne
  by_cases hxC : x ∈ C
  · have hm : y ∈ G.neighborFinset x := by
      rw [hfull x hxC]
      exact Finset.mem_erase.mpr ⟨hne.symm, hy⟩
    simpa only [mem_neighborFinset] using hm
  · by_cases hyC : y ∈ C
    · have hm : x ∈ G.neighborFinset y := by
        rw [hfull y hyC]
        exact Finset.mem_erase.mpr ⟨hne, hx⟩
      have hyx : G.Adj y x := by simpa only [mem_neighborFinset] using hm
      exact hyx.symm
    · exact hclique ((Finset.mem_union.mp hx).resolve_left hxC)
        ((Finset.mem_union.mp hy).resolve_left hyC) hne

theorem punctured_minor (C T : Finset V) (hC : C.card = 3) (hT : T.card ≤ 3)
    (hclique : G.IsClique (T : Set V))
    (hd : ∀ x ∈ C, 5 ≤ G.degree x)
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∪ T) :
    (CliqueTwoContractions.punctured 0 1).IsMinor G := by
  classical
  obtain ⟨hcard, hcomplete⟩ := six_clique G C T hC hT hclique hd hclosed
  have htype : Fintype.card ((C ∪ T : Finset V) : Set V) = 6 := by
    simpa only [Fintype.card_eq_nat_card, Finset.coe_sort_coe,
      Nat.card_eq_finsetCard] using hcard
  let e : Fin 6 ≃ ((C ∪ T : Finset V) : Set V) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using htype.symm)
  have hinj : Function.Injective (fun i => (e i).val) := by
    intro i j heq
    exact e.injective (Subtype.ext heq)
  refine ⟨{
    branchSet := fun i => {(e i).val}
    nonempty := fun _ => Set.singleton_nonempty _
    disjoint := fun i j hij => by
      rw [Set.disjoint_singleton]
      exact fun heq => hij (hinj heq)
    connected := fun i => (MinorModel.refl G).connected (e i).val
    adjacent := ?_ }⟩
  intro i j hij
  exact ⟨(e i).val, rfl, (e j).val, rfl,
    hcomplete (e i).property (e j).property (fun heq => hij.1 (hinj heq))⟩

end Paper.CliqueThreeAttachment
#print axioms Paper.CliqueThreeAttachment.six_clique
#print axioms Paper.CliqueThreeAttachment.punctured_minor
