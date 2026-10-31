import Paper.Optimality.Treewidth.CliqueEightCrossCount
import Paper.Optimality.Treewidth.CliqueFourMatchingChoice

/-! Extract the matching and its attachment rows from an actual eight-
vertex graph. The strict count is derived from actual degrees, not an
assumed minor certificate or density conclusion. Labels enumerate the
two genuine four-vertex sides and do not change their adjacency. -/
namespace Paper.CliqueEightMatchingData

open SimpleGraph CliqueFourMatchings
variable {V : Type} [Fintype V] [DecidableEq V]

theorem filter_card (S : Finset V) (e : Fin 4 ≃ (S : Set V))
    (P : V → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun a => P (e a).val)).card = (S.filter P).card := by
  classical
  have himage : (Finset.univ.filter (fun a => P (e a).val)).image
      (fun a => (e a).val) = S.filter P := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(e a).property, ha⟩
    · rintro ⟨hx, hP⟩
      obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      refine ⟨a, ?_, congrArg Subtype.val ha⟩
      rw [congrArg Subtype.val ha]
      exact hP
  have hinj : Function.Injective (fun a => (e a).val) := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  have hh := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ hinj] at hh
  exact hh

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

def outsideGraph : SimpleGraph (Fin 4) where
  Adj i j := G.Adj (eR i).val (eR j).val
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

instance outside_decidable : DecidableRel (outsideGraph G S eR).Adj :=
  fun i j => by
    change Decidable (G.Adj (eR i).val (eR j).val)
    infer_instance

def neighbors (a : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun b => G.Adj (eS a).val (eR b).val)

theorem neighbors_card (a : Fin 4) :
    (neighbors G S eS eR a).card = G.inducedDegree (eS a).val Sᶜ :=
  filter_card Sᶜ eR (G.Adj (eS a).val)

theorem outside_degree (i : Fin 4) :
    (outsideGraph G S eR).degree i = G.inducedDegree (eR i).val Sᶜ := by
  have he : (outsideGraph G S eR).neighborFinset i =
      Finset.univ.filter (fun j => G.Adj (eR i).val (eR j).val) := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  change ((outsideGraph G S eR).neighborFinset i).card = _
  rw [he]
  exact filter_card Sᶜ eR (G.Adj (eR i).val)

private theorem end_distinct : ∀ k : Fin 3,
    (ends k).1.1 ≠ (ends k).1.2 ∧ (ends k).2.1 ≠ (ends k).2.2 := by decide

theorem choose (hV : Fintype.card V = 8) (hS : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x)
    (hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y) :
    ∃ k ∈ available (outsideGraph G S eR),
      (CliqueFourMatchingChoice.bad (neighbors G S eS eR) k).card ≤ 1 := by
  classical
  have hdegree : ∀ i, 2 ≤ (outsideGraph G S eR).degree i := by
    intro i
    rw [outside_degree]
    exact CliqueEightCrossCount.outside_degree G S hS hd (eR i).val
      (hno (eR i).val (eR i).property)
  have hA := CliqueFourMatchings.at_least_two (outsideGraph G S eR) hdegree
  apply CliqueFourMatchingChoice.choose (neighbors G S eS eR) _ hA
  intro hsmall
  have hnot : ¬G.IsClique ((Sᶜ : Finset V) : Set V) := by
    intro hc
    have hevery : ∀ k, k ∈ available (outsideGraph G S eR) := by
      intro k
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · apply hc (eR (ends k).1.1).property (eR (ends k).1.2).property
        intro hh
        exact (end_distinct k).1 (eR.injective (Subtype.ext hh))
      · apply hc (eR (ends k).2.1).property (eR (ends k).2.2).property
        intro hh
        exact (end_distinct k).2 (eR.injective (Subtype.ext hh))
    have heq : available (outsideGraph G S eR) = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr hevery
    have hh := congrArg Finset.card heq
    rw [Finset.card_univ, Fintype.card_fin] at hh
    omega
  have hbound := CliqueEightCrossCount.noncomplete_support G hV hd S hS hnot
  have hfilter : Finset.univ.filter (fun a => (neighbors G S eS eR a).card = 2) =
      Finset.univ.filter (fun a => G.inducedDegree (eS a).val Sᶜ = 2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neighbors_card]
  rw [hfilter, filter_card S eS (fun x => G.inducedDegree x Sᶜ = 2)]
  exact hbound

end Paper.CliqueEightMatchingData

#print axioms Paper.CliqueEightMatchingData.filter_card
#print axioms Paper.CliqueEightMatchingData.neighbors_card
#print axioms Paper.CliqueEightMatchingData.outside_degree
#print axioms Paper.CliqueEightMatchingData.choose
