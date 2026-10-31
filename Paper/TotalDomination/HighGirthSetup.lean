import Paper.TotalDomination.HighGirthBudget
import Paper.TotalDomination.CostSaving

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
abbrev F := HighGirthSelection.selected G
abbrev Z := HighGirthSelection.remaining G
abbrev K := HighGirthSelection.candidates G
abbrev c := HighGirthSelection.boundaryCost G
abbrev B := HighGirthSelection.branch G

theorem branch_candidates : B G ⊆ K G := by
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have he := HighGirthSelection.near_cost G (subset_covered G (B G) hv)
  change 0 < HighGirthSelection.boundaryCost G v
  rw [he]; decide

noncomputable def input (x : V → ℝ) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) : Input G where
  candidates := K G
  demands := Z G
  eligible := B G
  eligible_subset := branch_candidates G
  x := x
  threshold := 2/3
  cutoff := 3
  identifier := identifier
  isolate_free := hfree

variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)
noncomputable abbrev I := input G x identifier hfree
noncomputable def linkedLast : Finset V := last G (I G x identifier hfree) ∩ neighbors G (F G)
noncomputable def requests : Finset V := last G (I G x identifier hfree) \ linkedLast G x identifier hfree
noncomputable def selected : Finset V := first G (I G x identifier hfree) ∪ high G (I G x identifier hfree) ∪
  (requests G x identifier hfree).image (request G (I G x identifier hfree))

theorem hits_le_degree (v : V) : hits G (I G x identifier hfree) v ≤ G.degree v := by
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_le_card (Finset.inter_subset_left (s₁ := G.neighborFinset v)
      (s₂ := residual G (I G x identifier hfree)))

theorem high_branch : high G (I G x identifier hfree) ⊆ B G := by
  intro v hv
  have hh := (Finset.mem_filter.mp hv).2
  have hd := hits_le_degree G x identifier hfree v
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,by change 3 ≤ hits G (I G x identifier hfree) v at hh; omega⟩

theorem full_cost {v : V} (hv : v ∈ first G (I G x identifier hfree) ∪ high G (I G x identifier hfree)) :
    c G v = 2 := by
  apply HighGirthSelection.near_cost G
  apply subset_covered G (B G)
  rcases Finset.mem_union.mp hv with hw | hh
  · exact (Finset.mem_filter.mp hw).1
  · exact high_branch G x identifier hfree hh

theorem high_weight {v : V} (hv : v ∈ high G (I G x identifier hfree)) : x v ≤ 2/3 := by
  have hb := high_branch G x identifier hfree hv
  have hn := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  by_contra hx
  apply hn
  exact Finset.mem_filter.mpr ⟨hb,lt_of_not_ge hx⟩

theorem other_hits_cost {v : V} (hv : v ∈ other G (I G x identifier hfree)) :
    hits G (I G x identifier hfree) v ≤ c G v := by
  have hR : residual G (I G x identifier hfree) ⊆ Z G := Finset.sdiff_subset
  have hh : hits G (I G x identifier hfree) v ≤ (G.neighborFinset v ∩ Z G).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left hR)
  have hp : (G.neighborFinset v ∩ F G).card + (G.neighborFinset v ∩ Z G).card = G.degree v := by
    have heq : G.neighborFinset v ∩ Z G = G.neighborFinset v \ F G := by
      ext u
      simp [Z,HighGirthSelection.remaining]
    rw [heq,add_comm]
    exact Finset.card_sdiff_add_card_inter _ _
  have hc := HighGirthSelection.cost_identity G v
  by_cases ht : (G.neighborFinset v ∩ F G).Nonempty
  · have hd := HighGirthSelection.touches_degree G ht
    change c G v + (G.neighborFinset v ∩ F G).card = 2 at hc
    omega
  · have hz : (G.neighborFinset v ∩ F G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ht)
    have hnH : v ∉ high G (I G x identifier hfree) := fun h =>
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ h)
    have hnW : v ∉ first G (I G x identifier hfree) := fun h =>
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ h)
    have hk := (Finset.mem_sdiff.mp hv).1
    have hhit : hits G (I G x identifier hfree) v < 3 := by
      by_contra hn
      exact hnH (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hk,hnW⟩,by change 3 ≤ hits G (I G x identifier hfree) v; omega⟩)
    change c G v + (G.neighborFinset v ∩ F G).card = 2 at hc
    omega

theorem total_dominates :
    ∀ r, ∃ v ∈ F G ∪ selected G x identifier hfree, G.Adj r v := by
  intro r
  by_cases hf : r ∈ F G
  · obtain ⟨v,hv,ha⟩ := HighGirthSelection.selected_neighbor G hf
    exact ⟨v,Finset.mem_union_left _ hv,ha⟩
  have hz : r ∈ Z G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hf⟩
  by_cases hw : r ∈ neighbors G (first G (I G x identifier hfree))
  · obtain ⟨v,hv,ha⟩ := (mem_neighbors G).mp hw
    exact ⟨v,Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv)),ha⟩
  have hr : r ∈ residual G (I G x identifier hfree) := Finset.mem_sdiff.mpr ⟨hz,hw⟩
  by_cases hh : r ∈ neighbors G (high G (I G x identifier hfree))
  · obtain ⟨v,hv,ha⟩ := (mem_neighbors G).mp hh
    exact ⟨v,Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv)),ha⟩
  have hu : r ∈ last G (I G x identifier hfree) :=
    Finset.mem_sdiff.mpr ⟨hr,fun hy => hh (Finset.mem_inter.mp hy).2⟩
  by_cases hl : r ∈ neighbors G (F G)
  · obtain ⟨v,hv,ha⟩ := (mem_neighbors G).mp hl
    exact ⟨v,Finset.mem_union_left _ hv,ha⟩
  refine ⟨request G (I G x identifier hfree) r,?_,request_adj G (I G x identifier hfree) r⟩
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨r,Finset.mem_sdiff.mpr ⟨hu,fun h => hl (Finset.mem_inter.mp h).2⟩,rfl⟩

theorem selected_card_le :
    ((selected G x identifier hfree).card : ℝ) ≤
      (first G (I G x identifier hfree)).card + (residual G (I G x identifier hfree)).card -
      surplus G (I G x identifier hfree) - (linkedLast G x identifier hfree).card := by
  have hcard := Finset.card_union_le (first G (I G x identifier hfree) ∪ high G (I G x identifier hfree))
    ((requests G x identifier hfree).image (request G (I G x identifier hfree)))
  have hfirst := Finset.card_union_le (first G (I G x identifier hfree)) (high G (I G x identifier hfree))
  have himage := Finset.card_image_le (s := requests G x identifier hfree)
    (f := request G (I G x identifier hfree))
  have hreq := Finset.card_sdiff_add_card_eq_card
    (show linkedLast G x identifier hfree ⊆ last G (I G x identifier hfree) from Finset.inter_subset_left)
  have hlast := Finset.card_sdiff_add_card_eq_card
    (show served G (I G x identifier hfree) ⊆ residual G (I G x identifier hfree) from Finset.inter_subset_left)
  have hn : (selected G x identifier hfree).card + (linkedLast G x identifier hfree).card +
      (served G (I G x identifier hfree)).card ≤
      (first G (I G x identifier hfree)).card + (high G (I G x identifier hfree)).card +
      (residual G (I G x identifier hfree)).card := by
    change (requests G x identifier hfree).card + (linkedLast G x identifier hfree).card = _ at hreq
    change (last G (I G x identifier hfree)).card + (served G (I G x identifier hfree)).card = _ at hlast
    change (selected G x identifier hfree).card ≤ _ at hcard
    omega
  have hr : ((selected G x identifier hfree).card : ℝ) + (linkedLast G x identifier hfree).card +
      (served G (I G x identifier hfree)).card ≤
      (first G (I G x identifier hfree)).card + (high G (I G x identifier hfree)).card +
      (residual G (I G x identifier hfree)).card := by exact_mod_cast hn
  unfold surplus
  linarith

end Paper.TotalDomination.HighGirthSetup
