import Paper.TotalDomination.IntegerLowCoverage
import Paper.Certificates.Counting.DisjointIncidence

namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def core : Finset V := high G (I G d x identifier hfree) ∩ residual G (I G d x identifier hfree)
noncomputable def outside : Finset V := high G (I G d x identifier hfree) \ residual G (I G d x identifier hfree)
noncomputable def servedLow : Finset V := served G (I G d x identifier hfree) \ high G (I G d x identifier hfree)
noncomputable def overlap : Finset V := core G d x identifier hfree \ served G (I G d x identifier hfree)
noncomputable def firstOut : Finset V := first G (I G d x identifier hfree) \ residual G (I G d x identifier hfree)
noncomputable def outsideZero : Finset V := outside G d x identifier hfree ∩
  neighbors G (first G (I G d x identifier hfree) ∩ residual G (I G d x identifier hfree))
noncomputable def outsideOne : Finset V := outside G d x identifier hfree \ outsideZero G d x identifier hfree

theorem core_outside_union : core G d x identifier hfree ∪ outside G d x identifier hfree = high G (I G d x identifier hfree) := by
  ext v
  simp only [core,outside,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  tauto

theorem block_disjoint :
    Disjoint (core G d x identifier hfree) (outside G d x identifier hfree) ∧
    Disjoint (core G d x identifier hfree) (servedLow G d x identifier hfree) ∧
    Disjoint (core G d x identifier hfree) (firstOut G d x identifier hfree) ∧
    Disjoint (outside G d x identifier hfree) (servedLow G d x identifier hfree) ∧
    Disjoint (outside G d x identifier hfree) (firstOut G d x identifier hfree) ∧
    Disjoint (servedLow G d x identifier hfree) (firstOut G d x identifier hfree) := by
  have hd := high_disjoint_first G (I G d x identifier hfree)
  have hh : ∀ v, v ∈ high G (I G d x identifier hfree) → v ∉ first G (I G d x identifier hfree) :=
    fun v hv hw => Finset.disjoint_left.mp hd hv hw
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals apply Finset.disjoint_left.mpr
  all_goals intro v hv hw
  all_goals simp only [core,outside,servedLow,firstOut,served,Finset.mem_inter,Finset.mem_sdiff] at hv hw
  all_goals first | exact hw.2 hv.2 | exact hv.2 hw.1 | exact hw.2 hv.1 | exact hv.2 hw.1.1 | exact hw.2 hv.1.1 | exact hh v hv.1 hw.1

theorem high_neighbor_residual {v r : V}
    (hv : v ∈ high G (I G d x identifier hfree))
    (hr : r ∈ residual G (I G d x identifier hfree)) (ha : G.Adj v r) :
    r ∈ core G d x identifier hfree ∪ servedLow G d x identifier hfree := by
  by_cases hh : r ∈ high G (I G d x identifier hfree)
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hh,hr⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨hr,(mem_neighbors G).mpr ⟨v,hv,ha.symm⟩⟩,hh⟩)

theorem interedges_to_residual (S : Finset V) (hS : S ⊆ high G (I G d x identifier hfree)) :
    G.interedges S (residual G (I G d x identifier hfree)) =
      G.interedges S (core G d x identifier hfree ∪ servedLow G d x identifier hfree) := by
  ext p
  simp only [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hu,hv,ha⟩
    exact ⟨hu,high_neighbor_residual G d x identifier hfree (hS hu) hv ha,ha⟩
  · rintro ⟨hu,hv,ha⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ⟨hu,(Finset.mem_inter.mp hv).2,ha⟩
    · exact ⟨hu,(Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1,ha⟩

theorem outside_neighbor_first {v : V} (hv : v ∈ outside G d x identifier hfree) :
    v ∈ neighbors G (first G (I G d x identifier hfree)) := by
  have hd := high_subset_demands G d x identifier hfree (Finset.mem_sdiff.mp hv).1
  by_contra hn
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨hd,hn⟩)

theorem outside_one_neighbor {v : V} (hv : v ∈ outsideOne G d x identifier hfree) :
    ∃ w ∈ firstOut G d x identifier hfree, G.Adj v w := by
  have ha := (Finset.mem_sdiff.mp hv).1
  obtain ⟨w,hw,hadj⟩ := (mem_neighbors G).mp (outside_neighbor_first G d x identifier hfree ha)
  have hnR : w ∉ residual G (I G d x identifier hfree) := by
    intro hr
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mpr
      ⟨ha,(mem_neighbors G).mpr ⟨w,Finset.mem_inter.mpr ⟨hw,hr⟩,hadj⟩⟩)
  exact ⟨w,Finset.mem_sdiff.mpr ⟨hw,hnR⟩,hadj⟩

theorem hits_sum (S : Finset V) : (∑ v ∈ S, hits G (I G d x identifier hfree) v) =
    (G.interedges S (residual G (I G d x identifier hfree))).card := by
  rw [Incidence.card_interedges_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  change (G.neighborFinset v ∩ residual G (I G d x identifier hfree)).card = _
  congr 1
  ext r
  simp only [Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset]
  exact and_comm

theorem outside_one_count : (outsideOne G d x identifier hfree).card ≤
    (G.interedges (outside G d x identifier hfree) (firstOut G d x identifier hfree)).card := by
  have hlow : (outsideOne G d x identifier hfree).card ≤
      (G.interedges (outsideOne G d x identifier hfree) (firstOut G d x identifier hfree)).card := by
    rw [Incidence.card_interedges_eq_sum]
    calc
      _ = ∑ _v ∈ outsideOne G d x identifier hfree, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun v hv => by
        obtain ⟨w,hw,ha⟩ := outside_one_neighbor G d x identifier hfree hv
        exact Finset.card_pos.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,ha⟩⟩
  apply hlow.trans
  apply Finset.card_le_card
  intro p hp
  simp only [SimpleGraph.mem_interedges_iff] at hp ⊢
  exact ⟨(Finset.mem_sdiff.mp hp.1).1,hp.2⟩

theorem outside_hits_lower : d*(outside G d x identifier hfree).card ≤
    (G.interedges (outside G d x identifier hfree) (residual G (I G d x identifier hfree))).card := by
  rw [← hits_sum]
  calc
    _ = ∑ _v ∈ outside G d x identifier hfree, d := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun v hv =>
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2

theorem excess_identity :
    (d:ℝ)*(high G (I G d x identifier hfree)).card + excess G (I G d x identifier hfree) ((d:ℝ)/2) =
      (G.interedges (high G (I G d x identifier hfree)) (residual G (I G d x identifier hfree))).card := by
  have hh : (∑ v ∈ high G (I G d x identifier hfree), (hits G (I G d x identifier hfree) v : ℝ)) =
      (G.interedges (high G (I G d x identifier hfree)) (residual G (I G d x identifier hfree))).card := by
    exact_mod_cast hits_sum G d x identifier hfree (high G (I G d x identifier hfree))
  simp only [excess,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  rw [hh]
  ring

theorem edge_budget (hden : Incidence.InducedDensityBound G ((d:ℝ)/2)) :
    excess G (I G d x identifier hfree) ((d:ℝ)/2) +
      (G.interedges (core G d x identifier hfree) (servedLow G d x identifier hfree)).card +
      2*(outsideOne G d x identifier hfree).card ≤
      (d:ℝ)*((servedLow G d x identifier hfree).card-(outside G d x identifier hfree).card+
        (firstOut G d x identifier hfree).card) := by
  let Q := core G d x identifier hfree
  let A := outside G d x identifier hfree
  let L := servedLow G d x identifier hfree
  let W := firstOut G d x identifier hfree
  obtain ⟨hQA,hQL,hQW,hAL,hAW,hLW⟩ := block_disjoint G d x identifier hfree
  have hbig : Disjoint (Q∪A) (L∪W) := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨hQL,hQW⟩,Finset.disjoint_union_right.mpr ⟨hAL,hAW⟩⟩
  have hnat := DisjointIncidence.four_blocks G Q A L W hQA hQL hQW hAL hAW hLW
  have hreal : ((G.interedges (Q∪A) (Q∪L)).card : ℝ) + (G.interedges A (Q∪L)).card +
      (G.interedges Q L).card + 2*(G.interedges A W).card ≤ 2*G.inducedEdgeCount ((Q∪A)∪(L∪W)) := by
    exact_mod_cast hnat
  have hcap := mul_le_mul_of_nonneg_left (hden ((Q∪A)∪(L∪W))) (by norm_num : (0:ℝ) ≤ 2)
  have hcard : (((Q∪A)∪(L∪W)).card : ℝ) =
      (high G (I G d x identifier hfree)).card+L.card+W.card := by
    rw [Finset.card_union_of_disjoint hbig,Finset.card_union_of_disjoint hLW]
    change (((core G d x identifier hfree ∪ outside G d x identifier hfree).card +
      ((servedLow G d x identifier hfree).card+(firstOut G d x identifier hfree).card) : ℕ):ℝ) = _
    rw [core_outside_union]
    push_cast
    ring
  rw [hcard] at hcap
  have he := excess_identity G d x identifier hfree
  have haN := outside_hits_lower G d x identifier hfree
  have haR : (d:ℝ)*A.card ≤ (G.interedges A (Q∪L)).card := by
    rw [← interedges_to_residual G d x identifier hfree A Finset.sdiff_subset]
    exact_mod_cast haN
  have h1N := outside_one_count G d x identifier hfree
  have h1R : ((outsideOne G d x identifier hfree).card : ℝ) ≤ (G.interedges A W).card := by
    exact_mod_cast h1N
  rw [interedges_to_residual G d x identifier hfree (high G (I G d x identifier hfree))
    (Finset.Subset.refl _)] at he
  have he' : (d:ℝ)*(high G (I G d x identifier hfree)).card + excess G (I G d x identifier hfree) ((d:ℝ)/2) =
      (G.interedges (Q∪A) (Q∪L)).card := by
    have hqun : Q∪A = high G (I G d x identifier hfree) := core_outside_union G d x identifier hfree
    rw [hqun]
    exact he
  nlinarith only [hreal,hcap,he',haR,h1R]

theorem surplus_identity : surplus G (I G d x identifier hfree) =
    (servedLow G d x identifier hfree).card - (outside G d x identifier hfree).card -
      (overlap G d x identifier hfree).card := by
  have hH := Finset.card_sdiff_add_card_inter (high G (I G d x identifier hfree))
    (residual G (I G d x identifier hfree))
  have hY := Finset.card_sdiff_add_card_inter (served G (I G d x identifier hfree))
    (high G (I G d x identifier hfree))
  have hQ := Finset.card_sdiff_add_card_inter (core G d x identifier hfree)
    (served G (I G d x identifier hfree))
  have heq : served G (I G d x identifier hfree) ∩ high G (I G d x identifier hfree) =
      core G d x identifier hfree ∩ served G (I G d x identifier hfree) := by
    ext v
    simp only [served,core,Finset.mem_inter]
    tauto
  rw [heq] at hY
  have hc : (served G (I G d x identifier hfree)).card +
      (outside G d x identifier hfree).card + (overlap G d x identifier hfree).card =
      (high G (I G d x identifier hfree)).card+(servedLow G d x identifier hfree).card := by
    change (outside G d x identifier hfree).card+(core G d x identifier hfree).card = _ at hH
    change (servedLow G d x identifier hfree).card+_ = _ at hY
    change (overlap G d x identifier hfree).card+_ = _ at hQ
    omega
  have hcR : ((served G (I G d x identifier hfree)).card : ℝ) +
      (outside G d x identifier hfree).card + (overlap G d x identifier hfree).card =
      (high G (I G d x identifier hfree)).card+(servedLow G d x identifier hfree).card := by exact_mod_cast hc
  unfold surplus
  linarith

theorem overlap_le_last : (overlap G d x identifier hfree).card ≤
    (last G (I G d x identifier hfree)).card := by
  apply Finset.card_le_card
  intro v hv
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2,
    (Finset.mem_sdiff.mp hv).2⟩

theorem edge_budget_surplus (hden : Incidence.InducedDensityBound G ((d:ℝ)/2)) :
    excess G (I G d x identifier hfree) ((d:ℝ)/2) +
      (G.interedges (core G d x identifier hfree) (servedLow G d x identifier hfree)).card +
      2*(outsideOne G d x identifier hfree).card ≤
      (d:ℝ)*(surplus G (I G d x identifier hfree)+(overlap G d x identifier hfree).card+
        (first G (I G d x identifier hfree)).card) := by
  have h := edge_budget G d x identifier hfree hden
  have hj := surplus_identity G d x identifier hfree
  have hW : ((firstOut G d x identifier hfree).card : ℝ) ≤ (first G (I G d x identifier hfree)).card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := first G (I G d x identifier hfree))
      (t := residual G (I G d x identifier hfree)))
  have hw := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hj' := congrArg (fun z : ℝ => (d:ℝ)*z) hj
  nlinarith only [h,hj',hw]

end Paper.TotalDomination.IntegerSetup

#print axioms Paper.TotalDomination.IntegerSetup.edge_budget_surplus
