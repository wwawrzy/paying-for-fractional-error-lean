import Paper.Initialization.Pruning.GeneralPruning

/-! Arbitrary pruning passes: the only behavioral requirements are the
literal residual update, selection of useful candidates or residual
vertices, and coverage of demands with short eligible lists. -/
namespace Paper.PruningRun
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Run (h f T : ℕ) where
  residual : ℕ → Finset V
  selected : ℕ → Finset V
  step : ∀ i, i < T → residual (i+1) = residual i \ covered G (selected i)
  support : ∀ i, i < T → selected i ⊆ candidates G h (residual i) ∪ residual i
  short_covered : ∀ i, i < T → ∀ v ∈ residual i,
    (eligibleList G h (residual i) v).card ≤ f → v ∈ covered G (selected i)

variable {h f T : ℕ} (P : Run G h f T)

theorem antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) : P.residual j ⊆ P.residual i := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j hij ih =>
    have hs : P.residual (j+1) ⊆ P.residual j := by
      rw [P.step j (by omega)]
      exact Finset.sdiff_subset
    exact hs.trans (ih (by omega))

theorem disjoint {i j : ℕ} (hi : i < T) (hj : j < T) (hne : i ≠ j) :
    Disjoint (P.selected i) (P.selected j) := by
  have forward : ∀ {i j}, i < j → j < T → Disjoint (P.selected i) (P.selected j) := by
    intro i j hij hj
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hdis : Disjoint (closed G v) (P.residual j) := by
      apply Finset.disjoint_left.mpr
      intro u hu huR
      have hu' := antitone G P (by omega : i+1 ≤ j) (by omega : j ≤ T) huR
      rw [P.step i (by omega)] at hu'
      exact (Finset.mem_sdiff.mp hu').2 (Finset.mem_biUnion.mpr ⟨v,hvi,hu⟩)
    rcases Finset.mem_union.mp (P.support j hj hvj) with hvC | hvR
    · have hc := (Finset.mem_filter.mp hvC).2
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_empty] at hc
      omega
    · exact Finset.disjoint_left.mp hdis (self_mem_closed G v) hvR
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact forward hij hj
  · exact (forward hji hi).symm

theorem surviving (i : ℕ) (hi : i < T) {v : V} (hv : v ∈ P.residual (i+1)) :
    f ≤ ((G.neighborFinset v) ∩ candidates G h (P.residual i)).card := by
  rw [P.step i hi] at hv
  have hmem := Finset.mem_sdiff.mp hv
  have hlarge : ¬ (eligibleList G h (P.residual i) v).card ≤ f := by
    intro hs
    exact hmem.2 (P.short_covered i hi v hmem.1 hs)
  have hc := closed_inter_card G (candidates G h (P.residual i)) v
  change ¬ ((closed G v) ∩ candidates G h (P.residual i)).card ≤ f at hlarge
  omega

noncomputable def union : Finset V := (Finset.range T).biUnion P.selected

theorem union_eq : union G P = Finset.univ.biUnion (fun i : Fin T => P.selected i.val) := by
  ext v
  simp only [union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i,hi,hv⟩ => ⟨⟨i,hi⟩,hv⟩, fun ⟨i,hv⟩ => ⟨i.val,i.isLt,hv⟩⟩

/-- Exact source coefficient and its at-most-four specialization. No
simultaneous forest or successful-region certificate is supplied. -/
theorem residual_bound (d : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T) (hdeg : G.IsKDegenerate d)
    (a : ℝ) (ha : 0 ≤ a) (hTa : 2*a ≤ T) (hden : MinorDensity.Bound G a)
    (hh : d+4*T*d ≤ h) (hf : d+4*T*T*d ≤ f) :
    ((P.residual T).card : ℝ) ≤ (2*(T : ℝ)/((T : ℝ)-a)) * (union G P).card ∧
      (P.residual T).card ≤ 4*(union G P).card := by
  let R : Fin (T+1) → Finset V := fun i => P.residual i.val
  let C : Fin T → Finset V := fun i => candidates G h (R i.castSucc)
  let S : Fin T → Finset V := fun i => P.selected i.val
  have hff : ∀ i v, v ∈ R i.succ → d+4*T*T*d ≤ ((G.neighborFinset v) ∩ C i).card := by
    intro i v hv
    exact hf.trans (surviving G P i.val i.isLt hv)
  have hhh : ∀ i v, v ∈ C i → d+4*T*d ≤ ((G.neighborFinset v) ∩ R i.castSucc).card := by
    intro i v hv
    exact hh.trans (candidate_neighbors G h (R i.castSucc) hv)
  have hX : ∀ i : Fin T, P.residual T ⊆ R i.succ := by
    intro i
    exact antitone G P (by omega : i.val+1 ≤ T) (le_refl T)
  have hdis : ∀ i j : Fin T, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hne
    exact disjoint G P i.isLt j.isLt (fun he => hne (Fin.ext he))
  have hremoved : ∀ i : Fin T, R i.castSucc \ R i.succ ⊆ covered G (S i) := by
    intro i v hv
    have hm := Finset.mem_sdiff.mp hv
    by_contra hn
    apply hm.2
    change v ∈ P.residual (i.val+1)
    rw [P.step i.val i.isLt]
    exact Finset.mem_sdiff.mpr ⟨hm.1,hn⟩
  have hs := GeneralPruning.pass_bound G hT hd hdeg ha hTa hden R C S hff hhh
    (P.residual T) hX hdis hremoved
  rw [← union_eq G P] at hs
  exact hs

/-- Literal residual identity for any number of completed passes. -/
theorem remaining (n : ℕ) (hn : n ≤ T) :
    P.residual n = P.residual 0 \ covered G ((Finset.range n).biUnion P.selected) := by
  induction n with
  | zero => simp [covered]
  | succ n ih =>
    rw [P.step n (by omega), ih (by omega)]
    ext v
    simp only [Finset.range_add_one, Finset.biUnion_insert, covered,
      Finset.union_biUnion, Finset.mem_sdiff, Finset.mem_union]
    tauto

theorem output_covers :
    P.residual 0 ⊆ covered G (union G P ∪ P.residual T) := by
  intro v hv
  by_cases hc : v ∈ covered G (union G P)
  · exact covered_mono G Finset.subset_union_left hc
  · have hr : v ∈ P.residual T := by
      rw [remaining G P T (le_refl T)]
      exact Finset.mem_sdiff.mpr ⟨hv,hc⟩
    exact subset_covered G _ (Finset.mem_union_right _ hr)

/-- The source's 5*T*c_P benchmark after self-selection of the residual. -/
theorem final_cost (d : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T) (hdeg : G.IsKDegenerate d)
    (a : ℝ) (ha : 0 ≤ a) (hTa : 2*a ≤ T) (hden : MinorDensity.Bound G a)
    (hh : d+4*T*d ≤ h) (hf : d+4*T*T*d ≤ f) (c K : ℝ)
    (hper : ∀ i, i < T → ((P.selected i).card : ℝ) ≤ c*K) :
    ((union G P ∪ P.residual T).card : ℝ) ≤ 5*(T : ℝ)*c*K := by
  have hr := (residual_bound G P d hd hT hdeg a ha hTa hden hh hf).2
  have hu := Finset.card_union_le (union G P) (P.residual T)
  have hfive : ((union G P ∪ P.residual T).card : ℝ) ≤ 5*(union G P).card := by
    exact_mod_cast (show (union G P ∪ P.residual T).card ≤ 5*(union G P).card by omega)
  have hb : ((union G P).card : ℝ) ≤ (T : ℝ)*c*K := by
    have hcard : (union G P).card ≤ ∑ i ∈ Finset.range T, (P.selected i).card :=
      Finset.card_biUnion_le
    have hc' : ((union G P).card : ℝ) ≤ ∑ i ∈ Finset.range T, ((P.selected i).card : ℝ) := by
      exact_mod_cast hcard
    have hs := Finset.sum_le_sum (s := Finset.range T) (fun i hi => hper i (Finset.mem_range.mp hi))
    calc
      _ ≤ _ := hc'
      _ ≤ ∑ _i ∈ Finset.range T, c*K := hs
      _ = _ := by simp; ring
  nlinarith

end Paper.PruningRun
