import Paper.Initialization.Pruning.InitialForest
import Paper.Preliminaries.RegionBoundary

/-! At least half of final residual roots have a region containing a demand
removed in every pass. This is proved from actual forest children. -/
namespace Paper.SuccessfulRegions
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def failed {T : ℕ} (R : Fin (T + 1) → Finset V) (X : Finset V)
    (parent : V → Option V) (rank : V → ℕ)
    (decrease : ∀ u v, parent u = some v → rank v < rank u) (i : Fin T) : Finset V :=
  X.filter (fun x => ¬ ∃ v ∈ R i.castSucc \ R i.succ,
    ForestRegions.owner parent rank decrease X v = some x)

theorem failed_boundary {T κ μ : ℕ} {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (M : InitialForest.Model G T κ μ R C) (hκ : 1 ≤ κ) (hμ : 1 ≤ μ)
    (X : Finset V) (i : Fin T) (hX : X ⊆ R i.succ) {x : V}
    (hx : x ∈ failed R X M.parent M.rank M.decrease i) :
    κ ≤ (RegionBoundary.boundary M.parent M.rank M.decrease X x).card := by
  classical
  have hxX := (Finset.mem_filter.mp hx).1
  have hno := (Finset.mem_filter.mp hx).2
  let own := ForestRegions.owner M.parent M.rank M.decrease X
  let Y := (R i.succ ∪ C i).filter (fun v => own v = some x)
  let Z := RegionBoundary.boundary M.parent M.rank M.decrease X x
  have hyx : x ∈ Y := Finset.mem_filter.mpr
    ⟨Finset.mem_union_left _ (hX hxX), ForestRegions.owner_center _ _ _ X hxX⟩
  have hremain : ∀ v, own v = some x → v ∈ R i.castSucc → v ∈ R i.succ := by
    intro v hv hRi
    by_contra hn
    exact hno ⟨v, Finset.mem_sdiff.mpr ⟨hRi, hn⟩, hv⟩
  have hmem : ∀ v u, own v = some x → M.parent u = some v →
      u ∈ R i.succ ∪ C i → u ∈ Y ∪ Z := by
    intro v u hv hp hu
    rcases RegionBoundary.child_in_region_or_boundary M.parent M.rank M.decrease X hv hp with hr | hz
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, hr⟩)
    · exact Finset.mem_union_right _ hz
  have hdemand : ∀ v, own v = some x → v ∈ R i.succ →
      κ ≤ ((Y ∪ Z).filter (fun u => M.parent u = some v)).card := by
    intro v hv hvR
    apply (M.demand_children i v hvR).trans
    apply Finset.card_le_card
    intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hmem v u hv hp
      (Finset.mem_union_right _ (Finset.mem_inter.mp hu).2), hp⟩
  apply RegionBoundary.expansion M.parent M.rank M.decrease X Y Z hyx
    (fun v hv => (Finset.mem_filter.mp hv).2) κ
  · intro v hv
    obtain ⟨hvS, hvOwn⟩ := Finset.mem_filter.mp hv
    rcases Finset.mem_union.mp hvS with hvR | hvC
    · exact hκ.trans (hdemand v hvOwn hvR)
    · apply hμ.trans ((M.candidate_children i v hvC).trans _)
      apply Finset.card_le_card
      intro u hu
      obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
      have huRi := (Finset.mem_inter.mp hu).2
      have hU : u ∈ Y ∪ Z := by
        rcases RegionBoundary.child_in_region_or_boundary M.parent M.rank M.decrease X hvOwn hp with hr | hz
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_union_left _ (hremain u hr huRi), hr⟩)
        · exact Finset.mem_union_right _ hz
      exact Finset.mem_filter.mpr ⟨hU, hp⟩
  · exact hdemand x (ForestRegions.owner_center _ _ _ X hxX) (hX hxX)

theorem failed_count {T κ μ : ℕ} {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (M : InitialForest.Model G T κ μ R C) (hκ : 1 ≤ κ) (hμ : 1 ≤ μ)
    (X : Finset V) (i : Fin T) (hX : X ⊆ R i.succ) :
    κ * (failed R X M.parent M.rank M.decrease i).card ≤ X.card :=
  RegionBoundary.roots_bound M.parent M.rank M.decrease X _ κ
    (fun _ hx => failed_boundary G M hκ hμ X i hX hx)

theorem many_successful {T μ : ℕ} {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (hT : 1 ≤ T) (M : InitialForest.Model G T (2 * T) μ R C) (hμ : 1 ≤ μ)
    (X : Finset V) (hX : ∀ i : Fin T, X ⊆ R i.succ) :
    ∃ Q : Finset V, Q ⊆ X ∧ X.card ≤ 2 * Q.card ∧
      ∀ x ∈ Q, ∀ i : Fin T, ∃ v ∈ R i.castSucc \ R i.succ,
        ForestRegions.owner M.parent M.rank M.decrease X v = some x := by
  classical
  let B := fun i => failed R X M.parent M.rank M.decrease i
  let bad := Finset.univ.biUnion B
  have hs : (2 * T) * (∑ i : Fin T, (B i).card) ≤ T * X.card := by
    calc
      _ = ∑ i : Fin T, (2 * T) * (B i).card := Finset.mul_sum ..
      _ ≤ ∑ _i : Fin T, X.card := Finset.sum_le_sum (fun i _ => failed_count G M (by omega) hμ X i (hX i))
      _ = _ := by simp
  have hsum : 2 * (∑ i : Fin T, (B i).card) ≤ X.card := by
    exact Nat.le_of_mul_le_mul_left (c := T) (by nlinarith [hs]) (by omega)
  have hbad : 2 * bad.card ≤ X.card :=
    (Nat.mul_le_mul_left 2 (Finset.card_biUnion_le)).trans hsum
  have hsub : bad ⊆ X := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hi).1
  refine ⟨X \ bad, Finset.sdiff_subset, ?_, ?_⟩
  · have hc := Finset.card_sdiff_add_card_eq_card hsub
    omega
  · intro x hx i
    have hx' := Finset.mem_sdiff.mp hx
    have hn : x ∉ B i := fun hi => hx'.2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    by_contra he
    exact hn (Finset.mem_filter.mpr ⟨hx'.1, he⟩)
end Paper.SuccessfulRegions
