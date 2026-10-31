import Paper.Preliminaries.ForestRegions

/-! Count exits from a nearest-ancestor region by the unique-parent rule. -/
namespace Paper.RegionBoundary
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [DecidableEq V]
variable (parent : V → Option V) (rank : V → ℕ)
variable (decrease : ∀ u v, parent u = some v → rank v < rank u)

noncomputable def strictOwner (X : Finset V) (u : V) : Option V :=
  (parent u).bind (ForestRegions.owner parent rank decrease X)

noncomputable def boundary (X : Finset V) (x : V) : Finset V :=
  X.filter (fun u => strictOwner parent rank decrease X u = some x)

theorem child_in_region_or_boundary (X : Finset V) {x v u : V}
    (hv : ForestRegions.owner parent rank decrease X v = some x) (hu : parent u = some v) :
    ForestRegions.owner parent rank decrease X u = some x ∨
      u ∈ boundary parent rank decrease X x := by
  by_cases hX : u ∈ X
  · right
    exact Finset.mem_filter.mpr ⟨hX, by simpa [strictOwner, hu] using hv⟩
  · left
    exact (ForestRegions.owner_parent parent rank decrease X hX hu).trans hv

/-- If every interior vertex has a child inside or on the marked boundary,
and the root has k such children, the boundary has at least k vertices.
No subtree exploration or selected witness map is assumed. -/
theorem expansion (X Y Z : Finset V) {x : V} (hx : x ∈ Y)
    (hregion : ∀ v ∈ Y, ForestRegions.owner parent rank decrease X v = some x)
    (k : ℕ)
    (hchild : ∀ v ∈ Y, 1 ≤ ((Y ∪ Z).filter (fun u => parent u = some v)).card)
    (hroot : k ≤ ((Y ∪ Z).filter (fun u => parent u = some x)).card) : k ≤ Z.card := by
  classical
  let U := Y ∪ Z
  let kids := fun v => U.filter (fun u => parent u = some v)
  let pars := fun u => Y.filter (fun v => parent u = some v)
  have hz : pars x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hm := Finset.mem_filter.mp hv
    have hr := ForestRegions.owner_rank parent rank decrease X (hregion v hm.1)
    have hd := decrease x v hm.2
    omega
  have hcap : ∀ u, (pars u).card ≤ 1 := by
    intro u
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  have heq : (∑ v ∈ Y, (kids v).card) = ∑ u ∈ U, (pars u).card := by
    simp only [kids, pars, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hxU : x ∈ U := Finset.mem_union_left Z hx
  have hup : (∑ u ∈ U, (pars u).card) ≤ U.card - 1 := by
    have hs := Finset.sum_erase_add U (fun u => (pars u).card) hxU
    change (∑ u ∈ U.erase x, (pars u).card) + (pars x).card = ∑ u ∈ U, (pars u).card at hs
    rw [hz, Finset.card_empty, add_zero] at hs
    rw [← hs]
    calc
      _ ≤ ∑ _u ∈ U.erase x, 1 := Finset.sum_le_sum (fun u _ => hcap u)
      _ = U.card - 1 := by simp [Finset.card_erase_of_mem hxU]
  have hlo : k + (Y.card - 1) ≤ ∑ v ∈ Y, (kids v).card := by
    have hs := Finset.sum_erase_add Y (fun v => (kids v).card) hx
    change (∑ v ∈ Y.erase x, (kids v).card) + (kids x).card = ∑ v ∈ Y, (kids v).card at hs
    have hm : (Y.erase x).card ≤ ∑ v ∈ Y.erase x, (kids v).card := by
      calc
        _ = ∑ _v ∈ Y.erase x, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun v hv => hchild v (Finset.mem_of_mem_erase hv))
    rw [Finset.card_erase_of_mem hx] at hm
    have hr : k ≤ (kids x).card := hroot
    omega
  have hc : U.card ≤ Y.card + Z.card := Finset.card_union_le Y Z
  have hp : 0 < Y.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

theorem total_boundary (X : Finset V) (B : Finset V) :
    (∑ x ∈ B, (boundary parent rank decrease X x).card) ≤ X.card := by
  classical
  have heq : (∑ x ∈ B, (boundary parent rank decrease X x).card) =
      ∑ u ∈ X, (B.filter (fun x => strictOwner parent rank decrease X u = some x)).card := by
    simp only [boundary, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [heq]
  calc
    _ ≤ ∑ _u ∈ X, 1 := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
    _ = X.card := by simp

theorem roots_bound (X B : Finset V) (k : ℕ)
    (h : ∀ x ∈ B, k ≤ (boundary parent rank decrease X x).card) : k * B.card ≤ X.card := by
  calc
    _ = ∑ _x ∈ B, k := by simp [mul_comm]
    _ ≤ ∑ x ∈ B, (boundary parent rank decrease X x).card := Finset.sum_le_sum h
    _ ≤ _ := total_boundary parent rank decrease X B
end Paper.RegionBoundary
