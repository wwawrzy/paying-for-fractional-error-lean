import Paper.Preliminaries.IntervalMinorModel

namespace Paper.IntervalBiclique
open IntervalMinorModel
abbrev A := Sum (Fin 3) (Fin 3)

/-- Every triple of real/integer positions can be put in increasing order. -/
theorem order_three (f : Fin 3 → ℤ) :
    ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ f i ≤ f j ∧ f j ≤ f k := by
  by_cases h01 : f 0 ≤ f 1
  · by_cases h12 : f 1 ≤ f 2
    · exact ⟨0, 1, 2, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : f 0 ≤ f 2
      · exact ⟨0, 2, 1, by decide, by decide, by decide, h02, by omega⟩
      · exact ⟨2, 0, 1, by decide, by decide, by decide, by omega, h01⟩
  · by_cases h02 : f 0 ≤ f 2
    · exact ⟨1, 0, 2, by decide, by decide, by decide, by omega, h02⟩
    · by_cases h12 : f 1 ≤ f 2
      · exact ⟨1, 2, 0, by decide, by decide, by decide, h12, by omega⟩
      · exact ⟨2, 1, 0, by decide, by decide, by decide, by omega, by omega⟩

variable (M : Model A)

def leftLow : ℤ := max (M.low (.inl 0)) (max (M.low (.inl 1)) (M.low (.inl 2)))
def leftHigh : ℤ := min (M.high (.inl 0)) (min (M.high (.inl 1)) (M.high (.inl 2)))

theorem low_left (i : Fin 3) : M.low (.inl i) ≤ leftLow M := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> unfold leftLow <;> omega
theorem high_left (i : Fin 3) : leftHigh M ≤ M.high (.inl i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> unfold leftHigh <;> omega

def Cross : Prop := ∀ i j : Fin 3,
  M.low (.inl i) ≤ M.high (.inr j) ∧ M.low (.inr j) ≤ M.high (.inl i)

theorem right_meets_core (hc : Cross M) (j : Fin 3) :
    M.low (.inr j) ≤ leftHigh M ∧ leftLow M ≤ M.high (.inr j) := by
  have h0 := hc 0 j
  have h1 := hc 1 j
  have h2 := hc 2 j
  unfold leftHigh leftLow
  omega

/-- Two right intervals cannot overlap the common interval of three left ones. -/
theorem right_disjoint (hc : Cross M) (hcore : leftLow M ≤ leftHigh M)
    (i j : Fin 3) (hij : i ≠ j) :
    M.high (.inr i) < M.low (.inr j) ∨ M.high (.inr j) < M.low (.inr i) := by
  by_contra hn
  push Not at hn
  let k := max (leftLow M) (max (M.low (.inr i)) (M.low (.inr j)))
  have hi := right_meets_core M hc i
  have hj := right_meets_core M hc j
  have hiself := M.low_le_high (.inr i)
  have hjself := M.low_le_high (.inr j)
  have hk : leftLow M ≤ k ∧ k ≤ leftHigh M ∧
      M.low (.inr i) ≤ k ∧ k ≤ M.high (.inr i) ∧
      M.low (.inr j) ≤ k ∧ k ≤ M.high (.inr j) := by dsimp [k]; omega
  let F : Finset A := {.inl 0, .inl 1, .inl 2, .inr i, .inr j}
  have hcard : F.card = 5 := by simp [F, hij]
  have hsub : F ⊆ M.bag k := by
    intro x hx
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(low_left M 0).trans hk.1, hk.2.1.trans (high_left M 0)⟩
    · exact ⟨(low_left M 1).trans hk.1, hk.2.1.trans (high_left M 1)⟩
    · exact ⟨(low_left M 2).trans hk.1, hk.2.1.trans (high_left M 2)⟩
    · exact ⟨hk.2.2.1, hk.2.2.2.1⟩
    · exact ⟨hk.2.2.2.2.1, hk.2.2.2.2.2⟩
  have hh := (Finset.card_le_card hsub).trans (M.bag_card k)
  omega

/-- A left branch avoids the three positions surrounding a right-branch point. -/
theorem missing_left (u : ℤ) (j : Fin 3) (hu : u ∈ M.pieces (.inr j)) :
    ∃ i : Fin 3, ∀ z ∈ M.pieces (.inl i), z < u-1 ∨ u+1 < z := by
  classical
  by_contra hn
  push Not at hn
  have hw : ∀ i : Fin 3, ∃ z ∈ M.pieces (.inl i), u-1 ≤ z ∧ z ≤ u+1 := by
    intro i
    obtain ⟨z, hz, hL, hR⟩ := hn i
    exact ⟨z, hz, by omega, by omega⟩
  let z (i : Fin 3) := (hw i).choose
  have hz i := (hw i).choose_spec
  have hne (i : Fin 3) : z i ≠ u := by
    intro he
    exact Finset.disjoint_left.mp (M.disjoint (.inl i) (.inr j) (by simp)) (he ▸ (hz i).1) hu
  let f : Fin 3 → Fin 2 := fun i => if z i < u then 0 else 1
  have hf : Function.Injective f := by
    intro i k he
    have hi := hz i
    have hk := hz k
    change z i ∈ M.pieces (.inl i) ∧ u-1 ≤ z i ∧ z i ≤ u+1 at hi
    change z k ∈ M.pieces (.inl k) ∧ u-1 ≤ z k ∧ z k ≤ u+1 at hk
    have hui := hne i
    have huk := hne k
    have heq : z i = z k := by
      have hv := congrArg Fin.val he
      by_cases hi' : z i < u <;> by_cases hk' : z k < u <;>
        simp only [f, hi', hk', if_true, if_false] at hv <;> omega
    by_contra hik
    exact Finset.disjoint_left.mp (M.disjoint (.inl i) (.inl k) (by simpa using hik)) hi.1 (heq.symm ▸ hk.1)
  have hc := Fintype.card_le_of_injective f hf
  norm_num at hc

/-- Three disjoint right intervals force a middle one wholly inside the
common core. Two consecutive bags then contradict branch-set connectivity. -/
theorem no_common_left (hc : Cross M) (hcore : leftLow M ≤ leftHigh M) : False := by
  obtain ⟨i, j, k, hij, hjk, hik, hlowij, hlowjk⟩ := order_three (fun j => M.low (.inr j))
  have hij' : M.high (.inr i) < M.low (.inr j) := by
    rcases right_disjoint M hc hcore i j hij with h | h
    · exact h
    · have hh := M.low_le_high (.inr j); omega
  have hjk' : M.high (.inr j) < M.low (.inr k) := by
    rcases right_disjoint M hc hcore j k hjk with h | h
    · exact h
    · have hh := M.low_le_high (.inr k); omega
  have hi := right_meets_core M hc i
  have hk := right_meets_core M hc k
  have hinside : leftLow M ≤ M.low (.inr j) ∧ M.high (.inr j) ≤ leftHigh M := by omega
  obtain ⟨u, hu⟩ := M.nonempty (.inr j)
  have huB := M.point_bounds hu
  obtain ⟨a, ha⟩ := missing_left M u j hu
  have hwin1 : leftLow M ≤ u-2 ∧ u-2 ≤ leftHigh M := by omega
  have hwin2 : leftLow M ≤ u-1 ∧ u-1 ≤ leftHigh M := by omega
  obtain ⟨x, hx, hxL, hxR⟩ := M.meets_bag (.inl a) (u-2)
    ((low_left M a).trans hwin1.1) (hwin1.2.trans (high_left M a))
  obtain ⟨y, hy, hyL, hyR⟩ := M.meets_bag (.inl a) (u-1)
    ((low_left M a).trans hwin2.1) (hwin2.2.trans (high_left M a))
  have hax := ha x hx
  have hay := ha y hy
  have hxval : x = u-2 := by omega
  have hyval : y = u+2 := by omega
  obtain ⟨z, hz, hzL, hzR⟩ := M.gap (.inl a) x hx y hy (u-1) (by omega) (by omega)
  have haz := ha z hz
  omega

/-- Six disjoint step-three connected sets cannot realize all nine cross
adjacencies, even when arbitrary extra within-side edges are permitted. -/
theorem no_cross (hc : Cross M) : False := by
  by_cases hleft : leftLow M ≤ leftHigh M
  · exact no_common_left M hc hleft
  let e := Equiv.sumComm (Fin 3) (Fin 3)
  let N := M.comap e e.injective
  have hcN : Cross N := by
    intro i j
    exact ⟨(hc j i).2, (hc j i).1⟩
  have h00 := hc 0 0
  have h01 := hc 0 1
  have h02 := hc 0 2
  have h10 := hc 1 0
  have h11 := hc 1 1
  have h12 := hc 1 2
  have h20 := hc 2 0
  have h21 := hc 2 1
  have h22 := hc 2 2
  have hNL : leftLow N ≤ leftHigh M := by
    change max (M.low (.inr 0)) (max (M.low (.inr 1)) (M.low (.inr 2))) ≤
      min (M.high (.inl 0)) (min (M.high (.inl 1)) (M.high (.inl 2)))
    omega
  have hNR : leftLow M ≤ leftHigh N := by
    change max (M.low (.inl 0)) (max (M.low (.inl 1)) (M.low (.inl 2))) ≤
      min (M.high (.inr 0)) (min (M.high (.inr 1)) (M.high (.inr 2)))
    omega
  exact no_common_left N hcN (by omega)

end Paper.IntervalBiclique
