import Paper.Preliminaries.OddPathGeometry
namespace Paper.OddPathPower

theorem degree_le_four (n : ℕ) (v : Fin n) : (graph n 3).degree v ≤ 4 := by
  let f : (graph n 3).neighborFinset v → Fin 4 := fun u =>
    ⟨(u.val.val+3-v.val)/2,by
      have h := ((graph n 3).mem_neighborFinset v u.val).mp u.property
      change (v ≠ u.val ∧ v.val ≤ u.val.val+3 ∧ u.val.val ≤ v.val+3) ∧ v.val%2 ≠ u.val.val%2 at h
      omega⟩
  have hi : Function.Injective f := by
    intro u w he
    have hu := ((graph n 3).mem_neighborFinset v u.val).mp u.property
    have hw := ((graph n 3).mem_neighborFinset v w.val).mp w.property
    change (v ≠ u.val ∧ v.val ≤ u.val.val+3 ∧ u.val.val ≤ v.val+3) ∧ v.val%2 ≠ u.val.val%2 at hu
    change (v ≠ w.val ∧ v.val ≤ w.val.val+3 ∧ w.val.val ≤ v.val+3) ∧ v.val%2 ≠ w.val.val%2 at hw
    have hh := congrArg Fin.val he
    dsimp only [f] at hh
    apply Subtype.ext
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,SimpleGraph.card_neighborFinset_eq_degree,Fintype.card_fin] using hc
end Paper.OddPathPower
#print axioms Paper.OddPathPower.degree_le_four
