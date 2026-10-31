import Paper.Preliminaries.OddPathPower
import Paper.TotalDomination.FractionalRepair
namespace Paper.OddPathPower

theorem isolate_free (n : ℕ) (hn : 2 ≤ n) : ∀ v, ((graph n 3).neighborFinset v).Nonempty := by
  intro v
  by_cases hv : v.val=0
  · refine ⟨⟨1,by omega⟩,?_⟩
    apply ((graph n 3).mem_neighborFinset v _).mpr
    change (v ≠ ⟨1,by omega⟩ ∧ v.val ≤ 1+3 ∧ 1 ≤ v.val+3) ∧ v.val%2 ≠ 1%2
    refine ⟨⟨?_,by omega,by omega⟩,by omega⟩
    intro h
    have hh := congrArg Fin.val h
    dsimp only at hh
    omega
  · refine ⟨⟨v.val-1,by omega⟩,?_⟩
    apply ((graph n 3).mem_neighborFinset v _).mpr
    change (v ≠ ⟨v.val-1,by omega⟩ ∧ v.val ≤ (v.val-1)+3 ∧ v.val-1 ≤ v.val+3) ∧ v.val%2 ≠ (v.val-1)%2
    refine ⟨⟨?_,by omega,by omega⟩,by omega⟩
    intro h
    have hh := congrArg Fin.val h
    dsimp only at hh
    omega

theorem degree_lower (n : ℕ) (v : Fin n) (hv : v ∉ PathPowerTotal.boundary n 3) :
    4 ≤ (graph n 3).degree v := by
  have hbound : 3 ≤ v.val ∧ v.val+3 < n := by
    simpa only [PathPowerTotal.boundary,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_lt,not_le] using hv
  let f : Fin 4 → (graph n 3).neighborFinset v := fun i =>
    if hi : i.val < 2 then
      ⟨⟨v.val-(2*i.val+1),by omega⟩,by
        apply ((graph n 3).mem_neighborFinset v _).mpr
        refine ⟨⟨?_,?_,?_⟩,?_⟩
        · intro he;have hh := congrArg Fin.val he; dsimp only at hh; omega
        · dsimp only; omega
        · dsimp only; omega
        · dsimp only; omega⟩
    else
      ⟨⟨v.val+(2*(i.val-2)+1),by omega⟩,by
        apply ((graph n 3).mem_neighborFinset v _).mpr
        refine ⟨⟨?_,?_,?_⟩,?_⟩
        · intro he;have hh := congrArg Fin.val he; dsimp only at hh; omega
        · dsimp only; omega
        · dsimp only; omega
        · dsimp only; omega⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hh := congrArg (fun w : (graph n 3).neighborFinset v => w.val.val) he
    dsimp only [f] at hh
    split_ifs at hh with hi hj hj <;> (try dsimp only at hh) <;> apply Fin.ext <;> omega
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_fin,Fintype.card_coe,SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem total_fractional_bound (n : ℕ) (hn : 2 ≤ n) :
    TotalDomination.FractionalSolver.fractionalNumber (graph n 3) ≤ (n:ℝ)/4+6 := by
  have hh := TotalDomination.FractionalRepair.number_bound (graph n 3) (isolate_free n hn)
    (PathPowerTotal.boundary n 3) 4 (by norm_num)
    (fun v hv => by exact_mod_cast degree_lower n v hv)
  have hb : ((PathPowerTotal.boundary n 3).card:ℝ) ≤ 6 := by exact_mod_cast PathPowerTotal.boundary_card n 3
  change TotalDomination.FractionalSolver.fractionalNumber (graph n 3) ≤ _ at hh
  simp only [Fintype.card_fin] at hh
  linarith
theorem connected (n : ℕ) (hn : 0 < n) : (graph n 3).Connected := by
  have hs : SimpleGraph.pathGraph n ≤ graph n 3 := by
    intro u v ha
    have hh := SimpleGraph.pathGraph_adj.mp ha
    refine ⟨⟨ha.ne,?_,?_⟩,?_⟩ <;> rcases hh with hh | hh <;> omega
  exact SimpleGraph.Connected.mono hs (PathGraphTree.tree n hn).connected

end Paper.OddPathPower
#print axioms Paper.OddPathPower.total_fractional_bound
