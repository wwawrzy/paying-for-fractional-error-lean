import Paper.TotalDomination.PathPowerFractional
import GraphTheory.SimpleGraph.Domination.Total

/-! Two consecutive selected residues in each period four, with one final
repair, form a total dominating set of size at most n/2+3. -/
namespace Paper.TotalDomination.PathTotalIntegral
open PathPowerTreewidth

def code (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun v => v.val%4 = 1 ∨ v.val%4 = 2)

def selection (n : ℕ) (hn : 2 ≤ n) : Finset (Fin n) := code n ∪ {⟨n-2,by omega⟩}

theorem total_dominates (n : ℕ) (hn : 2 ≤ n) :
    (graph n 1).IsTotalDominatingSetFinset (selection n hn) := by
  intro r
  by_cases hlow : r.val%4 = 0 ∨ r.val%4 = 1
  · by_cases hnext : r.val+1 < n
    · let v : Fin n := ⟨r.val+1,hnext⟩
      have hv : v ∈ code n := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        dsimp [v]
        omega
      refine ⟨v,Finset.mem_union_left _ hv,?_⟩
      change r ≠ v ∧ r.val ≤ v.val+1 ∧ v.val ≤ r.val+1
      refine ⟨?_,by dsimp [v];omega,by dsimp [v];omega⟩
      intro h
      have he := congrArg Fin.val h
      dsimp [v] at he
      omega
    · let v : Fin n := ⟨n-2,by omega⟩
      refine ⟨v,Finset.mem_union_right _ (Finset.mem_singleton_self _),?_⟩
      change r ≠ v ∧ r.val ≤ v.val+1 ∧ v.val ≤ r.val+1
      refine ⟨?_,by dsimp [v];omega,by dsimp [v];omega⟩
      intro h
      have he := congrArg Fin.val h
      dsimp [v] at he
      omega
  · let v : Fin n := ⟨r.val-1,by omega⟩
    have hv : v ∈ code n := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      dsimp [v]
      omega
    refine ⟨v,Finset.mem_union_left _ hv,?_⟩
    change r ≠ v ∧ r.val ≤ v.val+1 ∧ v.val ≤ r.val+1
    refine ⟨?_,by dsimp [v];omega,by dsimp [v];omega⟩
    intro h
    have he := congrArg Fin.val h
    dsimp [v] at he
    omega

theorem code_card (n : ℕ) : (code n).card ≤ 2*(n/4+1) := by
  let f : code n → Fin (2*(n/4+1)) := fun v =>
    ⟨2*(v.val.val/4)+(if v.val.val%4 = 2 then 1 else 0),by
      have hv := v.val.isLt
      split_ifs <;> omega⟩
  have hinj : Function.Injective f := by
    intro u v h
    have hu := (Finset.mem_filter.mp u.property).2
    have hv := (Finset.mem_filter.mp v.property).2
    have he := congrArg Fin.val h
    dsimp [f] at he
    split_ifs at he <;> apply Subtype.ext <;> apply Fin.ext <;> omega
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hinj

theorem number_bound (n : ℕ) (hn : 2 ≤ n) :
    ((graph n 1).totalDominationNumber:ℝ) ≤ (n:ℝ)/2+3 := by
  have hsel := (total_dominates n hn).totalDominationNumber_le
  have hcard : (selection n hn).card ≤ 2*(n/4+1)+1 := by
    exact (Finset.card_union_le _ _).trans (by simpa only [Finset.card_singleton] using Nat.add_le_add_right (code_card n) 1)
  have hnat : (graph n 1).totalDominationNumber ≤ 2*(n/4+1)+1 := hsel.trans hcard
  have hR : ((graph n 1).totalDominationNumber:ℝ) ≤ 2*((n/4:ℕ):ℝ)+3 := by exact_mod_cast hnat
  have hq : 4*(n/4) ≤ n := by omega
  have hqR : 4*((n/4:ℕ):ℝ) ≤ n := by exact_mod_cast hq
  linarith

end Paper.TotalDomination.PathTotalIntegral
#print axioms Paper.TotalDomination.PathTotalIntegral.number_bound
