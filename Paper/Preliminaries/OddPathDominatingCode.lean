import Paper.Preliminaries.OddPathGeometry
import Paper.Preliminaries.PathPowerDomination
namespace Paper.OddPathPower
open SevenFoundation

def code (n : ℕ) : Finset (Fin n) := PathPowerTotal.boundary n 3 ∪
  Finset.univ.filter (fun v => v.val%5=0)

theorem residue_neighbor (n : ℕ) (v : Fin n) (hv : v ∉ PathPowerTotal.boundary n 3) :
    ∃ u : Fin n, u.val%5=0 ∧ (u=v ∨ (graph n 3).Adj v u) := by
  have hb : 3 ≤ v.val ∧ v.val+3 < n := by
    simpa only [PathPowerTotal.boundary,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_lt,not_le] using hv
  have hm : v.val%5=0 ∨ v.val%5=1 ∨ v.val%5=2 ∨ v.val%5=3 ∨ v.val%5=4 := by omega
  rcases hm with h | h | h | h | h
  · exact ⟨v,h,Or.inl rfl⟩
  · refine ⟨⟨v.val-1,by omega⟩,by dsimp only;omega,Or.inr ?_⟩
    refine ⟨⟨?_,by dsimp only;omega,by dsimp only;omega⟩,by dsimp only;omega⟩
    intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega
  · refine ⟨⟨v.val+3,by omega⟩,by dsimp only;omega,Or.inr ?_⟩
    refine ⟨⟨?_,by dsimp only;omega,by dsimp only;omega⟩,by dsimp only;omega⟩
    intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega
  · refine ⟨⟨v.val-3,by omega⟩,by dsimp only;omega,Or.inr ?_⟩
    refine ⟨⟨?_,by dsimp only;omega,by dsimp only;omega⟩,by dsimp only;omega⟩
    intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega
  · refine ⟨⟨v.val+1,by omega⟩,by dsimp only;omega,Or.inr ?_⟩
    refine ⟨⟨?_,by dsimp only;omega,by dsimp only;omega⟩,by dsimp only;omega⟩
    intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega

theorem code_dominates (n : ℕ) : dominates (graph n 3) (code n) := by
  intro v
  by_cases hv : v ∈ PathPowerTotal.boundary n 3
  · exact subset_covered _ _ (Finset.mem_union_left _ hv)
  · obtain ⟨u,hu,ha⟩ := residue_neighbor n v hv
    refine Finset.mem_biUnion.mpr ⟨u,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩),?_⟩
    rcases ha with he | ha
    · subst u;exact self_mem_closed _ _
    · exact (mem_closed _ v u).mpr (Or.inr ha.symm)

theorem code_card (n : ℕ) : (code n).card ≤ n/5+7 := by
  let S := Finset.univ.filter (fun v : Fin n => v.val%5=0)
  let f : S → Fin (n/5+1) := fun v => ⟨v.val.val/5,by have h:=v.val.isLt;omega⟩
  have hi : Function.Injective f := by
    intro u v h
    have hh := congrArg Fin.val h
    have hu := (Finset.mem_filter.mp u.property).2
    have hv := (Finset.mem_filter.mp v.property).2
    dsimp only [f] at hh
    apply Subtype.ext
    apply Fin.ext
    omega
  have hS : S.card ≤ n/5+1 := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hi
  have hB := PathPowerTotal.boundary_card n 3
  have hU := Finset.card_union_le (PathPowerTotal.boundary n 3) S
  change (code n).card ≤ _ at hU
  omega

theorem domination_number_bound (n : ℕ) : ((graph n 3).dominationNumber:ℝ) ≤ (n:ℝ)/5+7 := by
  have hdom : (graph n 3).IsDominatingSetFinset (code n) := by
    intro v
    obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp (code_dominates n v)
    rcases (mem_closed (graph n 3) v u).mp hvu with he | ha
    · exact Or.inl (he ▸ hu)
    · exact Or.inr ⟨u,hu,ha.symm⟩
  have hc := hdom.dominationNumber_le
  have hcR : ((graph n 3).dominationNumber:ℝ) ≤ (code n).card := by exact_mod_cast hc
  have hcode : ((code n).card:ℝ) ≤ (n/5:ℕ)+7 := by exact_mod_cast code_card n
  have hn : ((n/5:ℕ):ℝ) ≤ (n:ℝ)/5 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<5)).mpr
    exact_mod_cast Nat.div_mul_le_self n 5
  linarith
end Paper.OddPathPower
#print axioms Paper.OddPathPower.domination_number_bound
