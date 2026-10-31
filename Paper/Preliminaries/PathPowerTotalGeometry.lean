import Paper.Preliminaries.PathPowerCounting

namespace Paper.PathPowerTotal
open SevenFoundation PathPowerTreewidth

def boundary (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val < t ∨ n ≤ v.val+t)

theorem isolate_free (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) :
    ∀ v, ((graph n t).neighborFinset v).Nonempty := by
  intro v
  by_cases hv : v.val = 0
  · refine ⟨⟨1,by (try dsimp only); omega⟩,?_⟩
    apply ((graph n t).mem_neighborFinset v _).mpr
    refine ⟨?_,by (try dsimp only); omega,by (try dsimp only); omega⟩
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_mk] at he
    omega
  · refine ⟨⟨v.val-1,by (try dsimp only); omega⟩,?_⟩
    apply ((graph n t).mem_neighborFinset v _).mpr
    refine ⟨?_,by (try dsimp only); omega,by (try dsimp only); omega⟩
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_mk] at hh
    omega

theorem degree_lower (n t : ℕ) (v : Fin n) (hv : v ∉ boundary n t) :
    2*t ≤ (graph n t).degree v := by
  have hv' : t ≤ v.val ∧ v.val+t < n := by
    simpa only [boundary,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_lt,not_le] using hv
  let f : Fin (2*t) → (graph n t).neighborFinset v := fun i =>
    if hi : i.val < t then
      ⟨⟨v.val-i.val-1,by (try dsimp only); omega⟩,by
        apply ((graph n t).mem_neighborFinset v _).mpr
        refine ⟨?_,by (try dsimp only); omega,by (try dsimp only); omega⟩
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_mk] at hh
        omega⟩
    else
      ⟨⟨v.val+(i.val-t+1),by (try dsimp only); omega⟩,by
        apply ((graph n t).mem_neighborFinset v _).mpr
        refine ⟨?_,by (try dsimp only); omega,by (try dsimp only); omega⟩
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_mk] at hh
        omega⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hh := congrArg (fun w : (graph n t).neighborFinset v => w.val.val) he
    dsimp only [f] at hh
    split_ifs at hh with hi hj hj <;> (try dsimp only at hh) <;> apply Fin.ext <;> omega
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_fin,Fintype.card_coe,SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem boundary_card (n t : ℕ) : (boundary n t).card ≤ 2*t := by
  let L := Finset.univ.filter (fun v : Fin n => v.val < t)
  let R := Finset.univ.filter (fun v : Fin n => n ≤ v.val+t)
  have hL : L.card ≤ t := by
    let f : L → Fin t := fun v => ⟨v.val.val,(Finset.mem_filter.mp v.property).2⟩
    have hi : Function.Injective f := by
      intro u v h
      have hh := congrArg Fin.val h
      change u.val.val = v.val.val at hh
      exact Subtype.ext (Fin.ext hh)
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hi
  have hR : R.card ≤ t := by
    let f : R → Fin t := fun v => ⟨n-1-v.val.val,by
      have h := (Finset.mem_filter.mp v.property).2
      have hn := v.val.isLt
      omega⟩
    have hi : Function.Injective f := by
      intro u v h
      apply Subtype.ext
      apply Fin.ext
      have hh := congrArg Fin.val h
      have hu := u.val.isLt
      have hv := v.val.isLt
      dsimp only [f] at hh
      omega
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hi
  have he : boundary n t = L∪R := by
    ext v
    simp only [boundary,L,R,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  rw [he]
  exact (Finset.card_union_le L R).trans (by (try dsimp only); omega)

end Paper.PathPowerTotal
#print axioms Paper.PathPowerTotal.degree_lower
