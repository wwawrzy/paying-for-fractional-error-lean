import Paper.Optimality.Treewidth.CliqueEightLabeling
import Paper.Optimality.Treewidth.CliqueEightResidualTemplates
namespace Paper.CliqueEightResidualRows
open SimpleGraph
variable (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
theorem degree_sum (i : Fin 8) : H.degree i = ∑ j : Fin 8, if H.Adj i j then 1 else 0 := by
  classical
  rw [← H.card_neighborFinset_eq_degree]
  simp only [Finset.sum_boole]
  congr 1
  ext j
  simp
theorem rows (hd : ∀ i, H.degree i ≤ 2) (he : H.edgeFinset.card = 6)
    (hroot : ∀ j, H.Adj 0 j ↔ j = 1 ∨ j = 2)
    (hN : ∀ i j : Fin 8, 3 ≤ i.val → 3 ≤ j.val →
      (H.Adj i j ↔ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5))) :
    ¬H.Adj 1 2 ∧
    (∑ k : Fin 5, if H.Adj 1 ⟨k.val+3,by omega⟩ then 1 else 0) = 1 ∧
    (∑ k : Fin 5, if H.Adj 2 ⟨k.val+3,by omega⟩ then 1 else 0) = 1 := by
  classical
  have h10 : H.Adj 1 0 := ((hroot 1).mpr (Or.inl rfl)).symm
  have hs := H.sum_degrees_eq_twice_card_edges
  rw [he] at hs
  have h1 := hd 1
  have h2 := hd 2
  simp only [degree_sum,Fin.sum_univ_succ] at hs h1 h2
  simp only [Fin.sum_univ_succ]
  norm_num at hs h1 h2 ⊢
  by_cases h12 : H.Adj 1 2
  · simp [h10,hroot,hN,H.adj_comm,h12,show H.Adj 2 1 ↔ H.Adj 1 2 from H.adj_comm 2 1, show H.Adj 2 0 ↔ H.Adj 0 2 from H.adj_comm 2 0] at hs h1 h2
    ring_nf at hs h1 h2
    omega
  · refine ⟨h12,?_,?_⟩ <;>
      simp [h10,hroot,hN,H.adj_comm,h12,show H.Adj 2 1 ↔ H.Adj 1 2 from H.adj_comm 2 1, show H.Adj 2 0 ↔ H.Adj 0 2 from H.adj_comm 2 0] at hs h1 h2 ⊢ <;> ring_nf at hs h1 h2 ⊢ <;> omega
theorem row_unique (i : Fin 8)
    (hs : (∑ k : Fin 5, if H.Adj i ⟨k.val+3,by omega⟩ then 1 else 0) = 1) :
    ∃ a : Fin 5, ∀ k : Fin 5, H.Adj i ⟨k.val+3,by omega⟩ ↔ k = a := by
  classical
  have hc : (Finset.univ.filter (fun k : Fin 5 => H.Adj i ⟨k.val+3,by omega⟩)).card = 1 := by
    simpa only [Finset.sum_boole] using hs
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a,?_⟩
  intro k
  have hm := Finset.ext_iff.mp ha k
  simpa using hm
end Paper.CliqueEightResidualRows


namespace Paper.CliqueEightResidualRows
open SimpleGraph
set_option maxHeartbeats 2000000
variable (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
theorem template (hd : ∀ i, H.degree i ≤ 2) (he : H.edgeFinset.card = 6)
    (hroot : ∀ j, H.Adj 0 j ↔ j = 1 ∨ j = 2)
    (hN : ∀ i j : Fin 8, 3 ≤ i.val → 3 ≤ j.val →
      (H.Adj i j ↔ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5))) :
    ∃ a b : Fin 5, H = (CliqueEightResidualTemplates.graph a b)ᶜ := by
  classical
  obtain ⟨h12,h1,h2⟩ := rows H hd he hroot hN
  obtain ⟨a,ha⟩ := row_unique H 1 h1
  obtain ⟨b,hb⟩ := row_unique H 2 h2
  have hr1 : ∀ j : Fin 8, 3 ≤ j.val → (H.Adj 1 j ↔ j.val = a.val+3) := by
    intro j hj
    let k : Fin 5 := ⟨j.val-3,by omega⟩
    have hk : (⟨k.val+3,by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp [k]; omega
    have hh := ha k
    rw [hk] at hh
    apply hh.trans
    change k = _ ↔ _
    rw [Fin.ext_iff]
    dsimp [k]
    omega
  have hr2 : ∀ j : Fin 8, 3 ≤ j.val → (H.Adj 2 j ↔ j.val = b.val+3) := by
    intro j hj
    let k : Fin 5 := ⟨j.val-3,by omega⟩
    have hk : (⟨k.val+3,by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp [k]; omega
    have hh := hb k
    rw [hk] at hh
    apply hh.trans
    change k = _ ↔ _
    rw [Fin.ext_iff]
    dsimp [k]
    omega
  refine ⟨a,b,?_⟩
  ext i j
  change H.Adj i j ↔ (i ≠ j ∧ ¬(i ≠ j ∧ s(i,j) ∉ CliqueEightResidualTemplates.missing a b))
  simp only [CliqueEightResidualTemplates.missing,Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff]
  fin_cases i <;> fin_cases j <;>
    simp [hroot,hN,hr1,hr2,H.adj_comm,h12] <;> (try simp only [Fin.ext_iff]) <;> norm_num <;> (try omega)
  all_goals exact ((hroot 1).mpr (Or.inl rfl)).symm
end Paper.CliqueEightResidualRows
