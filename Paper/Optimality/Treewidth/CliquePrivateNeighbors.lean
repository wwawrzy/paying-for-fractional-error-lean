import Paper.Optimality.Treewidth.CliqueEightComplement

/-! Two vertices with the same sole neighbor in a maximum independent
triple must be adjacent, or replacing that neighbor enlarges the triple. -/
namespace Paper.CliquePrivateNeighbors
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem independent_insert (T : Finset V) (hT : H.IsIndepSet (T : Set V))
    (z : V) (hz : ∀ w ∈ T, ¬H.Adj z w) : H.IsIndepSet ((insert z T : Finset V) : Set V) := by
  rw [Finset.coe_insert]
  exact hT.insert_of_symmetric (fun _ _ hn h => hn h.symm) (fun w hw _ => hz w hw)

theorem adjacent (D : Finset V) (hD : D.card = 3) (hind : H.IsIndepSet (D : Set V))
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 3)
    (d : V) (hd : d ∈ D) (x y : V) (hx : x ∉ D) (hy : y ∉ D) (hne : x ≠ y)
    (hxonly : ∀ w ∈ D, H.Adj x w → w = d)
    (hyonly : ∀ w ∈ D, H.Adj y w → w = d) : H.Adj x y := by
  classical
  by_contra hxy
  have herase : H.IsIndepSet ((D.erase d : Finset V) : Set V) := by
    intro a ha b hb hab
    exact hind (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
  have hynot : ∀ w ∈ D.erase d, ¬H.Adj y w := by
    intro w hw hyw
    exact (Finset.mem_erase.mp hw).1 (hyonly w (Finset.mem_of_mem_erase hw) hyw)
  have hi := independent_insert H (D.erase d) herase y hynot
  have hxnot : ∀ w ∈ insert y (D.erase d), ¬H.Adj x w := by
    intro w hw hxw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hxy hxw
    · exact (Finset.mem_erase.mp hw).1 (hxonly w (Finset.mem_of_mem_erase hw) hxw)
  have hj := independent_insert H (insert y (D.erase d)) hi x hxnot
  have hbound := hsmall (insert x (insert y (D.erase d))) hj
  have hxins : x ∉ insert y (D.erase d) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨hne, fun hh => hx hh.2⟩
  have hyerase : y ∉ D.erase d := fun hh => hy (Finset.mem_of_mem_erase hh)
  rw [Finset.card_insert_of_notMem hxins, Finset.card_insert_of_notMem hyerase,
    Finset.card_erase_of_mem hd, hD] at hbound
  omega

end Paper.CliquePrivateNeighbors
#print axioms Paper.CliquePrivateNeighbors.adjacent
