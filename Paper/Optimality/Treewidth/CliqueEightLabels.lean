import Paper.Optimality.Treewidth.CliqueFourMatchings

/-! Label an actual four-plus-four partition in the order used by the
two-contraction minor model. The matching permutation is finite data;
all graph vertices and their identifiers are retained by equivalences. -/
namespace Paper.CliqueEightLabels

open CliqueFourMatchings

private def permFun (k : Fin 3) : Fin 8 → Fin 8 :=
  ![![4, 6, 0, 1, 2, 3, 5, 7], ![4, 5, 0, 1, 2, 3, 6, 7],
    ![4, 5, 0, 1, 2, 3, 7, 6]] k

private theorem perm_bijective : ∀ k, Function.Bijective (permFun k) := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide

private noncomputable def permutation (k : Fin 3) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (permFun k) (perm_bijective k)

variable {V : Type} [Fintype V] [DecidableEq V]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

noncomputable def base : Fin 8 ≃ V :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm.trans
    ((Equiv.sumCongr eS (eR.trans (Equiv.setCongr (Finset.coe_compl S)))).trans
      (Equiv.Set.sumCompl (S : Set V)))

theorem base_left (a : Fin 4) : base S eS eR (Fin.castAdd 4 a) = (eS a).val := by
  fin_cases a <;> rfl

theorem base_right (a : Fin 4) : base S eS eR (Fin.natAdd 4 a) = (eR a).val := by
  fin_cases a <;> rfl

noncomputable def labeling (k : Fin 3) : Fin 8 ≃ V :=
  (permutation k).trans (base S eS eR)

theorem zero (k : Fin 3) : labeling S eS eR k 0 = (eR (ends k).1.1).val := by
  change base S eS eR (permFun k 0) = _
  have hi : permFun k 0 = Fin.natAdd 4 (ends k).1.1 := by fin_cases k <;> rfl
  rw [hi]
  exact base_right S eS eR _

theorem six (k : Fin 3) : labeling S eS eR k 6 = (eR (ends k).1.2).val := by
  change base S eS eR (permFun k 6) = _
  have hi : permFun k 6 = Fin.natAdd 4 (ends k).1.2 := by fin_cases k <;> rfl
  rw [hi]
  exact base_right S eS eR _

theorem one (k : Fin 3) : labeling S eS eR k 1 = (eR (ends k).2.1).val := by
  change base S eS eR (permFun k 1) = _
  have hi : permFun k 1 = Fin.natAdd 4 (ends k).2.1 := by fin_cases k <;> rfl
  rw [hi]
  exact base_right S eS eR _

theorem seven (k : Fin 3) : labeling S eS eR k 7 = (eR (ends k).2.2).val := by
  change base S eS eR (permFun k 7) = _
  have hi : permFun k 7 = Fin.natAdd 4 (ends k).2.2 := by fin_cases k <;> rfl
  rw [hi]
  exact base_right S eS eR _

theorem row (k : Fin 3) (a : Fin 4) :
    labeling S eS eR k ⟨a.val + 2, by omega⟩ = (eS a).val := by
  change base S eS eR (permFun k ⟨a.val + 2, by omega⟩) = _
  have hi : permFun k ⟨a.val + 2, by omega⟩ = Fin.castAdd 4 a := by
    have hall : ∀ k : Fin 3, ∀ a : Fin 4,
        permFun k ⟨a.val + 2, by omega⟩ = Fin.castAdd 4 a := by decide
    exact hall k a
  rw [hi]
  exact base_left S eS eR _

end Paper.CliqueEightLabels

#print axioms Paper.CliqueEightLabels.base_left
#print axioms Paper.CliqueEightLabels.base_right
#print axioms Paper.CliqueEightLabels.zero
#print axioms Paper.CliqueEightLabels.six
#print axioms Paper.CliqueEightLabels.one
#print axioms Paper.CliqueEightLabels.seven
#print axioms Paper.CliqueEightLabels.row
