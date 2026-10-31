import Paper.Solver.LocalSearch.SparseFractional

/-! Extra inactive role entries contribute exactly zero; absent entries
also decode as zero. No inactive communication invariant is assumed. -/
namespace Paper.SparseFractionalZero
open BroadcastModel
variable {Role A : Type} [LinearOrder Role]

theorem lookup_none (xs : List (Role × A)) (r : Role) (hr : r ∉ TaggedDictionary.keys xs) :
    TaggedDictionary.lookup xs r = none := by
  rw [TaggedDictionary.lookup, Option.map_eq_none_iff, List.find?_eq_none]
  intro p hp he
  exact hr ((TaggedDictionary.mem_keys xs r).mpr ⟨p, hp, of_decide_eq_true he⟩)

variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem scalar_inactive {b : ℕ} (C : BitCode V b) (D a B q M : ℕ)
    (s : V → FractionalSearch.Input V B) (v : V) (hv : (s v).active = false) :
    ((FractionalSearch.program C D a B q M).run G s v).val = 0 := by
  rw [FractionalSearch.run_program]
  simp only [hv, Bool.false_eq_true, ↓reduceIte, Fin.val_zero]

theorem inactive {b c : ℕ} (C : BitCode V b) (CR : BitCode Role c) (K D a B q M : ℕ)
    (xs : V → List (Role × FractionalSearch.Input V B))
    (hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ K)
    (s : V → Role → FractionalSearch.Input V B) (hs : ∀ v, TaggedDictionary.Consistent (s v) (xs v))
    (v : V) (r : Role) (hv : (s v r).active = false) :
    ((TaggedDictionary.lookup (((SparseFractional.program C CR K D a B q M).run G xs v).1) r).getD 0).val = 0 := by
  by_cases hr : r ∈ TaggedDictionary.keys (xs v)
  · rw [SparseFractional.key_run G C CR K D a B q M xs hK s hs v r hr]
    exact scalar_inactive _ C D a B q M (fun u => s u r) v hv
  · have hn : r ∉ TaggedDictionary.keys (((SparseFractional.program C CR K D a B q M).run G xs v).1) := by
      dsimp only [SparseFractional.program]
      rw [SparseParallelCorrect.execute_keys G CR K (FractionalSearch.program C D a B q M) xs v]
      exact hr
    rw [lookup_none _ r hn]
    rfl
end Paper.SparseFractionalZero
