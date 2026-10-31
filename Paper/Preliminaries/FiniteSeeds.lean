import Paper.Preliminaries.FiniteIteration

/-! Explicit equivalence between fresh finite stage products and one finite
function of stage indices. This will transfer independent priority sources. -/
namespace Paper.FiniteSeeds
universe u
variable (Ω : Type u)

def toFn : (n : ℕ) → FiniteIteration.Seeds Ω n → Fin n → Ω
  | 0, _ => Fin.elim0
  | n + 1, ω => Fin.cases ω.1 (toFn n ω.2)

def ofFn : (n : ℕ) → (Fin n → Ω) → FiniteIteration.Seeds Ω n
  | 0, _ => PUnit.unit
  | n + 1, ω => (ω 0, ofFn n (fun i => ω i.succ))

theorem of_to (n : ℕ) (ω : FiniteIteration.Seeds Ω n) : ofFn Ω n (toFn Ω n ω) = ω := by
  induction n with
  | zero =>
    change PUnit.unit = ω
    exact Subsingleton.elim _ _
  | succ n ih =>
    change (ω.1, ofFn Ω n (fun i => Fin.cases ω.1 (toFn Ω n ω.2) i.succ)) = ω
    simp only [Fin.cases_succ, ih]
    exact Prod.eta ω

theorem to_of (n : ℕ) (ω : Fin n → Ω) : toFn Ω n (ofFn Ω n ω) = ω := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change toFn Ω n (ofFn Ω n (fun i => ω i.succ)) j = ω j.succ
      exact congrFun (ih (fun i => ω i.succ)) j

def equiv (n : ℕ) : FiniteIteration.Seeds Ω n ≃ (Fin n → Ω) where
  toFun := toFn Ω n
  invFun := ofFn Ω n
  left_inv := of_to Ω n
  right_inv := to_of Ω n
end Paper.FiniteSeeds
