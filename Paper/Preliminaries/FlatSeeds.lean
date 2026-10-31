import Paper.Preliminaries.FiniteSeeds
import Paper.Preliminaries.UniformProjection

/-! Stage-by-coordinate finite sources, explicitly equivalent to fresh
products. Injective local indexing preserves exact finite averages. -/
namespace Paper.FlatSeeds
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I A B : Type*}

def equiv (I B : Type*) (n : ℕ) : FiniteIteration.Seeds (I → B) n ≃ ((Fin n × I) → B) :=
  (FiniteSeeds.equiv (I → B) n).trans (Equiv.curry (Fin n) I B).symm

def seed (n : ℕ) (ω : (Fin n × I) → B) : FiniteIteration.Seeds (I → B) n := (equiv I B n).symm ω

def coordinate (n : ℕ) (e : I → A) : Fin n × I → Fin n × A := fun x => (x.1, e x.2)

theorem coordinate_injective (n : ℕ) (e : I → A) (hinj : Function.Injective e) :
    Function.Injective (coordinate n e) := by
  intro x y he
  exact Prod.ext (congrArg (fun z : Fin n × A => z.1) he)
    (hinj (congrArg (fun z : Fin n × A => z.2) he))

theorem sum_seed [Fintype I] [Fintype B] [DecidableEq I] (n : ℕ) (f : FiniteIteration.Seeds (I → B) n → ℝ) :
    (∑ ω : (Fin n × I) → B, f (seed n ω)) = ∑ σ : FiniteIteration.Seeds (I → B) n, f σ :=
  Fintype.sum_equiv (equiv I B n).symm _ _ (fun _ => rfl)

theorem card_source [Fintype I] [Fintype B] [DecidableEq I] (n : ℕ) :
    Fintype.card ((Fin n × I) → B) = Fintype.card (I → B) ^ n :=
  (Fintype.card_congr (equiv I B n).symm).trans (FiniteIteration.card_seeds (I → B) n)

end Paper.FlatSeeds
