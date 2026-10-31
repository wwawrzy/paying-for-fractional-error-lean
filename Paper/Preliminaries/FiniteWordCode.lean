import Paper.Partitions.Local.PriorityTableCode

/-! Explicit computable numbering of fixed finite words. No abstract
Fintype enumeration or noncomputable finite equivalence is used. -/
namespace Paper.FiniteWordCode
open BroadcastModel

def split (Q n : ℕ) : (Fin (n + 1) → Fin Q) ≃ Fin Q × (Fin n → Fin Q) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

def words (Q : ℕ) : (n : ℕ) → (Fin n → Fin Q) ≃ Fin (Q ^ n)
  | 0 => {
      toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun f => by funext i; exact Fin.elim0 i
      right_inv := fun i => Fin.ext (by
        change 0 = i.val
        have hi := i.isLt
        simp only [pow_zero] at hi
        omega) }
  | n + 1 => (split Q n).trans ((Equiv.prodCongr (Equiv.refl _) (words Q n)).trans
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_comm]))))

def code (Q n : ℕ) : BitCode (Fin n → Fin Q) (Q ^ n) :=
  PacketCode.transport (SmallNumberCode.code (Q ^ n)) (words Q n).symm

end Paper.FiniteWordCode
