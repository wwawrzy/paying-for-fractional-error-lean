import Paper.Partitions.Local.PriorityPartitionBroadcast
import Paper.Preliminaries.SmallNumberCode

/-! Fully computational codec for the fixed finite priority table.
Boolean masks are explicitly enumerated by a recursive finite equivalence. -/
namespace Paper.PriorityTableCode
open BroadcastModel

def split (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

def masks : (n : ℕ) → (Fin n → Bool) ≃ Fin (2 ^ n)
  | 0 => {
      toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun f => by funext i; exact Fin.elim0 i
      right_inv := fun i => Fin.ext (by have hi := i.isLt; simp only [pow_zero] at hi; omega) }
  | n + 1 =>
    (split n).trans ((Equiv.prodCongr finTwoEquiv.symm (masks n)).trans
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_comm]))))

def tableEquiv (B n Q : ℕ) :
    (Fin (n * 2 ^ B) → Fin Q) ≃ ((Fin n × (Fin B → Bool)) → Fin Q) where
  toFun f p := f (finProdFinEquiv (p.1, masks B p.2))
  invFun f i := f ((finProdFinEquiv.symm i).1, (masks B).symm (finProdFinEquiv.symm i).2)
  left_inv f := by funext i; simp only [Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv f := by funext p; simp only [Equiv.symm_apply_apply, Prod.mk.eta]

def code (Δ k Q n : ℕ) : BitCode (PriorityPartitionBroadcast.Table Δ k Q n)
    ((n * 2 ^ ((Δ + 1) ^ k)) * Q) :=
  PacketCode.transport (PacketCode.vector (SmallNumberCode.code Q) (n * 2 ^ ((Δ + 1) ^ k)))
    (tableEquiv ((Δ + 1) ^ k) n Q)
end Paper.PriorityTableCode
