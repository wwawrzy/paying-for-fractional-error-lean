import Paper.Preliminaries.SmallNumberCode

/-! Fixed bounded counters with saturating addition. They form a genuine
commutative monoid, so rank-directed aggregation computes min(M,total)
without ever sending an unbounded integer. -/
namespace Paper.CappedCount
open BroadcastModel

structure Count (M : ℕ) where
  value : Fin (M + 1)
deriving DecidableEq

def cap (M n : ℕ) : Count M := ⟨⟨min n M, by have := min_le_right n M; omega⟩⟩

@[ext] theorem ext {M : ℕ} {a b : Count M} (h : a.value.val = b.value.val) : a = b := by
  cases a; cases b
  congr 1
  exact Fin.ext h

instance countZero (M : ℕ) : Zero (Count M) := ⟨cap M 0⟩

instance countAdd (M : ℕ) : Add (Count M) := ⟨fun a b => cap M (a.value.val + b.value.val)⟩

instance countAddCommMonoid (M : ℕ) : AddCommMonoid (Count M) where
  zero := cap M 0
  add a b := cap M (a.value.val + b.value.val)
  add_assoc a b c := by
    apply ext
    change min (min (a.value.val + b.value.val) M + c.value.val) M =
      min (a.value.val + min (b.value.val + c.value.val) M) M
    omega
  zero_add a := by
    apply ext
    change min (min 0 M + a.value.val) M = a.value.val
    have := a.value.isLt
    omega
  add_zero a := by
    apply ext
    change min (a.value.val + min 0 M) M = a.value.val
    have := a.value.isLt
    omega
  add_comm a b := by
    apply ext
    change min (a.value.val + b.value.val) M = min (b.value.val + a.value.val) M
    omega
  nsmul := nsmulRec

theorem cap_zero (M : ℕ) : cap M 0 = 0 := rfl

theorem cap_add (M a b : ℕ) : cap M (a + b) = cap M a + cap M b := by
  apply ext
  change min (a + b) M = min (min a M + min b M) M
  omega

theorem cap_sum {I : Type*} (M : ℕ) (s : Finset I) (f : I → ℕ) :
    cap M (∑ i ∈ s, f i) = ∑ i ∈ s, cap M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cap_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, cap_add, ih]

def code (M : ℕ) : BitCode (Count M) (M + 1) :=
  PacketCode.transport (SmallNumberCode.code (M + 1)) {
    toFun := Count.mk
    invFun := Count.value
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
end Paper.CappedCount
