import Paper.Preliminaries.CappedCount

/-! Computable binary-sized counter codes. Each binary digit is encoded
with two bits, avoiding any noncomputable finite-type enumeration. -/
namespace Paper.BinaryCounter
open BroadcastModel

def code : (b : ℕ) → BitCode (Fin (2 ^ b)) (2 * b)
  | 0 => PacketCode.ofInverse (fun _ _ => false) (fun _ => some ⟨0, by simp⟩)
      (by
        intro i
        apply congrArg some
        apply Fin.ext
        have hi := i.isLt
        norm_num at hi
        omega)
  | b + 1 =>
      PacketCode.transport (PacketCode.product (code b) (SmallNumberCode.code 2))
        (finProdFinEquiv.trans (finCongr (Nat.pow_succ 2 b).symm))

def bounded (b M : ℕ) (hM : M < 2 ^ b) : BitCode (CappedCount.Count M) (2 * b) :=
  PacketCode.ofInverse
    (fun x => (code b).encode ⟨x.value.val, by have := x.value.isLt; omega⟩)
    (fun bits => ((code b).decode bits).bind (fun i =>
      if h : i.val ≤ M then some ⟨⟨i.val, by omega⟩⟩ else none))
    (by
      intro x
      dsimp only
      rw [(code b).leftInverse]
      simp only [Option.bind_some]
      have hx : x.value.val ≤ M := by have := x.value.isLt; omega
      rw [dif_pos hx])

theorem order_bound {V : Type} [Fintype V] {b : ℕ} (C : BitCode V b) :
    Fintype.card V ≤ 2 ^ b := by
  have hh := Fintype.card_le_of_injective C.encode C.injective
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hh

def countCode (b : ℕ) : BitCode (CappedCount.Count (2 ^ b)) (2 * (b + 1)) :=
  bounded (b + 1) (2 ^ b) (by
    rw [Nat.pow_succ]
    have h : 0 < 2 ^ b := Nat.two_pow_pos b
    omega)
end Paper.BinaryCounter
