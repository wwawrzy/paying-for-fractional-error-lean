import Paper.Preliminaries.PacketCode
import Mathlib.Data.List.OfFn

/-! Actual computational bounded-list messages, with zero padding and
decoding. The message width is B*(b+1), including presence bits. -/
namespace Paper.ListPacket
open BroadcastModel
variable {A : Type*}

def pack (B : ℕ) (l : List A) (i : Fin B) : Option A := l[i.val]?

def unpack {B : ℕ} (f : Fin B → Option A) : List A := (List.ofFn f).filterMap id

theorem unpack_succ {B : ℕ} (f : Fin (B + 1) → Option A) :
    unpack f = match f 0 with
      | none => unpack (fun i => f i.succ)
      | some a => a :: unpack (fun i => f i.succ) := by
  unfold unpack
  rw [List.ofFn_succ]
  cases h : f 0 <;> simp [h]

theorem unpack_length {B : ℕ} (f : Fin B → Option A) : (unpack f).length ≤ B := by
  induction B with
  | zero => simp [unpack]
  | succ B ih =>
    rw [unpack_succ]
    have h := ih (fun i => f i.succ)
    cases hf : f 0 <;> simp only [List.length_cons] <;> omega

theorem unpack_pack (B : ℕ) (l : List A) (hl : l.length ≤ B) : unpack (pack B l) = l := by
  induction B generalizing l with
  | zero =>
    have he : l = [] := by simpa using (Nat.eq_zero_of_le_zero hl : l.length = 0)
    subst l
    rfl
  | succ B ih =>
    rw [unpack_succ]
    cases l with
    | nil =>
      change unpack (pack B ([] : List A)) = []
      exact ih [] (by simp)
    | cons a l =>
      change a :: unpack (pack B l) = a :: l
      apply congrArg (List.cons a)
      exact ih l (by simp only [List.length_cons] at hl; omega)

def bounded {b : ℕ} (C : BitCode A b) (B : ℕ) : BitCode {l : List A // l.length ≤ B} (B * (b + 1)) :=
  let D := PacketCode.vector C.option B
  PacketCode.ofInverse
    (fun l => D.encode (pack B l.val))
    (fun bits => (D.decode bits).map (fun f => ⟨unpack f, unpack_length f⟩))
    (by
      intro l
      dsimp only
      rw [D.leftInverse]
      simp only [Option.map_some]
      exact congrArg some (Subtype.ext (unpack_pack B l.val l.property)))

def truncate (B : ℕ) (l : List A) : {l : List A // l.length ≤ B} :=
  ⟨l.take B, by simp only [List.length_take]; exact Nat.min_le_left _ _⟩

theorem truncate_eq (B : ℕ) (l : List A) (hl : l.length ≤ B) : (truncate B l).val = l :=
  List.take_of_length_le hl

theorem logarithmic_width (B b c n : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    B * (b + 1) ≤ (B * (c + 1)) * Nat.clog 2 (n + 2) := by
  have h := Nat.mul_le_mul_left B (BroadcastModel.logarithmic_message_budget n b c hids).1
  simpa only [Nat.mul_assoc] using h
end Paper.ListPacket
