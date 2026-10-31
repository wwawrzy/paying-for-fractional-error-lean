import Paper.Communication.BroadcastModel

/-! Computable prefix codes for messages with no supplied global size bound.
Natural numbers use a continuation bit before each binary digit and a final
zero bit. The size bound is an analysis theorem, not an encoder input. -/
namespace Paper

structure PrefixCode (A : Type*) where
  encode : A → List Bool
  read : List Bool → Option (A × List Bool)
  read_append : ∀ a tail, read (encode a ++ tail) = some (a, tail)

namespace PrefixCode

def decode {A : Type*} (C : PrefixCode A) (bits : List Bool) : Option A :=
  (C.read bits).bind fun p => if p.2 = [] then some p.1 else none

theorem decode_encode {A : Type*} (C : PrefixCode A) (a : A) :
    C.decode (C.encode a) = some a := by
  have h := C.read_append a []
  simp only [List.append_nil] at h
  simp [decode, h]

theorem injective {A : Type*} (C : PrefixCode A) : Function.Injective C.encode := by
  intro a b h
  have hh := congrArg C.decode h
  simpa only [decode_encode, Option.some.injEq] using hh

def bool : PrefixCode Bool where
  encode b := [b]
  read
    | [] => none
    | b :: rest => some (b, rest)
  read_append _ _ := rfl

def product {A B : Type*} (C : PrefixCode A) (D : PrefixCode B) : PrefixCode (A × B) where
  encode p := C.encode p.1 ++ D.encode p.2
  read bits := (C.read bits).bind fun p => (D.read p.2).map fun q => ((p.1, q.1), q.2)
  read_append p tail := by
    simp only [List.append_assoc, C.read_append, Option.bind_some, D.read_append, Option.map_some]

def frame : List Bool → List Bool
  | [] => [false]
  | b :: rest => true :: b :: frame rest

def value : List Bool → ℕ
  | [] => 0
  | b :: rest => Nat.bit b (value rest)

def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: [] => none
  | true :: b :: rest => (readNat rest).map fun p => (Nat.bit b p.1, p.2)

theorem read_frame (bits tail : List Bool) :
    readNat (frame bits ++ tail) = some (value bits, tail) := by
  induction bits with
  | nil => rfl
  | cons b rest ih => simp only [frame, List.cons_append, readNat, ih, Option.map_some, value]

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => rw [Nat.bits_append_bit n b h]; simp only [value, ih]

def nat : PrefixCode ℕ where
  encode n := frame n.bits
  read := readNat
  read_append n tail := by rw [read_frame, value_bits]

theorem frame_length (bits : List Bool) : (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b rest ih => simp only [frame, List.length_cons, ih]; omega

theorem nat_length (n : ℕ) : (nat.encode n).length = 2 * n.size + 1 := by
  change (frame n.bits).length = _
  rw [frame_length, Nat.size_eq_bits_len]

theorem nat_length_bound (n : ℕ) : (nat.encode n).length ≤ 2 * Nat.clog 2 (n+1) + 1 := by
  rw [nat_length]
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (n+1)
  have hs : n.size ≤ Nat.clog 2 (n+1) := Nat.size_le.mpr (by omega)
  omega

theorem product_length {A B : Type*} (C : PrefixCode A) (D : PrefixCode B) (a : A) (b : B) :
    ((product C D).encode (a,b)).length = (C.encode a).length + (D.encode b).length :=
  List.length_append

/-- Counter packets have two natural fields and one flag. Neither field
requires a preannounced width or a common maximum degree. -/
def counters : PrefixCode (ℕ × ℕ × Bool) := product nat (product nat bool)

theorem counters_length (den exponent : ℕ) (flag : Bool) :
    (counters.encode (den,exponent,flag)).length ≤
      2 * Nat.clog 2 (den+1) + 2 * Nat.clog 2 (exponent+1) + 3 := by
  change ((product nat (product nat bool)).encode (den,exponent,flag)).length ≤ _
  rw [product_length, product_length]
  have hden := nat_length_bound den
  have hexp := nat_length_bound exponent
  change (nat.encode den).length + ((nat.encode exponent).length + 1) ≤ _
  omega

end PrefixCode
end Paper
#print axioms Paper.PrefixCode.decode_encode
#print axioms Paper.PrefixCode.injective
#print axioms Paper.PrefixCode.nat_length_bound
#print axioms Paper.PrefixCode.counters_length
