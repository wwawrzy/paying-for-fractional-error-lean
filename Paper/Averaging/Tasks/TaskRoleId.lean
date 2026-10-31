import Paper.Partitions.Local.PriorityTableCode
import Mathlib.Data.Prod.Lex

/-! Public role IDs: an anchor vertex ID and fixed finite metadata.
Enumeration traverses only a supplied finite anchor set, never all V. -/
namespace Paper.TaskRoleId
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Id (V : Type) (M : ℕ) := V ×ₗ Fin M

def make (v : V) {M : ℕ} (m : Fin M) : Id V M := toLex (v, m)

def code {b : ℕ} (C : BitCode V b) (M : ℕ) : BitCode (Id V M) (b + M) :=
  PacketCode.transport (PacketCode.product C (SmallNumberCode.code M)) {
    toFun := toLex
    invFun := ofLex
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def space (anchors : Finset V) (M : ℕ) : Finset (Id V M) :=
  (anchors ×ˢ (Finset.univ : Finset (Fin M))).image toLex

theorem mem_space (anchors : Finset V) (M : ℕ) (r : Id V M) :
    r ∈ space anchors M ↔ (ofLex r).1 ∈ anchors := by
  simp only [space, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨p, hp, he⟩
    exact congrArg (fun x : Id V M => (ofLex x).1) he ▸ hp
  · intro hp
    exact ⟨ofLex r, hp, rfl⟩

theorem card_space (anchors : Finset V) (M : ℕ) : (space anchors M).card = anchors.card * M := by
  have hi : Function.Injective (toLex : V × Fin M → Id V M) :=
    fun _ _ h => congrArg (ofLex : Id V M → V × Fin M) h
  calc
    _ = (anchors ×ˢ (Finset.univ : Finset (Fin M))).card := Finset.card_image_of_injective _ hi
    _ = _ := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]

theorem overlap_bound (anchors : Finset V) (M : ℕ) (roles : Finset (Id V M))
    (h : ∀ r ∈ roles, (ofLex r).1 ∈ anchors) : roles.card ≤ anchors.card * M := by
  rw [← card_space anchors M]
  exact Finset.card_le_card (fun r hr => (mem_space anchors M r).mpr (h r hr))

theorem logarithmic_width {b : ℕ} (C : BitCode V b) (M N c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (N + 2)) : b + M ≤ (c + M) * Nat.clog 2 (N + 2) := by
  have hl : 1 ≤ Nat.clog 2 (N + 2) := Nat.clog_pos (by omega) (by omega)
  nlinarith
end Paper.TaskRoleId
