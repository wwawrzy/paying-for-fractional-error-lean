import Paper.Preliminaries.RootPayloadRoute
import Paper.Preliminaries.RoleAnchorGeometry

/-! Exact actual root keys, bounded packets and common payload values.
The physical graph may have unbounded degree. -/
namespace Paper.RootPayloadCorrect
open BroadcastModel SevenFoundation
variable {V A : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem star_correct {w : ℕ} (P : BitCode A w) (D R : Finset V) (L : ℕ)
    (active : Finset V) (f : V → A) (v : V) :
    (OwnerPayloadRead.program P).run G
      (fun u => RootPayloadRoute.starInput (OwnerPayloadInputs.expected G D R L active f u)) v =
      if OwnerSupport.owner G D v ∈ active then
        some (OwnerSupport.owner G D v, f (OwnerSupport.owner G D v)) else none :=
  OwnerPayloadStarRead.correct G P D active f _ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) v

def raw {b w : ℕ} (C : BitCode V b) (P : BitCode A w)
    (s : V → OwnerPayloadRoute.Input V A) (v : V) : List (V × A) :=
  OwnerPayloadRoute.candidate G C P s v ++
    ((OwnerPayloadRead.program P).run G (fun u => RootPayloadRoute.starInput (s u)) v).toList

theorem raw_keys {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.keys (raw G C P (OwnerPayloadInputs.expected G D R L active f) v) =
      RoleAnchorGeometry.roots G D R L v ∩ active := by
  rw [raw, TaggedDictionary.keys_append,
    OwnerPayloadLocalKeys.candidate_keys G C P D R hcover L active f v,
    star_correct G P D R L active f v]
  unfold RoleAnchorGeometry.roots
  by_cases ha : OwnerSupport.owner G D v ∈ active
  · simp only [if_pos ha, Option.toList_some, TaggedDictionary.keys, List.map_cons,
      List.map_nil, List.toFinset_cons, List.toFinset_nil]
    ext k
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert,
      Finset.notMem_empty, or_false]
    aesop
  · simp only [if_neg ha, Option.toList_none, TaggedDictionary.keys, List.map_nil,
      List.toFinset_nil, Finset.union_empty]
    ext k
    simp only [Finset.mem_inter, Finset.mem_insert]
    aesop

theorem raw_bound {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    (TaggedDictionary.keys (raw G C P (OwnerPayloadInputs.expected G D R L active f) v)).card ≤ L + 1 := by
  rw [raw_keys G C P D R hcover L active f v]
  exact (Finset.card_le_card Finset.inter_subset_left).trans (RoleAnchorGeometry.roots_card G D R L v)

theorem raw_consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.Consistent f (raw G C P (OwnerPayloadInputs.expected G D R L active f) v) := by
  apply TaggedDictionary.append_consistent f _ _
    (OwnerPayloadLocalKeys.candidate_consistent G C P D R hcover L active f v)
  rw [star_correct G P D R L active f v]
  intro p hp
  split_ifs at hp
  · simp only [Option.toList_some, List.mem_singleton] at hp
    subst p
    rfl
  · simp at hp

theorem keys {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.keys (((RootPayloadRoute.program C P L).run G
      (OwnerPayloadInputs.expected G D R L active f) v).val) =
      RoleAnchorGeometry.roots G D R L v ∩ active := by
  rw [RootPayloadRoute.run_program]
  change TaggedDictionary.keys (TaggedDictionary.bounded (L + 1)
    (raw G C P (OwnerPayloadInputs.expected G D R L active f) v)).val = _
  rw [TaggedDictionary.keys_bounded_eq _ _ (raw_bound G C P D R hcover L active f v)]
  exact raw_keys G C P D R hcover L active f v

theorem consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.Consistent f (((RootPayloadRoute.program C P L).run G
      (OwnerPayloadInputs.expected G D R L active f) v).val) := by
  rw [RootPayloadRoute.run_program]
  exact TaggedDictionary.bounded_consistent _ f _ (raw_consistent G C P D R hcover L active f v)

theorem lookup {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v u : V)
    (hu : u ∈ RoleAnchorGeometry.roots G D R L v ∩ active) :
    TaggedDictionary.lookup (((RootPayloadRoute.program C P L).run G
      (OwnerPayloadInputs.expected G D R L active f) v).val) u = some (f u) := by
  apply TaggedDictionary.lookup_correct f _ (consistent G C P D R hcover L active f v)
  rwa [keys G C P D R hcover L active f v]

end Paper.RootPayloadCorrect
