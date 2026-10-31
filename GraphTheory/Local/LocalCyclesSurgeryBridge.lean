import GraphTheory.Local.LocalCyclesMirrorPotential
import GraphTheory.Local.LocalCyclesReflection

/-! Connect concrete finite-cycle LOCAL geometry to walks in the output automaton.
Theorems apply to any radius-r port-view rule, with fixed n and arbitrary auxiliary
data, conditional on validity on the specified original/modified inputs.
-/

noncomputable section

namespace LocalCyclesSurgeryBridge

open LocalCycles LocalCyclesReflection

variable {n : ℕ} [NeZero n] {Q A : Type*} {E : Q → Q → Prop}

theorem right_zero (i : Fin n) : right i 0 = i := by
  apply Fin.ext
  simp [right, Nat.mod_eq_of_lt i.isLt]

theorem right_add (i : Fin n) (a b : ℕ) : right (right i a) b = right i (a + b) := by
  apply Fin.ext
  simp only [right]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem right_distance (i j : Fin n) : right i (cyclicDistance i j) = j := by
  apply Fin.ext
  simp only [right, cyclicDistance]
  split_ifs with h
  · have he : i.val + (j.val - i.val) = j.val := by omega
    rw [he, Nat.mod_eq_of_lt j.isLt]
  · have he : i.val + (n + j.val - i.val) = n + j.val := by have := i.isLt; omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt j.isLt]

omit [NeZero n] in
theorem distance_positive (i j : Fin n) (hne : i ≠ j) : 0 < cyclicDistance i j := by
  have hne' : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
  have := i.isLt
  unfold cyclicDistance
  split_ifs <;> omega

/-- A cyclic valid output yields a walk of every traversed length. -/
theorem run_path (states : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1))) (i : Fin n) (k : ℕ) :
    ∃ a : Walk E (states i) (states (right i k)), a.length = k := by
  induction k with
  | zero =>
    rw [right_zero]
    exact ⟨.nil _, rfl⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    let e : Walk E (states (right i k)) (states (right (right i k) 1)) :=
      .cons (hvalid (right i k)) (.nil _)
    let z := (a.append e).castRight (congrArg states (right_add i k 1))
    refine ⟨z, ?_⟩
    simp [z, Walk.length_castRight, Walk.length_append, ha, e, Walk.length]

theorem run_path_between (states : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1))) (i j : Fin n) :
    ∃ a : Walk E (states i) (states j), a.length = cyclicDistance i j := by
  have h := run_path states hvalid i (cyclicDistance i j)
  rw [right_distance i j] at h
  exact h

def castEndpoints {u v u' v' : Q} (a : Walk E u v) (hu : u = u') (hv : v = v') :
    Walk E u' v' := hu ▸ hv ▸ a

theorem length_castEndpoints {u v u' v' : Q} (a : Walk E u v)
    (hu : u = u') (hv : v = v') : (castEndpoints a hu hv).length = a.length := by
  cases hu
  cases hv
  rfl

/-- Local geometry plus validity of two actual cyclic outputs yields both mirror
connectors. The reflected input is constructed, not supplied as an abstract walk. -/
theorem local_reflection_connectors (F : Rule r A Q) (rev : Q → Q)
    (I : Input n A) (b i anchor : Fin n)
    (hleft : r ≤ i.val) (hright : i.val + r ≤ b.val)
    (hcenter : b.val = 2 * i.val + 1)
    (hanchorLeft : b.val + r < anchor.val) (hanchorRight : anchor.val + r < n)
    (hedge : outputLeft F I (right i 1) = rev (outputRight F I i))
    (hvalid : ∀ j, E (outputRight F I j) (outputRight F I (right j 1)))
    (hreflected : ∀ j, E (outputRight F (reflect I b) j)
      (outputRight F (reflect I b) (right j 1))) :
    Nonempty (Walk E (outputRight F I i) (rev (outputRight F I i))) ∧
    Nonempty (Walk E (rev (outputRight F I i)) (outputRight F I i)) := by
  obtain ⟨xz, _⟩ := run_path_between (outputRight F I) hvalid i anchor
  obtain ⟨zx, _⟩ := run_path_between (outputRight F I) hvalid anchor i
  obtain ⟨rz, _⟩ := run_path_between (outputRight F (reflect I b)) hreflected i anchor
  obtain ⟨zr, _⟩ := run_path_between (outputRight F (reflect I b)) hreflected anchor i
  have hflip := reflection_edge_state F rev I b i hleft hright hcenter hedge
  have hfix := outputRight_reflect_remote F I b anchor hanchorLeft hanchorRight
  exact Walk.reflected_anchor_connectors rev xz zx
    (castEndpoints rz hflip hfix) (castEndpoints zr hfix hflip)

/-- A concrete relocated output supplies the returning-length witness. The path
has the original endpoint states and exactly one additional edge. -/
theorem local_relocation_path (F : Rule r A Q) (I : Input n A)
    (a b i anchor : Fin n) (hab : a.val ≤ b.val)
    (ha : a.val + r ≤ i.val) (hb : i.val + r < b.val)
    (hanchorLeft : r ≤ anchor.val) (hanchorRight : anchor.val + r < n)
    (hanchorOut : anchor.val + r < a.val ∨ b.val + r < anchor.val)
    (hvalid : ∀ j, E (outputRight F (relocate I a b hab) j)
      (outputRight F (relocate I a b hab) (right j 1))) :
    ∃ z : Walk E (outputRight F I (rollIndex a b i)) (outputRight F I anchor),
      z.length = cyclicDistance (rollIndex a b i) anchor + 1 := by
  obtain ⟨z, hz⟩ := run_path_between (outputRight F (relocate I a b hab)) hvalid i anchor
  have hroot := outputRight_relocate F I a b i hab ha hb
  have hanchor := outputRight_relocate_remote F I a b anchor hab
    hanchorLeft hanchorRight hanchorOut
  have hne : i ≠ anchor := by
    intro h
    have h' := congrArg Fin.val h
    omega
  refine ⟨castEndpoints z hroot hanchor, ?_⟩
  rw [length_castEndpoints, hz]
  exact cyclicDistance_roll a b i anchor (by omega) (by omega) hne

/-- Geometric packing assumptions for a fixed family of same-size relocations.
All positions are selected before any outputs or random tapes are observed. -/
structure Packing (n r k : ℕ) where
  root : Fin k → Fin n
  movedRoot : Fin k → Fin n
  lo : Fin k → Fin n
  hi : Fin k → Fin n
  ordered : ∀ i, (lo i).val ≤ (hi i).val
  leftMargin : ∀ i, (lo i).val + r ≤ (movedRoot i).val
  rightMargin : ∀ i, (movedRoot i).val + r < (hi i).val
  rootIdentity : ∀ i, rollIndex (lo i) (hi i) (movedRoot i) = root i
  rootInjective : Function.Injective root
  otherMargins : ∀ i j, i ≠ j → r ≤ (root j).val ∧ (root j).val + r < n ∧
    ((root j).val + r < (lo i).val ∨ (hi i).val + r < (root j).val)

/-- The finite-surgery implication for actual local outputs. All closed-walk
witnesses are derived from the specified original and modified input cycles. -/
theorem local_surgery_flexible [Fintype Q] (F : Rule r A Q) (rev : Q → Q)
    (I : Input n A) (P : Packing n r (Fintype.card Q + 1))
    (root anchor : Fin (Fintype.card Q + 1)) (reflectEnd : Fin n)
    (hleft : r ≤ (P.root root).val)
    (hright : (P.root root).val + r ≤ reflectEnd.val)
    (hcenter : reflectEnd.val = 2 * (P.root root).val + 1)
    (hanchorLeft : reflectEnd.val + r < (P.root anchor).val)
    (hanchorRight : (P.root anchor).val + r < n)
    (hedge : outputLeft F I (right (P.root root) 1) = rev (outputRight F I (P.root root)))
    (hvalid : ∀ j, E (outputRight F I j) (outputRight F I (right j 1)))
    (hreflected : ∀ j, E (outputRight F (reflect I reflectEnd) j)
      (outputRight F (reflect I reflectEnd) (right j 1)))
    (hmoved : ∀ i j, E (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) j)
      (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) (right j 1))) :
    ∃ K : ℕ, ∀ m ≥ K,
      (∃ z : Walk E (outputRight F I (P.root root)) (outputRight F I (P.root root)), z.length = m) ∧
      (∃ z : Walk E (outputRight F I (P.root root)) (rev (outputRight F I (P.root root))), z.length = m) ∧
      (∃ z : Walk E (rev (outputRight F I (P.root root))) (outputRight F I (P.root root)), z.length = m) ∧
      (∃ z : Walk E (rev (outputRight F I (P.root root))) (rev (outputRight F I (P.root root))), z.length = m) := by
  let states := fun i => outputRight F I (P.root i)
  have hpaths (i j) : ∃ z : Walk E (states i) (states j),
      z.length = cyclicDistance (P.root i) (P.root j) :=
    run_path_between (outputRight F I) hvalid (P.root i) (P.root j)
  have hreloc (i j) (hij : i ≠ j) : ∃ z : Walk E (states i) (states j),
      z.length = cyclicDistance (P.root i) (P.root j) + 1 := by
    obtain ⟨hjl, hjr, hjout⟩ := P.otherMargins i j hij
    have h := local_relocation_path F I (P.lo i) (P.hi i) (P.movedRoot i) (P.root j)
      (P.ordered i) (P.leftMargin i) (P.rightMargin i) hjl hjr hjout (hmoved i)
    rw [P.rootIdentity i] at h
    exact h
  let paths := fun i j => Classical.choose (hpaths i j)
  let moved := fun i j h => Classical.choose (hreloc i j h)
  have hpos : ∀ i j, i ≠ j → 0 < (paths i j).length := by
    intro i j hij
    rw [Classical.choose_spec (hpaths i j)]
    exact distance_positive _ _ (fun h => hij (P.rootInjective h))
  have hshift : ∀ i j (h : i ≠ j), (moved i j h).length = (paths i j).length + 1 := by
    intro i j h
    rw [Classical.choose_spec (hreloc i j h), Classical.choose_spec (hpaths i j)]
  obtain ⟨⟨forward⟩, ⟨back⟩⟩ := local_reflection_connectors F rev I reflectEnd
    (P.root root) (P.root anchor) hleft hright hcenter hanchorLeft hanchorRight
    hedge hvalid hreflected
  exact Walk.finite_surgery_core states paths moved hpos hshift root rev forward back

omit [NeZero n] in
theorem block_bound (r k : ℕ) (hn : k * (2 * r + 12) ≤ n)
    (i : Fin k) (offset : ℕ) (hoff : offset < 2 * r + 12) :
    i.val * (2 * r + 12) + offset < n := by
  calc
    i.val * (2 * r + 12) + offset < i.val * (2 * r + 12) + (2 * r + 12) :=
      Nat.add_lt_add_left hoff _
    _ = (i.val + 1) * (2 * r + 12) := by ring
    _ ≤ k * (2 * r + 12) := Nat.mul_le_mul_right _ (by have := i.isLt; omega)
    _ ≤ n := hn

def blockPosition (r k : ℕ) (hn : k * (2 * r + 12) ≤ n)
    (i : Fin k) (offset : ℕ) (hoff : offset < 2 * r + 12) : Fin n :=
  ⟨i.val * (2 * r + 12) + offset, block_bound r k hn i offset hoff⟩

/-- An explicit packing exists once n is a constant times the radius and number
of states. This discharges the geometric side conditions of the surgery family. -/
def standardPacking (r k : ℕ) (hn : k * (2 * r + 12) ≤ n) : Packing n r k where
  root i := blockPosition r k hn i (r + 4) (by omega)
  movedRoot i := blockPosition r k hn i (r + 3) (by omega)
  lo i := blockPosition r k hn i 2 (by omega)
  hi i := blockPosition r k hn i (2 * r + 7) (by omega)
  ordered i := by simp only [blockPosition]; omega
  leftMargin i := by simp only [blockPosition]; omega
  rightMargin i := by simp only [blockPosition]; omega
  rootIdentity i := by
    apply Fin.ext
    rw [rollIndex_val_mid]
    · simp only [blockPosition]
      omega
    · simp only [blockPosition]
      omega
    · simp only [blockPosition]
      omega
  rootInjective := by
    intro i j hij
    have hv := congrArg Fin.val hij
    simp only [blockPosition] at hv
    apply Fin.ext
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * r + 12 by omega)
    omega
  otherMargins i j hij := by
    have hnroot := block_bound r k hn j (2 * r + 4) (by omega)
    have hne : i.val ≠ j.val := by intro h; exact hij (Fin.ext h)
    simp only [blockPosition]
    refine ⟨by omega, by omega, ?_⟩
    by_cases hlt : i.val < j.val
    · have hprod := Nat.mul_le_mul_right (2 * r + 12) (show i.val + 1 ≤ j.val by omega)
      simp only [Nat.add_mul, one_mul] at hprod
      right
      omega
    · have hprod := Nat.mul_le_mul_right (2 * r + 12) (show j.val + 1 ≤ i.val by omega)
      simp only [Nat.add_mul, one_mul] at hprod
      left
      omega

/-- The modified input uses exactly the original node data, possibly at different
positions and with different external port attachments. Distinctness is in Input. -/
def SameData (I J : Input n A) : Prop :=
  ∀ v, ∃ u, J.ident v = I.ident u ∧ J.auxiliary v = I.auxiliary u

omit [NeZero n] in
theorem sameData_refl (I : Input n A) : SameData I I := fun v => ⟨v, rfl, rfl⟩

omit [NeZero n] in
omit [NeZero n] in
theorem sameData_reflect (I : Input n A) (b : Fin n) : SameData I (reflect I b) :=
  fun v => ⟨reflectIndex b v, rfl, rfl⟩

omit [NeZero n] in
theorem sameData_relocate (I : Input n A) (a b : Fin n) (hab : a.val ≤ b.val) :
    SameData I (relocate I a b hab) := fun v => ⟨rollIndex a b v, rfl, rfl⟩

omit [NeZero n] in
theorem sameData_preserves_ID_bound (I J : Input n A) (U : ℕ)
    (hI : ∀ v, I.ident v ≤ U) (h : SameData I J) : ∀ v, J.ident v ≤ U := by
  intro v
  obtain ⟨u, hu, _⟩ := h v
  rw [hu]
  exact hI u

/-- A fully geometric deterministic locality corollary. Correctness is needed
only on rearrangements of one fixed finite ID/data set, so polynomial ID bounds
are preserved. This theorem does not quantify over unbounded new identifiers. -/
theorem deterministic_local_output_is_mirror_flexible [Fintype Q] [Nonempty Q]
    (F : Rule r A Q) (rev : Q → Q) (I : Input n A)
    (hn : (Fintype.card Q + 1) * (2 * r + 12) ≤ n)
    (hedge : ∀ i, outputLeft F I (right i 1) = rev (outputRight F I i))
    (hvalid : ∀ J : Input n A, SameData I J →
      ∀ j, E (outputRight F J j) (outputRight F J (right j 1))) :
    ∃ (i : Fin n) (K : ℕ), ∀ m ≥ K,
      (∃ z : Walk E (outputRight F I i) (outputRight F I i), z.length = m) ∧
      (∃ z : Walk E (outputRight F I i) (rev (outputRight F I i)), z.length = m) ∧
      (∃ z : Walk E (rev (outputRight F I i)) (outputRight F I i), z.length = m) ∧
      (∃ z : Walk E (rev (outputRight F I i)) (rev (outputRight F I i)), z.length = m) := by
  let k := Fintype.card Q + 1
  have hk : 2 ≤ k := by have := Fintype.card_pos (α := Q); omega
  let root : Fin k := ⟨0, by omega⟩
  let anchor : Fin k := ⟨1, by omega⟩
  let P := standardPacking r k hn
  let b := blockPosition r k hn root (2 * r + 9) (by omega)
  have hl : r ≤ (P.root root).val := by simp [P, standardPacking, blockPosition, root]
  have hr : (P.root root).val + r ≤ b.val := by
    simp only [P, standardPacking, blockPosition, root, b, zero_mul, zero_add]
    omega
  have hc : b.val = 2 * (P.root root).val + 1 := by
    simp only [P, standardPacking, blockPosition, root, b, zero_mul, zero_add]
    omega
  have hal : b.val + r < (P.root anchor).val := by
    simp only [P, standardPacking, blockPosition, root, anchor, b, zero_mul, zero_add, one_mul]
    omega
  have har : (P.root anchor).val + r < n := by
    have h := block_bound r k hn anchor (2 * r + 4) (by omega)
    simp only [P, standardPacking, blockPosition]
    omega
  obtain ⟨K, hK⟩ := local_surgery_flexible F rev I P root anchor b hl hr hc hal har
    (hedge _) (hvalid I (sameData_refl I))
    (hvalid (reflect I b) (sameData_reflect I b))
    (fun i => hvalid (relocate I (P.lo i) (P.hi i) (P.ordered i))
      (sameData_relocate I (P.lo i) (P.hi i) (P.ordered i)))
  exact ⟨P.root root, K, hK⟩

end LocalCyclesSurgeryBridge

#print axioms LocalCyclesSurgeryBridge.run_path_between
#print axioms LocalCyclesSurgeryBridge.local_reflection_connectors

#print axioms LocalCyclesSurgeryBridge.local_relocation_path
#print axioms LocalCyclesSurgeryBridge.local_surgery_flexible

#print axioms LocalCyclesSurgeryBridge.standardPacking

#print axioms LocalCyclesSurgeryBridge.sameData_preserves_ID_bound
#print axioms LocalCyclesSurgeryBridge.deterministic_local_output_is_mirror_flexible
