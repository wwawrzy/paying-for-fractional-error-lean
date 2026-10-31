import Mathlib

/-! A geometric LOCAL reflection bridge on a finite cycle.
The input includes distinct IDs, arbitrary port numbering, and arbitrary per-node
auxiliary data (which may hold the full private random tape). A radius-r rule reads
an intrinsic port-rooted view, with no coordinate-equivariance assumption.
-/

namespace LocalCyclesReflection

variable {n : ℕ} [NeZero n]

structure Input (n : ℕ) (A : Type*) where
  ident : Fin n → ℕ
  unique : Function.Injective ident
  auxiliary : Fin n → A
  leftPort : Fin n → Bool

@[ext] structure View (r : ℕ) (A : Type*) where
  root : ℕ × A
  branch : Bool → Fin r → (ℕ × A) × Bool

/-- Positions reached without backtracking, interpreted cyclically. -/
def right (i : Fin n) (k : ℕ) : Fin n := ⟨(i.val + k) % n, Nat.mod_lt _ (NeZero.pos n)⟩
def left (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + n - k % n) % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem right_val (i : Fin n) (k : ℕ) (h : i.val + k < n) :
    (right i k).val = i.val + k := Nat.mod_eq_of_lt h

theorem left_val (i : Fin n) (k : ℕ) (h : k ≤ i.val) :
    (left i k).val = i.val - k := by
  have hk : k < n := lt_of_le_of_lt h i.isLt
  simp only [left, Nat.mod_eq_of_lt hk]
  have he : i.val + n - k = n + (i.val - k) := by omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (show i.val - k < n by omega)]

/-- Reverse a prefix of the cyclic coordinate, fixing all other positions. -/
def reflectIndex (b i : Fin n) : Fin n :=
  if h : i.val ≤ b.val then ⟨b.val - i.val, by omega⟩ else i

omit [NeZero n] in
theorem reflectIndex_val_of_le (b i : Fin n) (h : i.val ≤ b.val) :
    (reflectIndex b i).val = b.val - i.val := by simp [reflectIndex, h]

omit [NeZero n] in
theorem reflectIndex_eq_of_gt (b i : Fin n) (h : b.val < i.val) :
    reflectIndex b i = i := by simp [reflectIndex, Nat.not_le.mpr h]

omit [NeZero n] in
theorem reflectIndex_involutive (b : Fin n) : Function.Involutive (reflectIndex b) := by
  intro i
  by_cases h : i.val ≤ b.val
  · have h' : (reflectIndex b i).val ≤ b.val := by
      rw [reflectIndex_val_of_le b i h]
      omega
    apply Fin.ext
    rw [reflectIndex_val_of_le b (reflectIndex b i) h', reflectIndex_val_of_le b i h]
    omega
  · have he : reflectIndex b i = i := by simp [reflectIndex, h]
    rw [he, he]

def reflect {A : Type*} (I : Input n A) (b : Fin n) : Input n A where
  ident i := I.ident (reflectIndex b i)
  unique := I.unique.comp (reflectIndex_involutive b).injective
  auxiliary i := I.auxiliary (reflectIndex b i)
  leftPort i := if i.val ≤ b.val then !(I.leftPort (reflectIndex b i)) else I.leftPort i

/-- The root's ports, rather than a chosen global direction, index the branches.
At each branch position we record the ID, auxiliary data and incoming port. -/
def view {A : Type*} (I : Input n A) (r : ℕ) (i : Fin n) : View r A where
  root := (I.ident i, I.auxiliary i)
  branch port j :=
    if port = I.leftPort i then
      let v := left i (j.val + 1)
      ((I.ident v, I.auxiliary v), !(I.leftPort v))
    else
      let v := right i (j.val + 1)
      ((I.ident v, I.auxiliary v), I.leftPort v)

/-- Reflection changes a left step into a right step, while staying in the prefix. -/
theorem reflect_left (b i : Fin n) (k : ℕ)
    (hk : k ≤ i.val) (hi : i.val + k ≤ b.val) :
    reflectIndex b (left i k) = right (reflectIndex b i) k := by
  have hil : i.val ≤ b.val := by omega
  have hl : (left i k).val ≤ b.val := by rw [left_val i k hk]; omega
  have hr : (reflectIndex b i).val + k < n := by
    rw [reflectIndex_val_of_le b i hil]
    have := b.isLt
    omega
  apply Fin.ext
  rw [reflectIndex_val_of_le b (left i k) hl, left_val i k hk,
    right_val (reflectIndex b i) k hr, reflectIndex_val_of_le b i hil]
  omega

theorem reflect_right (b i : Fin n) (k : ℕ)
    (_hk : k ≤ i.val) (hi : i.val + k ≤ b.val) :
    reflectIndex b (right i k) = left (reflectIndex b i) k := by
  have hil : i.val ≤ b.val := by omega
  have hr : i.val + k < n := lt_of_le_of_lt hi b.isLt
  have hrb : (right i k).val ≤ b.val := by rw [right_val i k hr]; exact hi
  have hk' : k ≤ (reflectIndex b i).val := by
    rw [reflectIndex_val_of_le b i hil]
    omega
  apply Fin.ext
  rw [reflectIndex_val_of_le b (right i k) hrb, right_val i k hr,
    left_val (reflectIndex b i) k hk', reflectIndex_val_of_le b i hil]
  omega

/-- The reflected input has exactly the original intrinsic view at the reflected
vertex. This works for arbitrary IDs, port numbering and auxiliary/random tapes. -/
theorem view_reflect {A : Type*} (I : Input n A) (r : ℕ) (b i : Fin n)
    (hleft : r ≤ i.val) (hright : i.val + r ≤ b.val) :
    view (reflect I b) r i = view I r (reflectIndex b i) := by
  have hi : i.val ≤ b.val := by omega
  apply View.ext
  · rfl
  · funext port j
    have hk : j.val + 1 ≤ i.val := by have := j.isLt; omega
    have hkr : i.val + (j.val + 1) ≤ b.val := by have := j.isLt; omega
    have hl : (left i (j.val + 1)).val ≤ b.val := by rw [left_val i _ hk]; omega
    have hrn : i.val + (j.val + 1) < n := lt_of_le_of_lt hkr b.isLt
    have hr : (right i (j.val + 1)).val ≤ b.val := by rw [right_val i _ hrn]; exact hkr
    have hsl := reflect_left b i (j.val + 1) hk hkr
    have hsr := reflect_right b i (j.val + 1) hk hkr
    have hiF : i ≤ b := hi
    have hlF : left i (j.val + 1) ≤ b := hl
    have hrF : right i (j.val + 1) ≤ b := hr
    cases hp : I.leftPort (reflectIndex b i) <;> cases port <;>
      simp [view, reflect, hiF, hlF, hrF, hp, hsl, hsr]

/-- A remote vertex whose entire radius is outside the reflected prefix keeps
its intrinsic view, including all auxiliary/random data. -/
theorem view_reflect_remote {A : Type*} (I : Input n A) (r : ℕ) (b i : Fin n)
    (hleft : b.val + r < i.val) (hright : i.val + r < n) :
    view (reflect I b) r i = view I r i := by
  have hi : b.val < i.val := by omega
  have hni : ¬ i ≤ b := Nat.not_le.mpr hi
  have hei := reflectIndex_eq_of_gt b i hi
  apply View.ext
  · simp [view, reflect, hei]
  · funext port j
    have hk : j.val + 1 ≤ i.val := by have := j.isLt; omega
    have hrn : i.val + (j.val + 1) < n := by have := j.isLt; omega
    have hl : b.val < (left i (j.val + 1)).val := by
      rw [left_val i _ hk]
      have := j.isLt
      omega
    have hr : b.val < (right i (j.val + 1)).val := by
      rw [right_val i _ hrn]
      omega
    have hnl : ¬ left i (j.val + 1) ≤ b := Nat.not_le.mpr hl
    have hnr : ¬ right i (j.val + 1) ≤ b := Nat.not_le.mpr hr
    have hel := reflectIndex_eq_of_gt b (left i (j.val + 1)) hl
    have her := reflectIndex_eq_of_gt b (right i (j.val + 1)) hr
    simp [view, reflect, hei, hel, her, hni, hnl, hnr]

/-- A radius-r rule reads a port-rooted view and chooses one state per root port.
The same function is used on every input of this fixed n. It may depend on n. -/
abbrev Rule (r : ℕ) (A Q : Type*) := View r A → Bool → Q

def outputRight {A Q : Type*} (F : Rule r A Q) (I : Input n A) (i : Fin n) : Q :=
  F (view I r i) (!(I.leftPort i))

def outputLeft {A Q : Type*} (F : Rule r A Q) (I : Input n A) (i : Fin n) : Q :=
  F (view I r i) (I.leftPort i)

theorem outputRight_reflect {A Q : Type*} (F : Rule r A Q)
    (I : Input n A) (b i : Fin n) (hleft : r ≤ i.val)
    (hright : i.val + r ≤ b.val) :
    outputRight F (reflect I b) i = outputLeft F I (reflectIndex b i) := by
  have hi : i ≤ b := by change i.val ≤ b.val; omega
  unfold outputRight outputLeft
  rw [view_reflect I r b i hleft hright]
  simp [reflect, hi]

theorem outputRight_reflect_remote {A Q : Type*} (F : Rule r A Q)
    (I : Input n A) (b i : Fin n) (hleft : b.val + r < i.val)
    (hright : i.val + r < n) :
    outputRight F (reflect I b) i = outputRight F I i := by
  have hi : ¬ i ≤ b := by change ¬ i.val ≤ b.val; omega
  unfold outputRight
  rw [view_reflect_remote I r b i hleft hright]
  simp [reflect, hi]

/-- The central protected edge reverses its clockwise state. The only output
hypothesis is the original edge constraint; the local rule is otherwise arbitrary. -/
theorem reflection_edge_state {A Q : Type*} (F : Rule r A Q)
    (rev : Q → Q) (I : Input n A) (b i : Fin n)
    (hleft : r ≤ i.val) (hright : i.val + r ≤ b.val)
    (hcenter : b.val = 2 * i.val + 1)
    (hedge : outputLeft F I (right i 1) = rev (outputRight F I i)) :
    outputRight F (reflect I b) i = rev (outputRight F I i) := by
  have hi : i.val ≤ b.val := by omega
  have hir : i.val + 1 < n := by have := b.isLt; omega
  have hindex : reflectIndex b i = right i 1 := by
    apply Fin.ext
    rw [reflectIndex_val_of_le b i hi, right_val i 1 hir]
    omega
  rw [outputRight_reflect F I b i hleft hright, hindex]
  exact hedge

/-- One same-n input modification flips a protected edge and fixes a remote
anchor. Distinct IDs and arbitrary auxiliary tapes are preserved by construction. -/
theorem reflection_locality_core {A Q : Type*} (F : Rule r A Q)
    (rev : Q → Q) (I : Input n A) (b i anchor : Fin n)
    (hleft : r ≤ i.val) (hright : i.val + r ≤ b.val)
    (hcenter : b.val = 2 * i.val + 1)
    (hanchorLeft : b.val + r < anchor.val) (hanchorRight : anchor.val + r < n)
    (hedge : outputLeft F I (right i 1) = rev (outputRight F I i)) :
    ∃ J : Input n A,
      outputRight F J i = rev (outputRight F I i) ∧
      outputRight F J anchor = outputRight F I anchor ∧
      (∀ v, J.ident v = I.ident (reflectIndex b v)) ∧
      (∀ v, J.auxiliary v = I.auxiliary (reflectIndex b v)) := by
  exact ⟨reflect I b, reflection_edge_state F rev I b i hleft hright hcenter hedge,
    outputRight_reflect_remote F I b anchor hanchorLeft hanchorRight,
    fun _ => rfl, fun _ => rfl⟩

/-- Reindex all vertex data without reversing local left/right coordinates. -/
def reindex {A : Type*} (I : Input n A) (f : Fin n → Fin n)
    (hf : Function.Injective f) : Input n A where
  ident := I.ident ∘ f
  unique := I.unique.comp hf
  auxiliary := I.auxiliary ∘ f
  leftPort := I.leftPort ∘ f

theorem view_reindex {A : Type*} (I : Input n A) (f : Fin n → Fin n)
    (hf : Function.Injective f) (r : ℕ) (i : Fin n)
    (hl : ∀ k, k ≤ r → f (left i k) = left (f i) k)
    (hr : ∀ k, k ≤ r → f (right i k) = right (f i) k) :
    view (reindex I f hf) r i = view I r (f i) := by
  apply View.ext
  · rfl
  · funext port j
    have hk : j.val + 1 ≤ r := by have := j.isLt; omega
    simp [view, reindex, hl _ hk, hr _ hk, Function.comp_def]

/-- Move the vertex at a to b, shifting the intervening vertices one place left.
This function maps new positions to their original vertex identities. -/
def rollIndex (a b : Fin n) (i : Fin n) : Fin n :=
  if h : a.val ≤ i.val ∧ i.val < b.val then ⟨i.val + 1, by have := b.isLt; omega⟩
  else if i = b then a else i

omit [NeZero n] in
theorem rollIndex_injective (a b : Fin n) (hab : a.val ≤ b.val) :
    Function.Injective (rollIndex a b) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [rollIndex] at hv
  split_ifs at hv <;> simp_all [Fin.ext_iff] <;> omega

omit [NeZero n] in
theorem rollIndex_val_mid (a b i : Fin n) (ha : a.val ≤ i.val) (hb : i.val < b.val) :
    (rollIndex a b i).val = i.val + 1 := by simp [rollIndex, ha, hb]

omit [NeZero n] in
theorem rollIndex_fixed (a b i : Fin n) (hab : a.val ≤ b.val) (hout : i.val < a.val ∨ b.val < i.val) :
    rollIndex a b i = i := by
  have hmid : ¬ (a.val ≤ i.val ∧ i.val < b.val) := by omega
  have hib : i ≠ b := by intro h; subst i; omega
  have hmidF : ¬ (a ≤ i ∧ i < b) := hmid
  simp [rollIndex, hmidF, hib]

theorem roll_left (a b i : Fin n) (k : ℕ)
    (ha : a.val + k ≤ i.val) (hb : i.val + k < b.val) :
    rollIndex a b (left i k) = left (rollIndex a b i) k := by
  have hk : k ≤ i.val := by omega
  have ha0 : a.val ≤ i.val := by omega
  have hb0 : i.val < b.val := by omega
  have hal : a.val ≤ (left i k).val := by rw [left_val i k hk]; omega
  have hbl : (left i k).val < b.val := by rw [left_val i k hk]; omega
  have hk' : k ≤ (rollIndex a b i).val := by rw [rollIndex_val_mid a b i ha0 hb0]; omega
  apply Fin.ext
  rw [rollIndex_val_mid a b (left i k) hal hbl, left_val i k hk,
    left_val (rollIndex a b i) k hk', rollIndex_val_mid a b i ha0 hb0]
  omega

theorem roll_right (a b i : Fin n) (k : ℕ)
    (ha : a.val + k ≤ i.val) (hb : i.val + k < b.val) :
    rollIndex a b (right i k) = right (rollIndex a b i) k := by
  have ha0 : a.val ≤ i.val := by omega
  have hb0 : i.val < b.val := by omega
  have hr : i.val + k < n := by have := b.isLt; omega
  have har : a.val ≤ (right i k).val := by rw [right_val i k hr]; omega
  have hbr : (right i k).val < b.val := by rw [right_val i k hr]; exact hb
  have hr' : (rollIndex a b i).val + k < n := by
    rw [rollIndex_val_mid a b i ha0 hb0]
    have := b.isLt
    omega
  apply Fin.ext
  rw [rollIndex_val_mid a b (right i k) har hbr, right_val i k hr,
    right_val (rollIndex a b i) k hr', rollIndex_val_mid a b i ha0 hb0]
  omega

def relocate {A : Type*} (I : Input n A) (a b : Fin n) (hab : a.val ≤ b.val) : Input n A :=
  reindex I (rollIndex a b) (rollIndex_injective a b hab)

theorem view_relocate {A : Type*} (I : Input n A) (r : ℕ) (a b i : Fin n)
    (hab : a.val ≤ b.val) (ha : a.val + r ≤ i.val) (hb : i.val + r < b.val) :
    view (relocate I a b hab) r i = view I r (rollIndex a b i) := by
  apply view_reindex
  · intro k hk
    exact roll_left a b i k (by omega) (by omega)
  · intro k hk
    exact roll_right a b i k (by omega) (by omega)

theorem view_relocate_remote {A : Type*} (I : Input n A) (r : ℕ) (a b i : Fin n)
    (hab : a.val ≤ b.val) (hleft : r ≤ i.val) (hright : i.val + r < n)
    (hout : i.val + r < a.val ∨ b.val + r < i.val) :
    view (relocate I a b hab) r i = view I r i := by
  have hi : rollIndex a b i = i := rollIndex_fixed a b i hab (by omega)
  have hl : ∀ k, k ≤ r → rollIndex a b (left i k) = left (rollIndex a b i) k := by
    intro k hk
    rw [hi]
    apply rollIndex_fixed a b (left i k) hab
    rw [left_val i k (by omega)]
    omega
  have hr : ∀ k, k ≤ r → rollIndex a b (right i k) = right (rollIndex a b i) k := by
    intro k hk
    rw [hi]
    apply rollIndex_fixed a b (right i k) hab
    rw [right_val i k (by omega)]
    omega
  have hv := view_reindex I (rollIndex a b) (rollIndex_injective a b hab) r i hl hr
  simpa only [relocate, hi] using hv

theorem outputRight_relocate {A Q : Type*} (F : Rule r A Q)
    (I : Input n A) (a b i : Fin n) (hab : a.val ≤ b.val)
    (ha : a.val + r ≤ i.val) (hb : i.val + r < b.val) :
    outputRight F (relocate I a b hab) i = outputRight F I (rollIndex a b i) := by
  unfold outputRight
  rw [view_relocate I r a b i hab ha hb]
  rfl

theorem outputRight_relocate_remote {A Q : Type*} (F : Rule r A Q)
    (I : Input n A) (a b i : Fin n) (hab : a.val ≤ b.val)
    (hleft : r ≤ i.val) (hright : i.val + r < n)
    (hout : i.val + r < a.val ∨ b.val + r < i.val) :
    outputRight F (relocate I a b hab) i = outputRight F I i := by
  have hi : rollIndex a b i = i := rollIndex_fixed a b i hab (by omega)
  unfold outputRight
  rw [view_relocate_remote I r a b i hab hleft hright hout]
  simp [relocate, reindex, Function.comp_def, hi]

/-- Clockwise edge-index distance, in the range 0,...,n-1. -/
def cyclicDistance (i j : Fin n) : ℕ :=
  if i.val ≤ j.val then j.val - i.val else n + j.val - i.val

omit [NeZero n] in
theorem cyclicDistance_roll (a b i j : Fin n)
    (ha : a.val ≤ i.val) (hb : i.val < b.val) (hne : i ≠ j) :
    cyclicDistance i j = cyclicDistance (rollIndex a b i) j + 1 := by
  have hne' : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
  simp only [cyclicDistance, rollIndex_val_mid a b i ha hb]
  split_ifs <;> omega

/-- A same-n relocation preserves one protected root's local state (at its new
position), fixes every distant anchor, and increases all root-to-anchor distances
by exactly one. This is the geometric witness needed by the period-one argument. -/
theorem relocation_locality_core {A Q : Type*} (F : Rule r A Q)
    (I : Input n A) (a b i : Fin n) (anchors : Set (Fin n))
    (hab : a.val ≤ b.val) (ha : a.val + r ≤ i.val) (hb : i.val + r < b.val)
    (hanchors : ∀ j ∈ anchors, r ≤ j.val ∧ j.val + r < n ∧
      (j.val + r < a.val ∨ b.val + r < j.val)) :
    ∃ J : Input n A,
      outputRight F J i = outputRight F I (rollIndex a b i) ∧
      (∀ j ∈ anchors, outputRight F J j = outputRight F I j ∧
        cyclicDistance i j = cyclicDistance (rollIndex a b i) j + 1) ∧
      (∀ v, J.ident v = I.ident (rollIndex a b v)) ∧
      (∀ v, J.auxiliary v = I.auxiliary (rollIndex a b v)) := by
  refine ⟨relocate I a b hab, outputRight_relocate F I a b i hab ha hb, ?_,
    fun _ => rfl, fun _ => rfl⟩
  intro j hj
  obtain ⟨hjl, hjr, hjout⟩ := hanchors j hj
  refine ⟨outputRight_relocate_remote F I a b j hab hjl hjr hjout, ?_⟩
  apply cyclicDistance_roll a b i j (by omega) (by omega)
  intro heq
  have heq' := congrArg Fin.val heq
  omega

end LocalCyclesReflection

#print axioms LocalCyclesReflection.reflectIndex_involutive
#print axioms LocalCyclesReflection.view_reflect

#print axioms LocalCyclesReflection.view_reflect_remote
#print axioms LocalCyclesReflection.reflection_edge_state
#print axioms LocalCyclesReflection.reflection_locality_core

#print axioms LocalCyclesReflection.rollIndex_injective
#print axioms LocalCyclesReflection.view_relocate

#print axioms LocalCyclesReflection.view_relocate_remote
#print axioms LocalCyclesReflection.cyclicDistance_roll
#print axioms LocalCyclesReflection.relocation_locality_core
