import GraphTheory.Local.LocalCyclesRamseyReservoir
import GraphTheory.Local.LocalCyclesReflection

/-! The Ramsey coloring is the actual fixed-size LOCAL rule on sorted ID
windows. Homogeneity yields equal outgoing states in sorted block interiors.
No order-invariance assumption about the local rule is made. -/

noncomputable section

namespace LocalCyclesRamseyViews

open LocalCyclesRamseyReservoir LocalCyclesReflection

def middle (r : ℕ) : Fin (2*r+1) := ⟨r, by omega⟩
def before {r : ℕ} (j : Fin r) : Fin (2*r+1) := ⟨r-(j.val+1), by omega⟩
def after {r : ℕ} (j : Fin r) : Fin (2*r+1) := ⟨r+j.val+1, by omega⟩

def canonicalView {r : ℕ} (ids : Fin (2*r+1) → ℕ) : View r Unit where
  root := (ids (middle r), ())
  branch port j := if port then ((ids (after j), ()), false)
    else ((ids (before j), ()), true)

def color {r q : ℕ} (hq : 0 < q) (F : Rule r Unit (Fin q)) (S : Finset ℕ) : Fin q :=
  if hS : S.card = 2*r+1 then F (canonicalView (S.orderEmbOfFin hS)) true else ⟨0, hq⟩

variable {n : ℕ} [NeZero n]

def windowIndex (r : ℕ) (i : Fin n) (hleft : r ≤ i.val) (hright : i.val+r < n)
    (j : Fin (2*r+1)) : Fin n := ⟨i.val-r+j.val, by omega⟩

omit [NeZero n] in
theorem windowIndex_injective (r : ℕ) (i : Fin n) (hleft : r ≤ i.val)
    (hright : i.val+r < n) : Function.Injective (windowIndex r i hleft hright) := by
  intro a b hab
  have h := congrArg Fin.val hab
  dsimp [windowIndex] at h
  apply Fin.ext
  omega

omit [NeZero n] in
theorem windowIndex_middle (r : ℕ) (i : Fin n) (hl : r ≤ i.val) (hr : i.val+r < n) :
    windowIndex r i hl hr (middle r) = i := by
  apply Fin.ext
  dsimp [windowIndex, middle]
  omega

theorem windowIndex_before (r : ℕ) (i : Fin n) (hl : r ≤ i.val) (hr : i.val+r < n)
    (j : Fin r) : windowIndex r i hl hr (before j) = left i (j.val+1) := by
  apply Fin.ext
  rw [left_val i (j.val+1) (by omega)]
  dsimp [windowIndex, before]
  omega

theorem windowIndex_after (r : ℕ) (i : Fin n) (hl : r ≤ i.val) (hr : i.val+r < n)
    (j : Fin r) : windowIndex r i hl hr (after j) = right i (j.val+1) := by
  apply Fin.ext
  rw [right_val i (j.val+1) (by omega)]
  dsimp [windowIndex, after]
  omega

def windowIDs (I : Input n Unit) (r : ℕ) (i : Fin n)
    (hl : r ≤ i.val) (hr : i.val+r < n) : Finset ℕ :=
  Finset.univ.image (fun j => I.ident (windowIndex r i hl hr j))

omit [NeZero n] in
theorem windowIDs_card (I : Input n Unit) (r : ℕ) (i : Fin n)
    (hl : r ≤ i.val) (hr : i.val+r < n) :
    (windowIDs I r i hl hr).card = 2*r+1 := by
  have hinj : Function.Injective (fun j => I.ident (windowIndex r i hl hr j)) :=
    I.unique.comp (windowIndex_injective r i hl hr)
  rw [windowIDs, Finset.card_image_of_injective _ hinj]
  simp

theorem view_eq_canonical (I : Input n Unit) (r : ℕ) (i : Fin n)
    (hl : r ≤ i.val) (hr : i.val+r < n) (hports : ∀ v, I.leftPort v = false) :
    view I r i = canonicalView (fun j => I.ident (windowIndex r i hl hr j)) := by
  apply View.ext
  · simp [view, canonicalView, windowIndex_middle]
  · funext port j
    cases port <;>
      simp [view, canonicalView, hports, windowIndex_before, windowIndex_after]

/-- A sorted actual radius-r window is exactly the window used by the
Ramsey coloring, including the port-rooted view. -/
theorem outputRight_eq_color (I : Input n Unit) {r q : ℕ} (hq : 0 < q)
    (F : Rule r Unit (Fin q)) (i : Fin n) (hl : r ≤ i.val) (hr : i.val+r < n)
    (hports : ∀ v, I.leftPort v = false)
    (hmono : StrictMono (fun j => I.ident (windowIndex r i hl hr j))) :
    outputRight F I i = color hq F (windowIDs I r i hl hr) := by
  have he := Finset.orderEmbOfFin_unique (windowIDs_card I r i hl hr)
    (f := fun j => I.ident (windowIndex r i hl hr j))
    (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) hmono
  simp only [color, dif_pos (windowIDs_card I r i hl hr), outputRight, hports, Bool.not_false]
  rw [view_eq_canonical I r i hl hr hports, he]

theorem homogeneous_window_output (I : Input n Unit) {r q : ℕ} (hq : 0 < q)
    (F : Rule r Unit (Fin q)) (T : Finset ℕ) (col : Fin q)
    (hhom : ∀ A ⊆ T, A.card = 2*r+1 → color hq F A = col)
    (i : Fin n) (hl : r ≤ i.val) (hr : i.val+r < n)
    (hports : ∀ v, I.leftPort v = false)
    (hmono : StrictMono (fun j => I.ident (windowIndex r i hl hr j)))
    (hsub : windowIDs I r i hl hr ⊆ T) : outputRight F I i = col := by
  rw [outputRight_eq_color I hq F i hl hr hports hmono]
  exact hhom _ hsub (windowIDs_card I r i hl hr)

def blockIndex (a L : ℕ) (ha : a+L ≤ n) (j : Fin L) : Fin n :=
  ⟨a+j.val, by omega⟩

def blockWindowIndex (L r : ℕ) (j : Fin L) (hl : r ≤ j.val) (hr : j.val+r < L)
    (z : Fin (2*r+1)) : Fin L := ⟨j.val-r+z.val, by omega⟩

omit [NeZero n] in
theorem window_in_block (a L r : ℕ) (ha : a+L ≤ n) (j : Fin L)
    (hl : r ≤ j.val) (hr : j.val+r < L)
    (hleft : r ≤ (blockIndex a L ha j).val)
    (hright : (blockIndex a L ha j).val+r < n) (z : Fin (2*r+1)) :
    windowIndex r (blockIndex a L ha j) hleft hright z =
      blockIndex a L ha (blockWindowIndex L r j hl hr z) := by
  apply Fin.ext
  dsimp [windowIndex, blockIndex, blockWindowIndex]
  omega

/-- The actual output in every interior window of a sorted homogeneous block
equals its Ramsey color. The local rule F may depend arbitrarily on exact n. -/
theorem sorted_block_constant (I : Input n Unit) {r q : ℕ} (hq : 0 < q)
    (F : Rule r Unit (Fin q)) (T : Finset ℕ) (col : Fin q)
    (hhom : ∀ A ⊆ T, A.card = 2*r+1 → color hq F A = col)
    (hports : ∀ v, I.leftPort v = false) (a L : ℕ) (ha : a+L ≤ n)
    (hmono : StrictMono (fun j : Fin L => I.ident (blockIndex a L ha j)))
    (hIDs : ∀ j : Fin L, I.ident (blockIndex a L ha j) ∈ T)
    (j : Fin L) (hl : r ≤ j.val) (hr : j.val+r < L) :
    outputRight F I (blockIndex a L ha j) = col := by
  have hleft : r ≤ (blockIndex a L ha j).val := by dsimp [blockIndex]; omega
  have hright : (blockIndex a L ha j).val+r < n := by dsimp [blockIndex]; omega
  apply homogeneous_window_output I hq F T col hhom _ hleft hright hports
  · intro x y hxy
    dsimp only
    rw [window_in_block a L r ha j hl hr hleft hright x,
      window_in_block a L r ha j hl hr hleft hright y]
    apply hmono
    change j.val-r+x.val < j.val-r+y.val
    exact Nat.add_lt_add_left hxy _
  · intro b hb
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hb
    rw [window_in_block a L r ha j hl hr hleft hright z]
    exact hIDs _

theorem sorted_block_loop (I : Input n Unit) {r q : ℕ} (hq : 0 < q)
    (F : Rule r Unit (Fin q)) (T : Finset ℕ) (col : Fin q)
    (hhom : ∀ A ⊆ T, A.card = 2*r+1 → color hq F A = col)
    (hports : ∀ v, I.leftPort v = false) (a L : ℕ) (ha : a+L ≤ n)
    (hmono : StrictMono (fun j : Fin L => I.ident (blockIndex a L ha j)))
    (hIDs : ∀ j : Fin L, I.ident (blockIndex a L ha j) ∈ T)
    (j : Fin L) (hl : r ≤ j.val) (hr : j.val+r+1 < L) :
    outputRight F I (blockIndex a L ha j) =
      outputRight F I (right (blockIndex a L ha j) 1) := by
  let j' : Fin L := ⟨j.val+1, by omega⟩
  have hj' : right (blockIndex a L ha j) 1 = blockIndex a L ha j' := by
    apply Fin.ext
    rw [right_val _ 1 (by dsimp [blockIndex]; omega)]
    dsimp [blockIndex, j']
    omega
  rw [hj']
  exact (sorted_block_constant I hq F T col hhom hports a L ha hmono hIDs j hl (by omega)).trans
    (sorted_block_constant I hq F T col hhom hports a L ha hmono hIDs j'
      (by dsimp [j']; omega) (by dsimp [j']; omega)).symm

def blockLoops (a L r : ℕ) (ha : a+L ≤ n) (hL : 2*r+1 ≤ L) : Finset (Fin n) :=
  Finset.univ.image (fun z : Fin (L-(2*r+1)) =>
    blockIndex a L ha ⟨r+z.val, by omega⟩)

omit [NeZero n] in
theorem blockLoops_card (a L r : ℕ) (ha : a+L ≤ n) (hL : 2*r+1 ≤ L) :
    (blockLoops a L r ha hL).card = L-(2*r+1) := by
  have hinj : Function.Injective (fun z : Fin (L-(2*r+1)) =>
      blockIndex a L ha ⟨r+z.val, by omega⟩) := by
    intro x y hxy
    have he := congrArg Fin.val hxy
    dsimp [blockIndex] at he
    apply Fin.ext
    omega
  rw [blockLoops, Finset.card_image_of_injective _ hinj]
  simp

theorem actual_block_loops (I : Input n Unit) {r q : ℕ} (hq : 0 < q)
    (F : Rule r Unit (Fin q)) (T : Finset ℕ) (col : Fin q)
    (hhom : ∀ A ⊆ T, A.card = 2*r+1 → color hq F A = col)
    (hports : ∀ v, I.leftPort v = false) (a L : ℕ) (ha : a+L ≤ n)
    (hL : 2*r+1 ≤ L)
    (hmono : StrictMono (fun j : Fin L => I.ident (blockIndex a L ha j)))
    (hIDs : ∀ j : Fin L, I.ident (blockIndex a L ha j) ∈ T) :
    ∀ i ∈ blockLoops a L r ha hL, outputRight F I i = outputRight F I (right i 1) := by
  intro i hi
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
  apply sorted_block_loop I hq F T col hhom hports a L ha hmono hIDs
  · dsimp
    omega
  · dsimp
    have hz := z.isLt
    omega

#print axioms outputRight_eq_color
#print axioms homogeneous_window_output
#print axioms sorted_block_constant
#print axioms actual_block_loops

end LocalCyclesRamseyViews
