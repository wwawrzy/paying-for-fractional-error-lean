import Paper.Preliminaries.PathPowerDomination
import GraphTheory.Local.LocalCyclesRamseyInput

/-! Finite Ramsey packing for arbitrary identifier-sensitive window rules.
This is the combinatorial part; a distributed execution still needs its
separate locality bridge before this becomes a LOCAL lower bound. -/
noncomputable section
namespace Paper.PathPowerRamsey
open PathPowerTreewidth PathPowerCounting SevenFoundation
open LocalCyclesRamseyReservoir LocalCyclesRamseyInput LocalCyclesRamseyViews

abbrev Rule (r : ℕ) := (Fin (2 * r + 1) → ℕ) → Bool

def color {r : ℕ} (F : Rule r) (S : Finset ℕ) : Fin 2 :=
  if h : S.card = 2 * r + 1 then ⟨(F (S.orderEmbOfFin h)).toNat, by cases F (S.orderEmbOfFin h) <;> decide⟩
  else 0

def window {n : ℕ} (ids : Fin n → ℕ) (r : ℕ) (i : Fin n)
    (hl : r ≤ i.val) (hr : i.val + r < n) : Fin (2 * r + 1) → ℕ :=
  fun z => ids ⟨i.val - r + z.val, by omega⟩

/-- A rule may use exact identifiers and may have been chosen for this exact n.
No condition on boundary outputs is imposed. -/
def Agrees {n r : ℕ} (F : Rule r) (ids : Fin n → ℕ) (out : Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (hl : r ≤ i.val) (hr : i.val + r < n), out i = F (window ids r i hl hr)

theorem block_constant {n L r : ℕ} (P : Blocks n L) (F : Rule r)
    (out : Fin n → Bool) (hagree : Agrees F P.input.ident out)
    (b : Fin P.k) (col : Fin 2)
    (hhom : ∀ A ⊆ P.sets b, A.card = 2 * r + 1 → color F A = col)
    (j : Fin L) (hl : r ≤ j.val) (hr : j.val + r < L) :
    (out (blockIndex (b.val * L) L (P.block_fits b) j)).toNat = col.val := by
  let i := blockIndex (b.val * L) L (P.block_fits b) j
  have hiL : r ≤ i.val := by dsimp [i, blockIndex]; omega
  have hiR : i.val + r < n := by have hh := P.block_fits b; dsimp [i, blockIndex]; omega
  let f := window P.input.ident r i hiL hiR
  let A := Finset.univ.image f
  have heq (z : Fin (2 * r + 1)) :
      (⟨i.val-r+z.val, by omega⟩ : Fin n) =
        blockIndex (b.val*L) L (P.block_fits b) (blockWindowIndex L r j hl hr z) := by
    apply Fin.ext
    dsimp [i, blockIndex, blockWindowIndex]
    omega
  have hf : StrictMono f := by
    intro x y hxy
    change P.input.ident _ < P.input.ident _
    rw [heq x, heq y]
    apply P.input_block_strictMono b
    change j.val-r+x.val < j.val-r+y.val
    omega
  have hcard : A.card = 2 * r + 1 := by
    rw [Finset.card_image_of_injective _ hf.injective]
    simp
  have hsub : A ⊆ P.sets b := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    change P.input.ident _ ∈ _
    rw [heq z]
    exact P.input_block_mem b _
  have he := Finset.orderEmbOfFin_unique hcard
    (f := f) (fun z => Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩) hf
  have hh := congrArg Fin.val (hhom A hsub hcard)
  have hh' : (F (A.orderEmbOfFin hcard)).toNat = col.val := by
    simpa only [color, dif_pos hcard] using hh
  rw [← he] at hh'
  change (out i).toNat = col.val
  rw [hagree i hiL hiR]
  exact hh'

/-- Domination forces the homogeneous color to be selected. -/
theorem block_selected {n L r : ℕ} (P : Blocks n L) (t : ℕ) (F : Rule r)
    (out : Fin n → Bool) (hagree : Agrees F P.input.ident out)
    (hdom : dominates (graph n t) (Finset.univ.filter (fun v => out v = true)))
    (hL : 2 * r + 2 * t + 1 ≤ L) (b : Fin P.k)
    (hhom : Homogeneous (color F) (2 * r + 1) (P.sets b)) :
    ∀ j : Fin L, r ≤ j.val → j.val + r < L →
      out (blockIndex (b.val * L) L (P.block_fits b) j) = true := by
  obtain ⟨col, hcol⟩ := hhom
  let j₀ : Fin L := ⟨r + t, by omega⟩
  let v := blockIndex (b.val * L) L (P.block_fits b) j₀
  obtain ⟨w, hw, hv⟩ := Finset.mem_biUnion.mp (hdom v)
  have hsel := (Finset.mem_filter.mp hw).2
  have hnear := (mem_closed_iff n t v w).mp hv
  have hbounds : b.val * L + r ≤ w.val ∧ w.val + r < b.val * L + L := by
    dsimp [v, blockIndex, j₀] at hnear
    omega
  let jw : Fin L := ⟨w.val - b.val * L, by omega⟩
  have hew : blockIndex (b.val * L) L (P.block_fits b) jw = w := by
    apply Fin.ext
    dsimp [blockIndex, jw]
    omega
  have hcw := block_constant P F out hagree b col hcol jw
    (by dsimp [jw]; omega) (by dsimp [jw]; omega)
  rw [hew, hsel] at hcw
  intro j hl hr
  have hcj := block_constant P F out hagree b col hcol j hl hr
  have hh : (out (blockIndex (b.val * L) L (P.block_fits b) j)).toNat = 1 := hcj.trans hcw.symm
  cases he : out (blockIndex (b.val * L) L (P.block_fits b) j) <;> simp_all <;> omega

/-- Actual IDs in 1,...,n and an explicit finite boundary/remainder ledger. -/
theorem packing (n t r L : ℕ) (hL : 2 * r + 2 * t + 1 ≤ L) (F : Rule r) :
    ∃ ids : Fin n → ℕ, Function.Injective ids ∧
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
      ∀ out : Fin n → Bool, Agrees F ids out →
        dominates (graph n t) (Finset.univ.filter (fun v => out v = true)) →
        ∃ blocks rest : ℕ,
          n = blocks * L + rest ∧
          rest < ramseyBound 2 (2 * r) L ∧
          blocks * (L - (2 * r + 1)) ≤ (Finset.univ.filter (fun v => out v = true)).card := by
  obtain ⟨P, hrest, hhom⟩ := exists_blocks n 2 (2*r) L (by omega) (by omega) (color F)
  refine ⟨P.input.ident, P.input.unique, P.input_bounds, ?_⟩
  intro out hagree hdom
  refine ⟨P.k, P.rest.card, P.count, hrest, ?_⟩
  rw [← P.loopSet_card r (by omega)]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨b, _, hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    block_selected P t F out hagree hdom hL b (hhom b) _
      (by dsimp; omega) (by dsimp; have hz := z.isLt; omega)⟩

end Paper.PathPowerRamsey
