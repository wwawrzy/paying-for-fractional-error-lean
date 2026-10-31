import GraphTheory.Local.LocalCyclesRamseyViews
import GraphTheory.Local.LocalCyclesRamseyPacking

/-! Place the extracted homogeneous blocks on one actual n-cycle, preserving
all original identifiers. Finite equivalences provide the concatenation. -/

noncomputable section

namespace LocalCyclesRamseyInput

open LocalCyclesRamseyReservoir LocalCyclesRamseyViews LocalCyclesRamseyPacking
open LocalCyclesReflection
open scoped BigOperators

structure Blocks (n L : ℕ) where
  k : ℕ
  sets : Fin k → Finset ℕ
  rest : Finset ℕ
  card : ∀ b, (sets b).card = L
  disjoint : ∀ b c, b ≠ c → Disjoint (sets b) (sets c)
  rest_disjoint : ∀ b, Disjoint (sets b) rest
  count : n = k*L+rest.card
  bounds : ∀ b x, x ∈ sets b → 1 ≤ x ∧ x ≤ n
  rest_bounds : ∀ x, x ∈ rest → 1 ≤ x ∧ x ≤ n

namespace Blocks

variable {n L : ℕ} (P : Blocks n L)

def position : ((Fin P.k × Fin L) ⊕ Fin P.rest.card) ≃ Fin n :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (Fin.castOrderIso P.count.symm).toEquiv

def label : ((Fin P.k × Fin L) ⊕ Fin P.rest.card) → ℕ
  | .inl (b, j) => (P.sets b).orderEmbOfFin (P.card b) j
  | .inr j => P.rest.orderEmbOfFin rfl j

theorem label_injective : Function.Injective P.label := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      rcases x with ⟨b, i⟩
      rcases y with ⟨c, j⟩
      dsimp only [label] at hxy
      by_cases hbc : b = c
      · subst c
        have hij := (P.sets b).orderEmbOfFin (P.card b) |>.injective hxy
        subst j
        rfl
      · have hi := Finset.orderEmbOfFin_mem (P.sets b) (P.card b) i
        have hj := Finset.orderEmbOfFin_mem (P.sets c) (P.card c) j
        exact False.elim ((Finset.disjoint_left.mp (P.disjoint b c hbc)) hi (hxy.symm ▸ hj))
    | inr j =>
      rcases x with ⟨b, i⟩
      dsimp only [label] at hxy
      have hi := Finset.orderEmbOfFin_mem (P.sets b) (P.card b) i
      have hj := Finset.orderEmbOfFin_mem P.rest rfl j
      exact False.elim ((Finset.disjoint_left.mp (P.rest_disjoint b)) hi (hxy.symm ▸ hj))
  | inr i =>
    cases y with
    | inl y =>
      rcases y with ⟨b, j⟩
      dsimp only [label] at hxy
      have hi := Finset.orderEmbOfFin_mem P.rest rfl i
      have hj := Finset.orderEmbOfFin_mem (P.sets b) (P.card b) j
      exact False.elim ((Finset.disjoint_left.mp (P.rest_disjoint b)) hj (hxy ▸ hi))
    | inr j =>
      have hij := (P.rest.orderEmbOfFin rfl).injective hxy
      subst j
      rfl

def input : Input n Unit where
  ident i := P.label (P.position.symm i)
  unique := P.label_injective.comp P.position.symm.injective
  auxiliary _ := ()
  leftPort _ := false

theorem input_bounds (i : Fin n) : 1 ≤ P.input.ident i ∧ P.input.ident i ≤ n := by
  change 1 ≤ P.label (P.position.symm i) ∧ P.label (P.position.symm i) ≤ n
  cases h : P.position.symm i with
  | inl x =>
    exact P.bounds x.1 _ (Finset.orderEmbOfFin_mem (P.sets x.1) (P.card x.1) x.2)
  | inr j => exact P.rest_bounds _ (Finset.orderEmbOfFin_mem P.rest rfl j)

theorem block_fits (b : Fin P.k) : b.val*L+L ≤ n := by
  have hh := Nat.mul_le_mul_right L (show b.val+1 ≤ P.k by omega)
  nlinarith [P.count]

theorem position_block (b : Fin P.k) (j : Fin L) :
    P.position (.inl (b,j)) = blockIndex (b.val*L) L (P.block_fits b) j := by
  apply Fin.ext
  simp [position, finProdFinEquiv, blockIndex, Nat.add_comm, Nat.mul_comm]

theorem input_block (b : Fin P.k) (j : Fin L) :
    P.input.ident (blockIndex (b.val*L) L (P.block_fits b) j) =
      (P.sets b).orderEmbOfFin (P.card b) j := by
  rw [← P.position_block b j]
  change P.label (P.position.symm (P.position (.inl (b,j)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem input_block_strictMono (b : Fin P.k) :
    StrictMono (fun j : Fin L => P.input.ident (blockIndex (b.val*L) L (P.block_fits b) j)) := by
  simp_rw [P.input_block]
  exact (P.sets b).orderEmbOfFin (P.card b) |>.strictMono

theorem input_block_mem (b : Fin P.k) (j : Fin L) :
    P.input.ident (blockIndex (b.val*L) L (P.block_fits b) j) ∈ P.sets b := by
  rw [P.input_block]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem block_loop_interval (r : ℕ) (hL : 2*r+1 ≤ L) (b : Fin P.k)
    (i : Fin n) (hi : i ∈ blockLoops (b.val*L) L r (P.block_fits b) hL) :
    b.val*L ≤ i.val ∧ i.val < b.val*L+L := by
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
  dsimp [blockIndex]
  have hz := z.isLt
  omega

theorem block_loops_disjoint (r : ℕ) (hL : 2*r+1 ≤ L)
    (b c : Fin P.k) (hbc : b ≠ c) :
    Disjoint (blockLoops (b.val*L) L r (P.block_fits b) hL)
      (blockLoops (c.val*L) L r (P.block_fits c) hL) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hb := P.block_loop_interval r hL b i hi
  have hc := P.block_loop_interval r hL c i hj
  have hne : b.val ≠ c.val := fun hh => hbc (Fin.ext hh)
  rcases lt_or_gt_of_ne hne with h | h
  · have hmul := Nat.mul_le_mul_right L (show b.val+1 ≤ c.val by omega)
    nlinarith
  · have hmul := Nat.mul_le_mul_right L (show c.val+1 ≤ b.val by omega)
    nlinarith

def loopSet (r : ℕ) (hL : 2*r+1 ≤ L) : Finset (Fin n) :=
  Finset.univ.biUnion (fun b => blockLoops (b.val*L) L r (P.block_fits b) hL)

theorem loopSet_card (r : ℕ) (hL : 2*r+1 ≤ L) :
    (P.loopSet r hL).card = P.k*(L-(2*r+1)) := by
  classical
  unfold loopSet
  rw [Finset.card_biUnion (fun b _ c _ hbc => P.block_loops_disjoint r hL b c hbc)]
  simp [blockLoops_card, mul_comm]

theorem loopSet_ledger (r : ℕ) (hL : 2*r+1 ≤ L) :
    (P.loopSet r hL).card+P.rest.card+P.k*(2*r+1) = n := by
  rw [P.loopSet_card r hL]
  exact block_loop_budget n P.k L P.rest.card (2*r+1) P.count hL

theorem input_polynomial_ID_bounds [NeZero n] (degree : ℕ) (hdegree : 1 ≤ degree)
    (i : Fin n) : 1 ≤ P.input.ident i ∧ P.input.ident i ≤ n^degree := by
  obtain ⟨hl, hr⟩ := P.input_bounds i
  refine ⟨hl, hr.trans ?_⟩
  calc
    n = n^1 := by simp
    _ ≤ n^degree := Nat.pow_le_pow_right (NeZero.pos n) hdegree

theorem loopSet_actual [NeZero n] {r q : ℕ} (hq : 0 < q) (hL : 2*r+1 ≤ L)
    (F : Rule r Unit (Fin q))
    (hhom : ∀ b, Homogeneous (color hq F) (2*r+1) (P.sets b)) :
    ∀ i ∈ P.loopSet r hL, outputRight F P.input i = outputRight F P.input (right i 1) := by
  intro i hi
  obtain ⟨b, _, hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨col, hcol⟩ := hhom b
  exact actual_block_loops P.input hq F (P.sets b) col hcol (fun _ => rfl)
    (b.val*L) L (P.block_fits b) hL (P.input_block_strictMono b) (P.input_block_mem b) i hi

end Blocks

/-- Convert the proved finite Ramsey partition into an actual concatenation
of blocks, with identifiers exactly from 1,...,n. -/
theorem exists_blocks (n q k L : ℕ) (hq : 0 < q) (hL : k+1 ≤ L)
    (f : Finset ℕ → Fin q) :
    ∃ P : Blocks n L, P.rest.card < ramseyBound q k L ∧
      ∀ b, Homogeneous f (k+1) (P.sets b) := by
  classical
  obtain ⟨blocks, rest, hdis, hblock, hcover, hrestdis, hcount, hrest⟩ :=
    homogeneous_partition q k L hq hL f (Finset.Icc 1 n)
  let e : Fin blocks.card ≃ blocks := (Fintype.equivFinOfCardEq (by simp)).symm
  have hsub : ∀ b : Fin blocks.card, (e b).val ⊆ Finset.Icc 1 n := by
    intro b x hx
    rw [← hcover]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(e b).val, (e b).property, hx⟩)
  have hrestSub : rest ⊆ Finset.Icc 1 n := by
    rw [← hcover]
    exact Finset.subset_union_right
  let P : Blocks n L := {
    k := blocks.card
    sets := fun b => (e b).val
    rest := rest
    card := fun b => (hblock _ (e b).property).1
    disjoint := by
      intro b c hbc
      apply hdis (e b).property (e c).property
      intro he
      exact hbc (e.injective (Subtype.ext he))
    rest_disjoint := by
      intro b
      apply hrestdis.mono_left
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨(e b).val, (e b).property, hx⟩
    count := by simpa using hcount
    bounds := fun b x hx => Finset.mem_Icc.mp (hsub b hx)
    rest_bounds := fun x hx => Finset.mem_Icc.mp (hrestSub hx)
  }
  exact ⟨P, hrest, fun b => (hblock _ (e b).property).2⟩

/-- Exact fixed-n LOCAL bridge: a correct algorithm cannot avoid the actual
homogeneous loops by depending on n, on ID magnitudes, or on the ports.
The construction gives one allowed port assignment and IDs in 1,...,n. -/
theorem actual_ramsey_loop_packing {n : ℕ} [NeZero n] (q r L : ℕ)
    (hq : 0 < q) (hL : 2*r+1 ≤ L) (F : Rule r Unit (Fin q)) :
    ∃ (I : Input n Unit) (loops : Finset (Fin n)) (blocks rest : ℕ),
      (∀ i, 1 ≤ I.ident i ∧ I.ident i ≤ n) ∧
      n = blocks*L+rest ∧ rest < ramseyBound q (2*r) L ∧
      loops.card = blocks*(L-(2*r+1)) ∧
      ∀ i ∈ loops, outputRight F I i = outputRight F I (right i 1) := by
  obtain ⟨P, hrest, hhom⟩ := exists_blocks n q (2*r) L hq hL (color hq F)
  exact ⟨P.input, P.loopSet r hL, P.k, P.rest.card, P.input_bounds,
    P.count, hrest, P.loopSet_card r hL, P.loopSet_actual hq hL F hhom⟩

#print axioms Blocks.label_injective
#print axioms Blocks.input_bounds
#print axioms Blocks.input_block_strictMono
#print axioms Blocks.loopSet_card
#print axioms exists_blocks
#print axioms actual_ramsey_loop_packing

end LocalCyclesRamseyInput
