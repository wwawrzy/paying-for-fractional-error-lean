/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import GraphTheory.SimpleGraph.Domination.Basic
import GraphTheory.SimpleGraph.Domination.Bounds

/-!
# Total Dominating Sets in Simple Graphs

A set `D` is a *total* dominating set of a graph `G` if **every** vertex
(including those in `D`) is adjacent to some vertex in `D`.  Equivalently,
`D` totally dominates `G` iff the open neighborhood `N(D)` covers all of `V`,
in contrast to ordinary domination which only requires the closed
neighborhood `N[D]` to cover `V`.

Total domination is only possible when `G` has no isolated vertices, since
an isolated vertex can never be adjacent to any member of `D`.

## Main definitions

* `SimpleGraph.IsTotalDominatingSet` — a `Set`-based total dominating set predicate.
* `SimpleGraph.IsTotalDominatingSetFinset` — a `Finset`-based variant.
* `SimpleGraph.dominationNumber` — `γ(G)`, the minimum size of a dominating set
  (over a finite vertex type).
* `SimpleGraph.totalDominationNumber` — `γ_t(G)`, the minimum size of a total
  dominating set.

## Main results

* `SimpleGraph.IsTotalDominatingSet.isDominatingSet` — a total dominating set is
  a dominating set.
* `SimpleGraph.IsTotalDominatingSet.no_isolated` — if a total dominating set
  exists then no vertex is isolated (every vertex has a neighbor).
* `SimpleGraph.dominationNumber_le_totalDominationNumber` — `γ(G) ≤ γ_t(G)`.
* `SimpleGraph.totalDominationNumber_le_two_mul_dominationNumber` —
  `γ_t(G) ≤ 2 · γ(G)` for graphs without isolated vertices.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A set `D` is a **total dominating set** if every vertex (including those in
`D`) is adjacent to some vertex in `D`.  Unlike `IsDominatingSet`, there is no
`v ∈ D` disjunct: every vertex must have a *neighbor* in `D`. -/
def IsTotalDominatingSet (D : Set V) : Prop :=
  ∀ v : V, ∃ w ∈ D, G.Adj v w

variable {G}

/-- A total dominating set is a dominating set: if `v` has a neighbor `w ∈ D`,
then in particular the dominating-set disjunction `v ∈ D ∨ ∃ w ∈ D, G.Adj v w`
holds via its right branch. -/
theorem IsTotalDominatingSet.isDominatingSet {D : Set V}
    (hD : G.IsTotalDominatingSet D) : G.IsDominatingSet D :=
  fun v ↦ Or.inr (hD v)

/-- If a total dominating set exists, then `G` has no isolated vertices: every
vertex is adjacent to some other vertex. -/
theorem IsTotalDominatingSet.no_isolated {D : Set V}
    (hD : G.IsTotalDominatingSet D) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨w, _, hadj⟩ := hD v
  exact ⟨w, hadj⟩

/-- A larger set is still total dominating: if `D` totally dominates and
`D ⊆ D'`, then `D'` totally dominates. -/
theorem IsTotalDominatingSet.mono {D D' : Set V} (hD : G.IsTotalDominatingSet D)
    (h : D ⊆ D') : G.IsTotalDominatingSet D' :=
  fun v ↦ let ⟨w, hw, hadj⟩ := hD v; ⟨w, h hw, hadj⟩

section Finset

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A `Finset` version of `IsTotalDominatingSet`: every vertex is adjacent to
some member of `D`. -/
def IsTotalDominatingSetFinset (D : Finset V) : Prop :=
  ∀ v : V, ∃ w ∈ D, G.Adj v w

variable {G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `Finset` and `Set` notions of total domination agree (via the coercion
`↑D : Set V`). -/
theorem isTotalDominatingSetFinset_iff_coe {D : Finset V} :
    G.IsTotalDominatingSetFinset D ↔ G.IsTotalDominatingSet (↑D : Set V) := by
  constructor
  · intro hD v
    obtain ⟨w, hw, hadj⟩ := hD v
    exact ⟨w, Finset.mem_coe.mpr hw, hadj⟩
  · intro hD v
    obtain ⟨w, hw, hadj⟩ := hD v
    exact ⟨w, Finset.mem_coe.mp hw, hadj⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A `Finset` total dominating set is a `Finset` dominating set. -/
theorem IsTotalDominatingSetFinset.isDominatingSetFinset {D : Finset V}
    (hD : G.IsTotalDominatingSetFinset D) : G.IsDominatingSetFinset D :=
  fun v ↦ Or.inr (hD v)

end Finset

/-!
## Domination numbers

We define the (total) domination number as the infimum, over all (total)
dominating `Finset`s, of their cardinality.  When no total dominating set
exists (i.e. `G` has an isolated vertex), `totalDominationNumber` is `0` by the
`Nat.sInf ∅ = 0` convention; the meaningful comparison lemmas below therefore
carry an explicit "total dominating set exists" hypothesis.
-/

section Number

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The **domination number** `γ(G)`: the least cardinality of a dominating
`Finset`.  Well-defined because `Finset.univ` always dominates. -/
noncomputable def dominationNumber : ℕ :=
  sInf {n | ∃ D : Finset V, G.IsDominatingSetFinset D ∧ D.card = n}

/-- The **total domination number** `γ_t(G)`: the least cardinality of a total
dominating `Finset`.  If no total dominating set exists this is `0`. -/
noncomputable def totalDominationNumber : ℕ :=
  sInf {n | ∃ D : Finset V, G.IsTotalDominatingSetFinset D ∧ D.card = n}

variable {G}

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- `Finset.univ` is a dominating set. -/
theorem isDominatingSetFinset_univ : G.IsDominatingSetFinset Finset.univ :=
  fun v ↦ Or.inl (Finset.mem_univ v)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The set of cardinalities of dominating sets is nonempty (it contains
`|V|`). -/
theorem dominationNumber_spec_nonempty :
    {n | ∃ D : Finset V, G.IsDominatingSetFinset D ∧ D.card = n}.Nonempty :=
  ⟨Finset.univ.card, Finset.univ, isDominatingSetFinset_univ, rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The domination number is attained: there is a dominating set of size
`γ(G)`. -/
theorem exists_isDominatingSetFinset_card_eq_dominationNumber :
    ∃ D : Finset V, G.IsDominatingSetFinset D ∧ D.card = G.dominationNumber :=
  Nat.sInf_mem dominationNumber_spec_nonempty

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Any dominating set has cardinality at least `γ(G)`. -/
theorem IsDominatingSetFinset.dominationNumber_le {D : Finset V}
    (hD : G.IsDominatingSetFinset D) : G.dominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A finite dominating set is minimum exactly when its cardinality is the
domination number. -/
theorem isMinimumDominatingSetFinset_iff_card_eq_dominationNumber
    {D : Finset V} :
    G.IsMinimumDominatingSetFinset D ↔
      G.IsDominatingSetFinset D ∧ D.card = G.dominationNumber := by
  constructor
  · intro hD
    obtain ⟨D₀, hD₀, hcard₀⟩ :=
      exists_isDominatingSetFinset_card_eq_dominationNumber (G := G)
    refine ⟨hD.isDominatingSetFinset, Nat.le_antisymm ?_ ?_⟩
    · simpa [hcard₀] using hD.card_le hD₀
    · exact hD.isDominatingSetFinset.dominationNumber_le
  · rintro ⟨hD, hcard⟩
    refine ⟨hD, fun D' hD' ↦ ?_⟩
    rw [hcard]
    exact hD'.dominationNumber_le

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Every finite graph has a minimum dominating set. -/
theorem exists_minimumDominatingSetFinset :
    ∃ D : Finset V, G.IsMinimumDominatingSetFinset D := by
  obtain ⟨D, hD, hcard⟩ :=
    exists_isDominatingSetFinset_card_eq_dominationNumber (G := G)
  exact ⟨D, isMinimumDominatingSetFinset_iff_card_eq_dominationNumber.mpr ⟨hD, hcard⟩⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The domination number of a finite graph is at most its number of vertices. -/
theorem dominationNumber_le_card : G.dominationNumber ≤ Fintype.card V := by
  simpa using (isDominatingSetFinset_univ (G := G)).dominationNumber_le

/-- `D` is a factor-`c` approximation for MDS when it dominates and its size is
at most `c · γ(G)`. -/
def IsDominatingSetApproximation (D : Finset V) (c : ℕ) : Prop :=
  G.IsDominatingSetFinset D ∧ D.card ≤ c * G.dominationNumber

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An MDS approximation is, in particular, a dominating set. -/
theorem IsDominatingSetApproximation.isDominatingSetFinset {D : Finset V} {c : ℕ}
    (hD : G.IsDominatingSetApproximation D c) : G.IsDominatingSetFinset D :=
  hD.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An approximation guarantee remains valid after weakening its factor. -/
theorem IsDominatingSetApproximation.mono {D : Finset V} {c c' : ℕ}
    (hD : G.IsDominatingSetApproximation D c) (hcc' : c ≤ c') :
    G.IsDominatingSetApproximation D c' :=
  ⟨hD.1, hD.2.trans (Nat.mul_le_mul_right G.dominationNumber hcc')⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Factor-one MDS approximations are exactly minimum dominating sets. -/
theorem isDominatingSetApproximation_one_iff {D : Finset V} :
    G.IsDominatingSetApproximation D 1 ↔ G.IsMinimumDominatingSetFinset D := by
  rw [isMinimumDominatingSetFinset_iff_card_eq_dominationNumber]
  constructor
  · rintro ⟨hD, hcard⟩
    refine ⟨hD, Nat.le_antisymm ?_ hD.dominationNumber_le⟩
    simpa using hcard
  · rintro ⟨hD, hcard⟩
    exact ⟨hD, by simp [hcard]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Any total dominating set has cardinality at least `γ_t(G)`. -/
theorem IsTotalDominatingSetFinset.totalDominationNumber_le {D : Finset V}
    (hD : G.IsTotalDominatingSetFinset D) : G.totalDominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **`γ(G) ≤ γ_t(G)`.**  Whenever a total dominating set exists, the domination
number is at most the total domination number: an optimal total dominating set
is in particular a dominating set, so its size `γ_t(G)` bounds `γ(G)`. -/
theorem dominationNumber_le_totalDominationNumber
    (h : ∃ D : Finset V, G.IsTotalDominatingSetFinset D) :
    G.dominationNumber ≤ G.totalDominationNumber := by
  -- Pick a total dominating set of size `γ_t(G)`.
  obtain ⟨D₀, hD₀⟩ := h
  have hne : {n | ∃ D : Finset V, G.IsTotalDominatingSetFinset D ∧ D.card = n}.Nonempty :=
    ⟨D₀.card, D₀, hD₀, rfl⟩
  obtain ⟨D, hDtot, hDcard⟩ := Nat.sInf_mem hne
  -- It is also a dominating set, so `γ(G) ≤ |D| = γ_t(G)`.
  have : G.dominationNumber ≤ D.card :=
    hDtot.isDominatingSetFinset.dominationNumber_le
  rwa [hDcard] at this

omit [DecidableRel G.Adj] in
/-- **`γ_t(G) ≤ 2·γ(G)`** for graphs without isolated vertices.

Construction: take an optimal dominating set `D` of size `γ(G)`.  Choose for
every vertex a fixed neighbor `f v` (possible since there are no isolated
vertices).  Then `D' := D ∪ D.image f` is a *total* dominating set:

* if `v ∈ D`, then `f v ∈ D.image f ⊆ D'` and `v` is adjacent to `f v`;
* if `v ∉ D`, then since `D` dominates, `v` has a neighbor `w ∈ D ⊆ D'`.

Either way `v` has a neighbor in `D'`, and
`|D'| ≤ |D| + |D.image f| ≤ |D| + |D| = 2·|D| = 2·γ(G)`. -/
theorem totalDominationNumber_le_two_mul_dominationNumber
    (hmin : ∀ v : V, ∃ w, G.Adj v w) :
    G.totalDominationNumber ≤ 2 * G.dominationNumber := by
  classical
  -- A fixed-neighbor function: `f v` is some vertex adjacent to `v`.
  choose f hf using hmin
  -- An optimal dominating set `D` with `|D| = γ(G)`.
  obtain ⟨D, hDom, hDcard⟩ := exists_isDominatingSetFinset_card_eq_dominationNumber (G := G)
  -- The augmented set.
  set D' : Finset V := D ∪ D.image f with hD'
  -- `D'` is total dominating.
  have hD'tot : G.IsTotalDominatingSetFinset D' := by
    intro v
    rcases hDom v with hv | ⟨w, hw, hadj⟩
    · -- `v ∈ D`: use the chosen neighbor `f v ∈ D.image f`.
      refine ⟨f v, ?_, hf v⟩
      rw [hD', Finset.mem_union]
      exact Or.inr (Finset.mem_image_of_mem f hv)
    · -- `v ∉ D` (or in general): `v` is adjacent to `w ∈ D ⊆ D'`.
      refine ⟨w, ?_, hadj⟩
      rw [hD', Finset.mem_union]
      exact Or.inl hw
  -- Cardinality bound: `|D'| ≤ 2·|D|`.
  have hcard : D'.card ≤ 2 * D.card := by
    calc D'.card ≤ D.card + (D.image f).card := Finset.card_union_le _ _
      _ ≤ D.card + D.card := by
            exact Nat.add_le_add_left (Finset.card_image_le) _
      _ = 2 * D.card := by ring
  -- Conclude via the infimum bound.
  calc G.totalDominationNumber ≤ D'.card := hD'tot.totalDominationNumber_le
    _ ≤ 2 * D.card := hcard
    _ = 2 * G.dominationNumber := by rw [hDcard]

end Number

end SimpleGraph
