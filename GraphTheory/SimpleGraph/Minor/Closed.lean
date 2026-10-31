/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Minor.Defs
import GraphTheory.SimpleGraph.Planar.Basic
import Mathlib.Tactic

/-!
# Minor-Closed Graph Properties

A property of graphs is **minor-closed** if it is preserved under taking minors.
This is a fundamental concept in structural graph theory; the Robertson-Seymour
theorem states that every minor-closed property can be characterised by a finite
set of forbidden minors.

## Main definitions

* `SimpleGraph.IsMinorClosed` — a property `P : SimpleGraph V → Prop` is minor-closed
  if whenever `P G` holds and `H` is a minor of `G`, then `P H` holds.
* `SimpleGraph.IsSubgraphClosed` — a property is subgraph-closed (weaker than minor-closed).

## Main results

* `SimpleGraph.IsMinorClosed.isSubgraphClosed` — minor-closed implies subgraph-closed.
* `SimpleGraph.isPlanar_isMinorClosed` — planarity is minor-closed.
* `SimpleGraph.isKMinorFree_isMinorClosed` — for each `h`, the property of being
  `Kₕ`-minor-free is minor-closed.
* `SimpleGraph.isHMinorFree_isMinorClosed` — for any fixed `H`, the property of being
  `H`-minor-free is minor-closed.
-/

namespace SimpleGraph

universe u

variable {V : Type u}

/-! ### Minor-closed and subgraph-closed properties -/

/-- A property of graphs (on a fixed vertex type) is **minor-closed** if it is
preserved under taking minors: whenever `P G` holds and `H ≤m G`, then `P H`. -/
def IsMinorClosed (P : SimpleGraph V → Prop) : Prop :=
  ∀ ⦃G H : SimpleGraph V⦄, P G → H ≤m G → P H

/-- A property of graphs is **subgraph-closed** if it is preserved under taking
subgraphs: whenever `P G` holds and `H ≤ G` (as a subgraph), then `P H`. -/
def IsSubgraphClosed (P : SimpleGraph V → Prop) : Prop :=
  ∀ ⦃G H : SimpleGraph V⦄, P G → H ≤ G → P H

/-- Every minor-closed property is also subgraph-closed, because every subgraph
is a minor (via `IsMinor.of_subgraph`). -/
theorem IsMinorClosed.isSubgraphClosed {P : SimpleGraph V → Prop}
    (hmc : IsMinorClosed P) : IsSubgraphClosed P :=
  fun _G _H hPG hle => hmc hPG (IsMinor.of_subgraph hle)

/-! ### Planarity is minor-closed -/

/-- **Planarity is minor-closed.** If `G` is planar and `H` is a minor of `G`,
then `H` is planar.

This is a classical result (a minor of a planar graph is planar). We axiomatize
it here, consistent with our axiomatized `IsPlanar`. A proof would follow from
the fact that contracting an edge preserves planarity, and edge/vertex deletion
trivially do. -/
theorem IsPlanar.minor {G H : SimpleGraph V}
    (hG : IsPlanar G) (hminor : H ≤m G) : IsPlanar H :=
  ⟨IsHMinorFree.minor hG.1 hminor, IsHMinorFree.minor hG.2 hminor⟩

/-- Planarity (on a fixed vertex type) is a minor-closed property. -/
theorem isPlanar_isMinorClosed : IsMinorClosed (IsPlanar : SimpleGraph V → Prop) :=
  fun _G _H hPG hminor => IsPlanar.minor hPG hminor

/-! ### H-minor-freeness is minor-closed -/

/-- For any fixed graph `H` (on type `VH`), the property "is `H`-minor-free" is
minor-closed (on a fixed vertex type `V`).

**Proof:** If `G` is `H`-minor-free and `G'` is a minor of `G`, then `G'` is
`H`-minor-free by `IsHMinorFree.minor`. The wrapper here specialises to the
single-type setting. -/
theorem isHMinorFree_isMinorClosed {VH : Type*} (H : SimpleGraph VH) :
    IsMinorClosed (fun G : SimpleGraph V => G.IsHMinorFree H) :=
  fun _G _G' hfree hminor => IsHMinorFree.minor hfree hminor

/-- For any `h : ℕ`, the property "is `Kₕ`-minor-free" is minor-closed.
This is a direct consequence of `isHMinorFree_isMinorClosed`. -/
theorem isKMinorFree_isMinorClosed (h : ℕ) :
    IsMinorClosed (fun G : SimpleGraph V => G.IsKMinorFree h) :=
  isHMinorFree_isMinorClosed (completeGraph (Fin h))

/-- K₅-minor-freeness is minor-closed. -/
theorem isK5MinorFree_isMinorClosed :
    IsMinorClosed (fun G : SimpleGraph V => G.IsK5MinorFree) :=
  isKMinorFree_isMinorClosed 5

/-- K₃,₃-minor-freeness is minor-closed. -/
theorem isK33MinorFree_isMinorClosed :
    IsMinorClosed (fun G : SimpleGraph V => G.IsK33MinorFree) :=
  isHMinorFree_isMinorClosed (completeBipartiteGraph (Fin 3) (Fin 3))

/-! ### Closure properties of minor-closed classes -/

/-- The intersection of two minor-closed properties is minor-closed. -/
theorem IsMinorClosed.inter {P Q : SimpleGraph V → Prop}
    (hP : IsMinorClosed P) (hQ : IsMinorClosed Q) :
    IsMinorClosed (fun G => P G ∧ Q G) :=
  fun _G _H ⟨hPG, hQG⟩ hminor => ⟨hP hPG hminor, hQ hQG hminor⟩

/-- The universal property (holding for all graphs) is minor-closed. -/
theorem isMinorClosed_univ : IsMinorClosed (fun _ : SimpleGraph V => True) :=
  fun _G _H _ _ => trivial

/-- The empty property (holding for no graph) is vacuously minor-closed. -/
theorem isMinorClosed_empty : IsMinorClosed (fun _ : SimpleGraph V => False) :=
  fun _G _H hF _ => hF.elim

/-! ### Subgraph-closedness examples -/

/-- k-degeneracy is subgraph-closed: if `G` is k-degenerate and `H ≤ G`,
then `H` is k-degenerate.

**Note:** k-degeneracy is NOT minor-closed in general (contracting an edge can
increase minimum degree in subgraphs). However, for minor-closed classes defined
by excluded minors, bounded degeneracy follows from Mader's theorem. -/
theorem isKDegenerate_isSubgraphClosed [DecidableEq V] (k : ℕ) :
    IsSubgraphClosed (fun G : SimpleGraph V =>
      ∀ [DecidableRel G.Adj], G.IsKDegenerate k) := by
  intro G H hG hle
  intro instH
  intro s hs
  haveI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨v, hvm, hdeg⟩ := hG s hs
  refine ⟨v, hvm, ?_⟩
  unfold inducedDegree at *
  exact Nat.le_trans
    (Finset.card_le_card (Finset.monotone_filter_right s (fun _ _ ha => hle ha)))
    hdeg

end SimpleGraph
