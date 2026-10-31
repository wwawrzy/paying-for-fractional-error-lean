import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Global packing of bad ordered identifier words

The maximum ranges over every disjoint family of bad ordered words, rather
than segments in one fixed labeling. Thus its unused identifiers cannot
contain any bad ordered word. This is the packing step in sc:rounds-lower;
it does not assume a cycle-coloring lower bound or assert that endpoint.
-/
namespace Paper.CycleBadPacking

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

def support (w : Fin r → V) : Finset V := Finset.univ.image w

def covered (P : Finset (Fin r → V)) : Finset V := P.biUnion support

def Packing (bad : (Fin r → V) → Prop) (P : Finset (Fin r → V)) : Prop :=
  (∀ w ∈ P, Function.Injective w ∧ bad w) ∧
    (P : Set (Fin r → V)).PairwiseDisjoint support

/-- Global cardinal maximality includes all identifier orders. -/
def Maximum (bad : (Fin r → V) → Prop) (P : Finset (Fin r → V)) : Prop :=
  Packing bad P ∧ ∀ Q : Finset (Fin r → V), Packing bad Q → Q.card ≤ P.card

theorem support_card (w : Fin r → V) (hw : Function.Injective w) :
    (support w).card = r := by
  rw [support, Finset.card_image_of_injective _ hw]
  simp

theorem covered_card {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : (covered P).card = r * P.card := by
  rw [covered, Finset.card_biUnion hP.2]
  calc
    _ = ∑ _w ∈ P, r := Finset.sum_congr rfl (fun w hw => support_card w (hP.1 w hw).1)
    _ = _ := by simp [Nat.mul_comm]

theorem empty_packing (bad : (Fin r → V) → Prop) : Packing bad ∅ := by
  constructor
  · simp
  · intro w hw
    exact False.elim (Finset.notMem_empty _ hw)

theorem exists_maximum (bad : (Fin r → V) → Prop) :
    ∃ P : Finset (Fin r → V), Maximum bad P := by
  classical
  let families := (Finset.univ : Finset (Fin r → V)).powerset.filter (Packing bad)
  have he : ∅ ∈ families := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), empty_packing bad⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image families Finset.card ⟨∅, he⟩
  refine ⟨P, (Finset.mem_filter.mp hP).2, ?_⟩
  intro Q hQ
  exact hmax Q (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ Q), hQ⟩)

theorem insert_packing {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) (w : Fin r → V) (hw : Function.Injective w) (hb : bad w)
    (hdisj : Disjoint (support w) (covered P)) : Packing bad (insert w P) := by
  classical
  refine ⟨?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ⟨hw, hb⟩
    · exact hP.1 u hu
  · intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with hue | huP
    · subst u
      rcases Finset.mem_insert.mp hv with hve | hvP
      · exact False.elim (huv hve.symm)
      · apply hdisj.mono_right
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨v, hvP, hx⟩
    · rcases Finset.mem_insert.mp hv with hve | hvP
      · subst v
        apply Disjoint.symm
        apply hdisj.mono_right
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨u, huP, hx⟩
      · exact hP.2 huP hvP huv

/-- A bad word made entirely of unused identifiers would increase the global
packing, even if it never appeared consecutively in the original labeling. -/
theorem maximum_avoids {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hr : 0 < r) (hP : Maximum bad P) (w : Fin r → V) (hw : Function.Injective w)
    (houtside : ∀ i, w i ∉ covered P) : ¬ bad w := by
  classical
  intro hb
  have hdisj : Disjoint (support w) (covered P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact houtside i hxc
  have hn : w ∉ P := by
    intro hwP
    let i : Fin r := ⟨0, hr⟩
    exact houtside i (Finset.mem_biUnion.mpr
      ⟨w, hwP, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hh := hP.2 (insert w P) (insert_packing hP.1 w hw hb hdisj)
  rw [Finset.card_insert_of_notMem hn] at hh
  omega

/-- The separate cycle counting argument only needs to bound the covered
size of every packing. The reservoir and its avoidance property are outputs. -/
theorem exists_large_bad_free (bad : (Fin r → V) → Prop) (hr : 0 < r)
    (hsmall : ∀ P : Finset (Fin r → V), Packing bad P →
      2 * (r * P.card) < Fintype.card V) :
    ∃ S : Finset V, Fintype.card V / 2 < S.card ∧
      ∀ w : Fin r → V, Function.Injective w → (∀ i, w i ∈ S) → ¬ bad w := by
  classical
  obtain ⟨P, hP⟩ := exists_maximum bad
  let S := (Finset.univ : Finset V) \ covered P
  have hcount := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (covered P))
  have hsmallP := hsmall P hP.1
  rw [← covered_card hP.1] at hsmallP
  simp only [Finset.card_univ] at hcount
  refine ⟨S, by dsimp only [S]; omega, ?_⟩
  intro w hw hS
  exact maximum_avoids hr hP w hw (fun i => (Finset.mem_sdiff.mp (hS i)).2)

/-- The simulated smaller cycle can use a fixed injection into the reservoir. -/
theorem reservoir_injection [LinearOrder V] (S : Finset V) (n : ℕ) (hn : n ≤ S.card) :
    ∃ f : Fin n → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
  let e : Fin n → Fin S.card := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin S.card => z.val) h)
  refine ⟨fun i => S.orderEmbOfFin rfl (e i), (S.orderEmbOfFin rfl).injective.comp he, ?_⟩
  exact fun i => Finset.orderEmbOfFin_mem S rfl (e i)

end Paper.CycleBadPacking

#print axioms Paper.CycleBadPacking.exists_maximum
#print axioms Paper.CycleBadPacking.covered_card
#print axioms Paper.CycleBadPacking.maximum_avoids
#print axioms Paper.CycleBadPacking.exists_large_bad_free
#print axioms Paper.CycleBadPacking.reservoir_injection
