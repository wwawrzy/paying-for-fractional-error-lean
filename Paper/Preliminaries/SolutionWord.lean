import Paper.Preliminaries.CostTag
import Paper.Preliminaries.TableInterpretation

/-! One common solution type for all recursive budgets. It stores only
bounded-cost/ID tags, so terminal words with different row dimensions can
be returned through the same typed recursive broadcast interface. -/
namespace Paper.SolutionWord
variable {V : Type} [DecidableEq V]

abbrev Word (V : Type) (B : ℕ) := List (CostTag.Tag V B)

def id {B : ℕ} (t : CostTag.Tag V B) : V := (ofLex t).2

def tagPrice {B : ℕ} (t : CostTag.Tag V B) : ℕ := (ofLex t).1.val

def entries {B : ℕ} (w : Word V B) : List (TabularSearch.Entry V 0) :=
  w.map (fun t => ⟨id t, Fin.elim0, tagPrice t⟩)

def copies {B : ℕ} (w : Word V B) : V → ℕ := TableInterpretation.multiplicity (entries w)

def cost {B : ℕ} (w : Word V B) : ℕ := TabularSearch.price (entries w)

def ofEntry (B : ℕ) {T : ℕ} (e : TabularSearch.Entry V T) : CostTag.Tag V B :=
  toLex (⟨min e.price B, by have := min_le_right e.price B; omega⟩, e.id)

def fromEntries (B : ℕ) {T : ℕ} (w : List (TabularSearch.Entry V T)) : Word V B := w.map (ofEntry B)

def Consistent {B : ℕ} (c : V → Fin (B + 1)) (w : Word V B) : Prop :=
  ∀ t ∈ w, (ofLex t).1 = c (id t)

theorem copies_fromEntries (B : ℕ) {T : ℕ} (w : List (TabularSearch.Entry V T)) (v : V) :
    copies (fromEntries B w) v = TableInterpretation.multiplicity w v := by
  simp [copies, entries, fromEntries, TableInterpretation.multiplicity, List.map_map,
    Function.comp_def, ofEntry, id]

theorem length_fromEntries (B : ℕ) {T : ℕ} (w : List (TabularSearch.Entry V T)) :
    (fromEntries B w).length = w.length := List.length_map _

theorem copies_cons [Fintype V] {B : ℕ} (t : CostTag.Tag V B) (w : Word V B) (v : V) :
    copies (t :: w) v = (if v = id t then 1 else 0) + copies w v :=
  TableInterpretation.multiplicity_cons ⟨id t, Fin.elim0, tagPrice t⟩ (entries w) v

theorem cost_cons {B : ℕ} (t : CostTag.Tag V B) (w : Word V B) :
    cost (t :: w) = tagPrice t + cost w := rfl

theorem cost_fromEntries (B : ℕ) {T : ℕ} (w : List (TabularSearch.Entry V T))
    (hw : ∀ e ∈ w, e.price ≤ B) : cost (fromEntries B w) = TabularSearch.price w := by
  simp only [cost, entries, fromEntries, TabularSearch.price, List.map_map, Function.comp_def,
    tagPrice, ofEntry]
  exact TableInterpretation.sum_map_congr w _ _ (fun e he => min_eq_left (hw e he))

theorem consistent_fromEntries {B T : ℕ} (c : V → Fin (B + 1)) (w : List (TabularSearch.Entry V T))
    (hw : ∀ e ∈ w, e.price = (c e.id).val) : Consistent c (fromEntries B w) := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  apply Fin.ext
  change min e.price B = (c e.id).val
  rw [hw e he]
  exact min_eq_left (by have := (c e.id).isLt; omega)

variable [Fintype V]

theorem total_size {B : ℕ} (w : Word V B) : (∑ v, copies w v) = w.length := by
  simpa only [entries, List.length_map] using TableInterpretation.total_size (entries w)

theorem cost_eq {B : ℕ} (c : V → Fin (B + 1)) (w : Word V B) (hw : Consistent c w) :
    IntegralTable.cost (fun v => (c v).val) (copies w) = cost w := by
  apply TableInterpretation.cost_eq _ (entries w)
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact congrArg Fin.val (hw t ht)
end Paper.SolutionWord
