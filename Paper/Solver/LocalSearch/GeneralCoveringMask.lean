import Paper.Preliminaries.TableInterpretation

/-! Bounded masks for directed covering incidences. A candidate computes its
mask from its private set of covered demands and the announced demand IDs.
The existing integral table is reused without a graph-symmetry assumption. -/
namespace Paper.GeneralCoveringMask
open scoped BigOperators
variable {V : Type} [DecidableEq V]

def mask (T : ℕ) (l : List V) (targets : Finset V) : Fin T → Bool := fun i =>
  match ListPacket.pack T l i with
  | none => false
  | some r => decide (r ∈ targets)

theorem at_some (T : ℕ) (l : List V) (targets : Finset V)
    (r : V) (i : Fin T) (hi : l[i.val]? = some r) :
    mask T l targets i = decide (r ∈ targets) := by
  simp [mask, ListPacket.pack, hi]

theorem same_iff (T : ℕ) (l : List V) (hlen : l.length ≤ T) (A B : Finset V) :
    mask T l A = mask T l B ↔ ∀ r ∈ l, (r ∈ A ↔ r ∈ B) := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    have hip : l[i]? = some r := by simpa only [he] using List.getElem?_eq_getElem hi
    let i' : Fin T := ⟨i, lt_of_lt_of_le hi hlen⟩
    have hh := congrFun h i'
    rw [at_some T l A r i' hip, at_some T l B r i' hip] at hh
    simpa only [decide_eq_decide] using hh
  · intro h
    funext i
    cases hi : l[i.val]? with
    | none => simp [mask, ListPacket.pack, hi]
    | some r =>
      have hr : r ∈ l := List.mem_iff_getElem?.mpr ⟨i.val, hi⟩
      rw [at_some T l A r i hi, at_some T l B r i hi]
      simpa only [decide_eq_decide] using h r hr

variable [Fintype V] {T : ℕ}

/-- Both endpoints' local incidence bits describe the same covering relation. -/
theorem mass (C targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (l : List V) (p : V → ℕ) (i : Fin T) (r : V) (hi : l[i.val]? = some r) :
    IntegralTable.mass (fun v => mask T l (targets v)) p i = ∑ v ∈ C r, p v := by
  unfold IntegralTable.mass
  simp only [at_some T l _ r i hi, decide_eq_true_eq, hinc, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem covers (C targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (l : List V) (hlen : l.length ≤ T) (target : Fin T → ℕ) (b p : V → ℕ)
    (hb : ∀ r, r ∉ l → b r = 0)
    (ht : ∀ (i : Fin T) r, l[i.val]? = some r → target i = b r)
    (hcover : ∀ i, target i ≤ IntegralTable.mass (fun v => mask T l (targets v)) p i) :
    ∀ r, b r ≤ ∑ v ∈ C r, p v := by
  intro r
  by_cases hr : r ∈ l
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    have hip : l[i]? = some r := by simpa only [he] using List.getElem?_eq_getElem hi
    let i' : Fin T := ⟨i, lt_of_lt_of_le hi hlen⟩
    have hh := hcover i'
    rw [ht i' r hip, mass C targets hinc l p i' r hip] at hh
    exact hh
  · rw [hb r hr]
    exact Nat.zero_le _

/-- A returned table word covers the original incidence rows, with no change
to the generic word interpretation or multiplicity representation. -/
theorem word_covers (C targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (l : List V) (hlen : l.length ≤ T) (target : Fin T → ℕ) (b : V → ℕ)
    (hb : ∀ r, r ∉ l → b r = 0)
    (ht : ∀ (i : Fin T) r, l[i.val]? = some r → target i = b r)
    (w : List (TabularSearch.Entry V T))
    (hw : ∀ e ∈ w, e.row = mask T l (targets e.id))
    (hcover : ∀ i, target i ≤ TabularSearch.coverage w i) :
    ∀ r, b r ≤ ∑ v ∈ C r, TableInterpretation.multiplicity w v := by
  apply covers C targets hinc l hlen target b _ hb ht
  intro i
  rw [TableInterpretation.mass_eq _ w hw i]
  exact hcover i

end Paper.GeneralCoveringMask

#print axioms Paper.GeneralCoveringMask.word_covers
