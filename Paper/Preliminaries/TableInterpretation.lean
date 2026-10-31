import Paper.Preliminaries.IntegralTable
import Paper.Preliminaries.LocalDemandMask

/-! Interpret an actually returned table word as physical integer vertex
multiplicities, preserving number of copies, cost and coverage rows. -/
namespace Paper.TableInterpretation
open TabularSearch SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V] {T : ℕ}

def multiplicity (w : List (Entry V T)) (v : V) : ℕ := (w.map Entry.id).count v

theorem multiplicity_cons (e : Entry V T) (w : List (Entry V T)) (v : V) :
    multiplicity (e :: w) v = (if v = e.id then 1 else 0) + multiplicity w v := by
  by_cases h : e.id = v
  · subst v
    simp [multiplicity, Nat.add_comm]
  · have h' : v ≠ e.id := Ne.symm h
    simp [multiplicity, h, h']

theorem weighted_sum (f : V → ℕ) (w : List (Entry V T)) :
    (∑ v, f v * multiplicity w v) = (w.map (fun e => f e.id)).sum := by
  induction w with
  | nil => simp [multiplicity]
  | cons e w ih =>
    simp only [multiplicity_cons, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, List.map_cons, List.sum_cons]
    rw [ih]
    simp

theorem total_size (w : List (Entry V T)) : (∑ v, multiplicity w v) = w.length := by
  have he := weighted_sum (fun _ => 1) w
  have hones (l : List (Entry V T)) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
    induction l <;> simp_all <;> omega
  simpa only [one_mul, hones] using he

theorem sum_map_congr {A : Type*} (l : List A) (f g : A → ℕ)
    (h : ∀ a ∈ l, f a = g a) : (l.map f).sum = (l.map g).sum := by
  revert h
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    exact congrArg₂ Nat.add (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem mass_eq (row : V → Fin T → Bool) (w : List (Entry V T))
    (hw : ∀ e ∈ w, e.row = row e.id) (i : Fin T) :
    IntegralTable.mass row (multiplicity w) i = coverage w i := by
  rw [IntegralTable.mass, weighted_sum]
  exact sum_map_congr w _ _ (fun e he => by rw [hw e he])

theorem cost_eq (c : V → ℕ) (w : List (Entry V T)) (hw : ∀ e ∈ w, e.price = c e.id) :
    IntegralTable.cost c (multiplicity w) = price w := by
  rw [IntegralTable.cost, weighted_sum]
  exact sum_map_congr w _ _ (fun e he => (hw e he).symm)

theorem support (w : List (Entry V T)) (H : Finset V) (hw : ∀ e ∈ w, e.id ∈ H)
    {v : V} (hv : v ∉ H) : multiplicity w v = 0 := by
  have hm : v ∉ w.map Entry.id := by
    intro hm
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hm
    exact hv (hid ▸ hw e he)
  exact List.count_eq_zero.mpr hm

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_mass (l : List V) (p : V → ℕ) (i : Fin T) (r : V) (hi : l[i.val]? = some r) :
    IntegralTable.mass (fun v => LocalDemandMask.mask T l v (G.neighborFinset v)) p i =
      ∑ v ∈ closed G r, p v := by
  unfold IntegralTable.mass
  have hmask (v : V) := LocalDemandMask.at_some G T l v r i hi
  simp only [hmask, decide_eq_true_eq, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem graph_covers (l : List V) (hlen : l.length ≤ T) (target : Fin T → ℕ) (b p : V → ℕ)
    (hb : ∀ r, r ∉ l → b r = 0)
    (ht : ∀ (i : Fin T) r, l[i.val]? = some r → target i = b r)
    (hcover : ∀ i, target i ≤ IntegralTable.mass
      (fun v => LocalDemandMask.mask T l v (G.neighborFinset v)) p i) :
    ∀ r, b r ≤ ∑ v ∈ closed G r, p v := by
  intro r
  by_cases hr : r ∈ l
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    have hip : l[i]? = some r := by simpa only [he] using List.getElem?_eq_getElem hi
    let i' : Fin T := ⟨i, lt_of_lt_of_le hi hlen⟩
    have hh := hcover i'
    rw [ht i' r hip, graph_mass G l p i' r hip] at hh
    exact hh
  · rw [hb r hr]
    exact Nat.zero_le _
end Paper.TableInterpretation
