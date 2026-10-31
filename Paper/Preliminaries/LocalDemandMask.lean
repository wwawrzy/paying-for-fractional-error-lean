import Paper.Preliminaries.ListPacket
import Paper.Preliminaries.SevenFoundation

/-! Compute an incidence mask from a bounded list of demand identifiers,
own ID and own physical neighbor list only. -/
namespace Paper.LocalDemandMask
open SevenFoundation
variable {V : Type} [DecidableEq V]

def mask (T : ℕ) (l : List V) (v : V) (N : Finset V) : Fin T → Bool := fun i =>
  match ListPacket.pack T l i with
  | none => false
  | some r => decide (r = v ∨ r ∈ N)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem at_some (T : ℕ) (l : List V) (v r : V) (i : Fin T) (hi : l[i.val]? = some r) :
    mask T l v (G.neighborFinset v) i = decide (v ∈ closed G r) := by
  simp [mask, ListPacket.pack, hi, mem_closed, SimpleGraph.mem_neighborFinset,
    G.adj_comm, eq_comm]

theorem same_iff (T : ℕ) (l : List V) (hlen : l.length ≤ T) (v w : V) :
    mask T l v (G.neighborFinset v) = mask T l w (G.neighborFinset w) ↔
      ∀ r ∈ l, (v ∈ closed G r ↔ w ∈ closed G r) := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    have hip : l[i]? = some r := by simpa only [he] using List.getElem?_eq_getElem hi
    let i' : Fin T := ⟨i, lt_of_lt_of_le hi hlen⟩
    have hh := congrFun h i'
    rw [at_some G T l v r i' hip, at_some G T l w r i' hip] at hh
    simpa only [decide_eq_decide] using hh
  · intro h
    funext i
    cases hi : l[i.val]? with
    | none => simp [mask, ListPacket.pack, hi]
    | some r =>
      have hr : r ∈ l := List.mem_iff_getElem?.mpr ⟨i.val, hi⟩
      rw [at_some G T l v r i hi, at_some G T l w r i hi]
      simpa only [decide_eq_decide] using h r hr

theorem signature_iff (T : ℕ) (l : List V) (hlen : l.length ≤ T) (v w : V) :
    mask T l v (G.neighborFinset v) = mask T l w (G.neighborFinset w) ↔
      closed G v ∩ l.toFinset = closed G w ∩ l.toFinset := by
  rw [same_iff G T l hlen v w]
  constructor
  · intro h
    ext r
    by_cases hr : r ∈ l
    · simp only [Finset.mem_inter, List.mem_toFinset, hr, and_true]
      exact (closed_symm G r v).trans ((h r hr).trans (closed_symm G w r))
    · simp [hr]
  · intro h r hr
    have hh := Finset.ext_iff.mp h r
    simp only [Finset.mem_inter, List.mem_toFinset, hr, and_true] at hh
    exact (closed_symm G v r).trans (hh.trans (closed_symm G r w))
end Paper.LocalDemandMask
