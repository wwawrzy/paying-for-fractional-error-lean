import Paper.Preliminaries.FiniteWords
import Paper.Communication.BroadcastModel

/-! Concrete finite-word terminal search. The table and demand values are
ordinary local input already supplied by bounded-message task queries. -/
namespace Paper.TabularSearch
open BroadcastModel

structure Entry (V : Type*) (T : ℕ) where
  id : V
  row : Fin T → Bool
  price : ℕ

def coverage {V : Type*} {T : ℕ} (w : List (Entry V T)) (i : Fin T) : ℕ :=
  (w.map (fun e => if e.row i then 1 else 0)).sum

def price {V : Type*} {T : ℕ} (w : List (Entry V T)) : ℕ := (w.map Entry.price).sum

def valid {V : Type*} {T : ℕ} (target : Fin T → ℕ) (w : List (Entry V T)) : Bool :=
  decide (∀ i, target i ≤ coverage w i)

def choose {V : Type*} {T : ℕ} (alphabet : List (Entry V T)) (m : ℕ) (target : Fin T → ℕ) :=
  FiniteWords.search alphabet m (valid target) price

theorem choose_sound {V : Type*} {T : ℕ} (alphabet : List (Entry V T)) (m : ℕ)
    (target : Fin T → ℕ) {w : List (Entry V T)} (h : choose alphabet m target = some w) :
    w.length ≤ m ∧ (∀ e ∈ w, e ∈ alphabet) ∧ ∀ i, target i ≤ coverage w i := by
  obtain ⟨hlen, hall, hv⟩ := FiniteWords.sound alphabet m (valid target) price h
  exact ⟨hlen, hall, of_decide_eq_true hv⟩

theorem choose_complete {V : Type*} {T : ℕ} (alphabet : List (Entry V T)) (m : ℕ)
    (target : Fin T → ℕ) (w : List (Entry V T)) (hlen : w.length ≤ m)
    (hall : ∀ e ∈ w, e ∈ alphabet) (hv : ∀ i, target i ≤ coverage w i) :
    ∃ p, choose alphabet m target = some p ∧ price p ≤ price w :=
  FiniteWords.complete alphabet m (valid target) price w hlen hall (decide_eq_true hv)

def program {V : Type} (T m : ℕ) :
    Program V (List (Entry V T) × (Fin T → ℕ)) (Option (List (Entry V T))) :=
  .local fun _ _ s => choose s.1 m s.2

theorem rounds {V : Type} (T m : ℕ) : (program (V := V) T m).rounds = 0 := rfl

theorem maxBits {V : Type} (T m : ℕ) : (program (V := V) T m).maxBits = 0 := rfl
end Paper.TabularSearch
