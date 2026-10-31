import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-! Actual finite enumeration of bounded-length words over an explicit
candidate list, followed by a computable minimum-cost valid choice. -/
namespace Paper.FiniteWords
variable {A : Type*}

def words (alphabet : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun a => (words alphabet n).map (List.cons a))

def upTo (alphabet : List A) (m : ℕ) : List (List A) :=
  (List.range (m + 1)).flatMap (words alphabet)

theorem mem_words (alphabet : List A) (n : ℕ) (w : List A) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words, List.mem_flatMap, List.mem_map]
    | cons a w =>
      constructor
      · intro hw
        obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hw
        obtain ⟨t, ht, he⟩ := List.mem_map.mp hx
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hlen, hall⟩ := (ih t).mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact hall x hx
      · rintro ⟨hlen, hall⟩
        apply List.mem_flatMap.mpr
        refine ⟨a, hall a List.mem_cons_self, List.mem_map.mpr ⟨w, ?_, rfl⟩⟩
        apply (ih w).mpr
        exact ⟨by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen,
          fun x hx => hall x (List.mem_cons_of_mem a hx)⟩

theorem mem_upTo (alphabet : List A) (m : ℕ) (w : List A) :
    w ∈ upTo alphabet m ↔ w.length ≤ m ∧ ∀ a ∈ w, a ∈ alphabet := by
  constructor
  · intro hw
    obtain ⟨n, hn, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨hlen, hall⟩ := (mem_words alphabet n w).mp hw
    exact ⟨by have := List.mem_range.mp hn; omega, hall⟩
  · rintro ⟨hlen, hall⟩
    exact List.mem_flatMap.mpr ⟨w.length, List.mem_range.mpr (by omega),
      (mem_words alphabet w.length w).mpr ⟨rfl, hall⟩⟩

def search (alphabet : List A) (m : ℕ) (valid : List A → Bool) (cost : List A → ℕ) :
    Option (List A) := ((upTo alphabet m).filter valid).argmin cost

theorem sound (alphabet : List A) (m : ℕ) (valid : List A → Bool) (cost : List A → ℕ)
    {w : List A} (h : search alphabet m valid cost = some w) :
    w.length ≤ m ∧ (∀ a ∈ w, a ∈ alphabet) ∧ valid w = true := by
  have hm : w ∈ ((upTo alphabet m).filter valid).argmin cost := by simpa only [search, Option.mem_def] using h
  have hh := List.mem_filter.mp (List.argmin_mem hm)
  obtain ⟨hlen, hall⟩ := (mem_upTo alphabet m w).mp hh.1
  exact ⟨hlen, hall, hh.2⟩

theorem complete (alphabet : List A) (m : ℕ) (valid : List A → Bool) (cost : List A → ℕ)
    (w : List A) (hlen : w.length ≤ m) (hall : ∀ a ∈ w, a ∈ alphabet) (hv : valid w = true) :
    ∃ p, search alphabet m valid cost = some p ∧ cost p ≤ cost w := by
  have hw : w ∈ (upTo alphabet m).filter valid :=
    List.mem_filter.mpr ⟨(mem_upTo alphabet m w).mpr ⟨hlen, hall⟩, hv⟩
  cases hs : search alphabet m valid cost with
  | none =>
    have he : (upTo alphabet m).filter valid = [] := List.argmin_eq_none.mp hs
    simp only [he, List.not_mem_nil] at hw
  | some p =>
    have hp : p ∈ ((upTo alphabet m).filter valid).argmin cost := by
      simpa only [search, Option.mem_def] using hs
    exact ⟨p, rfl, List.le_of_mem_argmin hw hp⟩
end Paper.FiniteWords
