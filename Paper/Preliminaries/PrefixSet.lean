import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-! Computable bounded prefixes preserve small set unions and detect the
threshold exactly. This allows high-degree owner detection without sending
unbounded physical unions. No graph or vertex-universe assumption. -/
namespace Paper.PrefixSet
variable {V : Type} [LinearOrder V]

def take (f : ℕ) (s : Finset V) : Finset V := ((s.sort (· ≤ ·)).take f).toFinset

theorem subset (f : ℕ) (s : Finset V) : take f s ⊆ s := by
  intro v hv
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hv))

theorem card (f : ℕ) (s : Finset V) : (take f s).card = min f s.card := by
  rw [take, List.toFinset_card_of_nodup ((Finset.sort_nodup s (· ≤ ·)).take), List.length_take, Finset.length_sort]

theorem bound (f : ℕ) (s : Finset V) : (take f s).card ≤ f := by
  rw [card]
  exact Nat.min_le_left _ _

theorem eq_self (f : ℕ) (s : Finset V) (hs : s.card ≤ f) : take f s = s := by
  rw [take, List.take_of_length_le (by simpa only [Finset.length_sort] using hs), Finset.sort_toFinset]

def union (H : Finset (Finset V)) (f : ℕ) : Finset V := H.biUnion (take f)

theorem union_subset (H : Finset (Finset V)) (f : ℕ) : union H f ⊆ H.biUnion id := by
  intro v hv
  obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨s, hs, subset f s hv⟩

theorem member_small (H : Finset (Finset V)) (f : ℕ) (hsmall : (union H f).card < f) :
    ∀ s ∈ H, s.card < f := by
  intro s hs
  have hin : take f s ⊆ union H f := fun v hv => Finset.mem_biUnion.mpr ⟨s, hs, hv⟩
  have hh := Finset.card_le_card hin
  rw [card] at hh
  omega

theorem small_eq (H : Finset (Finset V)) (f : ℕ) (hsmall : (union H f).card < f) :
    union H f = H.biUnion id := by
  apply Finset.biUnion_congr rfl
  intro s hs
  exact eq_self f s (member_small H f hsmall s hs).le

theorem small_iff (H : Finset (Finset V)) (f : ℕ) :
    (union H f).card < f ↔ (H.biUnion id).card < f := by
  constructor
  · intro hh
    rwa [small_eq H f hh] at hh
  · intro hh
    exact (Finset.card_le_card (union_subset H f)).trans_lt hh

theorem threshold_iff (H : Finset (Finset V)) (f : ℕ) :
    f ≤ (union H f).card ↔ f ≤ (H.biUnion id).card := by
  have hh := small_iff H f
  omega

theorem capped_union_small_iff (H : Finset (Finset V)) (f : ℕ) :
    (take f (union H f)).card < f ↔ (H.biUnion id).card < f := by
  rw [card]
  have hh := small_iff H f
  omega

theorem capped_union_low_eq (H : Finset (Finset V)) (f : ℕ)
    (hlow : (take f (union H f)).card < f) : take f (union H f) = H.biUnion id := by
  have hs : (union H f).card < f := by rw [card] at hlow; omega
  rw [eq_self f _ hs.le, small_eq H f hs]
end Paper.PrefixSet
