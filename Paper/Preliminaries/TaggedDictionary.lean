import Paper.Preliminaries.ListPacket
import Mathlib.Data.Finset.Sort

/-! Computable ID-keyed payload dictionaries. Payloads need no order,
equality decision or global enumeration. Canonicalize by sorting just the
identifier keys and finding the first corresponding received payload. -/
namespace Paper.TaggedDictionary
variable {V A : Type} [LinearOrder V]

def keys (xs : List (V × A)) : Finset V := (xs.map Prod.fst).toFinset

def lookup (xs : List (V × A)) (k : V) : Option A :=
  (xs.find? (fun p => decide (p.1 = k))).map Prod.snd

theorem mem_keys (xs : List (V × A)) (k : V) : k ∈ keys xs ↔ ∃ p ∈ xs, p.1 = k := by
  simp only [keys, List.mem_toFinset, List.mem_map]

theorem keys_append (xs ys : List (V × A)) : keys (xs ++ ys) = keys xs ∪ keys ys := by
  simp only [keys, List.map_append, List.toFinset_append]

theorem mem_keys_flatMap {I : Type} (is : List I) (f : I → List (V × A)) (k : V) :
    k ∈ keys (is.flatMap f) ↔ ∃ i ∈ is, k ∈ keys (f i) := by
  simp only [mem_keys, List.mem_flatMap]
  constructor
  · rintro ⟨p, ⟨i, hi, hp⟩, hk⟩
    exact ⟨i, hi, p, hp, hk⟩
  · rintro ⟨i, hi, p, hp, hk⟩
    exact ⟨p, ⟨i, hi, hp⟩, hk⟩

theorem has_key (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) :
    (xs.find? (fun p => decide (p.1 = k))).isSome := by
  obtain ⟨p, hp, hkey⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
  exact List.find?_isSome.mpr ⟨p, hp, decide_eq_true hkey⟩

def entry (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) : V × A :=
  (xs.find? (fun p => decide (p.1 = k))).get (has_key xs k hk)

theorem find_entry (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) :
    xs.find? (fun p => decide (p.1 = k)) = some (entry xs k hk) := by
  simp only [entry, Option.some_get]

theorem entry_mem (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) : entry xs k hk ∈ xs :=
  List.mem_of_find?_eq_some (find_entry xs k hk)

theorem entry_key (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) : (entry xs k hk).1 = k :=
  of_decide_eq_true (List.find?_some (p := fun p : V × A => decide (p.1 = k)) (find_entry xs k hk))

def normalize (xs : List (V × A)) : List (V × A) :=
  (keys xs).sort.attach.map (fun k => entry xs k.val ((Finset.mem_sort (· ≤ ·)).mp k.property))

theorem length_normalize (xs : List (V × A)) : (normalize xs).length = (keys xs).card := by
  simp only [normalize, List.length_map, List.length_attach, Finset.length_sort]

theorem normalize_mem (xs : List (V × A)) (p : V × A) (hp : p ∈ normalize xs) : p ∈ xs := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact entry_mem xs k.val _

theorem normalize_has_key (xs : List (V × A)) (k : V) (hk : k ∈ keys xs) :
    entry xs k hk ∈ normalize xs := by
  apply List.mem_map.mpr
  exact ⟨⟨k, (Finset.mem_sort (· ≤ ·)).mpr hk⟩, List.mem_attach _ _, rfl⟩

theorem keys_normalize (xs : List (V × A)) : keys (normalize xs) = keys xs := by
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, normalize_mem xs p hp, hpk⟩)
  · intro hk
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry xs k hk, normalize_has_key xs k hk, entry_key xs k hk⟩)

def Consistent (f : V → A) (xs : List (V × A)) : Prop := ∀ p ∈ xs, p.2 = f p.1

theorem normalize_consistent (f : V → A) (xs : List (V × A)) (hs : Consistent f xs) :
    Consistent f (normalize xs) := fun p hp => hs p (normalize_mem xs p hp)

theorem lookup_correct (f : V → A) (xs : List (V × A)) (hs : Consistent f xs)
    (k : V) (hk : k ∈ keys xs) : lookup xs k = some (f k) := by
  rw [lookup, find_entry xs k hk]
  simp only [Option.map_some]
  rw [hs _ (entry_mem xs k hk), entry_key xs k hk]

def bounded (K : ℕ) (xs : List (V × A)) := ListPacket.truncate K (normalize xs)

theorem bounded_eq (K : ℕ) (xs : List (V × A)) (hs : (keys xs).card ≤ K) :
    (bounded K xs).val = normalize xs :=
  ListPacket.truncate_eq K _ (by rw [length_normalize]; exact hs)

theorem bounded_mem (K : ℕ) (xs : List (V × A)) (p : V × A) (hp : p ∈ (bounded K xs).val) : p ∈ xs :=
  normalize_mem xs p (List.mem_of_mem_take hp)

theorem bounded_lookup (K : ℕ) (f : V → A) (xs : List (V × A)) (hs : Consistent f xs)
    (hsize : (keys xs).card ≤ K) (k : V) (hk : k ∈ keys xs) :
    lookup (bounded K xs).val k = some (f k) := by
  rw [bounded_eq K xs hsize]
  exact lookup_correct f (normalize xs) (normalize_consistent f xs hs) k (keys_normalize xs ▸ hk)

theorem bounded_consistent (K : ℕ) (f : V → A) (xs : List (V × A)) (hs : Consistent f xs) :
    Consistent f (bounded K xs).val := fun p hp => hs p (bounded_mem K xs p hp)

theorem keys_bounded_subset (K : ℕ) (xs : List (V × A)) : keys (bounded K xs).val ⊆ keys xs := by
  intro k hk
  obtain ⟨p, hp, hpk⟩ := (mem_keys _ k).mp hk
  exact (mem_keys xs k).mpr ⟨p, bounded_mem K xs p hp, hpk⟩

theorem keys_bounded_eq (K : ℕ) (xs : List (V × A)) (hs : (keys xs).card ≤ K) :
    keys (bounded K xs).val = keys xs := by
  rw [bounded_eq K xs hs, keys_normalize]

theorem append_consistent (f : V → A) (xs ys : List (V × A))
    (hx : Consistent f xs) (hy : Consistent f ys) : Consistent f (xs ++ ys) := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hx p) (hy p)

theorem flatMap_consistent {I : Type} (f : V → A) (is : List I) (xs : I → List (V × A))
    (hs : ∀ i ∈ is, Consistent f (xs i)) : Consistent f (is.flatMap xs) := by
  intro p hp
  obtain ⟨i, hi, hp⟩ := List.mem_flatMap.mp hp
  exact hs i hi p hp
end Paper.TaggedDictionary
