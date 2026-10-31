import Paper.Preliminaries.TaggedDictionary

/-! Computable role-indexed state maps, with no equality/order on states. -/
namespace Paper.RoleDictionary
variable {R A B : Type} [LinearOrder R]

def mapValues (f : R → A → B) (xs : List (R × A)) : List (R × B) :=
  xs.map (fun p => (p.1, f p.1 p.2))

theorem keys_map (f : R → A → B) (xs : List (R × A)) :
    TaggedDictionary.keys (mapValues f xs) = TaggedDictionary.keys xs := by
  simp only [mapValues, TaggedDictionary.keys, List.map_map, Function.comp_def]

theorem consistent_map (f : R → A → B) (s : R → A) (xs : List (R × A))
    (hs : TaggedDictionary.Consistent s xs) :
    TaggedDictionary.Consistent (fun r => f r (s r)) (mapValues f xs) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  change f q.1 q.2 = f q.1 (s q.1)
  rw [hs q hq]

theorem lookup_map (f : R → A → B) (xs : List (R × A)) (r : R) :
    TaggedDictionary.lookup (mapValues f xs) r = (TaggedDictionary.lookup xs r).map (f r) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, a⟩
    by_cases he : k = r
    · subst k
      simp [mapValues, TaggedDictionary.lookup]
    · simpa [mapValues, TaggedDictionary.lookup, he] using ih
end Paper.RoleDictionary
