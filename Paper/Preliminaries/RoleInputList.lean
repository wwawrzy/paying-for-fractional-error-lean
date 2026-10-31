import Paper.Averaging.Tasks.TaskRoleId
import Paper.Preliminaries.TaggedDictionary

namespace Paper.RoleInputList
variable {Role A : Type} [LinearOrder Role]

def rows (rs : Finset Role) (f : Role → A) : List (Role × A) :=
  rs.sort.map (fun r => (r, f r))

theorem keys (rs : Finset Role) (f : Role → A) : TaggedDictionary.keys (rows rs f) = rs := by
  simp [rows, TaggedDictionary.keys, List.map_map, Function.comp_def, Finset.sort_toFinset]

theorem consistent (rs : Finset Role) (f : Role → A) : TaggedDictionary.Consistent f (rows rs f) := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem length (rs : Finset Role) (f : Role → A) : (rows rs f).length = rs.card := by
  simp only [rows, List.length_map, Finset.length_sort]

end Paper.RoleInputList
