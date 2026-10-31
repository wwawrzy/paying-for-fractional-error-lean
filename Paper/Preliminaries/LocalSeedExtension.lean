import Paper.Preliminaries.LocalSeedRecords

/-! Any values at distinct finite addresses have a global extension given
by ordinary finite lookup. Only the proof quantifies over all vertices. -/
namespace Paper.LocalSeedExtension
variable {V A : Type} [LinearOrder V]

theorem inputs_get (l : List V) (hl : l.Nodup) (τ : Fin l.length → A)
    (fallback : A) (i : Fin l.length) :
    FrameInterpreter.inputs (LocalSeedRecords.base l τ) fallback (l.get i) = τ i := by
  let xs := LocalSeedRecords.base l τ
  have hk : l.get i ∈ TaggedDictionary.keys xs := by
    rw [LocalSeedRecords.keys_base]
    exact List.mem_toFinset.mpr (List.get_mem _ _)
  have he := TaggedDictionary.entry_key xs (l.get i) hk
  have hm := TaggedDictionary.entry_mem xs (l.get i) hk
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  have hij : j = i := hl.injective_get (by rw [← hj] at he; exact he)
  rw [FrameInterpreter.inputs, TaggedDictionary.lookup,
    TaggedDictionary.find_entry xs (l.get i) hk]
  simp only [Option.map_some, Option.getD_some]
  rw [← hj, hij]

theorem consistent (l : List V) (hl : l.Nodup) (τ : Fin l.length → A) (fallback : A) :
    TaggedDictionary.Consistent (FrameInterpreter.inputs (LocalSeedRecords.base l τ) fallback)
      (LocalSeedRecords.base l τ) := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact (inputs_get l hl τ fallback i).symm

theorem base_extend (l : List V) (hl : l.Nodup) (τ : Fin l.length → A) (fallback : A) :
    LocalSeedRecords.base l
      (fun i => FrameInterpreter.inputs (LocalSeedRecords.base l τ) fallback (l.get i)) =
      LocalSeedRecords.base l τ := by
  congr 1
  funext i
  exact inputs_get l hl τ fallback i

end Paper.LocalSeedExtension
