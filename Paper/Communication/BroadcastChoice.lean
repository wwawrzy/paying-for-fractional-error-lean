import Paper.Communication.BroadcastModel

/-! Computably select one present message using only neighboring sender
identifiers. No ordering, equality test, or enumeration of payloads needed. -/
namespace Paper.BroadcastChoice
variable {V A : Type} [LinearOrder V]

def present (N : Finset V) (incoming : N → Option A) : Finset N :=
  N.attach.filter (fun w => (incoming w).isSome)

def choose (N : Finset V) (incoming : N → Option A) : Option A :=
  if h : (present N incoming).Nonempty then incoming ((present N incoming).min' h) else none

theorem origin (N : Finset V) (incoming : N → Option A) {x : A}
    (h : choose N incoming = some x) : ∃ w : N, incoming w = some x := by
  unfold choose at h
  split at h
  · exact ⟨_, h⟩
  · contradiction

theorem uniform (N : Finset V) (incoming : N → Option A) (x : A)
    (hi : ∀ w, incoming w = none ∨ incoming w = some x) :
    choose N incoming = none ∨ choose N incoming = some x := by
  unfold choose
  split
  · exact hi _
  · exact Or.inl rfl

theorem some_of_present (N : Finset V) (incoming : N → Option A) (x : A)
    (hi : ∀ w, incoming w = none ∨ incoming w = some x)
    (hex : ∃ w, incoming w = some x) : choose N incoming = some x := by
  obtain ⟨w, hw⟩ := hex
  have hn : (present N incoming).Nonempty :=
    ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, by simp [hw]⟩⟩
  rw [choose, dif_pos hn]
  let u := (present N incoming).min' hn
  have hu : (incoming u).isSome := (Finset.mem_filter.mp (Finset.min'_mem _ hn)).2
  rcases hi u with hu' | hu'
  · simp [hu'] at hu
  · exact hu'
end Paper.BroadcastChoice
