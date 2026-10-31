import Paper.Communication.BroadcastModel

/-! Computable minimum of the identifiers actually received. An absent
identifier contributes no candidate. No graph or global active set occurs
in these local functions. -/
namespace Paper.MaskedMinimum
variable {V : Type} [LinearOrder V]

def minimum (S : Finset V) : Option V :=
  if h : S.Nonempty then some (S.min' h) else none

def pool (N : Finset V) (self : Option V) (incoming : N → Option V) : Finset V :=
  self.toFinset ∪ N.attach.biUnion (fun u => (incoming u).toFinset)

theorem minimum_mem {S : Finset V} {u : V} (h : minimum S = some u) : u ∈ S := by
  unfold minimum at h
  split at h
  · cases Option.some.inj h
    exact Finset.min'_mem _ _
  · contradiction

theorem minimum_le {S : Finset V} {u : V} (hu : u ∈ S) :
    ∃ m, minimum S = some m ∧ m ≤ u := by
  have hn : S.Nonempty := ⟨u, hu⟩
  exact ⟨S.min' hn, dif_pos hn, Finset.min'_le _ _ hu⟩

theorem mem_pool_self (N : Finset V) {self : Option V} (incoming : N → Option V)
    {u : V} (h : self = some u) : u ∈ pool N self incoming := by
  subst self
  simp [pool]

theorem mem_pool_incoming (N : Finset V) (self : Option V) (incoming : N → Option V)
    (w : N) {u : V} (h : incoming w = some u) : u ∈ pool N self incoming := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_attach _ _, by simp [h]⟩

theorem pool_origin (N : Finset V) (self : Option V) (incoming : N → Option V)
    (P : V → Prop) (hs : ∀ u, self = some u → P u)
    (hi : ∀ w u, incoming w = some u → P u) {u : V}
    (hu : u ∈ pool N self incoming) : P u := by
  rcases Finset.mem_union.mp hu with hu | hu
  · exact hs u (by simpa using hu)
  · obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hu
    exact hi w u (by simpa using hw)
end Paper.MaskedMinimum
