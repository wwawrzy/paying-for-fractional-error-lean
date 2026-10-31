import Paper.Preliminaries.FrameInterpreter

/-! Computable seed records from a padded fixed-size array. Only the
received address list is enumerated, never the global vertex type. -/
namespace Paper.LocalSeedRecords
variable {V A : Type} [LinearOrder V]

def slot (l : List V) {K : ℕ} (hK : l.length ≤ K) (i : Fin l.length) : Fin K :=
  ⟨i.val, lt_of_lt_of_le i.isLt hK⟩

theorem slot_injective (l : List V) {K : ℕ} (hK : l.length ≤ K) :
    Function.Injective (slot l hK) := fun _ _ h => Fin.ext (congrArg (fun z : Fin K => z.val) h)

def base (l : List V) (τ : Fin l.length → A) : List (V × A) :=
  List.ofFn (fun i => (l.get i, τ i))

def records (l : List V) {K : ℕ} (hK : l.length ≤ K) (ω : Fin K → A) : List (V × A) :=
  base l (fun i => ω (slot l hK i))

theorem length_base (l : List V) (τ : Fin l.length → A) : (base l τ).length = l.length := by
  simp only [base, List.length_ofFn]

theorem keys_base (l : List V) (τ : Fin l.length → A) : TaggedDictionary.keys (base l τ) = l.toFinset := by
  ext u
  rw [TaggedDictionary.mem_keys, List.mem_toFinset, List.mem_iff_get]
  constructor
  · rintro ⟨p, hp, hpu⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨i, hpu⟩
  · rintro ⟨i, hi⟩
    exact ⟨(l.get i, τ i), List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

theorem consistent_base (l : List V) (s : V → A) :
    TaggedDictionary.Consistent s (base l (fun i => s (l.get i))) := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  rfl

theorem inputs_base (l : List V) (s : V → A) (fallback : A) (u : V) (hu : u ∈ l) :
    FrameInterpreter.inputs (base l (fun i => s (l.get i))) fallback u = s u := by
  apply FrameInterpreter.inputs_correct _ fallback s (consistent_base l s) u
  rw [keys_base]
  exact List.mem_toFinset.mpr hu

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem evaluate_base {Out : Type} {Δ : ℕ} (P : BroadcastModel.Program V A Out)
    (xs : List (TopologyGather.Record V Δ)) (l : List V) (s : V → A) (fallback : A) (v : V)
    (hxs : ∀ p ∈ xs, p.2.val.toFinset = G.neighborFinset p.1)
    (hx : NeighborBalls.ball (fun u => G.neighborFinset u) v P.rounds ⊆ TaggedDictionary.keys xs)
    (hl : NeighborBalls.ball (fun u => G.neighborFinset u) v P.rounds ⊆ l.toFinset) :
    FrameInterpreter.evaluate P xs (base l (fun i => s (l.get i))) fallback v = P.run G s v := by
  apply FrameInterpreter.correct G P xs _ fallback s v hxs (consistent_base l s) hx
  rw [keys_base]
  exact hl
end Paper.LocalSeedRecords
