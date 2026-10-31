import Paper.Communication.PortBroadcastModel
import Mathlib.Data.List.FinRange

/-! A literal one-round own-ID broadcast learns port-indexed neighbor IDs.
Only the evaluator knows the graph; subsequent local lookups use the list. -/
namespace Paper.PortDiscovery
open BroadcastModel (BitCode)
variable {V : Type} [DecidableEq V]

structure Env (V : Type) where
  ids : List V

def neighbors (e : Env V) : Finset V := e.ids.toFinset

def prepare {In : Type} {b : ℕ} (C : BitCode V b) : PortBroadcastModel.Program V In (In × Env V) :=
  .broadcast b C {
    send := fun v _ _ => v
    update := fun _ d st incoming => (st, ⟨List.ofFn incoming⟩) }

def read {Msg : Type} (e : Env V) (d : ℕ) (incoming : Fin d → Msg) (fallback : Msg) (v : V) : Msg :=
  let i := e.ids.idxOf v
  if hi : i < d then incoming ⟨i, hi⟩ else fallback

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def learned (ports : PortBroadcastModel.Numbering G) (v : V) : Env V :=
  ⟨List.ofFn (fun i => (ports v i).val)⟩

theorem prepare_correct {In : Type} {b : ℕ} (C : BitCode V b)
    (ports : PortBroadcastModel.Numbering G) (s : V → In) :
    (prepare C).run G ports s = fun v => (s v, learned G ports v) := rfl

theorem neighbors_correct (ports : PortBroadcastModel.Numbering G) (v : V) :
    neighbors (learned G ports v) = G.neighborFinset v := by
  ext u
  simp only [neighbors, learned, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact (ports v i).property
  · intro hu
    exact ⟨(ports v).symm ⟨u, hu⟩, congrArg Subtype.val ((ports v).apply_symm_apply ⟨u, hu⟩)⟩

theorem read_correct {Msg : Type} (ports : PortBroadcastModel.Numbering G) (v : V)
    (messages : V → Msg) (fallback : Msg) (u : G.neighborFinset v) :
    read (learned G ports v) (G.degree v) (fun i => messages (ports v i).val) fallback u.val = messages u.val := by
  let ids := (learned G ports v).ids
  have hmem : u.val ∈ ids := by
    apply List.mem_ofFn.mpr
    exact ⟨(ports v).symm u, congrArg Subtype.val ((ports v).apply_symm_apply u)⟩
  have hi : ids.idxOf u.val < G.degree v := by
    have hh := List.idxOf_lt_length_iff.mpr hmem
    simpa only [ids, learned, List.length_ofFn] using hh
  have hget : (ports v ⟨ids.idxOf u.val, hi⟩).val = u.val := by
    have hh := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)
    simpa only [ids, learned, List.getElem_ofFn] using hh
  change (if h : ids.idxOf u.val < G.degree v then
    messages (ports v ⟨ids.idxOf u.val, h⟩).val else fallback) = _
  rw [dif_pos hi, hget]

omit [DecidableEq V] [Fintype V] in
theorem rounds {In : Type} {b : ℕ} (C : BitCode V b) :
    (prepare (In := In) C).rounds = 1 := rfl

omit [DecidableEq V] [Fintype V] in
theorem maxBits {In : Type} {b : ℕ} (C : BitCode V b) :
    (prepare (In := In) C).maxBits = b := rfl

end Paper.PortDiscovery
