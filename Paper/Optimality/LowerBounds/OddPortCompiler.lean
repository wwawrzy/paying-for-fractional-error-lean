import Paper.Preliminaries.OddPathPower
import Paper.Optimality.LowerBounds.PortLocal
import Paper.Preliminaries.LineLocalWindow

namespace Paper.OddPortCompiler
open LineLocal

def middle (t : ℕ) : Ports t := ⟨t, by omega⟩

def slots {t : ℕ} (C : Context t) : Finset (Ports t) :=
  Finset.univ.filter (fun p => p ≠ middle t ∧ (C p).isSome ∧ p.val%2 ≠ t%2)

def slotEquiv {t : ℕ} (C : Context t) : Fin (slots C).card ≃ ↥(slots C) :=
  ((slots C).orderIsoOfFin rfl).toEquiv

def compact {t : ℕ} (C : Context t) : PortLocal.Context (slots C).card :=
  ⟨(C (middle t)).getD 0, fun p => (C (slotEquiv C p).val).getD 0⟩

def simulateRound {t : ℕ} {In Out Msg : Type} (R : PortLocal.Round In Out Msg) :
    LineLocal.Round t In Out (Option Msg) where
  send C s p := if hp : p ∈ slots C then some (R.send (slots C).card (compact C) s ((slotEquiv C).symm ⟨p, hp⟩)) else none
  update C s incoming := R.update (slots C).card (compact C) s (fun p =>
    (incoming (slotEquiv C p).val).join.getD (R.send (slots C).card (compact C) s p))

def translate (t : ℕ) {In Out : Type} : PortLocal.Program In Out → LineLocal.Program t In Out
  | .local f => .local fun C s => f (slots C).card (compact C) s
  | .round R => .round (simulateRound R)
  | .seq P Q => .seq (translate t P) (translate t Q)

theorem rounds (t : ℕ) {In Out : Type} (P : PortLocal.Program In Out) :
    (translate t P).rounds = P.rounds := by
  induction P with
  | «local» f => rfl
  | round R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (·+·) ihP ihQ

theorem delta_middle (t : ℕ) : delta (middle t) = 0 := by simp [delta, middle]

theorem delta_reverse {t : ℕ} (p : Ports t) : delta (reverse p) = -delta p := by
  have hh := p.isLt
  dsimp [delta, reverse]
  omega

theorem label_isSome {n : ℕ} (ids : Fin n → ℕ) (x : ℤ) :
    (LineLocalWindow.labels ids x).isSome ↔ 0 ≤ x ∧ x < n := by
  unfold LineLocalWindow.labels
  split_ifs <;> simp_all

theorem label_at {n : ℕ} (ids : Fin n → ℕ) (v : Fin n) :
    LineLocalWindow.labels ids v.val = some (ids v) := by
  rw [LineLocalWindow.labels, dif_pos (by omega)]
  rfl

/-- Available physical slots omit the self slot; they are compressed to
ordinary consecutive port numbers 0,...,degree-1. -/
def table {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n) : Context t :=
  context (LineLocalWindow.labels ids) v.val

theorem slot_bounds {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n) (p : Ports t)
    (hp : p ∈ slots (table (t := t) ids v)) :
    p ≠ middle t ∧ 0 ≤ (v.val : ℤ)+delta p ∧ (v.val : ℤ)+delta p < n := by
  have hh := (Finset.mem_filter.mp hp).2
  exact ⟨hh.1, (label_isSome ids _).mp hh.2.1⟩

def neighbor {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n)
    (p : Fin (slots (table (t := t) ids v)).card) : Fin n :=
  let q := slotEquiv (table (t := t) ids v) p
  ⟨((v.val : ℤ)+delta q.val).toNat, by
    have hh := slot_bounds ids v q.val q.property
    omega⟩

theorem neighbor_coord {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n)
    (p : Fin (slots (table (t := t) ids v)).card) :
    ((neighbor ids v p).val : ℤ) = v.val+delta (slotEquiv (table (t := t) ids v) p).val := by
  have hh := slot_bounds ids v _ (slotEquiv (table (t := t) ids v) p).property
  dsimp [neighbor]
  omega

theorem reverse_mem {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n)
    (p : Fin (slots (table (t := t) ids v)).card) :
    reverse (slotEquiv (table (t := t) ids v) p).val ∈
      slots (table (t := t) ids (neighbor ids v p)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro he
    have hh := slot_bounds ids v _ (slotEquiv (table (t := t) ids v) p).property
    have hv := congrArg Fin.val he
    dsimp [reverse, middle] at hv
    have hp := (slotEquiv (table (t := t) ids v) p).val.isLt
    apply hh.1
    apply Fin.ext
    dsimp [middle]
    omega
  · apply (label_isSome ids _).mpr
    rw [neighbor_coord, delta_reverse]
    have hv := v.isLt
    constructor <;> omega
  · have hh := (Finset.mem_filter.mp (slotEquiv (table (t := t) ids v) p).property).2.2.2
    have hb := (slotEquiv (table (t := t) ids v) p).val.isLt
    dsimp [reverse]
    omega

def network {n t : ℕ} (ids : Fin n → ℕ) : PortLocal.Network (Fin n) where
  degree v := (slots (table (t := t) ids v)).card
  neighbor v p := neighbor ids v p
  back v p := (slotEquiv (table (t := t) ids (neighbor ids v p))).symm
    ⟨reverse (slotEquiv (table (t := t) ids v) p).val, reverse_mem ids v p⟩
  reverse_neighbor v p := by
    apply Fin.ext
    have h := neighbor_coord ids (neighbor ids v p)
      ((slotEquiv (table (t := t) ids (neighbor ids v p))).symm
        ⟨reverse (slotEquiv (table (t := t) ids v) p).val, reverse_mem ids v p⟩)
    simp only [Equiv.apply_symm_apply] at h
    rw [neighbor_coord ids v p, delta_reverse] at h
    omega

theorem compatible {n t : ℕ} (ids : Fin n → ℕ) :
    (network (t := t) ids).Compatible (OddPathPower.graph n t) := by
  constructor
  · intro v p q he
    apply (slotEquiv (table (t := t) ids v)).injective
    apply Subtype.ext
    apply Fin.ext
    have hp := neighbor_coord ids v p
    have hq := neighbor_coord ids v q
    change neighbor ids v p = neighbor ids v q at he
    rw [he] at hp
    dsimp [delta] at hp hq
    omega
  · intro v w
    change ((PathPowerTreewidth.graph n t).Adj v w ∧ v.val%2 ≠ w.val%2) ↔ _
    rw [LineLocalWindow.neighbor_iff]
    constructor
    · rintro ⟨⟨hne, q, hq⟩,hpar⟩
      have hmem : q ∈ slots (table (t := t) ids v) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
        · intro he
          rw [he, delta_middle] at hq
          exact hne (Fin.ext (by omega))
        · apply (label_isSome ids _).mpr
          rw [← hq]
          constructor <;> omega
        · dsimp [delta] at hq
          omega
      refine ⟨(slotEquiv (table (t := t) ids v)).symm ⟨q, hmem⟩, ?_⟩
      apply Fin.ext
      have hh := neighbor_coord ids v ((slotEquiv (table (t := t) ids v)).symm ⟨q, hmem⟩)
      simp only [Equiv.apply_symm_apply] at hh
      change (neighbor ids v _).val = w.val
      omega
    · rintro ⟨p, rfl⟩
      constructor
      · refine ⟨?_, (slotEquiv (table (t := t) ids v) p).val, neighbor_coord ids v p⟩
        intro he
        have hh := neighbor_coord ids v p
        change v = neighbor ids v p at he
        rw [← he] at hh
        have hb := slot_bounds ids v _ (slotEquiv (table (t := t) ids v) p).property
        apply hb.1
        apply Fin.ext
        dsimp [delta, middle] at hh ⊢
        omega
      · change v.val%2 ≠ (neighbor ids v p).val%2
        have hh := neighbor_coord ids v p
        have hm := (Finset.mem_filter.mp (slotEquiv (table (t := t) ids v) p).property).2.2.2
        dsimp [delta] at hh
        omega

theorem compact_table {n t : ℕ} (ids : Fin n → ℕ) (v : Fin n) :
    compact (table (t := t) ids v) = (network (t := t) ids).context ids v := by
  have hroot : table (t := t) ids v (middle t) = some (ids v) := by
    change LineLocalWindow.labels ids (v.val+delta (middle t)) = _
    rw [delta_middle, add_zero, label_at]
  have hnbr (p : Fin (slots (table (t := t) ids v)).card) :
      table (t := t) ids v (slotEquiv (table (t := t) ids v) p).val = some (ids (neighbor ids v p)) := by
    change LineLocalWindow.labels ids (v.val+delta _) = _
    rw [← neighbor_coord ids v p, label_at]
  unfold compact PortLocal.Network.context
  dsimp only [network]
  rw [hroot]
  congr 1
  funext p
  rw [hnbr]
  rfl

/-- No message fallback is used on any actual physical port. -/
theorem send_slot {t : ℕ} {In Out Msg : Type} (R : PortLocal.Round In Out Msg)
    (C : Context t) (s : In) (p : Fin (slots C).card) :
    (simulateRound R).send C s (slotEquiv C p).val = some (R.send (slots C).card (compact C) s p) := by
  dsimp only [simulateRound]
  rw [dif_pos (slotEquiv C p).property]
  simp

/-- Exact simulation on every finite physical vertex. -/
theorem round_correct {n t : ℕ} {In Out Msg : Type} (R : PortLocal.Round In Out Msg)
    (ids : Fin n → ℕ) (s : ℤ → In) (z : Fin n → In) (hs : ∀ v, s v.val = z v) (v : Fin n) :
    LineLocal.eval (LineLocalWindow.labels ids) (simulateRound (t := t) R) s v.val =
      (PortLocal.Program.round R).run (network (t := t) ids) ids z v := by
  have hroot := compact_table (t := t) ids v
  change R.update _ (compact (table ids v)) (s v.val) _ = R.update _ _ (z v) _
  rw [hs, hroot]
  congr 1
  funext p
  let q := (slotEquiv (table (t := t) ids v) p).val
  let w := neighbor ids v p
  have hw : (w.val : ℤ) = v.val+delta q := neighbor_coord ids v p
  have hpres : LineLocalWindow.labels ids (v.val+delta q) = some (ids w) := by
    rw [← hw, label_at]
  have hsend : (simulateRound (t := t) R).send (table ids w) (s w.val) (reverse q) =
      some (R.send ((network (t := t) ids).degree w) ((network (t := t) ids).context ids w) (z w) ((network (t := t) ids).back v p)) := by
    change (if hp : reverse q ∈ slots (table (t := t) ids w) then _ else _) = _
    rw [dif_pos (reverse_mem ids v p), hs, compact_table]
    rfl
  change ((LineLocalWindow.labels ids (v.val+delta q)).map (fun _ =>
    (simulateRound R).send (context (LineLocalWindow.labels ids) (v.val+delta q))
      (s (v.val+delta q)) (reverse q))).join.getD _ = _
  rw [hpres, ← hw]
  change ((simulateRound R).send (table ids w) (s w.val) (reverse q)).getD _ = _
  rw [hsend]
  rfl

theorem translate_correct {n t : ℕ} {In Out : Type} (P : PortLocal.Program In Out)
    (ids : Fin n → ℕ) (s : ℤ → In) (z : Fin n → In) (hs : ∀ v, s v.val = z v) (v : Fin n) :
    (translate t P).run (LineLocalWindow.labels ids) s v.val =
      P.run (network (t := t) ids) ids z v := by
  induction P generalizing v with
  | «local» f =>
    change f _ (compact (table ids v)) (s v.val) = f _ _ (z v)
    rw [compact_table, hs]
    rfl
  | round R => exact round_correct R ids s z hs v
  | seq P Q ihP ihQ =>
    apply ihQ
    intro w
    exact ihP s z hs w

end Paper.OddPortCompiler

#print axioms Paper.OddPortCompiler.compatible
#print axioms Paper.OddPortCompiler.translate_correct
