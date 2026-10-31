import Paper.Optimality.LowerBounds.PortLocal
import Paper.Preliminaries.LineLocalWindow
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-! Periodic simulation on a closed cycle. The two physical ports are left
and right; the line's middle slot is ignored. No coordinates or cycle order
are supplied to any local instruction. -/
namespace Paper.CyclePortLocal

open scoped Fin.NatCast
open LineLocal

local instance (n : ℕ) : AddGroupWithOne (Fin (n + 3)) :=
  { Fin.instAddMonoidWithOne (n + 3), Fin.addCommGroup (n + 3) with }

def neighbor (n : ℕ) (v : Fin (n + 3)) (p : Fin 2) : Fin (n + 3) :=
  if p = 0 then v - 1 else v + 1

def back (p : Fin 2) : Fin 2 := if p = 0 then 1 else 0

def network (n : ℕ) : PortLocal.Network (Fin (n + 3)) where
  degree _ := 2
  neighbor := neighbor n
  back _ := back
  reverse_neighbor v p := by
    fin_cases p <;> simp [neighbor, back]

theorem left_ne_right (n : ℕ) (v : Fin (n + 3)) : v - 1 ≠ v + 1 := by
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

theorem compatible (n : ℕ) : (network n).Compatible (SimpleGraph.cycleGraph (n + 3)) := by
  constructor
  · intro v p q he
    fin_cases p <;> fin_cases q
    · rfl
    · exact False.elim (left_ne_right n v he)
    · exact False.elim (left_ne_right n v he.symm)
    · rfl
  · intro v w
    rw [← (SimpleGraph.cycleGraph (n + 3)).mem_neighborFinset,
      SimpleGraph.cycleGraph_neighborFinset]
    constructor
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact ⟨(0 : Fin 2), by simpa [network, neighbor] using h.symm⟩
      · exact ⟨(1 : Fin 2), by simpa [network, neighbor] using (Finset.mem_singleton.mp h).symm⟩
    · rintro ⟨p, rfl⟩
      fin_cases p <;> simp [network, neighbor]

def periodic {n : ℕ} (ids : Fin (n + 3) → ℕ) (x : ℤ) : Option ℕ :=
  some (ids (x : Fin (n + 3)))

def port (p : Fin 2) : Ports 1 := if p = 0 then 0 else 2

def compact (C : Context 1) : PortLocal.Context 2 :=
  ⟨(C 1).getD 0, fun p => (C (port p)).getD 0⟩

def simulateRound {In Out Msg : Type} (R : PortLocal.Round In Out Msg) :
    LineLocal.Round 1 In Out Msg where
  send C s q := R.send 2 (compact C) s (if q = 0 then 0 else 1)
  update C s incoming := R.update 2 (compact C) s (fun p =>
    (incoming (port p)).getD (R.send 2 (compact C) s p))

def translate {In Out : Type} : PortLocal.Program In Out → LineLocal.Program 1 In Out
  | .local f => .local fun C s => f 2 (compact C) s
  | .round R => .round (simulateRound R)
  | .seq P Q => .seq (translate P) (translate Q)

theorem rounds {In Out : Type} (P : PortLocal.Program In Out) :
    (translate P).rounds = P.rounds := by
  induction P with
  | «local» f => rfl
  | round R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

theorem neighbor_index (n : ℕ) (x : ℤ) (p : Fin 2) :
    ((x + delta (port p) : ℤ) : Fin (n + 3)) =
      (network n).neighbor (x : Fin (n + 3)) p := by
  fin_cases p <;> simp [network, neighbor, port, delta, Int.cast_add, sub_eq_add_neg]

theorem compact_periodic {n : ℕ} (ids : Fin (n + 3) → ℕ) (x : ℤ) :
    compact (context (periodic ids) x) =
      (network n).context ids (x : Fin (n + 3)) := by
  unfold compact PortLocal.Network.context
  congr 1
  · simp [context, periodic, delta]
  · funext p
    change (some (ids ((x + delta (port p) : ℤ) : Fin (n + 3)))).getD 0 = _
    rw [neighbor_index]
    rfl

theorem round_correct {n : ℕ} {In Out Msg : Type} (R : PortLocal.Round In Out Msg)
    (ids : Fin (n + 3) → ℕ) (s : ℤ → In) (z : Fin (n + 3) → In)
    (hs : ∀ x, s x = z (x : Fin (n + 3))) (x : ℤ) :
    LineLocal.eval (periodic ids) (simulateRound R) s x =
      (PortLocal.Program.round R).run (network n) ids z (x : Fin (n + 3)) := by
  change R.update 2 (compact (context (periodic ids) x)) (s x) _ =
    R.update 2 ((network n).context ids (x : Fin (n + 3)))
      (z (x : Fin (n + 3))) _
  rw [compact_periodic, hs]
  congr 1
  funext p
  change ((periodic ids (x + delta (port p))).map (fun _ =>
    (simulateRound R).send (context (periodic ids) (x + delta (port p)))
      (s (x + delta (port p))) (reverse (port p)))).getD _ = _
  simp only [periodic, Option.map_some, Option.getD_some, simulateRound,
    compact_periodic, hs]
  rw [neighbor_index]
  fin_cases p <;> rfl

theorem correct {n : ℕ} {In Out : Type} (P : PortLocal.Program In Out)
    (ids : Fin (n + 3) → ℕ) (s : ℤ → In) (z : Fin (n + 3) → In)
    (hs : ∀ x, s x = z (x : Fin (n + 3))) (x : ℤ) :
    (translate P).run (periodic ids) s x =
      P.run (network n) ids z (x : Fin (n + 3)) := by
  induction P generalizing x with
  | «local» f => exact congrArg₂ (f 2) (compact_periodic ids x) (hs x)
  | round R => exact round_correct R ids s z hs x
  | seq P Q ihP ihQ =>
    exact ihQ _ _ (fun y => ihP s z hs y) x

theorem index_val_of_bounds (n : ℕ) (x : ℤ) (h0 : 0 ≤ x) (h1 : x < n + 3) :
    (x : Fin (n + 3)).val = x.toNat := by
  have hx : x = (x.toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
  calc
    _ = (((x.toNat : ℕ) : ℤ) : Fin (n + 3)).val :=
      congrArg (fun y : ℤ => (y : Fin (n + 3)).val) hx
    _ = _ := by
      rw [Int.cast_natCast, Fin.val_cast_of_lt (show x.toNat < n + 3 by omega)]

theorem agrees {n : ℕ} (P : PortLocal.Program Unit Bool) (r : ℕ)
    (hr : P.rounds + 1 ≤ r) (ids : Fin (n + 3) → ℕ) :
    PathPowerRamsey.Agrees (LineLocalWindow.rule (translate P) r) ids
      (P.run (network n) ids (fun _ => ())) := by
  intro v hl hu
  have heval := correct P ids (fun _ => ()) (fun _ => ()) (fun _ => rfl) (v.val : ℤ)
  simp only [Int.cast_natCast, Fin.cast_val_eq_self] at heval
  rw [← heval]
  apply run_locality (translate P)
  · intro d hdL hdR
    have hrad : (translate P).radius ≤ r := by
      simpa only [Program.radius, rounds, Nat.one_mul] using hr
    have hdL' : -(r : ℤ) ≤ d := by omega
    have hdR' : d ≤ r := by omega
    dsimp only [periodic, LineLocalWindow.canonical]
    rw [dif_pos (by omega)]
    apply congrArg some
    unfold PathPowerRamsey.window
    congr 1
    apply Fin.ext
    have hn0 : 0 ≤ (v.val : ℤ) + d := by omega
    have hn1 : (v.val : ℤ) + d < n + 3 := by omega
    rw [index_val_of_bounds n _ hn0 hn1]
    dsimp only
    omega
  · intro d _ _
    rfl

end Paper.CyclePortLocal

#print axioms Paper.CyclePortLocal.compatible
#print axioms Paper.CyclePortLocal.correct
#print axioms Paper.CyclePortLocal.agrees
