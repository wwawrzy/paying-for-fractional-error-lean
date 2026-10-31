import Paper.Preliminaries.MaskedFlooding
import Paper.Preliminaries.DistanceTree

/-! Composition of actual masked minimum election, local source marking,
bounded-counter distance rounds and the parent selection broadcast. -/
namespace Paper.LeaderTree
open BroadcastModel
variable {V : Type} [LinearOrder V]

def mark : Program V (MaskedFlooding.State V) (Bool × Bool) :=
  .local fun v _ s => (s.active, decide (s.value = some v))

def program {b : ℕ} (C : BitCode V b) (D : ℕ) :
    Program V Bool (ParentElection.Node V D) :=
  .seq (MaskedFlooding.program C D) (.seq mark (DistanceTree.program D))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : V → Bool)

theorem run_eq {b : ℕ} (C : BitCode V b) (D : ℕ) (root : V)
    (har : A root = true) (hmin : ∀ v, A v = true → root ≤ v)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true) :
    (program C D).run G A = DistanceTree.output G D A
      (fun v => A v && decide (v = root)) := by
  obtain ⟨ha, hv, _, _⟩ := MaskedFlooding.elect_minimum G A C D root har hmin hdiam
  have hi : mark.run G ((MaskedFlooding.program C D).run G A) =
      fun v => (A v, A v && decide (v = root)) := by
    funext v
    change (((MaskedFlooding.program C D).run G A v).active,
      decide (((MaskedFlooding.program C D).run G A v).value = some v)) = _
    rw [ha, hv]
    cases h : A v <;> simp [h, eq_comm]
  change (DistanceTree.program D).run G (mark.run G ((MaskedFlooding.program C D).run G A)) = _
  rw [hi]
  rfl

theorem source_root (root : V) (ha : A root = true) :
    (A root && decide (root = root)) = true := by simp [ha]

theorem source_unique (root : V) {v : V} (h : (A v && decide (v = root)) = true) :
    v = root := by
  have hh : A v = true ∧ v = root := by simpa using h
  exact hh.2

theorem rounds {b : ℕ} (C : BitCode V b) (D : ℕ) :
    (program C D).rounds = 2 * D + 1 := by
  simp only [program, Program.rounds, mark, DistanceTree.rounds]
  have hr : (MaskedFlooding.program C D).rounds = D := by
    simp only [MaskedFlooding.program, MaskedFlooding.start, MaskedFlooding.step,
      Program.rounds, Program.iterate_rounds, Nat.mul_one, Nat.zero_add]
  rw [hr]
  omega

theorem maxBits {b : ℕ} (C : BitCode V b) (D : ℕ) :
    (program C D).maxBits ≤ max (b + 1) (D + 2) := by
  have hb : (MaskedFlooding.program C D).maxBits ≤ b + 1 :=
    max_le (Nat.zero_le _) (Program.iterate_maxBits (MaskedFlooding.step C) D)
  exact max_le (hb.trans (le_max_left _ _))
    (max_le (Nat.zero_le _) ((DistanceTree.maxBits (V := V) D).trans (le_max_right _ _)))
end Paper.LeaderTree
