import Paper.Preliminaries.NeighborInterpreter

/-! Exact dependency radius for arbitrary finite neighbor dictionaries.
The dictionary may be incomplete away from the dependency ball. -/
namespace Paper.NeighborLocality
open BroadcastModel NeighborBalls NeighborInterpreter
variable {V : Type} [DecidableEq V]

theorem locality {In Out : Type} (P : Program V In Out) :
    ∀ (N M : V → Finset V) (s t : V → In) (v : V),
      (∀ u ∈ ball N v P.rounds, N u = M u) →
      (∀ u ∈ ball N v P.rounds, s u = t u) →
      NeighborInterpreter.run N P s v = NeighborInterpreter.run M P t v := by
  induction P with
  | «local» f =>
    intro N M s t v hn hs
    have hn' := hn v (self_mem N v 0)
    have hs' := hs v (self_mem N v 0)
    change f v (N v) (s v) = f v (M v) (t v)
    rw [hn', hs']
  | broadcast w code R =>
    intro N M s t v hn hs
    have hn' := hn v (self_mem N v 1)
    have hs' := hs v (self_mem N v 1)
    change R.update v (N v) (s v) (fun u => R.send u.val (N u.val) (s u.val)) =
      R.update v (M v) (t v) (fun u => R.send u.val (M u.val) (t u.val))
    rw [← hn', ← hs']
    congr 1
    funext u
    have hu := neighbor_mem N v u.val u.property
    rw [hn u.val hu, hs u.val hu]
  | seq P Q ihP ihQ =>
    intro N M s t v hn hs
    change NeighborInterpreter.run N Q (NeighborInterpreter.run N P s) v =
      NeighborInterpreter.run M Q (NeighborInterpreter.run M P t) v
    apply ihQ N M _ _ v
    · intro u hu
      exact hn u (monotone N v (Nat.le_add_left Q.rounds P.rounds) hu)
    · intro u hu
      apply ihP N M s t u
      · intro x hx
        have hh := subball N Q.rounds P.rounds v u hu hx
        apply hn x
        simpa only [Program.rounds, Nat.add_comm] using hh
      · intro x hx
        have hh := subball N Q.rounds P.rounds v u hu hx
        apply hs x
        simpa only [Program.rounds, Nat.add_comm] using hh

theorem input_locality {In Out : Type} (P : Program V In Out)
    (N : V → Finset V) (s t : V → In) (v : V)
    (h : ∀ u ∈ ball N v P.rounds, s u = t u) :
    NeighborInterpreter.run N P s v = NeighborInterpreter.run N P t v :=
  locality P N N s t v (fun _ _ => rfl) h

theorem radius_locality {In Out : Type} (P : Program V In Out)
    (N M : V → Finset V) (s t : V → In) (v : V) (r : ℕ)
    (hr : P.rounds ≤ r) (hn : ∀ u ∈ ball N v r, N u = M u)
    (hs : ∀ u ∈ ball N v r, s u = t u) :
    NeighborInterpreter.run N P s v = NeighborInterpreter.run M P t v :=
  locality P N M s t v
    (fun u hu => hn u (monotone N v hr hu))
    (fun u hu => hs u (monotone N v hr hu))
end Paper.NeighborLocality
