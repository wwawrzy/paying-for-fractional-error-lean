import Paper.Communication.BroadcastChoice

/-! Broadcast one bounded-code payload through a marked physical region.
Only local active flags and received packets are read by the program. -/
namespace Paper.PayloadFlood
open BroadcastModel
variable {V A : Type} [LinearOrder V]

abbrev State (A : Type) := Bool × Option A

def round : Round V (State A) (State A) (Option A) where
  send _ _ s := if s.1 then s.2 else none
  update _ N s incoming := (s.1, if s.1 then
    match s.2 with
    | some a => some a
    | none => BroadcastChoice.choose N incoming
    else none)

def step {b : ℕ} (C : BitCode A b) : Program V (State A) (State A) :=
  .broadcast (b + 1) C.option round

def program {b : ℕ} (C : BitCode A b) (D : ℕ) : Program V (State A) (State A) :=
  (step C).iterate D

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : V → State A)

def state : ℕ → V → State A
  | 0 => S
  | n + 1 => eval G round (state n)

theorem active (n : ℕ) (v : V) : (state G S n v).1 = (S v).1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem uniform (x : A) (hi : ∀ v, (S v).2 = none ∨ (S v).2 = some x)
    (n : ℕ) (v : V) : (state G S n v).2 = none ∨ (state G S n v).2 = some x := by
  induction n generalizing v with
  | zero => exact hi v
  | succ n ih =>
    simp only [state, eval, round]
    cases ha : (state G S n v).1 with
    | false => exact Or.inl rfl
    | true =>
      rcases ih v with hn | hx
      · simp only [ha, hn, ↓reduceIte]
        apply BroadcastChoice.uniform
        intro w
        cases hw : (state G S n w).1 with
        | false => exact Or.inl rfl
        | true => exact ih w
      · simp [ha, hx]

theorem persistent (n : ℕ) (v : V) (x : A)
    (ha : (S v).1 = true) (hx : (state G S n v).2 = some x) :
    (state G S (n + 1) v).2 = some x := by
  simp [state, eval, round, active, ha, hx]

theorem source (root : V) (x : A) (ha : (S root).1 = true) (hx : (S root).2 = some x)
    (n : ℕ) : (state G S n root).2 = some x := by
  induction n with
  | zero => exact hx
  | succ n ih => exact persistent G S n root x ha ih

theorem neighbor (x : A) (hi : ∀ v, (S v).2 = none ∨ (S v).2 = some x)
    (n : ℕ) {v w : V} (hv : (S v).1 = true) (hw : (S w).1 = true)
    (ha : G.Adj v w) (hx : (state G S n w).2 = some x) :
    (state G S (n + 1) v).2 = some x := by
  rcases uniform G S x hi n v with hn | hs
  · change (if (state G S n v).1 then
      match (state G S n v).2 with
      | some a => some a
      | none => BroadcastChoice.choose (G.neighborFinset v)
          (fun u => if (state G S n u).1 then (state G S n u).2 else none)
      else none) = some x
    rw [active, hv, hn]
    simp only [↓reduceIte]
    apply BroadcastChoice.some_of_present
    · intro u
      cases hu : (state G S n u).1 with
      | false => exact Or.inl rfl
      | true => exact uniform G S x hi n u
    · refine ⟨⟨w, (G.mem_neighborFinset v w).mpr ha⟩, ?_⟩
      rw [active, hw, if_pos rfl]
      exact hx
  · exact persistent G S n v x hv hs

theorem of_walk (x : A) (hi : ∀ v, (S v).2 = none ∨ (S v).2 = some x)
    {v root : V} (p : G.Walk v root) (hp : ∀ z ∈ p.support, (S z).1 = true)
    (hx : (S root).2 = some x) (n : ℕ) (hn : p.length ≤ n) :
    (state G S n v).2 = some x := by
  induction p generalizing n with
  | nil => exact source G S _ x (hp _ (by simp)) hx n
  | @cons v w root ha p ih =>
    cases n with
    | zero => simp only [SimpleGraph.Walk.length_cons] at hn; omega
    | succ n =>
      have ht : ∀ z ∈ p.support, (S z).1 = true := fun z hz => hp z (by simp [hz])
      have hlen : p.length ≤ n := by simp only [SimpleGraph.Walk.length_cons] at hn; omega
      exact neighbor G S x hi n (hp _ (by simp)) (ht _ p.start_mem_support) ha (ih ht hx n hlen)

theorem run_program {b : ℕ} (C : BitCode A b) (D : ℕ) :
    (program (V := V) C D).run G S = state G S D := by
  induction D with
  | zero => rfl
  | succ n ih =>
    change eval G round ((program C n).run G S) = eval G round (state G S n)
    rw [ih]

theorem correct {b : ℕ} (C : BitCode A b) (D : ℕ) (root : V) (x : A)
    (hi : ∀ v, (S v).2 = none ∨ (S v).2 = some x) (hx : (S root).2 = some x)
    (hd : ∀ v, (S v).1 = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, (S z).1 = true) :
    (∀ v, (S v).1 = true → ((program (V := V) C D).run G S v).2 = some x) ∧
    (program (V := V) C D).rounds = D ∧
    (program (V := V) C D).maxBits ≤ b + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, hpa⟩ := hd v hv
    rw [run_program]
    exact of_walk G S x hi p hpa hx D hp
  · simp only [program, step, Program.iterate_rounds, Program.rounds, Nat.mul_one]
  · exact Program.iterate_maxBits (step C) D
end Paper.PayloadFlood
