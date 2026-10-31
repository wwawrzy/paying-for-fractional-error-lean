import Paper.Preliminaries.ClippedRank

/-! Actual bounded-counter broadcasts compute distances to marked active
sources. Input consists only of local active/source bits. -/
namespace Paper.MaskedDistance
open BroadcastModel ClippedRank
variable {V : Type} [DecidableEq V]

structure State (D : ℕ) where
  active : Bool
  rank : Rank D

def start (D : ℕ) : Program V (Bool × Bool) (State D) := .local fun _ _ s =>
  ⟨s.1, if s.1 && s.2 then ⟨0, by omega⟩ else top D⟩

def round (D : ℕ) : Round V (State D) (State D) (Rank D) where
  send _ _ s := if s.active then s.rank else top D
  update _ N s incoming := ⟨s.active,
    if s.active then choose D N s.rank incoming else top D⟩

def step (D : ℕ) : Program V (State D) (State D) :=
  .broadcast (D + 2) (SmallNumberCode.code (D + 2)) (round D)

def program (D T : ℕ) : Program V (Bool × Bool) (State D) :=
  .seq (start D) ((step D).iterate T)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D : ℕ) (A B : V → Bool)

def state : ℕ → V → State D
  | 0 => (start D).run G (fun v => (A v, B v))
  | n + 1 => eval G (round D) (state n)

theorem active (n : ℕ) (v : V) : (state G D A B n v).active = A v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem inactive (n : ℕ) {v : V} (h : A v = false) :
    (state G D A B n v).rank = top D := by
  cases n with
  | zero => simp [state, start, Program.run, h]
  | succ n => simp [state, eval, round, active, h]

theorem send_rank (n : ℕ) (v : V) :
    (round D).send v (G.neighborFinset v) (state G D A B n v) =
      (state G D A B n v).rank := by
  change (if (state G D A B n v).active then (state G D A B n v).rank else top D) = _
  rw [active]
  cases h : A v
  · simp [inactive G D A B n h]
  · rfl

theorem update_active (n : ℕ) {v : V} (h : A v = true) :
    (state G D A B (n + 1) v).rank = choose D (G.neighborFinset v)
      (state G D A B n v).rank (fun w => (state G D A B n w).rank) := by
  change (if (state G D A B n v).active then choose D (G.neighborFinset v)
    (state G D A B n v).rank
    (fun w => (round (V := V) D).send (w : V) (G.neighborFinset w) (state G D A B n w)) else top D) = _
  rw [active, h]
  simp only [↓reduceIte]
  congr 1
  funext w
  exact send_rank G D A B n w

theorem rank_le_previous (n : ℕ) (v : V) :
    (state G D A B (n + 1) v).rank.val ≤ (state G D A B n v).rank.val := by
  cases ha : A v with
  | false => rw [inactive G D A B (n + 1) ha, inactive G D A B n ha]
  | true => rw [update_active G D A B n ha]; exact choose_le_self _ _ _ _

theorem rank_le_neighbor (n : ℕ) {v w : V} (hv : A v = true) (ha : G.Adj v w) :
    (state G D A B (n + 1) v).rank.val ≤ (state G D A B n w).rank.val + 1 := by
  rw [update_active G D A B n hv]
  exact choose_le_neighbor D (G.neighborFinset v) _ _
    ⟨w, (G.mem_neighborFinset v w).mpr ha⟩

theorem source_zero (n : ℕ) {v : V} (ha : A v = true) (hb : B v = true) :
    (state G D A B n v).rank.val = 0 := by
  induction n with
  | zero => simp [state, start, Program.run, ha, hb]
  | succ n ih => have := rank_le_previous G D A B n v; omega

theorem rank_le_walk {v u : V} (p : G.Walk v u)
    (hp : ∀ z ∈ p.support, A z = true) (hb : B u = true)
    (n : ℕ) (hn : p.length ≤ n) : (state G D A B n v).rank.val ≤ p.length := by
  induction p generalizing n with
  | nil => simpa using (source_zero G D A B n (hp _ (by simp)) hb).le
  | @cons v w u ha p ih =>
    cases n with
    | zero => simp only [SimpleGraph.Walk.length_cons] at hn; omega
    | succ n =>
      have htail : ∀ z ∈ p.support, A z = true := fun z hz => hp z (by simp [hz])
      have hlen : p.length ≤ n := by simp only [SimpleGraph.Walk.length_cons] at hn; omega
      have hbound := rank_le_neighbor G D A B n (hp _ (by simp)) ha
      have hi := ih htail hb n hlen
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem run_program (T : ℕ) :
    (program (V := V) D T).run G (fun v => (A v, B v)) = state G D A B T := by
  induction T with
  | zero => rfl
  | succ n ih =>
    change eval G (round D) ((program D n).run G (fun v => (A v, B v))) =
      eval G (round D) (state G D A B n)
    rw [ih]

theorem rounds (T : ℕ) : (program (V := V) D T).rounds = T := by
  simp only [program, start, step, Program.rounds, Program.iterate_rounds,
    Nat.mul_one, Nat.zero_add]

theorem maxBits (T : ℕ) : (program (V := V) D T).maxBits ≤ D + 2 :=
  max_le (Nat.zero_le _) (Program.iterate_maxBits (step D) T)
end Paper.MaskedDistance
