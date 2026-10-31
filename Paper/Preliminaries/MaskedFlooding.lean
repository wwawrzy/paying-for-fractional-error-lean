import Paper.Preliminaries.MaskedMinimum

/-! Actual masked identifier flooding on the physical network. Membership
in the task is local input. A vertex outside the task never transmits an ID.
The program and decoder use the public identifier type, not a globally
known subtype of active vertices. -/
namespace Paper.MaskedFlooding
open BroadcastModel MaskedMinimum
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  active : Bool
  value : Option V

def start : Program V Bool (State V) := .local fun v _ a =>
  ⟨a, if a then some v else none⟩

def round : Round V (State V) (State V) (Option V) where
  send _ _ s := if s.active then s.value else none
  update _ N s incoming :=
    ⟨s.active, if s.active then minimum (pool N s.value incoming) else none⟩

def step {b : ℕ} (C : BitCode V b) : Program V (State V) (State V) :=
  .broadcast (b + 1) C.option round

def program {b : ℕ} (C : BitCode V b) (D : ℕ) : Program V Bool (State V) :=
  .seq start ((step C).iterate D)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : V → Bool)

def state : ℕ → V → State V
  | 0 => start.run G A
  | n + 1 => eval G round (state n)

theorem active (n : ℕ) (v : V) : (state G A n v).active = A v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem inactive (n : ℕ) {v : V} (h : A v = false) :
    (state G A n v).value = none := by
  cases n with
  | zero => simp [state, start, Program.run, h]
  | succ n => simp [state, eval, round, active, h]

theorem send_value (n : ℕ) (v : V) :
    round.send v (G.neighborFinset v) (state G A n v) = (state G A n v).value := by
  change (if (state G A n v).active then (state G A n v).value else none) = _
  rw [active]
  cases h : A v
  · simp [inactive G A n h]
  · rfl

theorem update_active (n : ℕ) {v : V} (h : A v = true) :
    (state G A (n + 1) v).value = minimum
      (pool (G.neighborFinset v) (state G A n v).value
        (fun w => (state G A n w).value)) := by
  change (if (state G A n v).active then minimum
    (pool (G.neighborFinset v) (state G A n v).value
      (fun w => round.send w (G.neighborFinset w) (state G A n w))) else none) = _
  rw [active, h]
  simp only [↓reduceIte]
  congr 2
  funext w
  exact send_value G A n w

theorem origin (n : ℕ) {v u : V} (h : (state G A n v).value = some u) : A u = true := by
  induction n generalizing v u with
  | zero =>
    change (if A v then some v else none) = some u at h
    cases ha : A v with
    | false => simp [ha] at h
    | true =>
      simp only [ha, ↓reduceIte] at h
      cases Option.some.inj h
      exact ha
  | succ n ih =>
    cases ha : A v with
    | false => rw [inactive G A (n + 1) ha] at h; contradiction
    | true =>
      rw [update_active G A n ha] at h
      exact pool_origin _ _ _ (fun u => A u = true)
        (fun _ hs => ih hs) (fun _ _ hs => ih hs) (minimum_mem h)

theorem le_initial (n : ℕ) {v : V} (h : A v = true) :
    ∃ u, (state G A n v).value = some u ∧ u ≤ v := by
  induction n with
  | zero => exact ⟨v, by simp [state, start, Program.run, h], le_rfl⟩
  | succ n ih =>
    obtain ⟨u, hu, huv⟩ := ih
    obtain ⟨m, hm, hmu⟩ := minimum_le (mem_pool_self (G.neighborFinset v)
      (fun w => (state G A n w).value) hu)
    exact ⟨m, (update_active G A n h).trans hm, hmu.trans huv⟩

theorem le_neighbor (n : ℕ) {v w u : V} (hv : A v = true) (ha : G.Adj v w)
    (hu : (state G A n w).value = some u) :
    ∃ m, (state G A (n + 1) v).value = some m ∧ m ≤ u := by
  let w' : G.neighborFinset v := ⟨w, (G.mem_neighborFinset v w).mpr ha⟩
  obtain ⟨m, hm, hmu⟩ := minimum_le (mem_pool_incoming (G.neighborFinset v)
    (state G A n v).value (fun z => (state G A n z).value) w' hu)
  exact ⟨m, (update_active G A n hv).trans hm, hmu⟩

theorem le_of_walk {v u : V} (p : G.Walk v u)
    (hp : ∀ z ∈ p.support, A z = true) (n : ℕ) (hn : p.length ≤ n) :
    ∃ m, (state G A n v).value = some m ∧ m ≤ u := by
  induction p generalizing n with
  | nil => exact le_initial G A n (hp _ (by simp))
  | @cons v w u ha p ih =>
    cases n with
    | zero => simp only [SimpleGraph.Walk.length_cons] at hn; omega
    | succ n =>
      have htail : ∀ z ∈ p.support, A z = true := by
        intro z hz
        exact hp z (by simp [hz])
      have hlen : p.length ≤ n := by
        simp only [SimpleGraph.Walk.length_cons] at hn
        omega
      obtain ⟨s, hs, hsu⟩ := ih htail n hlen
      obtain ⟨m, hm, hms⟩ := le_neighbor G A n (hp v (by simp)) ha hs
      exact ⟨m, hm, hms.trans hsu⟩

theorem run_program {b : ℕ} (C : BitCode V b) (D : ℕ) :
    (program C D).run G A = state G A D := by
  induction D with
  | zero => rfl
  | succ n ih =>
    change eval G round ((program C n).run G A) = eval G round (state G A n)
    rw [ih]

theorem elect_minimum {b : ℕ} (C : BitCode V b) (D : ℕ) (root : V)
    (hroot : A root = true) (hmin : ∀ v, A v = true → root ≤ v)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true) :
    (∀ v, ((program C D).run G A v).active = A v) ∧
    (∀ v, ((program C D).run G A v).value = if A v then some root else none) ∧
    (program C D).rounds = D ∧ (program C D).maxBits ≤ b + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v; rw [run_program]; exact active G A D v
  · intro v
    rw [run_program]
    cases hv : A v with
    | false => simpa [hv] using inactive G A D hv
    | true =>
      obtain ⟨p, hlen, hp⟩ := hdiam v hv
      obtain ⟨m, hm, hle⟩ := le_of_walk G A p hp D hlen
      have heq : m = root := le_antisymm hle (hmin m (origin G A D hm))
      simpa [hv, heq] using hm
  · simp only [program, start, step, Program.rounds, Program.iterate_rounds,
      Nat.mul_one, Nat.zero_add]
  · exact max_le (Nat.zero_le _) (Program.iterate_maxBits (step C) D)
end Paper.MaskedFlooding
