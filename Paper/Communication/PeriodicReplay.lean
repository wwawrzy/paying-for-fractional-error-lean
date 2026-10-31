import Mathlib.Data.Nat.Basic

/-!
A local cache replays an eventually constant trace of finite communication frames.
The frame type may, for example, be six finite bit strings sent in six consecutive
rounds. A cycle below summarizes that complete frame, and does not send an entire
frame in one round. No first-stop index or global stopping bound is used by the
state transitions. The notification is an input from the local computation.
-/
namespace Paper.PeriodicReplay

variable {A : Type*}

/-- Local silence state before a cycle. The notifying cycle is still sent. -/
def quiet (notify : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => quiet notify n || notify n

/-- A complete frame is either transmitted over its constituent rounds or omitted. -/
def wire (trace : ℕ → A) (notify : ℕ → Bool) (n : ℕ) : Option A :=
  if quiet notify n then none else some (trace n)

/-- Receiver state after the indicated number of complete cycles. -/
def cache (trace : ℕ → A) (notify : ℕ → Bool) (initial : A) : ℕ → A
  | 0 => initial
  | n + 1 => (wire trace notify n).getD (cache trace notify initial n)

/-- The notifying frame is already the frame for every later cycle. -/
def StableAfterNotification (trace : ℕ → A) (notify : ℕ → Bool) : Prop :=
  ∀ n, notify n = true → ∀ k, trace (n + k) = trace n

/-- Silence, once reached, persists. -/
theorem quiet_add (notify : ℕ → Bool) (n : ℕ)
    (h : quiet notify n = true) (k : ℕ) : quiet notify (n + k) = true := by
  induction k with
  | zero => simpa using h
  | succ k ih => simp [quiet, ih]

/-- A notification takes effect starting with the next complete cycle. -/
theorem notify_quiet (notify : ℕ → Bool) (n : ℕ)
    (h : notify n = true) (k : ℕ) : quiet notify (n + 1 + k) = true := by
  apply quiet_add
  simp [quiet, h]

/-- A quiet cycle transmits no frame. -/
theorem quiet_wire_none (trace : ℕ → A) (notify : ℕ → Bool) (n : ℕ)
    (h : quiet notify n = true) : wire trace notify n = none := by
  simp [wire, h]

/-- An active cycle sends exactly its ordinary frame. -/
theorem active_wire_some (trace : ℕ → A) (notify : ℕ → Bool) (n : ℕ)
    (h : quiet notify n = false) : wire trace notify n = some (trace n) := by
  simp [wire, h]

/-- Whenever the sender is quiet, the retained frame agrees with all future frames. -/
theorem quiet_cache_future (trace : ℕ → A) (notify : ℕ → Bool) (initial : A)
    (stable : StableAfterNotification trace notify) (n : ℕ) :
    ∀ k, quiet notify n = true → cache trace notify initial n = trace (n + k) := by
  induction n with
  | zero =>
      intro k h
      simp [quiet] at h
  | succ n ih =>
      intro k h
      cases hq : quiet notify n with
      | false =>
          have hn : notify n = true := by simpa [quiet, hq] using h
          simpa [cache, wire, hq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (stable n hn (k + 1)).symm
      | true =>
          simpa [cache, wire, hq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (k + 1) hq

/-- After every complete cycle the cache replays exactly that cycle's ordinary frame. -/
theorem cache_succ_eq_trace (trace : ℕ → A) (notify : ℕ → Bool) (initial : A)
    (stable : StableAfterNotification trace notify) (n : ℕ) :
    cache trace notify initial (n + 1) = trace n := by
  cases hq : quiet notify n with
  | false => simp [cache, wire, hq]
  | true =>
      simpa [cache, wire, hq] using quiet_cache_future trace notify initial stable n 0 hq

/-- Any local interpretation of a received frame is preserved by replay. -/
theorem replay_eq {B : Type*} (decode : A → B) (trace : ℕ → A)
    (notify : ℕ → Bool) (initial : A)
    (stable : StableAfterNotification trace notify) (n : ℕ) :
    decode (cache trace notify initial (n + 1)) = decode (trace n) := by
  rw [cache_succ_eq_trace trace notify initial stable n]

end Paper.PeriodicReplay
