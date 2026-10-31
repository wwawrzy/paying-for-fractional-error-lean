import Mathlib

/-! Deterministic unrestricted messages on a line with range t. Port p has
signed displacement p-t, with a harmless self slot. A missing vertex delivers
none. Instructions see identifiers in the one-hop port table (KT1), never
absolute coordinates. Messages may differ at every outgoing port. -/
namespace Paper.LineLocal

abbrev Ports (t : ℕ) := Fin (2*t+1)
abbrev Context (t : ℕ) := Ports t → Option ℕ

def delta {t : ℕ} (p : Ports t) : ℤ := (p.val : ℤ)-t

def reverse {t : ℕ} (p : Ports t) : Ports t := ⟨2*t-p.val, by omega⟩

theorem delta_bounds {t : ℕ} (p : Ports t) : -(t : ℤ) ≤ delta p ∧ delta p ≤ t := by
  have hh := p.isLt
  dsimp [delta]
  omega

structure Round (t : ℕ) (In Out Msg : Type) where
  send : Context t → In → Ports t → Msg
  update : Context t → In → (Ports t → Option Msg) → Out

inductive Program (t : ℕ) : Type → Type → Type 1 where
  | local {In Out : Type} (f : Context t → In → Out) : Program t In Out
  | round {In Out Msg : Type} (R : Round t In Out Msg) : Program t In Out
  | seq {In Mid Out : Type} (P : Program t In Mid) (Q : Program t Mid Out) : Program t In Out

def context {t : ℕ} (ids : ℤ → Option ℕ) (x : ℤ) : Context t := fun p => ids (x+delta p)

def eval {t : ℕ} {In Out Msg : Type} (ids : ℤ → Option ℕ) (R : Round t In Out Msg)
    (s : ℤ → In) (x : ℤ) : Out :=
  R.update (context ids x) (s x) (fun p =>
    (ids (x+delta p)).map (fun _ => R.send (context ids (x+delta p)) (s (x+delta p)) (reverse p)))

namespace Program

def run {t : ℕ} {In Out : Type} (ids : ℤ → Option ℕ) : Program t In Out → (ℤ → In) → ℤ → Out
  | .local f, s => fun x => f (context ids x) (s x)
  | .round R, s => eval ids R s
  | .seq P Q, s => Q.run ids (P.run ids s)

def rounds {t : ℕ} {In Out : Type} : Program t In Out → ℕ
  | .local _ => 0
  | .round _ => 1
  | .seq P Q => P.rounds+Q.rounds

/-- Radius after the KT1 initial table and the actual communication rounds. -/
def radius {t : ℕ} {In Out : Type} (P : Program t In Out) : ℕ := t*(P.rounds+1)

end Program

def Same {A : Type} (r : ℕ) (f g : ℤ → A) (i j : ℤ) : Prop :=
  ∀ d : ℤ, -(r : ℤ) ≤ d → d ≤ r → f (i+d) = g (j+d)

theorem Same.zero {A : Type} {r : ℕ} {f g : ℤ → A} {i j : ℤ} (h : Same r f g i j) :
    f i = g j := by simpa using h 0 (by omega) (by omega)

theorem Same.shift {A : Type} {r s : ℕ} {f g : ℤ → A} {i j : ℤ}
    (h : Same (r+s) f g i j) (d : ℤ) (hl : -(s : ℤ) ≤ d) (hr : d ≤ s) :
    Same r f g (i+d) (j+d) := by
  intro e heL heR
  have hh := h (d+e) (by push_cast; omega) (by push_cast; omega)
  simpa only [add_assoc] using hh

theorem Same.mono {A : Type} {r s : ℕ} {f g : ℤ → A} {i j : ℤ}
    (h : Same s f g i j) (hrs : r ≤ s) : Same r f g i j := by
  intro d hl hr
  exact h d (by omega) (by omega)

theorem context_eq {t : ℕ} {ids ids' : ℤ → Option ℕ} {i j : ℤ}
    (h : Same t ids ids' i j) : context (t := t) ids i = context (t := t) ids' j := by
  funext p
  exact h _ (delta_bounds p).1 (delta_bounds p).2

/-- Locality is proved for actual per-port message execution, for arbitrary
state/message types and exact identifier magnitudes. -/
theorem run_locality_core {t : ℕ} {In Out : Type} (P : Program t In Out)
    {ids ids' : ℤ → Option ℕ} {s s' : ℤ → In} {i j : ℤ}
    (hids : Same P.radius ids ids' i j) (hs : Same (t*P.rounds) s s' i j) :
    P.run ids s i = P.run ids' s' j := by
  induction P generalizing i j with
  | «local» f =>
    have hh : Same t ids ids' i j := by simpa only [Program.radius, Program.rounds, zero_add, mul_one] using hids
    exact congrArg₂ f (context_eq hh) hs.zero
  | round R =>
    change R.update _ _ _ = R.update _ _ _
    have hrad : t*(1+1) = t+t := by omega
    have hctx := context_eq (hids.mono (by change t ≤ t*(1+1); omega))
    rw [hctx, hs.zero]
    congr 1
    funext p
    have hb := delta_bounds p
    have hids' : Same (t+t) ids ids' i j := by simpa only [Program.radius, Program.rounds, hrad] using hids
    have hi := hids'.shift (delta p) hb.1 hb.2
    have hs' : Same t s s' i j := by simpa only [Program.rounds, mul_one] using hs
    have hh := hs' (delta p) hb.1 hb.2
    rw [hi.zero, context_eq hi, hh]
  | seq P Q ihP ihQ =>
    apply ihQ
    · exact hids.mono (by simp only [Program.radius, Program.rounds]; nlinarith)
    · intro d hl hr
      apply ihP
      · have he : (Program.seq P Q).radius = P.radius+t*Q.rounds := by
          simp only [Program.radius, Program.rounds]; ring
        rw [he] at hids
        exact hids.shift d hl hr
      · have he : t*(Program.seq P Q).rounds = t*P.rounds+t*Q.rounds := by
          simp only [Program.rounds]; ring
        rw [he] at hs
        exact hs.shift d hl hr

theorem run_locality {t : ℕ} {In Out : Type} (P : Program t In Out)
    {ids ids' : ℤ → Option ℕ} {s s' : ℤ → In} {i j : ℤ}
    (hids : Same P.radius ids ids' i j) (hs : Same P.radius s s' i j) :
    P.run ids s i = P.run ids' s' j :=
  run_locality_core P hids (hs.mono (by simp only [Program.radius]; nlinarith))

end Paper.LineLocal
