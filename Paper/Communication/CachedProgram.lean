import Paper.Communication.PrefixProgram

/-! Execution of finite-string programs with silent senders and local
receiver caches. A cache belongs to a receiver and is indexed by sender and
public slot within a repeated phase. Each receiver records its own local sends and messages from adjacent senders.
Silence is absence of a message; no cached word is transmitted again. -/
namespace Paper.PrefixBroadcast.Program
open BroadcastModel

abbrev Cache (V : Type) := V → V → ℕ → List Bool

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def sent {In Out : Type} : Program V In Out → (V → In) → ℕ → V → List Bool
  | .local _, _, _, _ => []
  | .broadcast P, s, i, v => if i = 0 then P.send v (G.neighborFinset v) (s v) else []
  | .seq P Q, s, i, v =>
      if i < P.rounds then sent P s i v else sent Q (P.run G s) (i-P.rounds) v

def wire {In Out : Type} (P : Round V In Out (List Bool)) (quiet : V → Bool)
    (s : V → In) (v : V) : Option (List Bool) :=
  if quiet v then none else some (P.send v (G.neighborFinset v) (s v))

def received {In Out : Type} (P : Round V In Out (List Bool)) (quiet : V → Bool)
    (s : V → In) (cache : Cache V) (offset : ℕ) (v u : V) : List Bool :=
  (wire G P quiet s u).getD (cache v u offset)

def cachedBroadcast {In Out : Type} (P : Round V In Out (List Bool))
    (quiet : V → Bool) (s : V → In) (cache : Cache V) (offset : ℕ) :
    (V → Out) × Cache V :=
  (fun v => P.update v (G.neighborFinset v) (s v)
      (fun u => received G P quiet s cache offset v u),
   fun v u i => if i = offset ∧ (v = u ∨ G.Adj v u) then received G P quiet s cache offset v u
      else cache v u i)

def cachedRun {In Out : Type} (quiet : V → Bool) :
    Program V In Out → (V → In) → Cache V → ℕ → (V → Out) × Cache V
  | .local f, s, cache, _ => (fun v => f v (G.neighborFinset v) (s v), cache)
  | .broadcast P, s, cache, offset => cachedBroadcast G P quiet s cache offset
  | .seq P Q, s, cache, offset =>
      let first := cachedRun quiet P s cache offset
      cachedRun quiet Q first.1 first.2 (offset+P.rounds)

/-- Ready caches are required only for silent neighbors and local self records,
never for active senders or unrelated vertices. The premise will come from a previous phase and
the sender's locally certified permanence of its phase messages. -/
theorem cachedRun_correct {In Out : Type} (quiet : V → Bool) (P : Program V In Out)
    (s : V → In) (cache : Cache V) (offset : ℕ)
    (hready : ∀ i < P.rounds, ∀ v u, (v = u ∨ G.Adj v u) → quiet u = true →
      cache v u (offset+i) = P.sent G s i u) :
    (P.cachedRun G quiet s cache offset).1 = P.run G s ∧
      (∀ v u i, (v = u ∨ G.Adj v u) → i < P.rounds →
        (P.cachedRun G quiet s cache offset).2 v u (offset+i) = P.sent G s i u) ∧
      (∀ v u i, (i < offset ∨ offset+P.rounds ≤ i ∨ ¬ (v = u ∨ G.Adj v u)) →
        (P.cachedRun G quiet s cache offset).2 v u i = cache v u i) := by
  induction P generalizing cache offset with
  | «local» f =>
    refine ⟨rfl, ?_, ?_⟩
    · intro v u i _ hi
      change i < 0 at hi
      omega
    · intro v u i _
      rfl
  | broadcast P =>
    have hmsg : ∀ v u, (v = u ∨ G.Adj v u) → received G P quiet s cache offset v u =
        P.send u (G.neighborFinset u) (s u) := by
      intro v u ha
      by_cases hq : quiet u = true
      · have hh := hready 0 (show 0 < 1 by decide) v u ha hq
        simpa only [received, wire, hq, ite_true, Option.getD_none,
          Nat.add_zero, sent, ite_true] using hh
      · simp only [received, wire, if_neg hq, Option.getD_some]
    refine ⟨?_, ?_, ?_⟩
    · funext v
      change P.update v (G.neighborFinset v) (s v) _ = P.update v (G.neighborFinset v) (s v) _
      congr 1
      funext u
      exact hmsg v u (Or.inr ((SimpleGraph.mem_neighborFinset G v u).mp u.property))
    · intro v u i ha hi
      have he : i = 0 := by change i < 1 at hi; omega
      subst i
      simp only [cachedRun, cachedBroadcast, Nat.add_zero, and_self, ha,
        ite_true, sent, hmsg v u ha]
    · intro v u i hout
      have hn : ¬ (i = offset ∧ (v = u ∨ G.Adj v u)) := by
        rintro ⟨he, ha⟩
        change i < offset ∨ offset+1 ≤ i ∨ ¬ (v = u ∨ G.Adj v u) at hout
        rcases hout with h | h | h
        · omega
        · omega
        · exact h ha
      exact if_neg hn
  | seq P Q ihP ihQ =>
    have hP : ∀ i < P.rounds, ∀ v u, (v = u ∨ G.Adj v u) → quiet u = true →
        cache v u (offset+i) = P.sent G s i u := by
      intro i hi v u ha hq
      have hh := hready i (by change i < P.rounds+Q.rounds; omega) v u ha hq
      simpa only [sent, if_pos hi] using hh
    have hp := ihP (s := s) (cache := cache) (offset := offset) hP
    have hQ : ∀ j < Q.rounds, ∀ v u, (v = u ∨ G.Adj v u) → quiet u = true →
        (P.cachedRun G quiet s cache offset).2 v u (offset+P.rounds+j) =
          Q.sent G (P.cachedRun G quiet s cache offset).1 j u := by
      intro j hj v u ha hq
      rw [hp.2.2 v u (offset+P.rounds+j) (Or.inr (Or.inl (by omega))), hp.1]
      have hh := hready (P.rounds+j) (by change P.rounds+j < P.rounds+Q.rounds; omega)
        v u ha hq
      simpa only [sent, if_neg (show ¬ P.rounds+j < P.rounds by omega),
        Nat.add_sub_cancel_left, Nat.add_assoc] using hh
    have hq := ihQ (s := (P.cachedRun G quiet s cache offset).1)
      (cache := (P.cachedRun G quiet s cache offset).2) (offset := offset+P.rounds) hQ
    refine ⟨?_, ?_, ?_⟩
    · change (Q.cachedRun G quiet (P.cachedRun G quiet s cache offset).1
        (P.cachedRun G quiet s cache offset).2 (offset+P.rounds)).1 = _
      rw [hq.1, hp.1]
      rfl
    · intro v u i ha hi
      change i < P.rounds+Q.rounds at hi
      change (Q.cachedRun G quiet (P.cachedRun G quiet s cache offset).1
        (P.cachedRun G quiet s cache offset).2 (offset+P.rounds)).2 v u (offset+i) = _
      by_cases hPi : i < P.rounds
      · rw [hq.2.2 v u (offset+i) (Or.inl (by omega)), hp.2.1 v u i ha hPi]
        simp only [sent, if_pos hPi]
      · have hj : i-P.rounds < Q.rounds := by omega
        have he : offset+i = offset+P.rounds+(i-P.rounds) := by omega
        rw [he, hq.2.1 v u (i-P.rounds) ha hj, hp.1]
        simp only [sent, if_neg hPi]
    · intro v u i hout
      change i < offset ∨ offset+(P.rounds+Q.rounds) ≤ i ∨ ¬ (v = u ∨ G.Adj v u) at hout
      have hqo : i < offset+P.rounds ∨ offset+P.rounds+Q.rounds ≤ i ∨ ¬ (v = u ∨ G.Adj v u) := by
        rcases hout with h | h | h
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr h)
      have hpo : i < offset ∨ offset+P.rounds ≤ i ∨ ¬ (v = u ∨ G.Adj v u) := by
        rcases hout with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr h)
      exact (hq.2.2 v u i hqo).trans (hp.2.2 v u i hpo)

end Paper.PrefixBroadcast.Program
#print axioms Paper.PrefixBroadcast.Program.cachedRun_correct
