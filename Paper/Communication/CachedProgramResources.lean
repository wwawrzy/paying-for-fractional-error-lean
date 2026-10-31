import Paper.Communication.CachedProgram

/-! Per-round transmissions of a program executed with receiver caches.
Silence contributes zero bits and introduces no encoding marker. The quiet
flags are fixed for this finite program, such as one six-round phase. -/
namespace Paper.PrefixBroadcast.Program
open BroadcastModel

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual optional transmission in a public slot of a cached execution. -/
def cachedSent {In Out : Type} (quiet : V → Bool) :
    Program V In Out → (V → In) → Cache V → ℕ → ℕ → V → Option (List Bool)
  | .local _, _, _, _, _, _ => none
  | .broadcast P, s, _, _, i, v => if i = 0 then wire G P quiet s v else none
  | .seq P Q, s, cache, offset, i, v =>
      if i < P.rounds then cachedSent quiet P s cache offset i v else
        let first := P.cachedRun G quiet s cache offset
        cachedSent quiet Q first.1 first.2 (offset + P.rounds) (i - P.rounds) v

theorem cachedSent_quiet {In Out : Type} (quiet : V → Bool) (P : Program V In Out)
    (s : V → In) (cache : Cache V) (offset i : ℕ) (v : V) (hq : quiet v = true) :
    P.cachedSent G quiet s cache offset i v = none := by
  induction P generalizing cache offset i with
  | «local» f => rfl
  | broadcast P => simp [cachedSent, wire, hq]
  | seq P Q ihP ihQ =>
      simp only [cachedSent]
      split_ifs
      · exact ihP _ _ _ _
      · exact ihQ _ _ _ _

/-- Ready caches preserve each active sender's exact ordinary bit string. -/
theorem cachedSent_correct {In Out : Type} (quiet : V → Bool) (P : Program V In Out)
    (s : V → In) (cache : Cache V) (offset i : ℕ) (v : V) (hi : i < P.rounds)
    (hready : ∀ j < P.rounds, ∀ r u, (r = u ∨ G.Adj r u) → quiet u = true →
      cache r u (offset+j) = P.sent G s j u) :
    P.cachedSent G quiet s cache offset i v =
      if quiet v then none else some (P.sent G s i v) := by
  induction P generalizing cache offset i with
  | «local» f => change i < 0 at hi; omega
  | broadcast P =>
      have he : i = 0 := by change i < 1 at hi; omega
      subst i
      simp only [cachedSent, sent, wire, ite_true]
  | seq P Q ihP ihQ =>
      have hP : ∀ j < P.rounds, ∀ r u, (r = u ∨ G.Adj r u) → quiet u = true →
          cache r u (offset+j) = P.sent G s j u := by
        intro j hj r u ha hq
        have hh := hready j (by change j < P.rounds+Q.rounds; omega) r u ha hq
        simpa only [sent, if_pos hj] using hh
      have hp := cachedRun_correct G quiet P s cache offset hP
      by_cases hPi : i < P.rounds
      · simpa only [cachedSent, sent, if_pos hPi] using ihP s cache offset i hPi hP
      · have hj : i - P.rounds < Q.rounds := by
          change i < P.rounds + Q.rounds at hi
          omega
        have hQ : ∀ j < Q.rounds, ∀ r u, (r = u ∨ G.Adj r u) → quiet u = true →
            (P.cachedRun G quiet s cache offset).2 r u (offset+P.rounds+j) =
              Q.sent G (P.cachedRun G quiet s cache offset).1 j u := by
          intro j hjs r u ha hq
          rw [hp.2.2 r u (offset+P.rounds+j) (Or.inr (Or.inl (by omega))), hp.1]
          have hh := hready (P.rounds+j)
            (by change P.rounds+j < P.rounds+Q.rounds; omega) r u ha hq
          simpa only [sent, if_neg (show ¬ P.rounds+j < P.rounds by omega),
            Nat.add_sub_cancel_left, Nat.add_assoc] using hh
        have hh := ihQ (s := (P.cachedRun G quiet s cache offset).1)
          (P.cachedRun G quiet s cache offset).2 (offset+P.rounds) (i-P.rounds) hj hQ
        simpa only [cachedSent, sent, if_neg hPi, hp.1] using hh

/-- Every ordinary message fits the program's executed-state width bound. -/
theorem sent_length_le {In Out : Type} (P : Program V In Out) :
    ∀ (s : V → In) (i : ℕ) (v : V), i < P.rounds →
      (P.sent G s i v).length ≤ P.maxBits G s := by
  induction P with
  | «local» f => intro s i v hi; change i < 0 at hi; omega
  | broadcast P =>
      intro s i v hi
      have he : i = 0 := by change i < 1 at hi; omega
      subst i
      simpa only [sent, ite_true, maxBits] using
        (Finset.le_sup (s := Finset.univ)
          (f := fun u => (P.send u (G.neighborFinset u) (s u)).length) (Finset.mem_univ v))
  | seq P Q ihP ihQ =>
      intro s i v hi
      by_cases hPi : i < P.rounds
      · simpa only [sent, if_pos hPi, maxBits] using
          (ihP s i v hPi).trans (Nat.le_max_left _ (Q.maxBits G (P.run G s)))
      · have hj : i - P.rounds < Q.rounds := by
          change i < P.rounds + Q.rounds at hi
          omega
        simpa only [sent, if_neg hPi, maxBits] using
          (ihQ (P.run G s) (i-P.rounds) v hj).trans (Nat.le_max_right (P.maxBits G s) _)

/-- Absence costs zero bits. A present finite string costs its length. -/
def sentBits (msg : Option (List Bool)) : ℕ :=
  match msg with
  | none => 0
  | some bits => bits.length

/-- Cached replay introduces no additional communication bits. -/
theorem cachedSent_bits_le {In Out : Type} (quiet : V → Bool) (P : Program V In Out)
    (s : V → In) (cache : Cache V) (offset i : ℕ) (v : V) (hi : i < P.rounds)
    (hready : ∀ j < P.rounds, ∀ r u, (r = u ∨ G.Adj r u) → quiet u = true →
      cache r u (offset+j) = P.sent G s j u) :
    sentBits (P.cachedSent G quiet s cache offset i v) ≤ P.maxBits G s := by
  rw [cachedSent_correct G quiet P s cache offset i v hi hready]
  split_ifs
  · exact Nat.zero_le _
  · exact sent_length_le G P s i v hi

end Paper.PrefixBroadcast.Program

#print axioms Paper.PrefixBroadcast.Program.cachedSent_quiet
#print axioms Paper.PrefixBroadcast.Program.cachedSent_correct
#print axioms Paper.PrefixBroadcast.Program.sent_length_le
#print axioms Paper.PrefixBroadcast.Program.cachedSent_bits_le
