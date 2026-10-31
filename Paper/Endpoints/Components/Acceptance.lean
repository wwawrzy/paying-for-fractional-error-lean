import Paper.Endpoints.Components.MinimumProvenance
import Paper.Preliminaries.LabelNeighborhood
import Paper.Communication.ProgramMemory
import Paper.Communication.EncodedProgram

/-! The acceptance test from the exact-component argument, evaluated on the
logical incidence graph `I`. The public radius and identifier codec precede
the graph. No physical-network simulation or subsequent exact search is claimed. -/
namespace Paper.ComponentAcceptance
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def labelProgram {b : ℕ} (C : BitCode V b) (d : ℕ) : Program V PUnit V :=
  .seq (.local fun _ _ _ => true)
    (.seq (MaskedFlooding.program C d) (.local fun v _ s => s.value.getD v))

def localMismatch (own : V) (received : Finset V) : Bool :=
  decide ((received.filter (fun u => u ≠ own)).Nonempty)

def mismatchProgram {b : ℕ} (C : BitCode V b) : Program V V Bool :=
  .seq (.local fun _ _ l => ((l, true), l))
    (.seq (ProgramMemory.carry (LabelNeighborhood.program C))
      (.local fun _ _ s => localMismatch s.2 s.1))

def unitCode : BitCode Unit 0 where
  encode _ := Fin.elim0
  injective := by intro x y _; cases x; cases y; rfl
  decode _ := some ()
  leftInverse _ := rfl

def flagSeed (flag : Bool) : PayloadFlood.State Unit :=
  (true, if flag then some () else none)

/-- An actual composition of minimum flooding, label exchange and flag flooding.
Its evaluator routes every phase on `I`, not on an ambient physical graph. -/
def program {b : ℕ} (C : BitCode V b) (d : ℕ) : Program V PUnit Bool :=
  .seq (labelProgram C d)
    (.seq (mismatchProgram C)
      (.seq (.local fun _ _ f => flagSeed f)
        (.seq (PayloadFlood.program unitCode (2 * d))
          (.local fun _ _ s => decide (s.2 = none)))))

variable [Fintype V] (I : SimpleGraph V) [DecidableRel I.Adj]

def label (d : ℕ) (v : V) : V :=
  (MaskedFlooding.state I (fun _ => true) d v).value.getD v

theorem label_value (d : ℕ) (v : V) :
    (MaskedFlooding.state I (fun _ => true) d v).value = some (label I d v) := by
  obtain ⟨u, hu, _⟩ := MaskedFlooding.le_initial I (fun _ => true) d (v := v) rfl
  simp [label, hu]

theorem label_source (d : ℕ) (v : V) :
    ∃ p : I.Walk v (label I d v), p.length ≤ d := by
  obtain ⟨p, hp, _⟩ := minimum_source_walk I (fun _ => true) d (label_value I d v)
  exact ⟨p, hp⟩

theorem label_le (d : ℕ) {v w : V} (p : I.Walk v w) (hp : p.length ≤ d) :
    label I d v ≤ w := by
  obtain ⟨u, hu, hle⟩ := MaskedFlooding.le_of_walk I (fun _ => true) p
    (by simp) d hp
  have heq := Option.some.inj (hu.symm.trans (label_value I d v))
  simpa [heq] using hle

def flag {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V) : Bool :=
  (mismatchProgram C).run I (label I d) v

theorem flag_iff {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V) :
    flag I C d v = true ↔ ∃ w, I.Adj v w ∧ label I d w ≠ label I d v := by
  unfold flag mismatchProgram
  change localMismatch (label I d v)
    ((ProgramMemory.carry (LabelNeighborhood.program C)).run I
      (fun u => ((label I d u, true), label I d u)) v).1 = true ↔ _
  rw [ProgramMemory.run]
  change localMismatch (label I d v)
    ((LabelNeighborhood.program C).run I (fun u => (label I d u, true)) v) = true ↔ _
  have hc := LabelNeighborhood.correct I C (label I d) Finset.univ v
  simp only [Finset.mem_univ, decide_true, Finset.inter_univ] at hc
  rw [hc]
  simp only [localMismatch, decide_eq_true_eq, Finset.filter_nonempty_iff,
    Finset.mem_image, mem_closed]
  constructor
  · rintro ⟨u, ⟨w, hw | hw, rfl⟩, hu⟩
    · subst w; exact False.elim (hu rfl)
    · exact ⟨w, hw, hu⟩
  · rintro ⟨w, hw, hne⟩
    exact ⟨label I d w, ⟨w, Or.inr hw, rfl⟩, hne⟩

def accepted {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V) : Prop :=
  ((PayloadFlood.program (V := V) unitCode (2 * d)).run I
    (fun w => flagSeed (flag I C d w)) v).2 = none

theorem labelProgram_run {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (labelProgram C d).run I (fun _ => PUnit.unit) = label I d := by
  funext v
  change ((MaskedFlooding.program C d).run I (fun _ => true) v).value.getD v = _
  rw [MaskedFlooding.run_program]
  rfl

/-- Correctness concerns the actual encoded program on the logical graph. -/
theorem program_correct {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V) :
    (program C d).runEncoded I (fun _ => PUnit.unit) v = true ↔ accepted I C d v := by
  rw [Program.runEncoded_eq_run]
  change decide (((PayloadFlood.program (V := V) unitCode (2 * d)).run I
    (fun w => flagSeed ((mismatchProgram C).run I
      ((labelProgram C d).run I (fun _ => PUnit.unit)) w)) v).2 = none) = true ↔ _
  rw [labelProgram_run]
  simp only [decide_eq_true_eq]
  rfl

omit [Fintype V] in
theorem program_rounds {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (program C d).rounds = 3 * d + 1 := by
  simp only [program, labelProgram, mismatchProgram, Program.rounds,
    ProgramMemory.rounds, LabelNeighborhood.rounds, MaskedFlooding.program,
    MaskedFlooding.start, MaskedFlooding.step, PayloadFlood.program,
    PayloadFlood.step, Program.iterate_rounds]
  omega

omit [Fintype V] in
theorem program_bits {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (program C d).maxBits ≤ b + 1 := by
  have hm := Program.iterate_maxBits (MaskedFlooding.step C) d
  have hf := Program.iterate_maxBits (PayloadFlood.step (V := V) unitCode) (2 * d)
  simp only [MaskedFlooding.step, PayloadFlood.step, Program.maxBits] at hm hf
  simp only [program, labelProgram, mismatchProgram, Program.maxBits,
    ProgramMemory.maxBits, LabelNeighborhood.maxBits, MaskedFlooding.program,
    MaskedFlooding.start, MaskedFlooding.step, PayloadFlood.step,
    Program.maxBits, PayloadFlood.program]
  omega

/-- Exact flag visibility: a vertex rejects precisely when some flagged vertex
has a logical walk of length at most `2*d` from it. -/
theorem accepted_iff {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V) :
    accepted I C d v ↔
      ∀ (w : V) (p : I.Walk v w), p.length ≤ 2 * d → flag I C d w = false := by
  unfold accepted
  rw [PayloadFlood.run_program]
  let S := fun w => flagSeed (flag I C d w)
  have ha : ∀ w, (S w).1 = true := fun _ => rfl
  have hi : ∀ w, (S w).2 = none ∨ (S w).2 = some () := by
    intro w; dsimp [S, flagSeed]; cases flag I C d w <;> simp
  constructor
  · intro hv w p hp
    cases hf : flag I C d w with
    | false => rfl
    | true =>
      have hs : (S w).2 = some () := by simp [S, flagSeed, hf]
      have h := PayloadFlood.of_walk I S () hi p (by simp [ha]) hs (2 * d) hp
      rw [hv] at h
      contradiction
  · intro hn
    rcases PayloadFlood.uniform I S () hi (2 * d) v with h | h
    · exact h
    · obtain ⟨w, p, hp, hs⟩ := payload_source_walk I S ha (2 * d) h
      have hf := hn w p hp
      simp [S, flagSeed, hf] at hs

/-- Two receivers with the same label are at most `2*d` logical edges apart,
because the actual packet provenance supplies the common carrier. -/
theorem same_label_walk (d : ℕ) {v w : V} (h : label I d v = label I d w) :
    ∃ p : I.Walk v w, p.length ≤ 2 * d := by
  obtain ⟨p, hp⟩ := label_source I d v
  obtain ⟨q, hq⟩ : ∃ q : I.Walk w (label I d v), q.length ≤ d := by
    exact Eq.mpr (congrArg (fun z => ∃ q : I.Walk w z, q.length ≤ d) h)
      (label_source I d w)
  refine ⟨p.append q.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-- Acceptance forces the same label throughout the receiver's component. -/
theorem accepted_label {b : ℕ} (C : BitCode V b) (d : ℕ) {v w : V}
    (hv : accepted I C d v) (p : I.Walk v w) : label I d w = label I d v := by
  have extend : ∀ u z, label I d u = label I d v → I.Adj u z →
      label I d z = label I d v := by
    intro u z hu huz
    obtain ⟨q, hq⟩ := same_label_walk I d hu.symm
    have hf := (accepted_iff I C d v).mp hv u q hq
    by_contra hz
    have ht := (flag_iff I C d u).mpr ⟨z, huz, by simpa [hu] using hz⟩
    rw [hf] at ht
    contradiction
  have walk_extend : ∀ {u z : V} (q : I.Walk u z),
      label I d u = label I d v → label I d z = label I d v := by
    intro u z q
    induction q with
    | nil => exact id
    | cons h q ih => intro hu; exact ih (extend _ _ hu h)
  exact walk_extend p rfl

/-- Acceptance is uniform on each logical connected component. -/
theorem accepted_uniform {b : ℕ} (C : BitCode V b) (d : ℕ) {v w : V}
    (p : I.Walk v w) : accepted I C d v ↔ accepted I C d w := by
  have forward : ∀ {u z : V}, I.Walk u z → accepted I C d u → accepted I C d z := by
    intro u z q hu
    apply (accepted_iff I C d z).mpr
    intro s r _
    cases hf : flag I C d s with
    | false => rfl
    | true =>
      obtain ⟨t, hst, hne⟩ := (flag_iff I C d s).mp hf
      have hs := accepted_label I C d hu (q.append r)
      have ht := accepted_label I C d hu (q.append (r.append (.cons hst .nil)))
      exact False.elim (hne (ht.trans hs.symm))
  exact ⟨forward p, forward p.reverse⟩

/-- Every two vertices of an accepted component have a walk of length at most
`2*d`. This is the diameter conclusion, without a separate distance convention. -/
theorem accepted_diameter {b : ℕ} (C : BitCode V b) (d : ℕ) {v : V}
    (hv : accepted I C d v) {w u : V} (p : I.Walk v w) (q : I.Walk v u) :
    ∃ r : I.Walk w u, r.length ≤ 2 * d := by
  exact same_label_walk I d ((accepted_label I C d hv p).trans
    (accepted_label I C d hv q).symm)

/-- A component of diameter at most `d` is accepted. The hypothesis only bounds
walk lengths for vertices reachable from `v`; no global diameter input is used. -/
theorem small_component_accepted {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V)
    (hd : ∀ w u, Nonempty (I.Walk v w) → Nonempty (I.Walk v u) →
      ∃ p : I.Walk w u, p.length ≤ d) : accepted I C d v := by
  have heq : ∀ (w : V) (p : I.Walk v w), label I d w = label I d v := by
    intro w p
    obtain ⟨rv, _⟩ := label_source I d v
    obtain ⟨rw, _⟩ := label_source I d w
    obtain ⟨q, hq⟩ := hd w (label I d v) ⟨p⟩ ⟨rv⟩
    obtain ⟨r, hr⟩ := hd v (label I d w) ⟨.nil⟩ ⟨p.append rw⟩
    exact le_antisymm (label_le I d q hq) (label_le I d r hr)
  apply (accepted_iff I C d v).mpr
  intro w p _
  cases hf : flag I C d w with
  | false => rfl
  | true =>
    obtain ⟨u, hwu, hne⟩ := (flag_iff I C d w).mp hf
    have hw := heq w p
    have hu := heq u (p.append (.cons hwu .nil))
    exact False.elim (hne (hu.trans hw.symm))

/-- Component-uniform decisions of the encoded executable composition. -/
theorem encoded_uniform {b : ℕ} (C : BitCode V b) (d : ℕ) {v w : V}
    (p : I.Walk v w) :
    (program C d).runEncoded I (fun _ => PUnit.unit) v =
      (program C d).runEncoded I (fun _ => PUnit.unit) w := by
  apply Bool.eq_iff_iff.mpr
  rw [program_correct, program_correct]
  exact accepted_uniform I C d p

theorem encoded_diameter {b : ℕ} (C : BitCode V b) (d : ℕ) {v : V}
    (hv : (program C d).runEncoded I (fun _ => PUnit.unit) v = true)
    {w u : V} (p : I.Walk v w) (q : I.Walk v u) :
    ∃ r : I.Walk w u, r.length ≤ 2 * d :=
  accepted_diameter I C d ((program_correct I C d v).mp hv) p q

theorem encoded_small_component {b : ℕ} (C : BitCode V b) (d : ℕ) (v : V)
    (hd : ∀ w u, Nonempty (I.Walk v w) → Nonempty (I.Walk v u) →
      ∃ p : I.Walk w u, p.length ≤ d) :
    (program C d).runEncoded I (fun _ => PUnit.unit) v = true :=
  (program_correct I C d v).mpr (small_component_accepted I C d v hd)

end Paper.ComponentAcceptance

#print axioms Paper.ComponentAcceptance.accepted_iff
#print axioms Paper.ComponentAcceptance.program_correct
#print axioms Paper.ComponentAcceptance.program_rounds
#print axioms Paper.ComponentAcceptance.program_bits
#print axioms Paper.ComponentAcceptance.accepted_uniform
#print axioms Paper.ComponentAcceptance.accepted_diameter
#print axioms Paper.ComponentAcceptance.small_component_accepted
#print axioms Paper.ComponentAcceptance.encoded_uniform
#print axioms Paper.ComponentAcceptance.encoded_diameter
#print axioms Paper.ComponentAcceptance.encoded_small_component
