import Paper.Communication.EncodedProgram
import Paper.Preliminaries.ListPacket

/-! One actual broadcast of the current b-bit color, followed by a local
set of first-difference positions paired with the sender's own bits.
The set separates adjacent proper input colors and contains at most one
pair per neighbor. Canonical padded words bound its finite palette.
No binary re-encoding of that palette or log-star iteration is claimed. -/
namespace Paper.DeterministicColorReductionStep
open BroadcastModel
open scoped BigOperators

abbrev Bits (b : ℕ) := Fin b → Bool
abbrev Pair (b : ℕ) := Fin b × Bool

/-- Total local rule: equal inputs yield no witness. Fin.find is the
computable least-index search over the finite bit positions. -/
def witness {b : ℕ} (s t : Bits b) : Finset (Pair b) :=
  if h : ∃ i, s i ≠ t i then
    {(Fin.find (fun i => s i ≠ t i) h, s (Fin.find (fun i => s i ≠ t i) h))}
  else ∅

theorem diff_exists {b : ℕ} (s t : Bits b) (hne : s ≠ t) : ∃ i, s i ≠ t i := by
  by_contra hn
  apply hne
  funext i
  by_contra hi
  exact hn ⟨i, hi⟩

theorem witness_nonempty {b : ℕ} (s t : Bits b) (hne : s ≠ t) : (witness s t).Nonempty := by
  have hh := diff_exists s t hne
  rw [witness, dif_pos hh]
  exact Finset.singleton_nonempty _

/-- The chosen position is the first difference, and the stored bit is s's. -/
theorem witness_spec {b : ℕ} (s t : Bits b) (p : Pair b) (hp : p ∈ witness s t) :
    p.2 = s p.1 ∧ s p.1 ≠ t p.1 ∧ ∀ j < p.1, s j = t j := by
  by_cases hh : ∃ i, s i ≠ t i
  · have he : p = (Fin.find (fun i => s i ≠ t i) hh, s (Fin.find (fun i => s i ≠ t i) hh)) := by
      simpa only [witness, dif_pos hh, Finset.mem_singleton] using hp
    subst p
    refine ⟨rfl, Fin.find_spec hh, ?_⟩
    intro j hj
    by_contra hn
    exact Fin.find_min hh hj hn
  · have he : witness s t = ∅ := dif_neg hh
    exact False.elim (Finset.notMem_empty p (he ▸ hp))

theorem witness_card {b : ℕ} (s t : Bits b) : (witness s t).card ≤ 1 := by
  unfold witness
  split_ifs <;> simp

/-- Ordinals for sorting pairs; this is not a binary message codec. -/
def pairCode (b : ℕ) : Pair b ≃ Fin (2 * b) :=
  ((Equiv.prodCongr (Equiv.refl (Fin b)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm b 2))

/-- Canonical sorted word of length at most Δ, padded by none. -/
def padded (b Δ : ℕ) (S : Finset (Pair b)) : Fin Δ → Option (Fin (2 * b)) :=
  ListPacket.pack Δ ((S.image (pairCode b)).sort (· ≤ ·))

theorem padded_injective (b Δ : ℕ) :
    Function.Injective (fun S : {S : Finset (Pair b) // S.card ≤ Δ} => padded b Δ S.val) := by
  intro S T he
  have hS : ((S.val.image (pairCode b)).sort (· ≤ ·)).length ≤ Δ := by
    rw [Finset.length_sort, Finset.card_image_of_injective _ (pairCode b).injective]
    exact S.property
  have hT : ((T.val.image (pairCode b)).sort (· ≤ ·)).length ≤ Δ := by
    rw [Finset.length_sort, Finset.card_image_of_injective _ (pairCode b).injective]
    exact T.property
  have hs := ListPacket.unpack_pack Δ ((S.val.image (pairCode b)).sort (· ≤ ·)) hS
  have ht := ListPacket.unpack_pack Δ ((T.val.image (pairCode b)).sort (· ≤ ·)) hT
  have hl : (S.val.image (pairCode b)).sort (· ≤ ·) = (T.val.image (pairCode b)).sort (· ≤ ·) :=
    hs.symm.trans ((congrArg (fun f : Fin Δ → Option (Fin (2 * b)) => ListPacket.unpack f) he).trans ht)
  have himage : S.val.image (pairCode b) = T.val.image (pairCode b) := by
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset hl
  exact Subtype.ext (Finset.image_injective (pairCode b).injective himage)

theorem palette_card (b Δ : ℕ) :
    Fintype.card {S : Finset (Pair b) // S.card ≤ Δ} ≤ (2 * b + 1) ^ Δ := by
  have hh := Fintype.card_le_of_injective
    (fun S : {S : Finset (Pair b) // S.card ≤ Δ} => padded b Δ S.val) (padded_injective b Δ)
  simpa only [Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin] using hh

variable {V : Type} [DecidableEq V]

/-- Mathematical specification using only the current local neighbor colors. -/
def output {b : ℕ} (N : V → Finset V) (c : V → Bits b) (v : V) : Finset (Pair b) :=
  (N v).biUnion (fun w => witness (c v) (c w))

theorem own_bit {b : ℕ} (N : V → Finset V) (c : V → Bits b) (v : V) (p : Pair b)
    (hp : p ∈ output N c v) : p.2 = c v p.1 := by
  obtain ⟨w, _, hp⟩ := Finset.mem_biUnion.mp hp
  exact (witness_spec (c v) (c w) p hp).1

/-- The witness against v is absent from v's entire result, regardless of
which neighbors v itself uses to select its own first differences. -/
theorem selected_absent {b : ℕ} (N : V → Finset V) (c : V → Bits b) (u v : V) (p : Pair b)
    (hp : p ∈ witness (c u) (c v)) : p ∉ output N c v := by
  intro hv
  have hh := witness_spec (c u) (c v) p hp
  exact hh.2.1 (hh.1.symm.trans (own_bit N c v p hv))

theorem separates {b : ℕ} (N : V → Finset V) (c : V → Bits b) (u v : V)
    (hneighbor : v ∈ N u) (hne : c u ≠ c v) : output N c u ≠ output N c v := by
  obtain ⟨p, hp⟩ := witness_nonempty (c u) (c v) hne
  have hu : p ∈ output N c u := Finset.mem_biUnion.mpr ⟨v, hneighbor, hp⟩
  intro he
  exact selected_absent N c u v p hp (he ▸ hu)

theorem local_size {b : ℕ} (N : V → Finset V) (c : V → Bits b) (v : V) :
    (output N c v).card ≤ (N v).card := by
  calc
    _ ≤ ∑ w ∈ N v, (witness (c v) (c w)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ N v, 1 := Finset.sum_le_sum (fun w _ => witness_card (c v) (c w))
    _ = _ := by simp

/-- The message is exactly the already supplied b bits, with identity decoding. -/
def bitsCode (b : ℕ) : BitCode (Bits b) b where
  encode := fun s => s
  injective := fun _ _ h => h
  decode := fun s => some s
  leftInverse := fun _ => rfl

def round (b : ℕ) : Round V (Bits b) (Finset (Pair b)) (Bits b) where
  send := fun _ _ s => s
  update := fun _ N s incoming => N.attach.biUnion (fun w => witness s (incoming w))

def program (b : ℕ) : Program V (Bits b) (Finset (Pair b)) := .broadcast b (bitsCode b) (round b)

theorem rounds (b : ℕ) : (program (V := V) b).rounds = 1 := rfl

theorem maxBits (b : ℕ) : (program (V := V) b).maxBits = b := rfl

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (b : ℕ) (c : V → Bits b) (v : V) :
    (program b).runEncoded G c v = output (fun u => G.neighborFinset u) c v := by
  rw [Program.runEncoded_eq_run]
  change (G.neighborFinset v).attach.biUnion (fun w => witness (c v) (c w)) =
    (G.neighborFinset v).biUnion (fun w => witness (c v) (c w))
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨w, hp⟩
    exact ⟨w.val, w.property, hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨⟨w, hw⟩, hp⟩

theorem proper (b : ℕ) (c : V → Bits b)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) (u v : V) (ha : G.Adj u v) :
    output (fun w => G.neighborFinset w) c u ≠ output (fun w => G.neighborFinset w) c v :=
  separates _ c u v ((G.mem_neighborFinset u v).mpr ha) (hc u v ha)

theorem encoded_proper (b : ℕ) (c : V → Bits b)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) (u v : V) (ha : G.Adj u v) :
    (program b).runEncoded G c u ≠ (program b).runEncoded G c v := by
  simpa only [correct] using proper G b c hc u v ha

theorem encoded_size (b Δ : ℕ) (c : V → Bits b) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    ((program b).runEncoded G c v).card ≤ Δ := by
  rw [correct]
  have hh := local_size (fun u => G.neighborFinset u) c v
  exact hh.trans (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v)

/-- Public injective identifier bits supply the first proper input coloring. -/
theorem identifiers_proper {b : ℕ} (C : BitCode V b) (u v : V) (ha : G.Adj u v) :
    C.encode u ≠ C.encode v := fun he => G.ne_of_adj ha (C.injective he)

end Graph
end Paper.DeterministicColorReductionStep

#print axioms Paper.DeterministicColorReductionStep.witness_spec
#print axioms Paper.DeterministicColorReductionStep.palette_card
#print axioms Paper.DeterministicColorReductionStep.correct
#print axioms Paper.DeterministicColorReductionStep.encoded_proper
#print axioms Paper.DeterministicColorReductionStep.encoded_size
#print axioms Paper.DeterministicColorReductionStep.rounds
#print axioms Paper.DeterministicColorReductionStep.maxBits
