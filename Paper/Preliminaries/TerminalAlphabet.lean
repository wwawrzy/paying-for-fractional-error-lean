import Paper.Preliminaries.MaskRepresentativesCorrect
import Paper.Solver.LocalSearch.TabularSearch

/-! Convert the actual aligned mask-query answers into the explicit local
alphabet used by finite-word enumeration. No graph data are read here. -/
namespace Paper.TerminalAlphabet
open BroadcastModel TabularSearch
variable {V : Type} [LinearOrder V]

def ofTag {B T : ℕ} (z : Fin T → Bool) (t : CostTag.Tag V B) : Entry V T :=
  ⟨(ofLex t).2, z, (ofLex t).1.val⟩

def alphabet {B T : ℕ} : List (Fin T → Bool) → List (Option (CostTag.Tag V B)) → List (Entry V T)
  | z :: zs, some t :: ts => ofTag z t :: alphabet zs ts
  | _ :: zs, none :: ts => alphabet zs ts
  | _, _ => []

theorem alphabet_map {B T : ℕ} (zs : List (Fin T → Bool)) (ans : (Fin T → Bool) → Option (CostTag.Tag V B)) :
    alphabet zs (zs.map ans) = zs.filterMap (fun z => (ans z).map (ofTag z)) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases hz : ans z <;> simp [alphabet, hz, ih]

theorem mem_alphabet_map {B T : ℕ} (zs : List (Fin T → Bool))
    (ans : (Fin T → Bool) → Option (CostTag.Tag V B)) (e : Entry V T) :
    e ∈ alphabet zs (zs.map ans) ↔
      ∃ z ∈ zs, ∃ t, ans z = some t ∧ ofTag z t = e := by
  rw [alphabet_map, List.mem_filterMap]
  constructor
  · rintro ⟨z, hz, he⟩
    cases ht : ans z with
    | none => simp [ht] at he
    | some t =>
      simp only [ht, Option.map_some, Option.some.injEq] at he
      exact ⟨z, hz, t, ht, he⟩
  · rintro ⟨z, hz, t, ht, he⟩
    refine ⟨z, hz, ?_⟩
    simp only [ht, Option.map_some, he]

theorem length_map_le {B T : ℕ} (zs : List (Fin T → Bool))
    (ans : (Fin T → Bool) → Option (CostTag.Tag V B)) :
    (alphabet zs (zs.map ans)).length ≤ zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases hz : ans z <;> simp only [List.map_cons, hz, alphabet,
      List.length_cons] <;> omega

def finish (B T : ℕ) : Program V (MaskRepresentatives.State V B)
    (MaskQuery.Input V B × List (Entry V T)) :=
  .local fun _ _ s => (s.1, alphabet (MaskRepresentatives.patterns T) s.2)

def program {b : ℕ} (C : BitCode V b) (D B T : ℕ) :=
  Program.seq (MaskRepresentatives.all C D B T) (finish B T)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D B T : ℕ) (s : V → MaskQuery.Input V B) :
    (program C D B T).run G s = fun v =>
      (((MaskRepresentatives.all C D B T).run G s v).1,
        alphabet (MaskRepresentatives.patterns T) ((MaskRepresentatives.all C D B T).run G s v).2) := rfl

theorem physical_alphabet {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (B T : ℕ) (l : List V) (cost : V → Fin (B + 1))
    (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, (s v).demands = l) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((program C (4 * k) B T).run G s v).2 =
        alphabet (MaskRepresentatives.patterns T) ((MaskRepresentatives.patterns T).map
          (MaskRepresentativesCorrect.answer G D R L Q I B T l cost)) := by
  intro v hv
  exact congrArg (alphabet (MaskRepresentatives.patterns T))
    (MaskRepresentativesCorrect.all_correct G D R L Q I hI k hsize B T l cost C s ha hc hl v hv)

theorem rounds {b : ℕ} (C : BitCode V b) (D B T : ℕ) :
    (program C D B T).rounds = 2 ^ T * (4 * D + 1) := by
  simp only [program, finish, Program.rounds, MaskRepresentativesCorrect.all_rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (D B T : ℕ) :
    (program C D B T).maxBits ≤ max (2 * b + B + 3) (D + 2) :=
  max_le (MaskRepresentativesCorrect.all_maxBits C D B T) (Nat.zero_le _)
end Paper.TerminalAlphabet
