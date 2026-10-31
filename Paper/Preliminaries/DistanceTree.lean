import Paper.Preliminaries.DistanceWitness
import Paper.Preliminaries.ParentElection
import Paper.Preliminaries.ParentForest

/-! Actual construction of an active physical communication tree from local
active/source bits. Distances and parents are computed by broadcast rounds. -/
namespace Paper.DistanceTree
open BroadcastModel ClippedRank
variable {V : Type} [LinearOrder V]

def program (D : ℕ) : Program V (Bool × Bool) (ParentElection.Node V D) :=
  .seq (MaskedDistance.program D D) (ParentElection.program D)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D : ℕ) (A B : V → Bool)

def output : V → ParentElection.Node V D := (program D).run G (fun v => (A v, B v))

theorem output_eq : output G D A B =
    (ParentElection.program D).run G (MaskedDistance.state G D A B D) := by
  change (ParentElection.program D).run G
    ((MaskedDistance.program D D).run G (fun v => (A v, B v))) = _
  rw [MaskedDistance.run_program]

theorem metadata (v : V) : (output G D A B v).active = A v ∧
    (output G D A B v).rank = (MaskedDistance.state G D A B D v).rank := by
  rw [output_eq]
  exact ⟨MaskedDistance.active G D A B D v, rfl⟩

theorem parent_mem {v u : V} (h : (output G D A B v).parent = some u) :
    A v = true ∧ G.Adj v u ∧
      (output G D A B u).rank.val < (output G D A B v).rank.val := by
  rw [output_eq] at h
  obtain ⟨ha, he, hl⟩ := ParentElection.parent_mem G D _ h
  exact ⟨(MaskedDistance.active G D A B D v).symm.trans ha, he,
    by simpa only [(metadata G D A B u).2, (metadata G D A B v).2] using hl⟩

theorem rank_bound (root : V) (hbr : B root = true)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true)
    {v : V} (ha : A v = true) : (output G D A B v).rank.val ≤ D := by
  obtain ⟨p, hp, hpa⟩ := hdiam v ha
  rw [(metadata G D A B v).2]
  exact (MaskedDistance.rank_le_walk G D A B p hpa hbr D hp).trans hp

theorem inactive {v : V} (ha : A v = false) : (output G D A B v).parent = none := by
  rw [output_eq]
  exact ParentElection.inactive G D _ ((MaskedDistance.active G D A B D v).trans ha)

theorem root_parent (root : V) (har : A root = true) (hbr : B root = true) :
    (output G D A B root).parent = none := by
  rw [output_eq]
  exact ParentElection.rank_zero G D _ (MaskedDistance.source_zero G D A B D har hbr)

theorem exists_parent (root : V) (hbr : B root = true)
    (hb : ∀ u, B u = true → u = root)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true)
    {v : V} (ha : A v = true) (hv : v ≠ root) :
    ∃ u, (output G D A B v).parent = some u := by
  have hf : (MaskedDistance.state G D A B D v).rank.val < D + 1 := by
    have hh := rank_bound G D A B root hbr hdiam ha
    rw [(metadata G D A B v).2] at hh
    omega
  obtain ⟨w, he, _, hl⟩ := DistanceWitness.lower_neighbor G D A B root hbr hb hv hf
  rw [output_eq]
  exact ParentElection.exists_parent G D _
    ((MaskedDistance.active G D A B D v).trans ha) ⟨w, he, hl⟩

theorem parent_active (root : V) (hbr : B root = true)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true)
    {v u : V} (h : (output G D A B v).parent = some u) : A u = true := by
  obtain ⟨ha, _, hl⟩ := parent_mem G D A B h
  have hv := rank_bound G D A B root hbr hdiam ha
  cases hu : A u with
  | true => rfl
  | false =>
    rw [(metadata G D A B u).2, MaskedDistance.inactive G D A B D hu] at hl
    change D + 1 < _ at hl
    omega

theorem forest :
    (ParentForest.graph (fun v => (output G D A B v).parent)
      (fun v => (output G D A B v).rank.val)
      (fun _ _ h => (parent_mem G D A B h).2.2)).IsAcyclic :=
  ParentForest.isAcyclic _ _ _

theorem rounds : (program (V := V) D).rounds = D + 1 := by
  simp only [program, Program.rounds, ParentElection.program, MaskedDistance.rounds]

theorem maxBits : (program (V := V) D).maxBits ≤ D + 2 :=
  max_le (MaskedDistance.maxBits D D) (le_refl _)
end Paper.DistanceTree
