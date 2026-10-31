import Paper.Preliminaries.MaskedDistance
import Paper.Preliminaries.MaskedMinimum

/-! One real bounded-counter broadcast selects a minimum-ID neighbor of
strictly smaller rank. Selection uses only own state and received ranks. -/
namespace Paper.ParentElection
open BroadcastModel ClippedRank
variable {V : Type} [LinearOrder V]

structure Node (V : Type) (D : ℕ) where
  active : Bool
  rank : Rank D
  parent : Option V

def candidates (D : ℕ) (N : Finset V) (r : Rank D) (incoming : N → Rank D) : Finset V :=
  (N.attach.filter (fun w => incoming w < r)).image Subtype.val

def round (D : ℕ) : Round V (MaskedDistance.State D) (Node V D) (Rank D) where
  send _ _ s := s.rank
  update _ N s incoming := ⟨s.active, s.rank,
    if s.active then MaskedMinimum.minimum (candidates D N s.rank incoming) else none⟩

def program (D : ℕ) : Program V (MaskedDistance.State D) (Node V D) :=
  .broadcast (D + 2) (SmallNumberCode.code (D + 2)) (round D)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem parent_mem (D : ℕ) (s : V → MaskedDistance.State D) {v u : V}
    (h : ((program D).run G s v).parent = some u) :
    (s v).active = true ∧ G.Adj v u ∧ (s u).rank.val < (s v).rank.val := by
  change (if (s v).active then MaskedMinimum.minimum
    (candidates D (G.neighborFinset v) (s v).rank (fun w => (s w).rank)) else none) = some u at h
  cases ha : (s v).active with
  | false => simp [ha] at h
  | true =>
    simp only [ha, ↓reduceIte] at h
    have hm := MaskedMinimum.minimum_mem h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
    have hlow := (Finset.mem_filter.mp hw).2
    subst u
    exact ⟨rfl, (G.mem_neighborFinset v w).mp w.property, hlow⟩

theorem exists_parent (D : ℕ) (s : V → MaskedDistance.State D) {v : V}
    (ha : (s v).active = true)
    (hex : ∃ u, G.Adj v u ∧ (s u).rank.val < (s v).rank.val) :
    ∃ u, ((program D).run G s v).parent = some u := by
  obtain ⟨u, hu, hlow⟩ := hex
  let w : G.neighborFinset v := ⟨u, (G.mem_neighborFinset v u).mpr hu⟩
  have hm : u ∈ candidates D (G.neighborFinset v) (s v).rank (fun z => (s z).rank) :=
    Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hlow⟩, rfl⟩
  obtain ⟨m, hmin, _⟩ := MaskedMinimum.minimum_le hm
  exact ⟨m, by simpa [program, Program.run, eval, round, ha] using hmin⟩

theorem inactive (D : ℕ) (s : V → MaskedDistance.State D) {v : V}
    (ha : (s v).active = false) : ((program D).run G s v).parent = none := by
  simp [program, Program.run, eval, round, ha]

theorem rank_zero (D : ℕ) (s : V → MaskedDistance.State D) {v : V}
    (hr : (s v).rank.val = 0) : ((program D).run G s v).parent = none := by
  cases hp : ((program D).run G s v).parent with
  | none => rfl
  | some u =>
    have hh := (parent_mem G D s hp).2.2
    omega

theorem metadata (D : ℕ) (s : V → MaskedDistance.State D) (v : V) :
    ((program D).run G s v).active = (s v).active ∧
    ((program D).run G s v).rank = (s v).rank := ⟨rfl, rfl⟩
end Paper.ParentElection
