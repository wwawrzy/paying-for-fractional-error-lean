import Paper.Preliminaries.WeightedHaven
import Paper.Preliminaries.CoveyBound

/-! The finite configuration and decreasing potential used in the separator
argument. A minimum is constructed from an actual empty configuration. -/
namespace Paper.HavenConfig
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def vertices (C : Finset (Finset V)) : Finset V := C.biUnion id

structure Good (h r : ℕ) (H : Haven G (h * r)) (C : Finset (Finset V)) (X : Finset V) : Prop where
  covey : IsCovey G C
  card : C.card ≤ h
  cover : X ⊆ vertices C
  overlap : ∀ S ∈ C, (X ∩ S).card ≤ r
  separate : ∀ S ∈ C, Disjoint S (H.region X)

theorem Good.sizeX {h r : ℕ} {H : Haven G (h * r)} {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) : X.card ≤ h * r := by
  classical
  have hs : X ⊆ C.biUnion (fun S => X ∩ S) := by
    intro v hv
    obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp (good.cover hv)
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_inter.mpr ⟨hv, hvS⟩⟩
  calc
    _ ≤ (C.biUnion (fun S => X ∩ S)).card := Finset.card_le_card hs
    _ ≤ ∑ S ∈ C, (X ∩ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ C, r := Finset.sum_le_sum good.overlap
    _ = C.card * r := by simp
    _ ≤ _ := Nat.mul_le_mul_right r good.card

theorem empty_good (h r : ℕ) (H : Haven G (h * r)) : Good h r H ∅ ∅ := by
  refine ⟨Covey.empty G, by simp, Finset.empty_subset _, ?_, ?_⟩ <;> simp

noncomputable def score {k : ℕ} (H : Haven G k) (C : Finset (Finset V)) (X : Finset V) : ℕ :=
  C.card + 2 * ((H.region X).card + (X ∪ H.region X).card)

theorem exists_min (h r : ℕ) (H : Haven G (h * r)) :
    ∃ C X, Good h r H C X ∧ ∀ D Y, Good h r H D Y → score H C X ≤ score H D Y := by
  classical
  let P := fun q => ∃ C X, Good h r H C X ∧ score H C X = q
  have hex : ∃ q, P q := ⟨score H ∅ ∅, ∅, ∅, empty_good h r H, rfl⟩
  obtain ⟨C, X, hgood, hscore⟩ := Nat.find_spec hex
  refine ⟨C, X, hgood, ?_⟩
  intro D Y hDY
  rw [hscore]
  exact Nat.find_min' hex ⟨D, Y, hDY, rfl⟩
end Paper.HavenConfig
