import Paper.Partitions.Separators.MappedSeparatorProfile
import Paper.Owners.Separators.OwnerSeparator
import Paper.Owners.Construction.OwnerVirtualFacts

/-! Actual physical minor density gives a uniform separator profile for
the public low-owner graph, including all its isolated nonowner IDs. -/
namespace Paper.OwnerPublicProfile
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem spec (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L) {a : ℝ}
    (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    SeparatorProfile.Bound (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
      (OwnerSeparator.constant a h L + 1) := by
  let Q := OwnerVirtualFacts.high G D R L Δ
  let J := OwnerTasks.graph G D R L Q
  let e := fun i : OwnerTasks.Low D Q => i.val.val
  have heD : ∀ i : OwnerTasks.Low D Q, e i ∈ D := fun i => i.val.property
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have hp : SeparatorProfile.Bound J (OwnerSeparator.constant a h L) :=
    OwnerSeparator.represented_profile G D R L hL J e hinj heD
      (fun i j ha => OwnerInteraction.graph_le_augmented G D R L ha) hden ha h hh
  have hpos : (0 : ℝ) < h := by linarith
  have hn : 1 ≤ h := by
    have hh' : 0 < h := by exact_mod_cast hpos
    omega
  exact MappedSeparatorProfile.bound J (PublicOwners.embedding D Q)
    (OwnerSeparator.constant_pos a ha h L hn hL).le hp

end Paper.OwnerPublicProfile
