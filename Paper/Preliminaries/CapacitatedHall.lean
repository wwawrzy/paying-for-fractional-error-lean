import Paper.Certificates.Counting.FloatingCore
import Mathlib.Combinatorics.Hall.Basic

/-! Capacitated Hall for all witness requirements simultaneously. -/
namespace Paper.CapacitatedHall
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem demand_sum_le_union (N : J → Finset I) (k : J → ℕ) (L : ℕ) (hL : 1 ≤ L)
    (hrow : ∀ r, L * k r ≤ (N r).card)
    (hcol : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ L) (T : Finset J) :
    (∑ r ∈ T, k r) ≤ (T.biUnion N).card := by
  classical
  let U := T.biUnion N
  have heq : (∑ r ∈ T, (N r).card) = ∑ v ∈ U, (T.filter (fun r => v ∈ N r)).card := by
    rw [← FloatingCore.incidence_sum N T U]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.inter_eq_left.mpr (fun v hv => Finset.mem_biUnion.mpr ⟨r, hr, hv⟩)]
  have hl : L * (∑ r ∈ T, k r) ≤ ∑ r ∈ T, (N r).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => hrow r)
  have hu : (∑ r ∈ T, (N r).card) ≤ L * U.card := by
    rw [heq]
    calc
      _ ≤ ∑ _v ∈ U, L := Finset.sum_le_sum (fun v _ =>
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ T))).trans (hcol v))
      _ = _ := by simp [mul_comm]
  exact Nat.le_of_mul_le_mul_left (hl.trans hu) (by omega)

theorem copies_card_le (k : J → ℕ) (S : Finset (Σ r, Fin (k r))) :
    S.card ≤ ∑ r ∈ S.image Sigma.fst, k r := by
  classical
  let T := S.image Sigma.fst
  have hs : S ⊆ T.biUnion (fun r => (Finset.univ : Finset (Fin (k r))).image (fun i : Fin (k r) => (⟨r, i⟩ : Σ r, Fin (k r)))) := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨z.fst, Finset.mem_image.mpr ⟨z, hz, rfl⟩,
      Finset.mem_image.mpr ⟨z.snd, Finset.mem_univ _, rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ∑ r ∈ T, ((Finset.univ : Finset (Fin (k r))).image (fun i : Fin (k r) => (⟨r, i⟩ : Σ r, Fin (k r)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ r ∈ T, k r := Finset.sum_le_sum (fun r _ => by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (f := fun i : Fin (k r) => (⟨r, i⟩ : Σ r, Fin (k r))) (s := Finset.univ)))

/-- Every requirement copy receives a different actual eligible child. -/
theorem exists_assignment (N : J → Finset I) (k : J → ℕ) (L : ℕ) (hL : 1 ≤ L)
    (hrow : ∀ r, L * k r ≤ (N r).card)
    (hcol : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ L) :
    ∃ f : (Σ r, Fin (k r)) → I, Function.Injective f ∧ ∀ z, f z ∈ N z.fst := by
  classical
  have hHall : ∀ S : Finset (Σ r, Fin (k r)), S.card ≤ (S.biUnion (fun z => N z.fst)).card := by
    intro S
    have heq : (S.image Sigma.fst).biUnion N = S.biUnion (fun z => N z.fst) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_image]
      aesop
    calc
      _ ≤ _ := copies_card_le k S
      _ ≤ ((S.image Sigma.fst).biUnion N).card := demand_sum_le_union N k L hL hrow hcol _
      _ = _ := by rw [heq]
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective (fun z : Σ r, Fin (k r) => N z.fst)).mp hHall
end Paper.CapacitatedHall
