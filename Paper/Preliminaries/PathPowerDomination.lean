import Paper.Preliminaries.PathPowerCounting
import GraphTheory.SimpleGraph.Domination.Total

namespace Paper.PathPowerDomination
open SevenFoundation PathPowerTreewidth PathPowerCounting

/-- One centre per block of length `2*t+1`, clipped at the last vertex. -/
def center (n t : ℕ) (j : Fin (n ⌈/⌉ (2 * t + 1))) : Fin n :=
  ⟨min ((2 * t + 1) * j.val + t) (n - 1), by
    have hs : (2 * t + 1) * j.val < n := by
      by_contra h
      have hh := (ceilDiv_le_iff_le_mul (by omega : 0 < 2 * t + 1)).mpr (Nat.le_of_not_gt h)
      omega
    omega⟩

def code (n t : ℕ) : Finset (Fin n) := Finset.univ.image (center n t)

theorem code_card (n t : ℕ) : (code n t).card ≤ n ⌈/⌉ (2 * t + 1) := by
  exact (Finset.card_image_le).trans_eq (by simp)

theorem code_dominates (n t : ℕ) : dominates (graph n t) (code n t) := by
  intro v
  have hw : 0 < 2 * t + 1 := by omega
  have hn : n ≤ (2 * t + 1) * (n ⌈/⌉ (2 * t + 1)) :=
    (ceilDiv_le_iff_le_mul hw).mp le_rfl
  let j : Fin (n ⌈/⌉ (2 * t + 1)) :=
    ⟨v.val / (2 * t + 1), (Nat.div_lt_iff_lt_mul hw).mpr (by simpa only [mul_comm] using v.isLt.trans_le hn)⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨center n t j, Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
  rw [mem_closed_iff]
  have hmod := Nat.mod_lt v.val hw
  have hdiv := Nat.div_add_mod v.val (2 * t + 1)
  change v.val ≤ min ((2 * t + 1) * (v.val / (2 * t + 1)) + t) (n - 1) + t ∧
    min ((2 * t + 1) * (v.val / (2 * t + 1)) + t) (n - 1) ≤ v.val + t
  omega

theorem dominates_iff (n t : ℕ) (D : Finset (Fin n)) :
    dominates (graph n t) D ↔ (graph n t).IsDominatingSetFinset D := by
  constructor
  · intro h v
    obtain ⟨w, hw, hv⟩ := Finset.mem_biUnion.mp (h v)
    rcases (mem_closed _ _ _).mp hv with he | ha
    · exact Or.inl (he ▸ hw)
    · exact Or.inr ⟨w, hw, ha.symm⟩
  · intro h v
    rcases h v with hv | ⟨w, hw, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv, (mem_closed _ _ _).mpr (Or.inl rfl)⟩
    · exact Finset.mem_biUnion.mpr ⟨w, hw, (mem_closed _ _ _).mpr (Or.inr ha.symm)⟩

/-- Exact integral optimum, including empty paths and `t=0`. -/
theorem dominationNumber_eq (n t : ℕ) :
    (graph n t).dominationNumber = n ⌈/⌉ (2 * t + 1) := by
  apply Nat.le_antisymm
  · exact ((dominates_iff n t _).mp (code_dominates n t)).dominationNumber_le.trans (code_card n t)
  · obtain ⟨D, hD, he⟩ := SimpleGraph.exists_isDominatingSetFinset_card_eq_dominationNumber
      (G := graph n t)
    rw [← he]
    exact (ceilDiv_le_iff_le_mul (by omega : 0 < 2 * t + 1)).mpr
      (domination_count n t D ((dominates_iff n t D).mpr hD))

end Paper.PathPowerDomination
