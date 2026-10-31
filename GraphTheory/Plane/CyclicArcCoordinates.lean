import GraphTheory.Plane.CyclicAttachment

/-!
# Natural coordinates on a proper circular arc

The Wagner gap lemma uses absolute cyclic positions; insertion of two fans
uses consecutive iterates starting at the first gap endpoint. These lemmas
are the arithmetic bridge, including a gap crossing position zero.
-/

namespace PlaneTopology.CyclicArcCoordinates

open PlaneTopology.CyclicAttachment

/-- The positive forward distance between two distinct positions. -/
def distance (L a b : ℕ) : ℕ := if a < b then b - a else L - a + b

/-- The distance of a proper arc is positive and shorter than its circle. -/
theorem distance_bounds {L a b : ℕ} (ha : a < L) (hb : b < L) (hab : a ≠ b) :
    0 < distance L a b ∧ distance L a b < L := by
  unfold distance
  split_ifs <;> omega

/-- The endpoint is reached after exactly the forward distance. -/
theorem add_distance_mod {L a b : ℕ} (ha : a < L) (hb : b < L) :
    (a + distance L a b) % L = b := by
  unfold distance
  split_ifs with hab
  · rw [Nat.add_sub_of_le (by omega), Nat.mod_eq_of_lt hb]
  · have heq : a + (L - a + b) = L + b := by omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hb]

/-- Positive offsets strictly before the endpoint lie in the open arc. -/
theorem openArc_add_mod {L a b k : ℕ} (ha : a < L) (hb : b < L)
    (hk : 0 < k) (hkd : k < distance L a b) :
    openArc a b ((a + k) % L) := by
  unfold distance at hkd
  unfold openArc
  split_ifs at hkd ⊢ with hab
  · rw [Nat.mod_eq_of_lt (by omega : a + k < L)]
    omega
  · by_cases hw : a + k < L
    · rw [Nat.mod_eq_of_lt hw]
      omega
    · have heq : a + k = L + (a + k - L) := by omega
      have hlt : a + k - L < L := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, zero_add, Nat.mod_eq_of_lt hlt]
      omega

/-- Every closed-arc position has a bounded forward offset from its start. -/
theorem exists_offset_of_closedArc {L a b x : ℕ}
    (ha : a < L) (hb : b < L) (hx : x < L)
    (h : closedArc a b x) :
    ∃ k ≤ distance L a b, (a + k) % L = x := by
  rcases h with h | h | h
  · subst x
    exact ⟨0, Nat.zero_le _, by simp [Nat.mod_eq_of_lt ha]⟩
  · subst x
    exact ⟨distance L a b, le_rfl, add_distance_mod ha hb⟩
  · unfold openArc at h
    by_cases hax : a ≤ x
    · refine ⟨x - a, ?_, ?_⟩
      · unfold distance
        split_ifs at * <;> omega
      · rw [Nat.add_sub_of_le hax, Nat.mod_eq_of_lt hx]
    · refine ⟨L - a + x, ?_, ?_⟩
      · unfold distance
        split_ifs at * <;> omega
      · have heq : a + (L - a + x) = L + x := by omega
        rw [heq, Nat.add_mod]
        simp [Nat.mod_eq_of_lt hx]

/-- A closed arc of positive length is covered by the endpoints of its
successive darts, indexed from zero through distance minus one. -/
theorem exists_edge_offset_of_closedArc {L a b x : ℕ}
    (ha : a < L) (hb : b < L) (hx : x < L) (hab : a ≠ b)
    (h : closedArc a b x) :
    ∃ i ≤ distance L a b - 1,
      x = (a + i) % L ∨ x = (a + (i + 1)) % L := by
  obtain ⟨k, hk, heq⟩ := exists_offset_of_closedArc ha hb hx h
  have hpos := (distance_bounds ha hb hab).1
  by_cases hlast : k = distance L a b
  · refine ⟨k - 1, by omega, Or.inr ?_⟩
    have hsucc : k - 1 + 1 = k := by omega
    rw [hsucc]
    exact heq.symm
  · exact ⟨k, by omega, Or.inl heq.symm⟩

/-- No attachment occurs at an internal offset of a consecutive gap. -/
theorem not_mem_of_consecutive {L a b i : ℕ} {X : Finset ℕ}
    (ha : a < L) (hb : b < L) (hgap : Consecutive X a b)
    (hi : i < distance L a b - 1) : (a + (i + 1)) % L ∉ X := by
  intro hx
  exact hgap.2.2.2 _ hx (openArc_add_mod ha hb (by omega) (by omega))

#print axioms exists_edge_offset_of_closedArc
#print axioms not_mem_of_consecutive

end PlaneTopology.CyclicArcCoordinates
