import GraphTheory.Plane.WagnerSeparatorMinor

/-! Simultaneous separator projection. One connected branch outside the
retained side is absorbed into a retained anchor. Every boundary edge is
realized by the same minor model, rather than separate incompatible models. -/
namespace Paper.CliqueStarProjection

open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

def fill (A : Set V) (u : A) (S : Set V) : SimpleGraph A where
  Adj a b := G.Adj a.val b.val ∨
    (a ≠ b ∧ ((a = u ∧ ∃ z ∈ S, G.Adj z b.val) ∨
      (b = u ∧ ∃ z ∈ S, G.Adj z a.val)))
  symm a b h := h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩)
  loopless := ⟨fun a h => h.elim (G.loopless.irrefl a.val) (fun h => h.1 rfl)⟩

noncomputable instance fill_decidable (A : Set V) (u : A) (S : Set V) :
    DecidableRel (fill G A u S).Adj := by
  classical
  exact fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

noncomputable def model (A : Set V) (u : A) (S : Set V)
    (huS : u.val ∈ S) (hconn : (G.induce S).Connected)
    (hside : ∀ z ∈ S, z ∈ A → z = u.val) : MinorModel (fill G A u S) G := by
  classical
  let B : A → Set V := fun a => if a = u then S else {a.val}
  have hself (a : A) : a.val ∈ B a := by
    by_cases ha : a = u
    · subst a
      simpa [B] using huS
    · simp [B, ha]
  refine {
    branchSet := B
    nonempty := fun a => ⟨a.val, hself a⟩
    disjoint := ?_
    connected := ?_
    adjacent := ?_
  }
  · intro a b hab
    rw [Set.disjoint_left]
    intro z hza hzb
    by_cases ha : a = u
    · subst a
      have hb : b ≠ u := Ne.symm hab
      have hzS : z ∈ S := by simpa [B] using hza
      have hzb' : z = b.val := by simpa [B, hb] using hzb
      exact hb (Subtype.ext (hside b.val (hzb' ▸ hzS) b.property))
    · by_cases hb : b = u
      · subst b
        have hzS : z ∈ S := by simpa [B] using hzb
        have hza' : z = a.val := by simpa [B, ha] using hza
        exact ha (Subtype.ext (hside a.val (hza' ▸ hzS) a.property))
      · have hza' : z = a.val := by simpa [B, ha] using hza
        have hzb' : z = b.val := by simpa [B, hb] using hzb
        exact hab (Subtype.ext (hza'.symm.trans hzb'))
  · intro a
    by_cases ha : a = u
    · change (G.induce (if a = u then S else {a.val})).Connected
      rw [if_pos ha]
      exact hconn
    · change (G.induce (if a = u then S else {a.val})).Connected
      rw [if_neg ha]
      exact (MinorModel.refl G).connected a.val
  · intro a b hab
    rcases hab with hold | ⟨_, hnew⟩
    · exact ⟨a.val, hself a, b.val, hself b, hold⟩
    · rcases hnew with ⟨ha, z, hz, hzb⟩ | ⟨hb, z, hz, hza⟩
      · subst a
        exact ⟨z, by simpa [B] using hz, b.val, hself b, hzb⟩
      · subst b
        exact ⟨a.val, hself a, z, by simpa [B] using hz, hza.symm⟩

theorem isMinor (A : Set V) (u : A) (S : Set V)
    (huS : u.val ∈ S) (hconn : (G.induce S).Connected)
    (hside : ∀ z ∈ S, z ∈ A → z = u.val) : (fill G A u S).IsMinor G :=
  ⟨model G A u S huS hconn hside⟩

/-- An actual connected outside set can be absorbed into an adjacent anchor. -/
theorem outside (A C : Set V) (u : A) (hC : (G.induce C).Connected)
    (houtside : Disjoint C A) (hadj : ∃ z ∈ C, G.Adj u.val z) :
    (fill G A u (insert u.val C)).IsMinor G := by
  obtain ⟨z, hz, huz⟩ := hadj
  have hsingle := (MinorModel.refl G).connected u.val
  have hconn : (G.induce (insert u.val C)).Connected := by
    simpa only [Set.singleton_union] using
      connected_induce_union hsingle.preconnected hC.preconnected
        (Set.mem_singleton u.val) hz huz
  refine isMinor G A u (insert u.val C) (Set.mem_insert _ _) hconn ?_
  intro w hw hwA
  rcases hw with hwu | hwC
  · exact hwu
  · exact False.elim ((Set.disjoint_left.mp houtside) hwC hwA)

end Paper.CliqueStarProjection

#print axioms Paper.CliqueStarProjection.model
#print axioms Paper.CliqueStarProjection.isMinor
#print axioms Paper.CliqueStarProjection.outside
