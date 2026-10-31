import GraphTheory.SimpleGraph.Planar.MinorClosed

/-!
# A filled separator side is a real minor

A path between two retained vertices whose interior lies outside the retained
side can be contracted to the missing separator edge. The proof gives the
actual branch-set model: the first endpoint absorbs the path except its last
vertex, and every other retained vertex has a singleton branch set.
-/

namespace PlaneTopology.WagnerSeparatorMinor

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A connected outside branch meeting the retained side only at u realizes
the added separator edge by a genuine branch-set minor model. -/
noncomputable def filledSideMinorModel (A : Set V) (u v : A) (S : Set V)
    (huS : u.val ∈ S) (hconn : (G.induce S).Connected)
    (hside : ∀ z ∈ S, z ∈ A → z = u.val)
    (hcross : ∃ z ∈ S, G.Adj z v.val) :
    MinorModel ((G.induce A) ⊔ edge u v) G := by
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
    rcases hab with hold | hedge
    · exact ⟨a.val, hself a, b.val, hself b, hold⟩
    · rcases ((edge_adj u v a b).mp hedge).1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst a
        subst b
        obtain ⟨z, hzS, hzv⟩ := hcross
        exact ⟨z, by simpa [B] using hzS, v.val, hself v, hzv⟩
      · subst a
        subst b
        obtain ⟨z, hzS, hzv⟩ := hcross
        exact ⟨v.val, hself v, z, by simpa [B] using hzS, hzv.symm⟩

/-- A simple outside path gives the required connected first-endpoint branch.
The final vertex is excluded using the actual path's no-repetition proof. -/
theorem outsidePath_prefix_side (A : Set V) (u v : A) (hne : u ≠ v)
    (p : G.Walk u.val v.val) (hp : p.IsPath)
    (hout : ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val) :
    ∀ z ∈ p.dropLast.support, z ∈ A → z = u.val := by
  have hnil : ¬p.Nil := Walk.not_nil_of_ne (fun h => hne (Subtype.ext h))
  have hnd : (p.dropLast.support ++ [v.val]).Nodup := by
    rw [p.support_dropLast_concat hnil]
    exact hp.support_nodup
  have hvnot : v.val ∉ p.dropLast.support := by
    intro hv
    exact (List.disjoint_of_nodup_append hnd) hv (by simp)
  intro z hz hzA
  have hzfull : z ∈ p.support := by
    rw [← p.support_dropLast_concat hnil]
    exact List.mem_append_left _ hz
  rcases hout z hzfull hzA with hzu | hzv
  · exact hzu
  · exact (hvnot (hzv ▸ hz)).elim

/-- Contracting an actual u-v path outside the retained side creates exactly
the added separator edge while retaining all original induced-side edges. -/
theorem filledSide_minor_of_outsidePath (A : Set V) (u v : A) (hne : u ≠ v)
    (p : G.Walk u.val v.val) (hp : p.IsPath)
    (hout : ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val) :
    ((G.induce A) ⊔ edge u v) ≤m G := by
  have hnil : ¬p.Nil := Walk.not_nil_of_ne (fun h => hne (Subtype.ext h))
  exact ⟨filledSideMinorModel G A u v {z | z ∈ p.dropLast.support}
    p.dropLast.start_mem_support p.dropLast.connected_induce_support
    (outsidePath_prefix_side G A u v hne p hp hout)
    ⟨p.penultimate, p.dropLast.end_mem_support, p.adj_penultimate hnil⟩⟩

/-- Minor-defined planarity transfers to the actually filled separator side.
This is derived from a branch-set model, not an embedding assumption. -/
theorem filledSide_isPlanar_of_outsidePath (hG : G.IsPlanar)
    (A : Set V) (u v : A) (hne : u ≠ v)
    (p : G.Walk u.val v.val) (hp : p.IsPath)
    (hout : ∀ z ∈ p.support, z ∈ A → z = u.val ∨ z = v.val) :
    ((G.induce A) ⊔ edge u v).IsPlanar := by
  have hm := filledSide_minor_of_outsidePath G A u v hne p hp hout
  exact ⟨IsHMinorFree.minor hG.1 hm, IsHMinorFree.minor hG.2 hm⟩

#print axioms filledSideMinorModel
#print axioms filledSide_minor_of_outsidePath
#print axioms filledSide_isPlanar_of_outsidePath

end PlaneTopology.WagnerSeparatorMinor
