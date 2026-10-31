import Paper.Certificates.Counting.HallOrientation

/-! Actual incoming and outgoing neighborhoods of the Hall orientation. -/
namespace Paper.OrientedNeighborhoods
attribute [local instance] Classical.propDecidable
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An actual graph edge with proof-independent endpoint order. -/
def edge {u v : V} (h : G.Adj u v) : G.edgeFinset :=
  ⟨s(u, v), by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h⟩

def directs {a : ℕ} (O : HallOrientation.Orientation G a) (u v : V) : Prop :=
  ∃ h : G.Adj u v, HallOrientation.tail G O (edge G h) = u

theorem directs_adj {a : ℕ} (O : HallOrientation.Orientation G a) {u v : V}
    (h : directs G O u v) : G.Adj u v := h.choose

theorem edge_reverse {u v : V} (h : G.Adj u v) : edge G h = edge G h.symm :=
  Subtype.ext Sym2.eq_swap

theorem directs_or {a : ℕ} (O : HallOrientation.Orientation G a) {u v : V}
    (h : G.Adj u v) : directs G O u v ∨ directs G O v u := by
  have hm := O.incident (edge G h)
  have hm' : HallOrientation.tail G O (edge G h) = u ∨
      HallOrientation.tail G O (edge G h) = v := by
    simpa only [Sym2.mem_toFinset, edge, Sym2.mem_iff] using hm
  rcases hm' with hu | hv
  · exact Or.inl ⟨h, hu⟩
  · exact Or.inr ⟨h.symm, by rw [← edge_reverse G h]; exact hv⟩

theorem directs_asymm {a : ℕ} (O : HallOrientation.Orientation G a) {u v : V}
    (hu : directs G O u v) : ¬ directs G O v u := by
  rintro ⟨hv, htail⟩
  obtain ⟨h, ht⟩ := hu
  have he : edge G hv = edge G h := Subtype.ext Sym2.eq_swap
  rw [he, ht] at htail
  exact h.ne htail

noncomputable def outgoing {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) : Finset V :=
  Finset.univ.filter (directs G O v)

noncomputable def incoming {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) : Finset V :=
  Finset.univ.filter (fun u => directs G O u v)

theorem outgoing_card_le {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) :
    (outgoing G O v).card ≤ a := by
  classical
  have hmap : ∀ u ∈ outgoing G O v, s(v, u) ∈
      (HallOrientation.outEdges G O v).image (fun e => e.val) := by
    intro u hu
    obtain ⟨ha, ht⟩ := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨edge G ha,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
  have hinj : Set.InjOn (fun u => s(v, u)) (outgoing G O v : Set V) := by
    intro u _ w _ h
    rcases (@Sym2.mk_eq_mk_iff V (v, u) (v, w)).mp h with he | he
    · exact congrArg Prod.snd he
    · exact (congrArg Prod.snd he).trans (congrArg Prod.fst he)
  have h := Finset.card_le_card_of_injOn (fun u => s(v, u)) hmap hinj
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h.trans (HallOrientation.outEdges_card_le G O v)

theorem incoming_disjoint_outgoing {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) :
    Disjoint (incoming G O v) (outgoing G O v) := by
  apply Finset.disjoint_left.mpr
  intro u hi ho
  exact directs_asymm G O (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp ho).2

theorem nonincoming_subset {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) :
    closed G v \ incoming G O v ⊆ insert v (outgoing G O v) := by
  intro u hu
  rcases (mem_closed G u v).mp (Finset.mem_sdiff.mp hu).1 with he | ha
  · exact Finset.mem_insert.mpr (Or.inl he)
  · rcases directs_or G O ha with hout | hin
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩))
    · exact False.elim ((Finset.mem_sdiff.mp hu).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩))

theorem nonincoming_card_le {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) :
    (closed G v \ incoming G O v).card ≤ a + 1 := by
  exact (Finset.card_le_card (nonincoming_subset G O v)).trans
    ((Finset.card_insert_le v _).trans (Nat.add_le_add_right (outgoing_card_le G O v) 1))
end Paper.OrientedNeighborhoods
