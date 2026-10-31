import Paper.Preliminaries.DepthOne

/-! Project a shallow minor of a clique-role graph by assigning each
physical vertex one branch label. Every outcome is a genuine physical star
minor. The density transfer still needs a separate finite counting proof. -/
namespace Paper.BlowupProjection
attribute [local instance] Classical.propDecidable
universe u
variable {V A : Type u} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def blowup (c : ℕ) : SimpleGraph (V × Fin c) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1)
  symm := by rintro x y ⟨hne, h⟩; exact ⟨hne.symm, h.elim (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G} {c : ℕ} {J : SimpleGraph A} (M : DepthOne.StarModel J (blowup G c))

noncomputable def copyLabel (z : V × Fin c) : Option A :=
  if h : ∃ a, z ∈ M.branchSet a then some h.choose else none

theorem label_of_mem {z : V × Fin c} {a : A} (ha : z ∈ M.branchSet a) : copyLabel M z = some a := by
  classical
  have he : ∃ b, z ∈ M.branchSet b := ⟨a, ha⟩
  rw [copyLabel, dif_pos he]
  congr 1
  by_contra hn
  exact Set.disjoint_left.mp (M.disjoint he.choose a hn) he.choose_spec ha

theorem mem_of_label {z : V × Fin c} {a : A} (ha : copyLabel M z = some a) : z ∈ M.branchSet a := by
  classical
  by_cases he : ∃ b, z ∈ M.branchSet b
  · rw [copyLabel, dif_pos he] at ha
    exact (Option.some.inj ha) ▸ he.choose_spec
  · simp [copyLabel, he] at ha

noncomputable def sampleLabel (ω : V → Fin c) (v : V) : Option A := copyLabel M (v, ω v)

noncomputable def retained (ω : V → Fin c) : Finset A :=
  Finset.univ.filter (fun a => sampleLabel M ω (M.root a).1 = some a)

def graph (ω : V → Fin c) : SimpleGraph (retained M ω) where
  Adj a b := a ≠ b ∧ ∃ u v, sampleLabel M ω u = some a.val ∧
    sampleLabel M ω v = some b.val ∧ G.Adj u v
  symm := by rintro a b ⟨hne, u, v, hu, hv, ha⟩; exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem physical_radius (ω : V → Fin c) {a : A} {v : V} (hv : sampleLabel M ω v = some a) :
    (M.root a).1 = v ∨ G.Adj (M.root a).1 v := by
  have hm := mem_of_label M hv
  rcases M.radius_one a (v, ω v) hm with he | ha
  · exact Or.inl (congrArg Prod.fst he)
  · exact ha.2

noncomputable def model (ω : V → Fin c) : DepthOne.StarModel (graph M ω) G where
  branchSet a := {v | sampleLabel M ω v = some a.val}
  nonempty a := ⟨(M.root a.val).1, (Finset.mem_filter.mp a.property).2⟩
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    exact hab (Subtype.ext (Option.some.inj (ha.symm.trans hb)))
  connected a := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨(M.root a.val).1, (Finset.mem_filter.mp a.property).2⟩, ?_⟩
    intro v
    rcases physical_radius M ω v.property with he | ha
    · have hs : (⟨(M.root a.val).1, (Finset.mem_filter.mp a.property).2⟩ :
          {v | sampleLabel M ω v = some a.val}) = v := Subtype.ext he
      rw [hs]
    · exact (show (G.induce {v | sampleLabel M ω v = some a.val}).Adj
        ⟨(M.root a.val).1, (Finset.mem_filter.mp a.property).2⟩ v from ha).reachable
  adjacent a b hab := by
    obtain ⟨_, u, v, hu, hv, ha⟩ := hab
    exact ⟨u, hu, v, hv, ha⟩
  root a := (M.root a.val).1
  root_mem a := (Finset.mem_filter.mp a.property).2
  radius_one a v hv := physical_radius M ω hv

theorem outcome_density {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) (ω : V → Fin c) :
    ((graph M ω).edgeFinset.card : ℝ) ≤ a * Fintype.card A := by
  classical
  have hh := hden (retained M ω) (graph M ω) (model M ω)
  have hc : Fintype.card (retained M ω) ≤ Fintype.card A := Fintype.card_subtype_le _
  have hc' : (Fintype.card (retained M ω) : ℝ) ≤ Fintype.card A := by exact_mod_cast hc
  exact hh.trans (mul_le_mul_of_nonneg_left hc' ha)
end Paper.BlowupProjection
