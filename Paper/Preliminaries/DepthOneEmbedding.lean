import Paper.Preliminaries.DepthOne

/-! Transport shallow minor models along a genuine injective graph map. -/
namespace Paper.DepthOneEmbedding
attribute [local instance] Classical.propDecidable
universe u
variable {U V A : Type u} [DecidableEq U] [DecidableEq V]
variable {G : SimpleGraph U} {H : SimpleGraph V} {J : SimpleGraph A}

noncomputable def map (e : U → V) (hinj : Function.Injective e)
    (hedge : ∀ u v, G.Adj u v → H.Adj (e u) (e v)) (M : DepthOne.StarModel J G) :
    DepthOne.StarModel J H where
  branchSet a := e '' M.branchSet a
  nonempty a := (M.nonempty a).image e
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    rintro v ⟨x, hx, he⟩ ⟨y, hy, hf⟩
    have hxy := hinj (he.trans hf.symm)
    exact Set.disjoint_left.mp (M.disjoint a b hab) hx (hxy ▸ hy)
  connected a := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨e (M.root a), Set.mem_image_of_mem e (M.root_mem a)⟩, ?_⟩
    intro v
    obtain ⟨x, hx, he⟩ := v.property
    rcases M.radius_one a x hx with heq | ha
    · have hv : (⟨e (M.root a), Set.mem_image_of_mem e (M.root_mem a)⟩ :
          {v // v ∈ e '' M.branchSet a}) = v := Subtype.ext ((congrArg e heq).trans he)
      rw [hv]
    · have ha' : H.Adj (e (M.root a)) v.val := he ▸ hedge _ _ ha
      exact (show (H.induce (e '' M.branchSet a)).Adj
        ⟨e (M.root a), Set.mem_image_of_mem e (M.root_mem a)⟩ v from ha').reachable
  adjacent a b hab := by
    obtain ⟨x, hx, y, hy, ha⟩ := M.adjacent a b hab
    exact ⟨e x, Set.mem_image_of_mem e hx, e y, Set.mem_image_of_mem e hy, hedge _ _ ha⟩
  root a := e (M.root a)
  root_mem a := Set.mem_image_of_mem e (M.root_mem a)
  radius_one a v hv := by
    obtain ⟨x, hx, rfl⟩ := hv
    exact (M.radius_one a x hx).elim (fun he => Or.inl (congrArg e he)) (fun ha => Or.inr (hedge _ _ ha))

theorem bound [Fintype U] [Fintype V] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : U → V) (hinj : Function.Injective e)
    (hedge : ∀ u v, G.Adj u v → H.Adj (e u) (e v)) {a : ℝ} (hden : DepthOne.Bound H a) :
    DepthOne.Bound G a := by
  intro A _ _ J _ M
  exact hden A J (map e hinj hedge M)
end Paper.DepthOneEmbedding
