import GraphTheory.Surfaces.SignedRotationCorners

/-! A four-flag face can only occur on an edge whose endpoints are leaves. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

theorem degree_eq_one_of_corner_dart_fixed (x : Flag G)
    (hx : (r.cornerFlip x).1 = x.1) : G.degree x.1.fst = 1 := by
  have hs : r.σ x.1 = x.1 := by
    cases hb : x.2
    · simpa only [cornerFlip, hb, Bool.false_eq_true, if_false] using hx
    · have h : r.σ.symm x.1 = x.1 := by
        simpa only [cornerFlip, hb, if_true] using hx
      simpa only [Equiv.apply_symm_apply] using (congrArg r.σ h).symm
  have hn : G.neighborFinset x.1.fst = {x.1.snd} := by
    ext w
    simp only [G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hw
      let d : G.Dart := ⟨(x.1.fst, w), hw⟩
      have hd : x.1 = d := (r.cyclic x.1 d rfl).eq_of_left hs
      exact (congrArg (fun q : G.Dart => q.snd) hd).symm
    · rintro rfl
      exact x.1.adj
  change (G.neighborFinset x.1.fst).card = 1
  rw [hn, Finset.card_singleton]

theorem corner_dart_fixed_of_face_square (x : Flag G)
    (h : r.cornerFlip (r.edgeFlip x) = r.edgeFlip (r.cornerFlip x)) :
    (r.cornerFlip x).1 = x.1 := by
  have ht := congrArg (fun z : Flag G => z.1.fst) h
  change (r.cornerFlip (r.edgeFlip x)).1.fst = (r.cornerFlip x).1.snd at ht
  have hs : (r.cornerFlip x).1.snd = x.1.snd := by
    rw [r.cornerFlip_source] at ht
    exact ht.symm
  exact Dart.ext _ _ (Prod.ext (r.cornerFlip_source x) hs)

theorem face_square_endpoints_degree_one (x : Flag G)
    (h : r.cornerFlip (r.edgeFlip x) = r.edgeFlip (r.cornerFlip x)) :
    G.degree x.1.fst = 1 ∧ G.degree x.1.snd = 1 := by
  constructor
  · exact r.degree_eq_one_of_corner_dart_fixed x (r.corner_dart_fixed_of_face_square x h)
  · have he : r.cornerFlip (r.edgeFlip (r.edgeFlip x)) =
        r.edgeFlip (r.cornerFlip (r.edgeFlip x)) := by
      rw [r.edgeFlip_involutive, h, r.edgeFlip_involutive]
    exact r.degree_eq_one_of_corner_dart_fixed (r.edgeFlip x)
      (r.corner_dart_fixed_of_face_square (r.edgeFlip x) he)

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.degree_eq_one_of_corner_dart_fixed
#print axioms SimpleGraph.SignedRotation.face_square_endpoints_degree_one
