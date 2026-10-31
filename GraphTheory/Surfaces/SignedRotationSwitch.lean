import GraphTheory.Surfaces.SignedRotation
namespace SimpleGraph.SignedRotation
variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
theorem inverse_source (d : G.Dart) : (r.σ.symm d).fst = d.fst := by
  have h := r.σ_source (r.σ.symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

def switchPerm (t : V → Bool) : Equiv.Perm G.Dart where
  toFun d := if t d.fst then r.σ.symm d else r.σ d
  invFun d := if t d.fst then r.σ d else r.σ.symm d
  left_inv d := by
    cases ht : t d.fst <;> simp [ht,r.σ_source,r.inverse_source]
  right_inv d := by
    cases ht : t d.fst <;> simp [ht,r.σ_source,r.inverse_source]

theorem switchPerm_source (t : V → Bool) (d : G.Dart) :
    (r.switchPerm t d).fst = d.fst := by
  change (if t d.fst then r.σ.symm d else r.σ d).fst = _
  split <;> simp only [r.σ_source,r.inverse_source]

theorem perm_pow_source (p : Equiv.Perm G.Dart) (hp : ∀ d, (p d).fst = d.fst)
    (d : G.Dart) (n : ℕ) : ((p ^ n) d).fst = d.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hp,ih]

theorem switchPerm_pow (t : V → Bool) (d : G.Dart) (n : ℕ) :
    (r.switchPerm t ^ n) d = if t d.fst then (r.σ.symm ^ n) d else (r.σ ^ n) d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih]
    cases ht : t d.fst
    · simp only [ht,Bool.false_eq_true,↓reduceIte]
      change (if t ((r.σ ^ n) d).fst then _ else _) = _
      rw [perm_pow_source r.σ r.σ_source d n,ht]
      simp only [Bool.false_eq_true,↓reduceIte,pow_succ',Equiv.Perm.mul_apply]
    · simp only [ht,↓reduceIte]
      change (if t ((r.σ.symm ^ n) d).fst then _ else _) = _
      rw [perm_pow_source r.σ.symm r.inverse_source d n,ht]
      simp only [↓reduceIte,pow_succ',Equiv.Perm.mul_apply]

variable [Fintype V] [DecidableRel G.Adj]
theorem switchPerm_cyclic (t : V → Bool) (d e : G.Dart) (h : d.fst = e.fst) :
    (r.switchPerm t).SameCycle d e := by
  cases ht : t d.fst
  · obtain ⟨n,hn⟩ := (r.cyclic d e h).exists_nat_pow_eq
    refine ⟨(n : ℤ),?_⟩
    rw [zpow_natCast,switchPerm_pow]
    simpa only [ht,Bool.false_eq_true,↓reduceIte] using hn
  · obtain ⟨n,hn⟩ := (r.cyclic d e h).inv.exists_nat_pow_eq
    refine ⟨(n : ℤ),?_⟩
    rw [zpow_natCast,switchPerm_pow]
    simpa only [ht,↓reduceIte] using hn

def switch (t : V → Bool) : SignedRotation G where
  σ := r.switchPerm t
  σ_source := r.switchPerm_source t
  cyclic := r.switchPerm_cyclic t
  twist d := xor (xor (r.twist d) (t d.fst)) (t d.snd)
  twist_symm d := by
    simp only [r.twist_symm]
    change xor (xor (r.twist d) (t d.snd)) (t d.fst) = xor (xor (r.twist d) (t d.fst)) (t d.snd)
    cases r.twist d <;> cases t d.fst <;> cases t d.snd <;> rfl
def flagSwitch (t : V → Bool) : Flag G ≃ Flag G where
  toFun x := (x.1,xor x.2 (t x.1.fst))
  invFun x := (x.1,xor x.2 (t x.1.fst))
  left_inv x := by
    rcases x with ⟨d,b⟩
    change (d,xor (xor b (t d.fst)) (t d.fst)) = (d,b)
    cases b <;> cases t d.fst <;> rfl
  right_inv x := by
    rcases x with ⟨d,b⟩
    change (d,xor (xor b (t d.fst)) (t d.fst)) = (d,b)
    cases b <;> cases t d.fst <;> rfl

theorem flagSwitch_side (t : V → Bool) (x : Flag G) :
    flagSwitch t (sideFlip x) = sideFlip (flagSwitch t x) := by
  rcases x with ⟨d,b⟩
  change (d,xor (!b) (t d.fst)) = (d,!(xor b (t d.fst)))
  cases b <;> cases t d.fst <;> rfl

theorem flagSwitch_edge (t : V → Bool) (x : Flag G) :
    flagSwitch t ((r.switch t).edgeFlip x) = r.edgeFlip (flagSwitch t x) := by
  rcases x with ⟨d,b⟩
  change (d.symm,xor (if xor (xor (r.twist d) (t d.fst)) (t d.snd) then b else !b) (t d.snd)) =
    (d.symm,if r.twist d then xor b (t d.fst) else !(xor b (t d.fst)))
  cases r.twist d <;> cases t d.fst <;> cases t d.snd <;> cases b <;> rfl

theorem flagSwitch_corner (t : V → Bool) (x : Flag G) :
    flagSwitch t ((r.switch t).cornerFlip x) = r.cornerFlip (flagSwitch t x) := by
  rcases x with ⟨d,b⟩
  cases b <;> cases ht : t d.fst <;>
    simp [flagSwitch,cornerFlip,switch,switchPerm,ht,r.σ_source,r.inverse_source]

theorem eqvGen_map_switch {A B : Type*} {R : A → A → Prop} {S : B → B → Prop}
    (f : A → B) (hf : ∀ x y, R x y → S (f x) (f y)) {x y : A}
    (h : Relation.EqvGen R x y) : Relation.EqvGen S (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem eqvGen_equiv_switch {A B : Type*} {R : A → A → Prop} {S : B → B → Prop}
    (e : A ≃ B) (he : ∀ x y, R x y ↔ S (e x) (e y)) (x y : A) :
    Relation.EqvGen R x y ↔ Relation.EqvGen S (e x) (e y) := by
  constructor
  · exact eqvGen_map_switch e (fun x y h => (he x y).mp h)
  · intro h
    have hm : ∀ u v, S u v → R (e.symm u) (e.symm v) := by
      intro u v huv
      apply (he (e.symm u) (e.symm v)).mpr
      simpa using huv
    simpa using eqvGen_map_switch e.symm hm h

noncomputable def switchFaceEquiv (t : V → Bool) : (r.switch t).Face ≃ r.Face :=
  Quotient.congr (flagSwitch t) (by
    intro x y
    apply eqvGen_equiv_switch (flagSwitch t)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← r.flagSwitch_edge t, ← r.flagSwitch_corner t]
    simp only [Equiv.apply_eq_iff_eq])

noncomputable def switchVertexEquiv (t : V → Bool) : (r.switch t).Vertex ≃ r.Vertex :=
  Quotient.congr (flagSwitch t) (by
    intro x y
    apply eqvGen_equiv_switch (flagSwitch t)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← flagSwitch_side t, ← r.flagSwitch_corner t]
    simp only [Equiv.apply_eq_iff_eq])
noncomputable def switchEdgeEquiv (t : V → Bool) : (r.switch t).Edge ≃ r.Edge :=
  Quotient.congr (flagSwitch t) (by
    intro x y
    apply eqvGen_equiv_switch (flagSwitch t)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← r.flagSwitch_edge t, ← flagSwitch_side t]
    simp only [Equiv.apply_eq_iff_eq])
noncomputable def switchComponentEquiv (t : V → Bool) : (r.switch t).Component ≃ r.Component :=
  Quotient.congr (flagSwitch t) (by
    intro x y
    apply eqvGen_equiv_switch (flagSwitch t)
    intro a b
    change (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
    rw [← r.flagSwitch_edge t, ← flagSwitch_side t, ← r.flagSwitch_corner t]
    simp only [Equiv.apply_eq_iff_eq])
theorem switch_eulerGenus (t : V → Bool) : (r.switch t).eulerGenus = r.eulerGenus := by
  unfold eulerGenus eulerCharacteristic
  rw [Nat.card_congr (r.switchComponentEquiv t), Nat.card_congr (r.switchVertexEquiv t),
    Nat.card_congr (r.switchEdgeEquiv t), Nat.card_congr (r.switchFaceEquiv t)]

/-- A vertex switch can make any chosen edge untwisted without changing genus. -/
theorem exists_untwisted_same_genus [DecidableEq V] (d : G.Dart) :
    ∃ q : SignedRotation G, q.twist d = false ∧ q.eulerGenus = r.eulerGenus := by
  let t : V → Bool := fun v => if v = d.fst then r.twist d else false
  refine ⟨r.switch t, ?_, r.switch_eulerGenus t⟩
  have hne : d.snd ≠ d.fst := fun h => G.irrefl (h ▸ d.adj)
  change xor (xor (r.twist d) (t d.fst)) (t d.snd) = false
  simp only [t, if_pos rfl, if_neg hne]
  cases r.twist d <;> rfl

end SimpleGraph.SignedRotation


