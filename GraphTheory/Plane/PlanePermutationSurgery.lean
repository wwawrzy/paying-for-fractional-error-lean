import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Exact permutation surgery for inserting edges into actual plane maps

The elementary operation swaps two incoming successors in one facial cycle.
Its cycle factorization is proved here from concrete lists, rather than
postulated as an Euler-count provider.
-/

namespace PlaneTopology.PlanePermutationSurgery

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- Cutting a cyclic list before `a` and `b` splits it into the two displayed
cycles. The order of multiplication is the actual permutation order. -/
theorem swap_mul_formPerm_split (a b : α) (l m : List α)
    (h : (a :: (l ++ b :: m)).Nodup) :
    swap a b * (a :: (l ++ b :: m)).formPerm =
      (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp [List.formPerm_cons_cons]
  | cons c l ih =>
    have htail : (c :: (l ++ b :: m)).Nodup := (List.nodup_cons.mp h).2
    have hac : a ≠ c := fun heq => h.notMem (by simp [heq])
    have hab : a ≠ b := by
      intro heq
      subst b
      exact h.notMem (by simp)
    have hcb : c ≠ b := by
      intro heq
      subst b
      exact htail.notMem (by simp)
    have ht := ih c htail
    have hswap : swap a b * swap a c = swap a c * swap c b := by
      ext x
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [← mul_assoc, hswap, mul_assoc, ht, ← mul_assoc]

/-- Permutations formed from disjoint lists act on disjoint supports. Unlike
the standard equivalence, this implication also admits singleton lists. -/
theorem formPerm_disjoint_of_list_disjoint (l m : List α)
    (h : l.Disjoint m) : l.formPerm.Disjoint m.formPerm := by
  intro x
  by_cases hx : x ∈ l
  · right
    exact List.formPerm_apply_of_notMem (fun hm => h hx hm)
  · left
    exact List.formPerm_apply_of_notMem hx

/-- Two nontrivial pieces of one cycle contribute exactly two cycle factors. -/
theorem cycleType_card_swap_mul_formPerm_split [Fintype α]
    (a b : α) (l m : List α)
    (h : (a :: (l ++ b :: m)).Nodup)
    (hl : 1 ≤ l.length) (hm : 1 ≤ m.length) :
    (swap a b * (a :: (l ++ b :: m)).formPerm).cycleType.card = 2 := by
  have hsplit : ((a :: l) ++ (b :: m)).Nodup := h
  have hleft : (a :: l).Nodup := (List.nodup_append.mp hsplit).1
  have hright : (b :: m).Nodup := (List.nodup_append.mp hsplit).2.1
  have hd := formPerm_disjoint_of_list_disjoint (a :: l) (b :: m)
    (fun _ hx hy => (List.nodup_append.mp hsplit).2.2 _ hx _ hy rfl)
  rw [swap_mul_formPerm_split a b l m h, hd.cycleType_mul,
    ((List.isCycle_formPerm hleft (by simpa using hl))).cycleType,
    ((List.isCycle_formPerm hright (by simpa using hm))).cycleType]
  simp

#print axioms swap_mul_formPerm_split
#print axioms cycleType_card_swap_mul_formPerm_split

/-- The complement of one cycle: it agrees with `p` off the orbit of `a`
and fixes that entire orbit. -/
noncomputable def offCycle [Fintype α] (p : Perm α) (a : α) : Perm α := by
  classical
  exact Equiv.Perm.ofSubtype
    (p.subtypePerm (p := fun x => ¬p.SameCycle a x)
      (fun x => not_congr (sameCycle_apply_right (f := p) (x := a) (y := x))))

theorem offCycle_apply [Fintype α] (p : Perm α) (a x : α) :
    offCycle p a x = if p.SameCycle a x then x else p x := by
  classical
  unfold offCycle
  by_cases h : p.SameCycle a x
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (a := x) (ha := not_not.mpr h)]
    simp [h]
  · rw [Equiv.Perm.ofSubtype_apply_of_mem (a := x) (ha := h)]
    simp [h]

/-- Exact factorization into the selected cycle and its disjoint complement. -/
theorem cycleOf_mul_offCycle [Fintype α] (p : Perm α) (a : α) :
    p.cycleOf a * offCycle p a = p := by
  classical
  ext x
  by_cases h : p.SameCycle a x
  · simp [offCycle_apply, h, cycleOf_apply]
  · simp [offCycle_apply, h, cycleOf_apply, sameCycle_apply_right]

theorem cycleOf_disjoint_offCycle [Fintype α] (p : Perm α) (a : α) :
    (p.cycleOf a).Disjoint (offCycle p a) := by
  classical
  intro x
  by_cases h : p.SameCycle a x
  · right
    simp [offCycle_apply, h]
  · left
    simp [cycleOf_apply, h]

/-- A swap within the selected orbit remains disjoint from every other cycle. -/
theorem swap_cycleOf_disjoint_offCycle [Fintype α] (p : Perm α) (a b : α)
    (hab : p.SameCycle a b) :
    (swap a b * p.cycleOf a).Disjoint (offCycle p a) := by
  classical
  intro x
  by_cases h : p.SameCycle a x
  · right
    simp [offCycle_apply, h]
  · left
    have hxa : x ≠ a := fun hx => h (hx ▸ SameCycle.refl p a)
    have hxb : x ≠ b := fun hx => h (hx ▸ hab)
    simp [cycleOf_apply, h, Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Any two nonadjacent positions in one permutation cycle admit the actual
two-piece cyclic-list decomposition needed by edge insertion. -/
theorem exists_cycleList_split [Fintype α] (p : Perm α) (a b : α)
    (hab : a ≠ b) (hcycle : p.SameCycle a b)
    (hab' : p a ≠ b) (hba' : p b ≠ a) :
    ∃ l m : List α, (a :: (l ++ b :: m)).Nodup ∧
      1 ≤ l.length ∧ 1 ≤ m.length ∧
      (a :: (l ++ b :: m)).formPerm = p.cycleOf a := by
  classical
  have hmove : p a ≠ a := fun ha => hab (hcycle.eq_of_left ha)
  have hmem : a ∈ p.support := mem_support.mpr hmove
  have hpos := length_toList_pos_of_mem_support p a hmem
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (by
    intro hnil
    simp [hnil] at hpos : p.toList a ≠ [])
  have hhead := toList_getElem_zero p a hmem
  have hca : c = a := by simpa [hcs] using hhead
  subst c
  have hb : b ∈ cs := by
    have := mem_toList_iff.mpr ⟨hcycle, hmem⟩
    simpa [hcs, hab.symm] using this
  obtain ⟨l, m, rfl⟩ := List.mem_iff_append.mp hb
  have hnodup : (a :: (l ++ b :: m)).Nodup := by
    simpa [hcs] using nodup_toList p a
  have heq : (a :: (l ++ b :: m)).formPerm = p.cycleOf a := by
    rw [← hcs, formPerm_toList]
  have hl : 1 ≤ l.length := by
    by_contra! hlt
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    have h := congrArg (fun f : Perm α => f a) heq
    dsimp only at h
    rw [List.nil_append, List.formPerm_apply_head a b m hnodup,
      cycleOf_apply_self] at h
    exact hab' h.symm
  have hm : 1 ≤ m.length := by
    by_contra! hmt
    have hm0 : m = [] := List.length_eq_zero_iff.mp (by omega)
    subst m
    have h := congrArg (fun f : Perm α => f b) heq
    dsimp only at h
    rw [List.formPerm_cons_concat_apply_last, hcycle.cycleOf_apply] at h
    exact hba' h.symm
  exact ⟨l, m, hnodup, hl, hm, heq⟩

/-- Swapping two nonadjacent positions of the same cycle increases the number
of nontrivial cycles by exactly one. This is the facial splitting count. -/
theorem cycleType_card_swap_mul_of_sameCycle [Fintype α]
    (p : Perm α) (a b : α) (hab : a ≠ b) (hcycle : p.SameCycle a b)
    (hab' : p a ≠ b) (hba' : p b ≠ a) :
    (swap a b * p).cycleType.card = p.cycleType.card + 1 := by
  classical
  obtain ⟨l, m, hnodup, hl, hm, heq⟩ :=
    exists_cycleList_split p a b hab hcycle hab' hba'
  have htwo : (swap a b * p.cycleOf a).cycleType.card = 2 := by
    rw [← heq]
    exact cycleType_card_swap_mul_formPerm_split a b l m hnodup hl hm
  have hone : (p.cycleOf a).cycleType.card = 1 := by
    rw [(isCycle_cycleOf p (fun ha => hab (hcycle.eq_of_left ha))).cycleType]
    simp
  have hp := (cycleOf_disjoint_offCycle p a).cycleType_mul
  rw [cycleOf_mul_offCycle] at hp
  have hq := (swap_cycleOf_disjoint_offCycle p a b hcycle).cycleType_mul
  rw [mul_assoc, cycleOf_mul_offCycle] at hq
  rw [hq, hp, Multiset.card_add, Multiset.card_add, htwo, hone]
  omega

#print axioms cycleType_card_swap_mul_of_sameCycle

omit [DecidableEq α] in
/-- If every step of `p` stays in one `q`-cycle, entire `p`-cycles do too. -/
theorem sameCycle_of_steps [Finite α] (p q : Perm α)
    (hstep : ∀ x, q.SameCycle x (p x)) {x y : α} (hxy : p.SameCycle x y) :
    q.SameCycle x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact SameCycle.refl q x
  | succ n ih =>
    rw [pow_succ', mul_apply]
    exact ih.trans (hstep _)

/-- Inserting a formerly fixed point into one cycle preserves every old
same-cycle relation. This is the faithful-vertex invariant for edge insertion. -/
theorem sameCycle_swap_mul_of_fixed [Finite α] (p : Perm α) (a b : α)
    (hb : p b = b) {x y : α} (hxy : p.SameCycle x y) :
    (swap a b * p).SameCycle x y := by
  apply sameCycle_of_steps p _ _ hxy
  intro z
  by_cases hza : p z = a
  · have hfirst : (swap a b * p) z = b := by simp [mul_apply, hza]
    have hsecond : (swap a b * p) b = a := by simp [mul_apply, hb]
    rw [hza]
    refine ⟨2, ?_⟩
    change ((swap a b * p) ^ (2 : ℕ)) z = a
    rw [pow_two, mul_apply, hfirst, hsecond]
  · by_cases hzb : p z = b
    · have hzeq : z = b := p.injective (hzb.trans hb.symm)
      rw [hzeq, hb]
    · exact ⟨1, by simp [mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]⟩

/-- Inserting a fixed point `b` immediately before `a` in an actual cyclic
order produces a cyclic order on the enlarged set. -/
theorem isCycleOn_swap_mul_insert [Finite α] (p : Perm α) (S : Set α)
    (hp : p.IsCycleOn S) (a b : α) (ha : a ∈ S) (hb : p b = b) :
    (swap a b * p).IsCycleOn (insert b S) := by
  have hmap : Set.MapsTo (swap a b * p) (insert b S) (insert b S) := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      simpa [mul_apply, hb] using (Set.mem_insert_of_mem b ha)
    · have hpx : p x ∈ S := hp.1.mapsTo hx
      by_cases hpa : p x = a
      · simp [mul_apply, hpa]
      · by_cases hpb : p x = b
        · simpa [mul_apply, hpb] using (Set.mem_insert_of_mem b ha)
        · simp only [mul_apply, Equiv.swap_apply_of_ne_of_ne hpa hpb]
          exact Set.mem_insert_of_mem b hpx
  refine ⟨(Set.toFinite _).injOn_iff_bijOn_of_mapsTo hmap |>.mp
    (swap a b * p).injective.injOn, ?_⟩
  intro x hx y hy
  have hba : (swap a b * p).SameCycle b a :=
    ⟨1, by simp [mul_apply, hb]⟩
  have hax (z : α) (hz : z ∈ insert b S) : (swap a b * p).SameCycle a z := by
    rcases hz with rfl | hz
    · exact hba.symm
    · exact sameCycle_swap_mul_of_fixed p a b hb (hp.2 ha hz)
  exact (hax x hx).symm.trans (hax y hy)

#print axioms isCycleOn_swap_mul_insert

omit [DecidableEq α] in
/-- An intertwining map transports actual permutation orbits. -/
theorem sameCycle_map {β : Type*} [Finite α] (p : Perm α) (q : Perm β)
    (f : α → β) (hf : ∀ x, q (f x) = f (p x)) {x y : α}
    (hxy : p.SameCycle x y) : q.SameCycle (f x) (f y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hp (k : ℕ) : (q ^ k) (f x) = f ((p ^ k) x) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [pow_succ', mul_apply, ih, hf]
  exact ⟨n, by simpa [hn] using hp n⟩

/-- Swapping two points in the same fibre preserves the fibre map. -/
theorem map_swap_eq {β : Type*} (f : α → β) (a b x : α) (hab : f a = f b) :
    f (swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa using hab
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Inserting a fresh fixed point into a nontrivial cycle leaves the number
of nontrivial cycles unchanged. -/
theorem cycleType_card_swap_mul_of_fixed [Fintype α] (p : Perm α) (a b : α)
    (ha : p a ≠ a) (hb : p b = b) :
    (swap a b * p).cycleType.card = p.cycleType.card := by
  classical
  have hab : a ≠ b := fun h => ha (by simpa [h] using hb)
  have hmem : a ∈ p.support := mem_support.mpr ha
  have hn : p.toList a ≠ [] := by
    intro hnil
    have hpos := length_toList_pos_of_mem_support p a hmem
    rw [hnil] at hpos
    contradiction
  obtain ⟨c, l, hcl⟩ := List.exists_cons_of_ne_nil hn
  have hca : c = a := by simpa [hcl] using toList_getElem_zero p a hmem
  subst c
  have hnodup : (a :: l).Nodup := by simpa [hcl] using nodup_toList p a
  have hbnot : b ∉ a :: l := by
    intro hbl
    have hs : p.SameCycle a b := (mem_toList_iff.mp (hcl ▸ hbl)).1
    exact hab (hs.eq_of_right hb)
  have hnew : (b :: a :: l).Nodup := List.nodup_cons.mpr ⟨hbnot, hnodup⟩
  have heq : swap a b * p.cycleOf a = (b :: a :: l).formPerm := by
    rw [← formPerm_toList, hcl, List.formPerm_cons_cons, Equiv.swap_comm a b]
  have hone : (swap a b * p.cycleOf a).cycleType.card = 1 := by
    rw [heq, (List.isCycle_formPerm hnew (by simp)).cycleType]
    simp
  have hold : (p.cycleOf a).cycleType.card = 1 := by
    rw [(isCycle_cycleOf p ha).cycleType]
    simp
  have hd : (swap a b * p.cycleOf a).Disjoint (offCycle p a) := by
    intro x
    by_cases hx : p.SameCycle a x
    · right
      simp [offCycle_apply, hx]
    · by_cases hxb : x = b
      · right
        simp [offCycle_apply, hxb, hb]
      · left
        have hxa : x ≠ a := fun h => hx (h ▸ SameCycle.refl p a)
        simp [cycleOf_apply, hx, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hq := hd.cycleType_mul
  rw [mul_assoc, cycleOf_mul_offCycle] at hq
  have hp := (cycleOf_disjoint_offCycle p a).cycleType_mul
  rw [cycleOf_mul_offCycle] at hp
  simp only [hq, hp, Multiset.card_add, hone, hold]

/-- Cycle type is invariant under an equivalence of the underlying dart type. -/
theorem cycleType_permCongr [Fintype α] {β : Type*} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Perm α) : (e.permCongr p).cycleType = p.cycleType := by
  classical
  let t : α ≃ {b : β // True} :=
    { toFun := fun a => ⟨e a, trivial⟩
      invFun := fun b => e.symm b.val
      left_inv := fun a => e.symm_apply_apply a
      right_inv := fun b => Subtype.ext (e.apply_symm_apply b.val) }
  have ht : e.permCongr p = p.extendDomain t := by
    ext b
    have hb : b = (t (e.symm b)).val := by simp [t]
    conv_rhs => rw [hb, Equiv.Perm.extendDomain_apply_image]
    simp [t]
  rw [ht, cycleType_extendDomain]

/-- Adding a summand of fixed points does not change the nontrivial cycle type. -/
theorem cycleType_sumCongr_refl [Fintype α] {β : Type*} [Fintype β] [DecidableEq β]
    (p : Perm α) : Equiv.Perm.cycleType (Equiv.sumCongr p (Equiv.refl β)) = p.cycleType := by
  classical
  let t : α ≃ {x : α ⊕ β // x.isLeft} :=
    { toFun := fun a => ⟨Sum.inl a, rfl⟩
      invFun := fun x => x.val.getLeft x.property
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Subtype.ext
        cases x with | mk x hx => cases x <;> simp_all }
  have ht : Equiv.sumCongr p (Equiv.refl β) = p.extendDomain t := by
    ext x
    cases x with
    | inl a =>
      change Sum.inl (p a) = p.extendDomain t (t a).val
      rw [Equiv.Perm.extendDomain_apply_image]
      rfl
    | inr b =>
      rw [Equiv.Perm.extendDomain_apply_not_subtype]
      · rfl
      · simp
  rw [ht, cycleType_extendDomain]

#print axioms cycleType_card_swap_mul_of_fixed
#print axioms cycleType_permCongr
#print axioms cycleType_sumCongr_refl

/-- Facial permutation after adding the two orientations of a chord. -/
def chordPerm (p : Perm α) (a b : α) : Perm (α ⊕ Bool) :=
  swap (Sum.inl b) (Sum.inr true) *
    (swap (Sum.inl a) (Sum.inr false) *
      Equiv.sumCongr p (swap false true))

/-- The new facial permutation is two fixed-point insertions followed by
one transposition inside the original face cycle. -/
theorem chordPerm_factorization (p : Perm α) (a b : α) (hab : a ≠ b) :
    chordPerm p a b = swap (Sum.inl a) (Sum.inl b) *
      (swap (Sum.inl b) (Sum.inr true) *
        (swap (Sum.inl a) (Sum.inr false) *
          Equiv.sumCongr p (Equiv.refl Bool))) := by
  ext x
  cases x with
  | inl x =>
    by_cases hpa : p x = a <;> by_cases hpb : p x = b <;>
      simp_all [chordPerm, mul_apply, Equiv.swap_apply_def]
  | inr x =>
    cases x <;> simp_all [chordPerm, mul_apply, Equiv.swap_apply_def]

/-- Inserting a chord between two distinct positions of one nontrivial face
increases the actual number of facial cycles by exactly one. -/
theorem cycleType_card_chordPerm [Fintype α] (p : Perm α) (a b : α)
    (hab : a ≠ b) (hcycle : p.SameCycle a b) (ha : p a ≠ a) :
    (chordPerm p a b).cycleType.card = p.cycleType.card + 1 := by
  classical
  let p₀ : Perm (α ⊕ Bool) := Equiv.sumCongr p (Equiv.refl Bool)
  let p₁ := swap (Sum.inl a) (Sum.inr false) * p₀
  let p₂ := swap (Sum.inl b) (Sum.inr true) * p₁
  have hb : p b ≠ b := fun hb => hab (hcycle.eq_of_right hb)
  have hp₀N : p₀ (Sum.inr false) = Sum.inr false := rfl
  have hp₀a : p₀ (Sum.inl a) ≠ Sum.inl a := by simpa [p₀] using ha
  have hp₁M : p₁ (Sum.inr true) = Sum.inr true := by
    simp [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁b : p₁ (Sum.inl b) ≠ Sum.inl b := by
    by_cases hpa : p b = a <;> simp_all [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁N : p₁ (Sum.inr false) = Sum.inl a := by simp [p₁, p₀, mul_apply]
  have hp₂N : p₂ (Sum.inr false) = Sum.inl a := by
    simp [p₂, mul_apply, hp₁N, Equiv.swap_apply_def, hab]
  have hp₂M : p₂ (Sum.inr true) = Sum.inl b := by simp [p₂, mul_apply, hp₁M]
  have hp₂a : p₂ (Sum.inl a) ≠ Sum.inl b := by
    intro h
    have := p₂.injective (h.trans hp₂M.symm)
    contradiction
  have hp₂b : p₂ (Sum.inl b) ≠ Sum.inl a := by
    intro h
    have := p₂.injective (h.trans hp₂N.symm)
    contradiction
  have hcycle₀ : p₀.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_map p p₀ Sum.inl (fun _ => rfl) hcycle
  have hcycle₁ : p₁.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_swap_mul_of_fixed p₀ _ _ hp₀N hcycle₀
  have hcycle₂ : p₂.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_swap_mul_of_fixed p₁ _ _ hp₁M hcycle₁
  have hcount₀ : p₀.cycleType.card = p.cycleType.card := by
    rw [cycleType_sumCongr_refl (β := Bool)]
  have hcount₁ : p₁.cycleType.card = p₀.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₀ _ _ hp₀a hp₀N
  have hcount₂ : p₂.cycleType.card = p₁.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₁ _ _ hp₁b hp₁M
  rw [chordPerm_factorization p a b hab]
  change (swap (Sum.inl a) (Sum.inl b) * p₂).cycleType.card = _
  rw [cycleType_card_swap_mul_of_sameCycle p₂ _ _ (by simpa using hab)
    hcycle₂ hp₂a hp₂b, hcount₂, hcount₁, hcount₀]

#print axioms cycleType_card_chordPerm

end PlaneTopology.PlanePermutationSurgery
