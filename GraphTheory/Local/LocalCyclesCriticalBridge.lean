import GraphTheory.Local.LocalCyclesSurgeryBridge

/-! Weighted costs of actual cyclic LOCAL outputs and critical-graph surgery.
This file connects the geometric local-rule model to the endpoint cost argument.
-/

noncomputable section

namespace LocalCyclesCriticalBridge

open LocalCycles LocalCyclesReflection LocalCyclesSurgeryBridge
open scoped BigOperators

variable {n : ℕ} [NeZero n] {Q A : Type*} {E : Q → Q → Prop}

theorem right_n (i : Fin n) : right i n = i := by
  apply Fin.ext
  simp [right, Nat.mod_eq_of_lt i.isLt]

/-- Clockwise successor is an actual permutation, including the wraparound. -/
def nextPerm : Equiv.Perm (Fin n) where
  toFun i := right i 1
  invFun i := right i (n - 1)
  left_inv i := by
    change right (right i 1) (n - 1) = i
    rw [LocalCyclesSurgeryBridge.right_add]
    have h : 1 + (n - 1) = n := by have := NeZero.pos n; omega
    rw [h, right_n]
  right_inv i := by
    change right (right i (n - 1)) 1 = i
    rw [LocalCyclesSurgeryBridge.right_add]
    have h : n - 1 + 1 = n := by have := NeZero.pos n; omega
    rw [h, right_n]

/-- Total vertex cost of the actual clockwise edge-state sequence. -/
def runCost (c : Q → Q → ℝ) (states : Fin n → Q) : ℝ :=
  ∑ i : Fin n, c (states i) (states (right i 1))

theorem runCost_reduced (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ)
    (states : Fin n → Q) :
    runCost (reduced c B p) states = runCost c states - B * n := by
  have hp : (∑ i : Fin n, p (states (right i 1))) = ∑ i : Fin n, p (states i) :=
    Equiv.sum_comp (nextPerm (n := n)) (fun i => p (states i))
  simp only [runCost, reduced, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- At an exact mean bound, every transition of the actual output is tight. -/
theorem actual_run_tight (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ)
    (states : Fin n → Q)
    (hfeasible : ∀ i, 0 ≤ reduced c B p (states i) (states (right i 1)))
    (hcost : runCost c states ≤ B * n) :
    ∀ i, reduced c B p (states i) (states (right i 1)) = 0 := by
  have htotal : runCost (reduced c B p) states ≤ 0 := by
    rw [runCost_reduced]
    linarith
  intro i
  have hi : reduced c B p (states i) (states (right i 1)) ≤
      runCost (reduced c B p) states :=
    Finset.single_le_sum (fun j _ => hfeasible j) (Finset.mem_univ i)
  exact le_antisymm (le_trans hi htotal) (hfeasible i)

/-- Tight relation retains legality as well as zero reduced cost. -/
def tightRelation (E : Q → Q → Prop) (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ) :
    Q → Q → Prop := fun u v => E u v ∧ reduced c B p u v = 0

theorem tight_validity (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ)
    (states : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1)))
    (hfeasible : ∀ u v, E u v → 0 ≤ reduced c B p u v)
    (hcost : runCost c states ≤ B * n) :
    ∀ i, tightRelation E c B p (states i) (states (right i 1)) := by
  have hz := actual_run_tight c B p states
    (fun i => hfeasible _ _ (hvalid i)) hcost
  exact fun i => ⟨hvalid i, hz i⟩

/-- Four-way eventual filling between a state and its mirror. -/
def MirrorFlexible (E : Q → Q → Prop) (rev : Q → Q) (q : Q) : Prop :=
  ∃ K : ℕ, ∀ m ≥ K,
    (∃ z : Walk E q q, z.length = m) ∧
    (∃ z : Walk E q (rev q), z.length = m) ∧
    (∃ z : Walk E (rev q) q, z.length = m) ∧
    (∃ z : Walk E (rev q) (rev q), z.length = m)

/-- Actual finite-family cost bounds force the geometric surgery witnesses into
one tight relation. The common feasible potential is still an explicit hypothesis. -/
theorem weighted_local_surgery [Fintype Q] (F : Rule r A Q) (rev : Q → Q)
    (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ) (I : Input n A)
    (P : Packing n r (Fintype.card Q + 1))
    (root anchor : Fin (Fintype.card Q + 1)) (reflectEnd : Fin n)
    (hleft : r ≤ (P.root root).val)
    (hright : (P.root root).val + r ≤ reflectEnd.val)
    (hcenter : reflectEnd.val = 2 * (P.root root).val + 1)
    (hanchorLeft : reflectEnd.val + r < (P.root anchor).val)
    (hanchorRight : (P.root anchor).val + r < n)
    (hedge : outputLeft F I (right (P.root root) 1) = rev (outputRight F I (P.root root)))
    (hfeasible : ∀ u v, E u v → 0 ≤ reduced c B p u v)
    (hvalid : ∀ j, E (outputRight F I j) (outputRight F I (right j 1)))
    (hreflected : ∀ j, E (outputRight F (reflect I reflectEnd) j)
      (outputRight F (reflect I reflectEnd) (right j 1)))
    (hmoved : ∀ i j, E (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) j)
      (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) (right j 1)))
    (hcost : runCost c (outputRight F I) ≤ B * n)
    (hcostReflect : runCost c (outputRight F (reflect I reflectEnd)) ≤ B * n)
    (hcostMoved : ∀ i, runCost c (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i))) ≤ B * n) :
    MirrorFlexible (tightRelation E c B p) rev (outputRight F I (P.root root)) := by
  exact local_surgery_flexible F rev I P root anchor reflectEnd hleft hright hcenter
    hanchorLeft hanchorRight hedge
    (tight_validity c B p _ hvalid hfeasible hcost)
    (tight_validity c B p _ hreflected hfeasible hcostReflect)
    (fun i => tight_validity c B p _ (hmoved i) hfeasible (hcostMoved i))

/-- Membership of the strongly connected component of a specified state. -/
def InComponent (E : Q → Q → Prop) (root v : Q) : Prop :=
  Nonempty (Walk E root v) ∧ Nonempty (Walk E v root)

theorem component_refl (q : Q) : InComponent E q q := ⟨⟨.nil q⟩, ⟨.nil q⟩⟩

theorem component_trans {u v w : Q} (huv : InComponent E u v)
    (hvw : InComponent E v w) : InComponent E u w := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := huv
  obtain ⟨⟨c⟩, ⟨d⟩⟩ := hvw
  exact ⟨⟨a.append c⟩, ⟨d.append b⟩⟩

/-- Reverse a walk using the automaton involution on its states. -/
def mirrorWalk (rev : Q → Q) (hrev : ∀ u v, E u v → E (rev v) (rev u)) :
    {u v : Q} → Walk E u v → Walk E (rev v) (rev u)
  | _, _, .nil u => .nil (rev u)
  | _, _, @Walk.cons _ _ u v _ h tail =>
    (mirrorWalk rev hrev tail).append (.cons (hrev u v h) (.nil (rev u)))

theorem component_mirror (rev : Q → Q)
    (hrev : ∀ u v, E u v → E (rev v) (rev u)) {root v : Q}
    (hm : InComponent E root (rev root)) (hv : InComponent E root v) :
    InComponent E root (rev v) := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := hv
  exact component_trans hm ⟨⟨mirrorWalk rev hrev b⟩, ⟨mirrorWalk rev hrev a⟩⟩

theorem flexible_component_mirror (rev : Q → Q)
    (hrev : ∀ u v, E u v → E (rev v) (rev u)) {root v : Q}
    (hf : MirrorFlexible E rev root) (hv : InComponent E root v) :
    InComponent E root (rev v) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨_, ⟨a, _⟩, ⟨b, _⟩, _⟩ := hK K le_rfl
  exact component_mirror rev hrev ⟨⟨a⟩, ⟨b⟩⟩ hv

theorem actual_run_component (states : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1))) (i j : Fin n) :
    InComponent E (states i) (states j) := by
  obtain ⟨a, _⟩ := run_path_between states hvalid i j
  obtain ⟨b, _⟩ := run_path_between states hvalid j i
  exact ⟨⟨a⟩, ⟨b⟩⟩

/-- A shared protected state puts every state of a modified run in the original
component. No assumptions about unobserved states of the automaton are needed. -/
theorem shared_state_component (states other : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1)))
    (hother : ∀ i, E (other i) (other (right i 1)))
    (root anchor moved : Fin n) (hshared : other moved = states anchor) :
    ∀ j, InComponent E (states root) (other j) := by
  intro j
  have h := actual_run_component other hother moved j
  rw [hshared] at h
  exact component_trans (actual_run_component states hvalid root anchor) h

/-- The infimum construction only needs to control the root component; states
outside it are harmless, even if their cycles have smaller mean. -/
theorem component_potential (c : Q → Q → ℝ) (B : ℝ) (root : Q)
    (hmean : ∀ a : Walk E root root, B * a.length ≤ a.cost c) :
    ∃ p : Q → ℝ, ∀ u v, E u v → InComponent E root u →
      InComponent E root v → 0 ≤ reduced c B p u v := by
  let d := reduced c B (fun _ => 0)
  let costs (v : Q) : Set ℝ := {x | ∃ a : Walk E root v, a.cost d = x}
  have hne (v : Q) (hv : InComponent E root v) : (costs v).Nonempty := by
    obtain ⟨a⟩ := hv.1
    exact ⟨a.cost d, a, rfl⟩
  have hbounded (v : Q) (hv : InComponent E root v) : BddBelow (costs v) := by
    obtain ⟨b⟩ := hv.2
    refine ⟨-b.cost d, ?_⟩
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    have h : 0 ≤ (a.append b).cost d := by
      dsimp only [d]
      rw [Walk.cost_reduced]
      have hm := hmean (a.append b)
      linarith
    rw [Walk.cost_append] at h
    linarith
  refine ⟨fun v => sInf (costs v), ?_⟩
  intro u v huv hu hv
  have hbound : sInf (costs v) - d u v ≤ sInf (costs u) := by
    apply le_csInf (hne u hu)
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    let e : Walk E u v := .cons huv (.nil v)
    have he : e.cost d = d u v := by simp [e, Walk.cost]
    have h : sInf (costs v) ≤ (a.append e).cost d :=
      csInf_le (hbounded v hv) ⟨a.append e, rfl⟩
    rw [Walk.cost_append, he] at h
    linarith
  dsimp [d, reduced] at hbound ⊢
  linarith

theorem symmetric_component_potential (rev : Q → Q) (hinv : Function.Involutive rev)
    (c : Q → Q → ℝ) (B : ℝ) (root : Q)
    (hrev : ∀ u v, E u v → E (rev v) (rev u))
    (hsym : ∀ u v, E u v → c (rev v) (rev u) = c u v)
    (hflex : MirrorFlexible E rev root)
    (hmean : ∀ a : Walk E root root, B * a.length ≤ a.cost c) :
    ∃ p : Q → ℝ, (∀ u, p (rev u) = -p u) ∧
      (∀ u v, E u v → InComponent E root u →
        InComponent E root v → 0 ≤ reduced c B p u v) := by
  obtain ⟨p, hp⟩ := component_potential c B root hmean
  refine ⟨mirrorPotential rev p, mirrorPotential_antisymm rev hinv p, ?_⟩
  intro u v huv hu hv
  rw [reduced_mirror_average rev c B p u v (hsym u v huv)]
  exact div_nonneg (add_nonneg (hp u v huv hu hv)
    (hp _ _ (hrev u v huv) (flexible_component_mirror rev hrev hflex hv)
      (flexible_component_mirror rev hrev hflex hu))) (by norm_num)

/-- An antisymmetric potential makes tightness itself invariant under reversal. -/
theorem tight_reversal (rev : Q → Q) (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ)
    (hp : ∀ u, p (rev u) = -p u)
    (hrev : ∀ u v, E u v → E (rev v) (rev u))
    (hsym : ∀ u v, E u v → c (rev v) (rev u) = c u v)
    {u v : Q} (h : tightRelation E c B p u v) :
    tightRelation E c B p (rev v) (rev u) := by
  refine ⟨hrev u v h.1, ?_⟩
  have hz := h.2
  simp only [reduced, hp, hsym u v h.1] at hz ⊢
  linarith

theorem component_tight_validity (c : Q → Q → ℝ) (B : ℝ) (p : Q → ℝ)
    (root : Q) (states : Fin n → Q)
    (hvalid : ∀ i, E (states i) (states (right i 1)))
    (hcomponent : ∀ i, InComponent E root (states i))
    (hfeasible : ∀ u v, E u v → InComponent E root u →
      InComponent E root v → 0 ≤ reduced c B p u v)
    (hcost : runCost c states ≤ B * n) :
    ∀ i, tightRelation E c B p (states i) (states (right i 1)) := by
  have hz := actual_run_tight c B p states
    (fun i => hfeasible _ _ (hvalid i) (hcomponent i) (hcomponent (right i 1))) hcost
  exact fun i => ⟨hvalid i, hz i⟩

/-- A mean lower bound at one state of an actual cyclic output bounds its entire
cost, without identifying the custom walk traversal with a Finset sum. -/
theorem actual_run_cost_lower (c : Q → Q → ℝ) (B : ℝ) (states : Fin n → Q)
    (root : Fin n) (hvalid : ∀ i, E (states i) (states (right i 1)))
    (hmean : ∀ a : Walk E (states root) (states root), B * a.length ≤ a.cost c) :
    B * n ≤ runCost c states := by
  obtain ⟨p, hp⟩ := component_potential c B (states root) hmean
  have hc := actual_run_component states hvalid root
  have ht : 0 ≤ runCost (reduced c B p) states :=
    Finset.sum_nonneg (fun i _ => hp _ _ (hvalid i) (hc i) (hc (right i 1)))
  rw [runCost_reduced] at ht
  linarith

/-- All relocations stay in the same output component because either the chosen
root moves with its entire view or another protected root remains unchanged. -/
theorem relocated_run_component [Fintype Q] (F : Rule r A Q) (I : Input n A)
    (P : Packing n r (Fintype.card Q + 1)) (root i : Fin (Fintype.card Q + 1))
    (hvalid : ∀ j, E (outputRight F I j) (outputRight F I (right j 1)))
    (hmoved : ∀ j, E (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) j)
      (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) (right j 1))) :
    ∀ j, InComponent E (outputRight F I (P.root root))
      (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) j) := by
  by_cases hi : i = root
  · subst i
    have hshared := outputRight_relocate F I (P.lo root) (P.hi root)
      (P.movedRoot root) (P.ordered root) (P.leftMargin root) (P.rightMargin root)
    rw [P.rootIdentity root] at hshared
    exact shared_state_component _ _ hvalid hmoved (P.root root) (P.root root)
      (P.movedRoot root) hshared
  · obtain ⟨hl, hr, hout⟩ := P.otherMargins i root hi
    have hshared := outputRight_relocate_remote F I (P.lo i) (P.hi i)
      (P.root root) (P.ordered i) hl hr hout
    exact shared_state_component _ _ hvalid hmoved (P.root root) (P.root root)
      (P.root root) hshared

/-- Weighted endpoint necessity for the actual finite surgery family. The common
potential is now a conclusion: the semantic mean lower bound on mirror-flexible
components supplies it on the single component shared by every modified run. -/
theorem critical_local_surgery [Fintype Q] (F : Rule r A Q) (rev : Q → Q)
    (c : Q → Q → ℝ) (B : ℝ) (I : Input n A)
    (hinv : Function.Involutive rev)
    (hrev : ∀ u v, E u v → E (rev v) (rev u))
    (hsym : ∀ u v, E u v → c (rev v) (rev u) = c u v)
    (P : Packing n r (Fintype.card Q + 1))
    (root anchor : Fin (Fintype.card Q + 1)) (reflectEnd : Fin n)
    (hleft : r ≤ (P.root root).val)
    (hright : (P.root root).val + r ≤ reflectEnd.val)
    (hcenter : reflectEnd.val = 2 * (P.root root).val + 1)
    (hanchorLeft : reflectEnd.val + r < (P.root anchor).val)
    (hanchorRight : (P.root anchor).val + r < n)
    (hedge : outputLeft F I (right (P.root root) 1) = rev (outputRight F I (P.root root)))
    (hmean : ∀ q, MirrorFlexible E rev q →
      ∀ a : Walk E q q, B * a.length ≤ a.cost c)
    (hvalid : ∀ j, E (outputRight F I j) (outputRight F I (right j 1)))
    (hreflected : ∀ j, E (outputRight F (reflect I reflectEnd) j)
      (outputRight F (reflect I reflectEnd) (right j 1)))
    (hmoved : ∀ i j, E (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) j)
      (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i)) (right j 1)))
    (hcost : runCost c (outputRight F I) ≤ B * n)
    (hcostReflect : runCost c (outputRight F (reflect I reflectEnd)) ≤ B * n)
    (hcostMoved : ∀ i, runCost c (outputRight F (relocate I (P.lo i) (P.hi i) (P.ordered i))) ≤ B * n) :
    ∃ p : Q → ℝ, (∀ u, p (rev u) = -p u) ∧
      (∀ u v, E u v → InComponent E (outputRight F I (P.root root)) u →
        InComponent E (outputRight F I (P.root root)) v → 0 ≤ reduced c B p u v) ∧
      MirrorFlexible (tightRelation E c B p) rev (outputRight F I (P.root root)) := by
  have hflex : MirrorFlexible E rev (outputRight F I (P.root root)) :=
    local_surgery_flexible F rev I P root anchor reflectEnd hleft hright hcenter
      hanchorLeft hanchorRight hedge hvalid hreflected hmoved
  obtain ⟨p, hpanti, hp⟩ := symmetric_component_potential rev hinv c B
    (outputRight F I (P.root root)) hrev hsym hflex (hmean _ hflex)
  have hc : ∀ j, InComponent E (outputRight F I (P.root root)) (outputRight F I j) :=
    actual_run_component _ hvalid (P.root root)
  have hcr : ∀ j, InComponent E (outputRight F I (P.root root))
      (outputRight F (reflect I reflectEnd) j) :=
    shared_state_component _ _ hvalid hreflected (P.root root) (P.root anchor)
      (P.root anchor)
      (outputRight_reflect_remote F I reflectEnd (P.root anchor) hanchorLeft hanchorRight)
  have hcm := fun i => relocated_run_component F I P root i hvalid (hmoved i)
  refine ⟨p, hpanti, hp, ?_⟩
  exact local_surgery_flexible F rev I P root anchor reflectEnd hleft hright hcenter
    hanchorLeft hanchorRight hedge
    (component_tight_validity c B p _ _ hvalid hc hp hcost)
    (component_tight_validity c B p _ _ hreflected hcr hp hcostReflect)
    (fun i => component_tight_validity c B p _ _ (hmoved i) (hcm i) hp (hcostMoved i))

end LocalCyclesCriticalBridge

#print axioms LocalCyclesCriticalBridge.runCost_reduced
#print axioms LocalCyclesCriticalBridge.actual_run_tight

#print axioms LocalCyclesCriticalBridge.weighted_local_surgery
#print axioms LocalCyclesCriticalBridge.component_potential
#print axioms LocalCyclesCriticalBridge.critical_local_surgery
