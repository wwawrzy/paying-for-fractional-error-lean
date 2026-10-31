import Paper.Solver.LocalSearch.IntegralFractionalOptima
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.IntervalCases

/-!
# Split graph example for the fixed-surface integrality gap

This file records the concrete finite graph from `sc:gap` and proves the
finite core-count and uniform-weight identities used in its hand proof. It
also verifies that the uniform core assignment is a feasible fractional
dominating vector of cost two. It also proves
`gapGraph.dominationNumber = 15` and the strict factor-seven separation.
-/

namespace Paper.SplitGraphGap

open Paper.SevenFoundation
open scoped BigOperators

/-- The 28-vertex clique core. -/
abbrev Core := Fin 28

/-- One leaf type for each 14-element subset of the core. -/
abbrev Leaf := {S : Finset Core // S.card = 14}

/-- Core vertices and leaf vertices are disjoint by construction. -/
abbrev Vertex := Core ⊕ Leaf

/-- The split graph: the core is a clique and a leaf is adjacent exactly to
the core vertices in its indexing set. There are no leaf-leaf edges. -/
def gapGraph : SimpleGraph Vertex where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inl b => a ≠ b
    | Sum.inl a, Sum.inr S => a ∈ S.val
    | Sum.inr S, Sum.inl a => a ∈ S.val
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b => exact Ne.symm
      | inr S => exact id
    | inr S =>
      cases y with
      | inl a => exact id
      | inr T => exact id
  loopless := by
    refine ⟨fun x h => ?_⟩
    cases x with
    | inl a => exact h rfl
    | inr S => exact h

/-- Decidable adjacency, needed by the ordinary covering instance. -/
instance decidableAdj : DecidableRel gapGraph.Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [gapGraph] <;> infer_instance

@[simp]
theorem core_adj_iff (a b : Core) :
    gapGraph.Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b := Iff.rfl

@[simp]
theorem core_leaf_adj_iff (a : Core) (S : Leaf) :
    gapGraph.Adj (Sum.inl a) (Sum.inr S) ↔ a ∈ S.val := Iff.rfl

@[simp]
theorem leaf_core_adj_iff (S : Leaf) (a : Core) :
    gapGraph.Adj (Sum.inr S) (Sum.inl a) ↔ a ∈ S.val := Iff.rfl

@[simp]
theorem no_leaf_leaf_edge (S T : Leaf) :
    ¬ gapGraph.Adj (Sum.inr S) (Sum.inr T) := id

/-- The number of 14-subsets avoiding a chosen j-element core set is the
binomial coefficient appearing in the paper's domination lower bound. -/
theorem unhit_fourteen_count (D : Finset Core) :
    ((Finset.univ \ D).powersetCard 14).card = Nat.choose (28 - D.card) 14 := by
  rw [Finset.card_powersetCard]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  simp

/-- The exact elementary inequality behind the lower bound: j selected core
vertices plus all 14-subsets avoiding them total at least 15. -/
theorem core_plus_unhit_fourteen_bound (j : ℕ) :
    j + Nat.choose (28 - j) 14 ≥ 15 := by
  by_cases hj : j ≤ 13
  · have hc := Nat.choose_le_choose 14 (show 15 ≤ 28 - j by omega)
    have hbase : Nat.choose 15 14 = 15 := Nat.choose_succ_self_right 14
    rw [hbase] at hc
    omega
  · by_cases he : j = 14
    · subst j
      norm_num
    · omega

/-- Restatement in terms of an actual chosen core subset. -/
theorem core_subset_plus_unhit_fourteen_bound (D : Finset Core) :
    D.card + ((Finset.univ \ D).powersetCard 14).card ≥ 15 := by
  rw [unhit_fourteen_count]
  exact core_plus_unhit_fourteen_bound D.card

/-- Uniform weight 1/14 on a leaf's 14 core neighbors has exactly unit mass. -/
theorem uniform_weight_covers_leaf_index (S : Finset Core) (hS : S.card = 14) :
    (∑ z ∈ S, (1 / 14 : ℝ)) = 1 := by
  simp [hS]

/-- Uniform weight 1/14 on the entire 28-vertex core has total mass two. -/
theorem uniform_weight_core_mass :
    (∑ z : Core, (1 / 14 : ℝ)) = 2 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  norm_num

/-- The paper's proposed fractional assignment, expressed before the graph
closed-neighborhood bridge: unit coverage on each 14-subset and total core
mass two. -/
theorem uniform_assignment_core_facts :
    (∀ S : Finset Core, S.card = 14 →
      (∑ z ∈ S, (1 / 14 : ℝ)) = 1) ∧
    (∑ z : Core, (1 / 14 : ℝ)) = 2 := by
  exact ⟨fun S hS => uniform_weight_covers_leaf_index S hS,
    uniform_weight_core_mass⟩

/-- The core vertices, viewed as a subset of the disjoint union vertex type. -/
def coreVertices : Finset Vertex := Finset.univ.image (fun z : Core => Sum.inl z)

/-- The core vertices indexed by a particular subset. -/
def liftedCoreSet (S : Finset Core) : Finset Vertex :=
  S.image (fun z => Sum.inl z)

/-- The candidate fractional dominating vector: mass `1/14` on each core
vertex and zero on every leaf. -/
noncomputable def uniformWeight : Vertex → ℝ
  | Sum.inl _ => 1 / 14
  | Sum.inr _ => 0

theorem uniformWeight_nonneg (v : Vertex) : 0 ≤ uniformWeight v := by
  cases v <;> simp [uniformWeight] <;> norm_num

theorem uniformWeight_coreVertices_mass :
    (∑ v ∈ coreVertices, uniformWeight v) = 2 := by
  rw [coreVertices, Finset.sum_image (by
    intro a ha b hb hab
    exact Sum.inl.inj hab)]
  simpa [uniformWeight] using uniform_weight_core_mass

theorem uniformWeight_liftedCoreSet_mass (S : Finset Core) :
    (∑ v ∈ liftedCoreSet S, uniformWeight v) =
      (∑ z ∈ S, (1 / 14 : ℝ)) := by
  rw [liftedCoreSet, Finset.sum_image (by
    intro a ha b hb hab
    exact Sum.inl.inj hab)]
  simp [uniformWeight]

theorem coreVertices_subset_closed_core (a : Core) :
    coreVertices ⊆ closed gapGraph (Sum.inl a) := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  apply (mem_closed gapGraph (Sum.inl b) (Sum.inl a)).2
  rcases eq_or_ne b a with h | h
  · exact Or.inl (congrArg Sum.inl h)
  · exact Or.inr ((core_adj_iff a b).2 h.symm)

theorem liftedCoreSet_subset_closed_leaf (S : Leaf) :
    liftedCoreSet S.val ⊆ closed gapGraph (Sum.inr S) := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  apply (mem_closed gapGraph (Sum.inl a) (Sum.inr S)).2
  exact Or.inr ((leaf_core_adj_iff S a).2 ha)

/-- The core-supported assignment covers every closed neighborhood. At a core
vertex its whole core mass is present; at a leaf its indexing 14-set has unit
mass. -/
theorem uniformWeight_feasible :
    feasible (ordinary gapGraph) uniformWeight := by
  refine ⟨uniformWeight_nonneg, ?_, ?_⟩
  · intro v hv
    exact False.elim (hv (Finset.mem_univ v))
  · intro r hr
    cases r with
    | inl a =>
        change 1 ≤ ∑ v ∈ closed gapGraph (Sum.inl a), uniformWeight v
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg
          (coreVertices_subset_closed_core a)
          (fun v _ _ => uniformWeight_nonneg v)
        rw [uniformWeight_coreVertices_mass] at hsum
        linarith
    | inr S =>
        change 1 ≤ ∑ v ∈ closed gapGraph (Sum.inr S), uniformWeight v
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg
          (liftedCoreSet_subset_closed_leaf S)
          (fun v _ _ => uniformWeight_nonneg v)
        rw [uniformWeight_liftedCoreSet_mass, uniform_weight_covers_leaf_index S.val S.property]
          at hsum
        exact hsum

/-- The feasible assignment has total fractional cost exactly two. -/
theorem uniformWeight_cost : cost (ordinary gapGraph) uniformWeight = 2 := by
  rw [ordinary_cost]
  rw [Fintype.sum_sum_type]
  simp only [uniformWeight]
  rw [uniform_weight_core_mass]
  simp

/-- The split graph has fractional domination number at most two. -/
theorem fractionalNumber_le_two : fractionalNumber gapGraph ≤ 2 := by
  unfold fractionalNumber
  apply csInf_le (feasibleCosts_bddBelow gapGraph)
  refine ⟨uniformWeight, uniformWeight_feasible, ?_⟩
  exact uniformWeight_cost

/-- Core indices selected by an integral dominating set. -/
def selectedCore (D : Finset Vertex) : Finset Core :=
  Finset.univ.filter (fun a => Sum.inl a ∈ D)

/-- Leaf indices whose corresponding leaf vertices are selected. -/
def selectedLeaves (D : Finset Vertex) : Finset Leaf :=
  Finset.univ.filter (fun S => Sum.inr S ∈ D)

/-- All 14-subsets whose corresponding leaf is not adjacent to any selected
core vertex. -/
def unhitLeaves (C : Finset Core) : Finset Leaf :=
  Finset.univ.filter (fun S => S.val ⊆ Finset.univ \ C)

/-- The indices of `unhitLeaves`, with the subtype proof erased. -/
def unhitLeafIndices (C : Finset Core) : Finset (Finset Core) :=
  (unhitLeaves C).image Subtype.val

theorem unhitLeafIndices_eq (C : Finset Core) :
    unhitLeafIndices C = (Finset.univ \ C).powersetCard 14 := by
  ext T
  constructor
  · intro h
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_filter.mp hS).2, S.property⟩
  · intro h
    have hT := Finset.mem_powersetCard.mp h
    refine Finset.mem_image.mpr ⟨⟨T, hT.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT.1⟩

theorem unhitLeaves_card (C : Finset Core) :
    (unhitLeaves C).card = ((Finset.univ \ C).powersetCard 14).card := by
  calc
    (unhitLeaves C).card = (unhitLeafIndices C).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ = ((Finset.univ \ C).powersetCard 14).card :=
      congrArg Finset.card (unhitLeafIndices_eq C)

theorem unhitLeaves_subset_selectedLeaves (D : Finset Vertex)
    (hD : dominates gapGraph D) :
    unhitLeaves (selectedCore D) ⊆ selectedLeaves D := by
  intro S hS
  have havoid : S.val ⊆ Finset.univ \ selectedCore D :=
    (Finset.mem_filter.mp hS).2
  have hdom : Sum.inr S ∈ covered gapGraph D := hD (Sum.inr S)
  obtain ⟨v, hvD, hvclosed⟩ := Finset.mem_biUnion.mp hdom
  have hvclosed' := (closed_symm gapGraph (Sum.inr S) v).mp hvclosed
  have hvMembership := (mem_closed gapGraph v (Sum.inr S)).mp hvclosed'
  cases v with
  | inl a =>
      rcases hvMembership with heq | hadj
      · cases heq
      · have haS : a ∈ S.val := (leaf_core_adj_iff S a).mp hadj
        have haC : a ∈ selectedCore D :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD⟩
        have haAvoid := havoid haS
        exact False.elim ((Finset.mem_sdiff.mp haAvoid).2 haC)
  | inr T =>
      rcases hvMembership with heq | hadj
      · have hTS : T = S := Sum.inr.inj heq
        subst T
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD⟩
      · exact False.elim (no_leaf_leaf_edge S T hadj)

/-- A finite set of vertices is the disjoint union of its core and leaf parts. -/
theorem selected_parts_card (D : Finset Vertex) :
    D.card = (selectedCore D).card + (selectedLeaves D).card := by
  let C : Finset Vertex := (selectedCore D).image (fun a => (Sum.inl a : Vertex))
  let L : Finset Vertex := (selectedLeaves D).image (fun S => (Sum.inr S : Vertex))
  have hparts : D = C ∪ L := by
    ext v
    cases v <;> simp [C, L, selectedCore, selectedLeaves]
  have hdisj : Disjoint C L := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvL
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvC
    obtain ⟨S, hS, hEq⟩ := Finset.mem_image.mp hvL
    exact Sum.inl_ne_inr hEq.symm
  conv_lhs => rw [hparts]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]

/-- Every unhit leaf must itself be selected by a dominating set. -/
theorem dominates_unhit_leaves (D : Finset Vertex)
    (hD : dominates gapGraph D) :
    unhitLeaves (selectedCore D) ⊆ selectedLeaves D := by
  exact unhitLeaves_subset_selectedLeaves D hD

/-- The integral lower bound for every dominating set. -/
theorem dominates_card_ge_fifteen (D : Finset Vertex)
    (hD : dominates gapGraph D) : 15 ≤ D.card := by
  have hparts := selected_parts_card D
  have hunhit := Finset.card_le_card (dominates_unhit_leaves D hD)
  rw [unhitLeaves_card] at hunhit
  have hcount := core_subset_plus_unhit_fourteen_bound (selectedCore D)
  omega

/-- The first 15 core vertices form the integral upper-bound witness. -/
def firstFifteen : Finset Core :=
  Finset.univ.image (fun i : Fin 15 =>
    (⟨i.val, Nat.lt_trans i.isLt (by omega)⟩ : Core))

theorem firstFifteen_card : firstFifteen.card = 15 := by
  rw [firstFifteen, Finset.card_image_of_injective _ (by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Core => x.val) hij)]
  simp

theorem zero_mem_firstFifteen :
    (⟨0, by omega⟩ : Core) ∈ firstFifteen := by
  apply Finset.mem_image.mpr
  refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  rfl

theorem firstFifteen_complement_card :
    (Finset.univ \ firstFifteen).card = 13 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ firstFifteen),
    Finset.card_univ, firstFifteen_card]
  norm_num

theorem every_leaf_hits_firstFifteen (S : Leaf) :
    ∃ a, a ∈ S.val ∧ a ∈ firstFifteen := by
  by_contra h
  have hsubset : S.val ⊆ Finset.univ \ firstFifteen := by
    intro a ha
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_univ _
    · intro ha15
      exact h ⟨a, ha, ha15⟩
  have hcard := Finset.card_le_card hsubset
  rw [S.property, firstFifteen_complement_card] at hcard
  omega

/-- The chosen 15 core vertices, as vertices of the split graph. -/
def firstFifteenVertices : Finset Vertex :=
  firstFifteen.image (fun a => Sum.inl a)

theorem firstFifteenVertices_card : firstFifteenVertices.card = 15 := by
  rw [firstFifteenVertices, Finset.card_image_of_injective _ Sum.inl_injective,
    firstFifteen_card]

theorem firstFifteen_dominates : dominates gapGraph firstFifteenVertices := by
  intro v
  cases v with
  | inl a =>
      let b : Core := ⟨0, by omega⟩
      have hb : b ∈ firstFifteen := zero_mem_firstFifteen
      have hbV : Sum.inl b ∈ firstFifteenVertices :=
        Finset.mem_image.mpr ⟨b, hb, rfl⟩
      have hclosed : Sum.inl a ∈ closed gapGraph (Sum.inl b) := by
        apply (mem_closed gapGraph (Sum.inl a) (Sum.inl b)).2
        by_cases h : a = b
        · exact Or.inl (congrArg Sum.inl h)
        · exact Or.inr ((core_adj_iff b a).2 (fun hba => h hba.symm))
      exact Finset.mem_biUnion.mpr ⟨Sum.inl b, hbV, hclosed⟩
  | inr S =>
      obtain ⟨a, haS, ha15⟩ := every_leaf_hits_firstFifteen S
      have haV : Sum.inl a ∈ firstFifteenVertices :=
        Finset.mem_image.mpr ⟨a, ha15, rfl⟩
      have hclosed : Sum.inr S ∈ closed gapGraph (Sum.inl a) := by
        apply (mem_closed gapGraph (Sum.inr S) (Sum.inl a)).2
        exact Or.inr ((core_leaf_adj_iff a S).2 haS)
      exact Finset.mem_biUnion.mpr ⟨Sum.inl a, haV, hclosed⟩

/-- The split graph has domination number exactly 15. -/
theorem dominationNumber_eq_fifteen : gapGraph.dominationNumber = 15 := by
  apply Nat.le_antisymm
  · have hdom :=
      (IntegralFractionalOptima.dominates_iff gapGraph firstFifteenVertices).mp
        firstFifteen_dominates
    have hle := hdom.dominationNumber_le
    rw [firstFifteenVertices_card] at hle
    exact hle
  · obtain ⟨D, hD, hcard⟩ :=
      SimpleGraph.exists_isDominatingSetFinset_card_eq_dominationNumber
        (G := gapGraph)
    have hlow := dominates_card_ge_fifteen D
      ((IntegralFractionalOptima.dominates_iff gapGraph D).mpr hD)
    omega

/-- The integral domination number is strictly larger than seven times the
fractional domination number, certifying the advertised gap. -/
theorem strict_gap_above_seven :
    7 * fractionalNumber gapGraph < (gapGraph.dominationNumber : ℝ) := by
  have hf := mul_le_mul_of_nonneg_left fractionalNumber_le_two
    (by norm_num : (0 : ℝ) ≤ 7)
  rw [dominationNumber_eq_fifteen]
  norm_num at hf ⊢
  linarith

end Paper.SplitGraphGap
