import Paper.Optimality.Treewidth.PathPowerTreewidth
import Paper.Optimality.Treewidth.TreewidthDensity

/-! Finite path decompositions and their actual minor-density consequence.
The decomposition is a proof witness, never a distributed algorithm input. -/
namespace Paper.Pathwidth

open SimpleGraph
variable {V W : Type} {G : SimpleGraph V} {J : SimpleGraph W}

/-- A finite path decomposition has nonempty consecutive bag positions.
Empty bags are allowed, including the single empty bag of the empty graph. -/
def Bound (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ n : ℕ, ∃ D : G.TreeDecomposition (pathGraph (n + 1)), D.IsWidthLE r

def trivial (G : SimpleGraph V) : G.TreeDecomposition (pathGraph 1) where
  bag _ := Set.univ
  isTree := PathGraphTree.tree 1 (by decide)
  cover v := ⟨0, Set.mem_univ v⟩
  edge_mem _ _ _ := ⟨0, Set.mem_univ _, Set.mem_univ _⟩
  bag_connected := by intros; exact Set.mem_univ _

theorem exists_bound [Finite V] (G : SimpleGraph V) : ∃ r, Bound G r := by
  refine ⟨Nat.card V, 0, trivial G, ?_⟩
  intro i
  refine ⟨Set.toFinite _, ?_⟩
  simp only [trivial, Set.ncard_univ]
  omega

theorem Bound.mono {r s : ℕ} (h : Bound G r) (hrs : r ≤ s) : Bound G s := by
  obtain ⟨n, D, hD⟩ := h
  exact ⟨n, D, hD.mono hrs⟩

/-- The standard finite pathwidth: minimum width of a finite path decomposition. -/
noncomputable def width [Finite V] (G : SimpleGraph V) : ℕ :=
  by classical exact Nat.find (exists_bound G)

theorem width_le_iff [Finite V] (r : ℕ) : width G ≤ r ↔ Bound G r := by
  classical
  constructor
  · intro h
    exact (Nat.find_spec (exists_bound G)).mono h
  · exact fun h => Nat.find_min' (exists_bound G) h

theorem treeWidth_le [Finite V] {r : ℕ} (h : Bound G r) : G.treeWidth ≤ r := by
  obtain ⟨n, D, hD⟩ := h
  exact treeWidth_le_of_isWidthLE D hD

theorem treeWidth_le_width [Finite V] : G.treeWidth ≤ width G :=
  treeWidth_le ((width_le_iff (G := G) _).mp le_rfl)

theorem minor [Finite W] {r : ℕ} (h : Bound G r) (hm : J.IsMinor G) : Bound J r := by
  obtain ⟨n, D, hD⟩ := h
  obtain ⟨M⟩ := hm
  exact ⟨n, TreewidthMinor.map D M, TreewidthMinor.width D M r hD⟩

theorem width_mono [Finite V] [Finite W] (hm : J.IsMinor G) : width J ≤ width G :=
  (width_le_iff _).mpr (minor ((width_le_iff (G := G) _).mp le_rfl) hm)

theorem edge_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r : ℕ} (h : Bound G r) : G.edgeFinset.card ≤ r * Fintype.card V :=
  TreewidthDensity.edge_bound G r (treeWidth_le h)

theorem minor_density [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r : ℕ} (h : Bound G r) : MinorDensity.Bound G (r : ℝ) :=
  TreewidthDensity.minor_density G r (treeWidth_le h)

theorem pathPower_bound (n r : ℕ) : Bound (PathPowerTreewidth.graph n r) r := by
  cases n with
  | zero =>
    refine ⟨0, trivial _, ?_⟩
    intro i
    refine ⟨Set.toFinite _, ?_⟩
    simp [trivial]
  | succ n =>
    exact ⟨n, PathPowerTreewidth.decomposition (n + 1) r (by omega),
      PathPowerTreewidth.width (n + 1) r (by omega)⟩

theorem pathPower_width (n r : ℕ) : width (PathPowerTreewidth.graph n r) ≤ r :=
  (width_le_iff _).mpr (pathPower_bound n r)

end Paper.Pathwidth

#print axioms Paper.Pathwidth.width_le_iff
#print axioms Paper.Pathwidth.minor
#print axioms Paper.Pathwidth.minor_density
#print axioms Paper.Pathwidth.pathPower_width
