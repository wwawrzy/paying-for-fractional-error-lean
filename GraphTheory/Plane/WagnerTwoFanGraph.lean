import GraphTheory.Plane.WagnerContractionGraph
import GraphTheory.Plane.PlaneTwoFans

/-!
# The two-fan graph is exactly the original graph before contraction

After deleting the two endpoints of an edge, every remaining vertex is an
old vertex of the two-fan construction. The two fresh apices replace the two
deleted endpoints. Their neighbor sets are the actual original neighbor
sets, and the constructed inter-apex edge is the original contracted edge.
-/

namespace PlaneTopology.WagnerTwoFanGraph

open SimpleGraph PlaneTopology.WagnerContractionGraph PlaneTopology.PlaneFanInsertion PlaneTopology.PlaneTwoFans

variable {V : Type*} (G : SimpleGraph V) (u v : V)

/-- The actual original graph after deleting both edge endpoints. -/
def residualGraph : SimpleGraph (ResidualVertex u v) :=
  G.induce {w | w ≠ u ∧ w ≠ v}

/-- Decode the two fresh apices and residual vertices back to old vertices. -/
def vertexDecode : Option (Option (ResidualVertex u v)) → V
  | none => v
  | some none => u
  | some (some w) => w.val

/-- The two-apex coding has no collisions when the endpoints are distinct. -/
theorem vertexDecode_injective (hne : u ≠ v) : Function.Injective (vertexDecode u v) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases b with
      | none => exact (hne hab.symm).elim
      | some b => exact (b.property.2 hab.symm).elim
  | some a =>
    cases a with
    | none =>
      cases b with
      | none => exact (hne hab).elim
      | some b =>
        cases b with
        | none => rfl
        | some b => exact (b.property.1 hab.symm).elim
    | some a =>
      cases b with
      | none => exact (a.property.2 hab).elim
      | some b =>
        cases b with
        | none => exact (a.property.1 hab).elim
        | some b => exact congrArg some (congrArg some (Subtype.ext hab))

/-- Every old vertex is either an endpoint or a surviving residual vertex. -/
theorem vertexDecode_surjective : Function.Surjective (vertexDecode u v) := by
  intro w
  by_cases hwu : w = u
  · exact ⟨some none, hwu.symm⟩
  · by_cases hwv : w = v
    · exact ⟨none, hwv.symm⟩
    · exact ⟨some (some ⟨w, hwu, hwv⟩), rfl⟩

/-- Actual vertex equivalence, with a fully specified decoding function. -/
noncomputable def vertexEquiv (hne : u ≠ v) :
    Option (Option (ResidualVertex u v)) ≃ V :=
  Equiv.ofBijective (vertexDecode u v)
    ⟨vertexDecode_injective u v hne, vertexDecode_surjective u v⟩

theorem vertexEquiv_apply (hne : u ≠ v) (w : Option (Option (ResidualVertex u v))) :
    vertexEquiv u v hne w = vertexDecode u v w := rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Actual old neighbors of the first deleted endpoint, restricted to residual vertices. -/
def firstNeighbors : Finset (ResidualVertex u v) :=
  Finset.univ.filter (fun w => G.Adj u w.val)

/-- Actual old neighbors of the second deleted endpoint, restricted to residual vertices. -/
def secondNeighbors : Finset (ResidualVertex u v) :=
  Finset.univ.filter (fun w => G.Adj v w.val)

@[simp] theorem mem_firstNeighbors (w : ResidualVertex u v) :
    w ∈ firstNeighbors G u v ↔ G.Adj u w.val := by simp [firstNeighbors]

@[simp] theorem mem_secondNeighbors (w : ResidualVertex u v) :
    w ∈ secondNeighbors G u v ↔ G.Adj v w.val := by simp [secondNeighbors]

instance residualGraphDecidableRel : DecidableRel (residualGraph G u v).Adj := by
  unfold residualGraph
  infer_instance

/-- The exact two-apex graph is isomorphic to the original graph, including
every old edge, every incident endpoint edge, and the endpoint edge itself. -/
noncomputable def twoFanIso (huv : G.Adj u v) :
    twoFanGraph (residualGraph G u v) (firstNeighbors G u v) (secondNeighbors G u v) ≃g G where
  toEquiv := vertexEquiv u v huv.ne
  map_rel_iff' := by
    rintro (_ | (_ | a)) (_ | (_ | b)) <;>
      simp [vertexEquiv_apply, vertexDecode, twoFanGraph, apexGraph, residualGraph,
        huv, huv.symm, G.adj_comm, Subtype.ext_iff] <;> try rfl
    · exact fun _ => b.property
    · exact fun _ => a.property

/-- The graph isomorphism sends each surviving old vertex to itself. -/
theorem twoFanIso_apply_old (huv : G.Adj u v) (w : ResidualVertex u v) :
    twoFanIso G u v huv (some (some w)) = w.val := rfl

/-- The first fresh apex really is the first deleted endpoint. -/
theorem twoFanIso_apply_first (huv : G.Adj u v) :
    twoFanIso G u v huv (some none) = u := rfl

/-- The second fresh apex really is the second deleted endpoint. -/
theorem twoFanIso_apply_second (huv : G.Adj u v) :
    twoFanIso G u v huv none = v := rfl

/-- The requested original-to-two-fan orientation of the graph isomorphism. -/
noncomputable def originalIsoTwoFan (huv : G.Adj u v) :
    G ≃g twoFanGraph (residualGraph G u v) (firstNeighbors G u v) (secondNeighbors G u v) :=
  (twoFanIso G u v huv).symm

/-- Forgetting the residual subtype removes exactly the second endpoint
from the first endpoint's original neighbor finset. -/
theorem image_firstNeighbors :
    (firstNeighbors G u v).image Subtype.val = (G.neighborFinset u).erase v := by
  ext w
  simp only [Finset.mem_image, mem_firstNeighbors, Finset.mem_erase, mem_neighborFinset]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property.2, ha⟩
  · rintro ⟨hwv, huw⟩
    exact ⟨⟨w, huw.ne.symm, hwv⟩, huw, rfl⟩

/-- The analogous exact neighbor finset identity for the second endpoint. -/
theorem image_secondNeighbors :
    (secondNeighbors G u v).image Subtype.val = (G.neighborFinset v).erase u := by
  ext w
  simp only [Finset.mem_image, mem_secondNeighbors, Finset.mem_erase, mem_neighborFinset]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property.1, ha⟩
  · rintro ⟨hwu, hvw⟩
    exact ⟨⟨w, hwu, hvw.ne.symm⟩, hvw, rfl⟩

/-- The first residual attachment count is its old degree minus the edge uv. -/
theorem card_firstNeighbors_add_one (huv : G.Adj u v) :
    (firstNeighbors G u v).card + 1 = G.degree u := by
  have hcard := Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  rw [← image_firstNeighbors G u v,
    Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard

/-- The second residual attachment count is its old degree minus the edge uv. -/
theorem card_secondNeighbors_add_one (huv : G.Adj u v) :
    (secondNeighbors G u v).card + 1 = G.degree v := by
  have hcard := Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  rw [← image_secondNeighbors G u v,
    Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard

/-- Three-connectivity forces at least two first-apex attachments after uv
is removed, exactly as required by the Wagner gap theorem. -/
theorem two_le_card_firstNeighbors (huv : G.Adj u v) (h3 : G.IsKConnected 3) :
    2 ≤ (firstNeighbors G u v).card := by
  haveI : Nontrivial V := ⟨⟨u, v, huv.ne⟩⟩
  have hdeg := SimpleGraph.EdgeContraction.isKConnected_le_degree G h3 u
  have hcard := card_firstNeighbors_add_one G u v huv
  omega

/-- Three-connectivity also forces at least two second-apex attachments. -/
theorem two_le_card_secondNeighbors (huv : G.Adj u v) (h3 : G.IsKConnected 3) :
    2 ≤ (secondNeighbors G u v).card := by
  haveI : Nontrivial V := ⟨⟨u, v, huv.ne⟩⟩
  have hdeg := SimpleGraph.EdgeContraction.isKConnected_le_degree G h3 v
  have hcard := card_secondNeighbors_add_one G u v huv
  omega

#print axioms twoFanIso
#print axioms two_le_card_firstNeighbors
#print axioms two_le_card_secondNeighbors

end PlaneTopology.WagnerTwoFanGraph
