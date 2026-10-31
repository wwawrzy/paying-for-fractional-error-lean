import GraphTheory.Surfaces.SignedRotationComponentFaces
import GraphTheory.Surfaces.SignedRotationEdges
import Mathlib.Logic.Equiv.Sum

/-! Directed edges and surface edge classes decompose over connected components. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G)

def componentDartEquiv :
    (Σ c : G.ConnectedComponent, (G.induce c.supp).Dart) ≃ G.Dart :=
  (Equiv.sigmaCongrRight (fun c : G.ConnectedComponent => closedDartEquiv c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv))).trans
      (Equiv.sigmaFiberEquiv (fun d : G.Dart => G.connectedComponentMk d.fst))

theorem dart_card_sum [Fintype G.ConnectedComponent] :
    Nat.card G.Dart = ∑ c : G.ConnectedComponent, Nat.card (G.induce c.supp).Dart := by
  classical
  letI (c : G.ConnectedComponent) : Finite (G.induce c.supp).Dart := by infer_instance
  rw [← Nat.card_congr (componentDartEquiv (G := G)), Nat.card_sigma]

theorem dart_card_twice_edges : Nat.card G.Dart = 2 * Nat.card r.Edge := by
  classical
  rw [Nat.card_eq_fintype_card, r.edge_card, G.dart_card_eq_twice_card_edges]

theorem edge_card_sum [Fintype G.ConnectedComponent] :
    Nat.card r.Edge = ∑ c : G.ConnectedComponent, Nat.card (r.restrictComponent c).Edge := by
  classical
  have h := dart_card_sum (G := G)
  rw [r.dart_card_twice_edges] at h
  have hc (c : G.ConnectedComponent) : Nat.card (G.induce c.supp).Dart =
      2 * Nat.card (r.restrictComponent c).Edge :=
    (r.restrictComponent c).dart_card_twice_edges
  simp_rw [hc] at h
  rw [← Finset.mul_sum] at h
  omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.componentDartEquiv
#print axioms SimpleGraph.SignedRotation.dart_card_sum
#print axioms SimpleGraph.SignedRotation.edge_card_sum
