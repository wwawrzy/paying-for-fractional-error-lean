import GraphTheory.CycleCutSpace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Dimensions of cycle and cut spaces of a connected graph

This file proves the exact finite connected dimension formulas from Diestel
Theorem 1.9.6.  The key step identifies the kernel of the coboundary map with
the one-dimensional space of constant vertex functions.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On an edge `uv`, the coboundary of `h` is `h u + h v` over `F₂`. -/
lemma coboundary_apply_adj (h : V → ZMod 2) {u v : V} (huv : G.Adj u v) :
    G.coboundary h
      (⟨s(u, v), G.mem_edgeFinset.mpr huv⟩ : G.edgeFinset) =
      h u + h v := by
  classical
  unfold coboundary incidenceMatrix
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite]
  rw [show (Finset.univ.filter fun x : V => x ∈ s(u, v)) = {u, v} by
    ext x
    simp [Sym2.mem_iff]]
  rw [Finset.sum_pair huv.ne]
  simp

/-- Constant vertex functions lie in the kernel of the coboundary map. -/
lemma coboundary_const (c : ZMod 2) :
    G.coboundary (fun _ => c) = 0 := by
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := G.mem_edgeFinset.mp he
      rw [Pi.zero_apply, G.coboundary_apply_adj (fun _ => c) huv]
      calc
        c + c = c + (-c) := congrArg (c + ·) (ZMod.neg_eq_self_mod_two c).symm
        _ = 0 := add_neg_cancel c

/-- A zero-coboundary function takes equal values at adjacent vertices. -/
lemma eq_of_coboundary_eq_zero_of_adj
    (h : V → ZMod 2) (hh : G.coboundary h = 0)
    {u v : V} (huv : G.Adj u v) :
    h u = h v := by
  have hz := congr_fun hh
    (⟨s(u, v), G.mem_edgeFinset.mpr huv⟩ : G.edgeFinset)
  rw [Pi.zero_apply, G.coboundary_apply_adj h huv] at hz
  have hneg : h u = -h v := eq_neg_of_add_eq_zero_left hz
  simpa only [ZMod.neg_eq_self_mod_two] using hneg

/-- A zero-coboundary function is constant along every walk. -/
lemma eq_of_coboundary_eq_zero_of_walk
    (h : V → ZMod 2) (hh : G.coboundary h = 0)
    {u v : V} (p : G.Walk u v) :
    h u = h v := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      exact (G.eq_of_coboundary_eq_zero_of_adj h hh huv).trans ih

/-- On a connected graph, every zero-coboundary vertex function is constant. -/
lemma eq_of_coboundary_eq_zero
    (hG : G.Connected) (h : V → ZMod 2) (hh : G.coboundary h = 0)
    (u v : V) :
    h u = h v :=
  G.eq_of_coboundary_eq_zero_of_walk h hh (Classical.choice (hG u v))

/-- For a connected graph, the kernel of the coboundary map consists exactly
of constant functions and therefore has dimension one. -/
theorem finrank_ker_coboundary_eq_one (hG : G.Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker G.coboundary) = 1 := by
  let r : V := Classical.choice hG.nonempty
  let e : LinearMap.ker G.coboundary ≃ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun h => h.1 r
      invFun := fun c => ⟨fun _ => c, G.coboundary_const c⟩
      left_inv := by
        intro h
        apply Subtype.ext
        funext v
        exact (G.eq_of_coboundary_eq_zero hG h.1 h.2 v r).symm
      right_inv := by intro c; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  rw [LinearEquiv.finrank_eq e]
  simp

/-- **Diestel Theorem 1.9.6, cut-space formula.**
For connected `G`, `dim C*(G) = |V(G)| - 1`. -/
theorem finrank_cutSpace_eq_card_sub_one (hG : G.Connected) :
    Module.finrank (ZMod 2) G.CutSpace = Fintype.card V - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change Module.finrank (ZMod 2) (LinearMap.range G.coboundary) = _
  have hrn := LinearMap.finrank_range_add_finrank_ker G.coboundary
  have hV : Module.finrank (ZMod 2) (V → ZMod 2) = Fintype.card V := by
    rw [Module.finrank_pi]
  rw [hV, G.finrank_ker_coboundary_eq_one hG] at hrn
  omega

/-- **Diestel Theorem 1.9.6, cycle-space formula.**
For connected `G`, `dim C(G) = |E(G)| + 1 - |V(G)|`.  This ordering avoids
the misleading truncated-natural expression `m - n + 1` at `K₁`. -/
theorem finrank_cycleSpace_eq_edges_add_one_sub_vertices (hG : G.Connected) :
    Module.finrank (ZMod 2) G.CycleSpace =
      G.edgeFinset.card + 1 - Fintype.card V := by
  have hcut := G.finrank_cutSpace_eq_card_sub_one hG
  have hdim := G.cycle_cut_dim
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hG.nonempty
  omega

/-! ### The formulas for an arbitrary finite graph -/

/-- The kernel of the coboundary map is linearly equivalent to one copy of
`ZMod 2` for each connected component. -/
private noncomputable def kerCoboundaryEquivComponentFunctions :
    LinearMap.ker G.coboundary ≃ₗ[ZMod 2]
      (G.ConnectedComponent → ZMod 2) where
  toFun h := ConnectedComponent.lift (fun v => h.1 v)
    (fun _ _ p _ => G.eq_of_coboundary_eq_zero_of_walk h.1 h.2 p)
  invFun f := ⟨fun v => f (G.connectedComponentMk v), by
    funext e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        rw [Pi.zero_apply, G.coboundary_apply_adj _ huv]
        rw [ConnectedComponent.connectedComponentMk_eq_of_adj huv]
        calc
          f (G.connectedComponentMk v) + f (G.connectedComponentMk v) =
              f (G.connectedComponentMk v) + (-f (G.connectedComponentMk v)) :=
            congrArg (f (G.connectedComponentMk v) + ·)
              (ZMod.neg_eq_self_mod_two _).symm
          _ = 0 := add_neg_cancel _⟩
  left_inv h := by
    apply Subtype.ext
    funext v
    rfl
  right_inv f := by
    funext C
    exact C.ind (fun _ => rfl)
  map_add' h k := by
    funext C
    exact C.ind (fun _ => rfl)
  map_smul' c h := by
    funext C
    exact C.ind (fun _ => rfl)

/-- **Diestel's disconnected cycle/cut dimension formula, kernel form.**
The dimension of the zero-coboundary vertex functions is the number of
connected components. -/
theorem finrank_ker_coboundary_eq_card_connectedComponent :
    Module.finrank (ZMod 2) (LinearMap.ker G.coboundary) =
      Fintype.card G.ConnectedComponent := by
  rw [LinearEquiv.finrank_eq G.kerCoboundaryEquivComponentFunctions]
  exact Module.finrank_pi (ZMod 2)

/-- **Diestel's disconnected cycle/cut dimension formula, cut-space form.**
For every finite graph, `dim C*(G) = |V(G)| - c(G)`. -/
theorem finrank_cutSpace_eq_vertices_sub_components :
    Module.finrank (ZMod 2) G.CutSpace =
      Fintype.card V - Fintype.card G.ConnectedComponent := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change Module.finrank (ZMod 2) (LinearMap.range G.coboundary) = _
  have hrn := LinearMap.finrank_range_add_finrank_ker G.coboundary
  have hV : Module.finrank (ZMod 2) (V → ZMod 2) = Fintype.card V := by
    rw [Module.finrank_pi]
  rw [hV, G.finrank_ker_coboundary_eq_card_connectedComponent] at hrn
  omega

/-- **Diestel's disconnected cycle/cut dimension formula, cycle-space form.**
For every finite graph, `dim C(G) = |E(G)| + c(G) - |V(G)|`. -/
theorem finrank_cycleSpace_eq_edges_add_components_sub_vertices :
    Module.finrank (ZMod 2) G.CycleSpace =
      G.edgeFinset.card + Fintype.card G.ConnectedComponent - Fintype.card V := by
  have hcut := G.finrank_cutSpace_eq_vertices_sub_components
  have hdim := G.cycle_cut_dim
  have hcomponents : Fintype.card G.ConnectedComponent ≤ Fintype.card V :=
    Fintype.card_le_of_surjective G.connectedComponentMk
      (fun C => C.ind (fun v => ⟨v, rfl⟩))
  omega

end SimpleGraph
