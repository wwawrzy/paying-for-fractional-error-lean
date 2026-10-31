import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cycle and cut spaces (Diestel §1.9)

Linear algebra over `GF(2) = ZMod 2` for the edge space of a finite graph.

* `EdgeSpace G` — the F₂-vector space of `ZMod 2`-valued functions on `G.edgeFinset`.
* `incidenceMatrix G` — the V × E(G) incidence matrix over F₂.
* `boundary G` — boundary linear map `∂ : E(G) →ₗ (V → ZMod 2)`,
  given by the incidence matrix.
* `coboundary G` — coboundary linear map `δ : (V → ZMod 2) →ₗ E(G)`,
  given by the transpose incidence matrix.
* `CycleSpace G` — kernel of `∂` (cycle space `C(G)`).
* `CutSpace G` — image of `δ` (cut space `C*(G)`).
* `cutIndicator G S` — cut indicator `δ(S)` for `S : Finset V`,
  defined as `δ(χ_S)`.

Diestel Thm 1.9.5: orthogonality (`cycle_cut_orthogonal`) and dimension
(`cycle_cut_dim`).

The orthogonality follows from the adjointness `⟨∂f, h⟩ = ⟨f, δh⟩` for the
standard pairings. The dimension equation follows from rank–nullity for `∂`
together with the fact that `∂` and `δ` have the same rank (transpose of
the incidence matrix).
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edge space `E(G)`: F₂-vector space of `ZMod 2`-valued functions on the edges of `G`.
A function corresponds to a subset of `G.edgeFinset`; addition is symmetric difference. -/
abbrev EdgeSpace : Type _ := G.edgeFinset → ZMod 2

/-- Incidence matrix of `G` over `F₂`: row indexed by vertices, column indexed by
edges of `G`, with entry `1` iff the vertex is an endpoint of the edge. -/
noncomputable def incidenceMatrix : Matrix V G.edgeFinset (ZMod 2) :=
  fun v e => if v ∈ (e.1 : Sym2 V) then 1 else 0

/-- Boundary map `∂ : E(G) →ₗ (V → ZMod 2)` given by the incidence matrix.
Concretely, `∂(f)(v) = ∑_{e ∋ v} f(e)` over edges of `G`. -/
noncomputable def boundary : EdgeSpace G →ₗ[ZMod 2] (V → ZMod 2) :=
  G.incidenceMatrix.mulVecLin

/-- Coboundary map `δ : (V → ZMod 2) →ₗ E(G)` given by the transpose incidence
matrix. For an edge `e = s(a, b)` of `G` with `a ≠ b`,
`δ(h)(e) = h(a) + h(b)` in `ZMod 2`. -/
noncomputable def coboundary : (V → ZMod 2) →ₗ[ZMod 2] EdgeSpace G :=
  G.incidenceMatrix.transpose.mulVecLin

/-- Cycle space `C(G) := ker ∂`: edge functions whose boundary is zero everywhere. -/
noncomputable def CycleSpace : Submodule (ZMod 2) (EdgeSpace G) :=
  LinearMap.ker (G.boundary)

/-- Cut space `C*(G) := image δ`: spanned by all `δ(h)` for `h : V → ZMod 2`,
equivalently by cut indicators `δ(S)` for `S ⊆ V`. -/
noncomputable def CutSpace : Submodule (ZMod 2) (EdgeSpace G) :=
  LinearMap.range (G.coboundary)

/-- Cut indicator `δ(S)`: the coboundary of the characteristic function of `S`.
Equivalently, the function on `G.edgeFinset` taking value `1` on edges with
exactly one endpoint in `S` and `0` otherwise. -/
noncomputable def cutIndicator (S : Finset V) : EdgeSpace G :=
  G.coboundary (fun v => if v ∈ S then 1 else 0)

/-- Cut indicators land in the cut space. -/
lemma cutIndicator_mem_cutSpace (S : Finset V) : G.cutIndicator S ∈ G.CutSpace :=
  ⟨_, rfl⟩

/-- **Adjointness of boundary and coboundary** (key lemma for Diestel Thm 1.9.5).
For all `f : E(G)` and `h : V → ZMod 2`,
`∑_e f(e) · δ(h)(e) = ∑_v ∂(f)(v) · h(v)`. -/
lemma boundary_coboundary_adjoint (f : EdgeSpace G) (h : V → ZMod 2) :
    ∑ e, f e * G.coboundary h e = ∑ v, G.boundary f v * h v := by
  -- Both sides equal the iterated sum `∑_v ∑_e f e * M v e * h v`.
  unfold boundary coboundary
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  -- Goal: `∑ e, f e * (∑ v, M v e * h v) = ∑ v, (∑ e, M v e * f e) * h v`
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-- **Diestel Thm 1.9.5 (orthogonality).** The cycle space and the cut space
are orthogonal: every cycle and every cut share an even number of edges. -/
theorem cycle_cut_orthogonal :
    ∀ f ∈ G.CycleSpace, ∀ g ∈ G.CutSpace,
      (∑ e, f e * g e) = 0 := by
  rintro f hf _ ⟨h, rfl⟩
  rw [boundary_coboundary_adjoint]
  have hf' : G.boundary f = 0 := hf
  simp [hf']

/-- The matrix rank of the incidence matrix equals the rank of the boundary map. -/
private lemma finrank_range_boundary :
    Module.finrank (ZMod 2) (G.boundary.range) = G.incidenceMatrix.rank := by
  unfold boundary
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]

/-- The matrix rank of the transpose incidence matrix equals the rank of the
coboundary map. -/
private lemma finrank_range_coboundary :
    Module.finrank (ZMod 2) (G.coboundary.range) = G.incidenceMatrix.transpose.rank := by
  unfold coboundary
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]

/-- **Diestel Thm 1.9.5 (dimensions).** `dim C(G) + dim C*(G) = |E(G)|`. -/
theorem cycle_cut_dim :
    Module.finrank (ZMod 2) G.CycleSpace +
      Module.finrank (ZMod 2) G.CutSpace
      = G.edgeFinset.card := by
  -- Unfold to `ker ∂ + range δ = |E|`.
  change Module.finrank (ZMod 2) G.boundary.ker
       + Module.finrank (ZMod 2) G.coboundary.range = _
  -- Rank–nullity for ∂. Need `ZMod 2` as a field; provided by `Nat.fact_prime_two`.
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.boundary)
  -- finrank E(G) = |G.edgeFinset|.
  have hE : Module.finrank (ZMod 2) (EdgeSpace G) = G.edgeFinset.card := by
    change Module.finrank (ZMod 2) (G.edgeFinset → ZMod 2) = _
    rw [Module.finrank_pi]
    simp
  rw [hE] at hrn
  -- `finrank range coboundary = finrank range boundary` via matrix rank-transpose.
  have heq : Module.finrank (ZMod 2) (G.coboundary.range)
            = Module.finrank (ZMod 2) (G.boundary.range) := by
    rw [finrank_range_boundary, finrank_range_coboundary, Matrix.rank_transpose]
  rw [heq, add_comm]
  exact hrn

/-- Characteristic vector of a finite set of edges.  This is the concrete
bridge between Diestel's edge subsets and the function model `EdgeSpace G`. -/
def edgeIndicator (F : Finset G.edgeFinset) : EdgeSpace G :=
  fun e => if e ∈ F then 1 else 0

/-- The dot product of two edge indicators is the cardinality of their
intersection, cast to `ZMod 2`. -/
lemma edgeIndicator_dot_eq_card_inter (F F' : Finset G.edgeFinset) :
    (∑ e, G.edgeIndicator F e * G.edgeIndicator F' e) =
      ((F ∩ F').card : ZMod 2) := by
  classical
  simp only [edgeIndicator, ite_mul, one_mul, zero_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  apply congrArg Finset.card
  ext e
  simp

/-- **Diestel §1.9, scalar-product fact.**  Two edge subsets
are orthogonal over `F₂` exactly when their intersection has even size. -/
theorem edgeIndicator_dot_eq_zero_iff_even (F F' : Finset G.edgeFinset) :
    (∑ e, G.edgeIndicator F e * G.edgeIndicator F' e) = 0 ↔
      Even ((F ∩ F').card) := by
  rw [G.edgeIndicator_dot_eq_card_inter F F']
  exact ZMod.natCast_eq_zero_iff_even

/-- Boundary of an edge indicator at a vertex: the parity-valued number of
selected edges incident with that vertex. -/
lemma boundary_edgeIndicator_apply (F : Finset G.edgeFinset) (v : V) :
    G.boundary (G.edgeIndicator F) v =
      ((F.filter fun e => v ∈ (e.1 : Sym2 V)).card : ZMod 2) := by
  classical
  unfold boundary
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, incidenceMatrix,
    edgeIndicator, ite_mul, one_mul, zero_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  apply congrArg Finset.card
  ext e
  simp [and_comm]

/-- **Diestel Proposition 1.9.2.**  An edge set belongs to the
cycle space iff every vertex has even degree in the subgraph formed by those
edges.  The degree is written explicitly as the number of selected incident
edges, so isolated vertices are included without a side condition. -/
theorem edgeIndicator_mem_cycleSpace_iff_even_incident
    (F : Finset G.edgeFinset) :
    G.edgeIndicator F ∈ G.CycleSpace ↔
      ∀ v : V, Even ((F.filter fun e => v ∈ (e.1 : Sym2 V)).card) := by
  change G.boundary (G.edgeIndicator F) = 0 ↔ _
  constructor
  · intro h v
    have hv := congr_fun h v
    rw [Pi.zero_apply, G.boundary_edgeIndicator_apply F v] at hv
    exact ZMod.natCast_eq_zero_iff_even.mp hv
  · intro h
    funext v
    rw [Pi.zero_apply, G.boundary_edgeIndicator_apply F v]
    exact ZMod.natCast_eq_zero_iff_even.mpr (h v)

/-- The family of elementary vertex cuts `E(v)`. -/
def vertexCutFamily : Set (EdgeSpace G) :=
  Set.range (fun v : V => G.cutIndicator {v})

/-- **Diestel Proposition 1.9.3.**  The cut space is generated by
the elementary cuts `E(v)`.  In particular, all cuts form a subspace because
the left-hand side is the range of the linear coboundary map. -/
theorem cutSpace_eq_span_vertexCutFamily :
    G.CutSpace = Submodule.span (ZMod 2) G.vertexCutFamily := by
  apply le_antisymm
  · rintro g ⟨h, rfl⟩
    have h_decomp :
        h = ∑ v : V, h v • (fun w : V => if w = v then (1 : ZMod 2) else 0) := by
      funext w
      simp
    rw [h_decomp, map_sum]
    refine Submodule.sum_mem _ (fun v _ => ?_)
    rw [LinearMap.map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨v, ?_⟩
    unfold cutIndicator
    funext w
    simp [eq_comm]
  · apply Submodule.span_le.2
    rintro g ⟨v, rfl⟩
    exact G.cutIndicator_mem_cutSpace {v}

/-- **Diestel §1.9, vertex-cut basis fact.**  One can select from
the elementary cuts `E(v)` a linearly independent spanning family for the cut
space.  Its cardinality is exactly `dim C*(G)`, so the returned set is a basis
written inside the ambient edge space. -/
theorem exists_vertexCutBasis :
    ∃ b : Set (EdgeSpace G),
      b ⊆ G.vertexCutFamily ∧
      Submodule.span (ZMod 2) b = G.CutSpace ∧
      LinearIndependent (ZMod 2) ((↑) : b → EdgeSpace G) ∧
      Module.finrank (ZMod 2) G.CutSpace = b.ncard := by
  obtain ⟨b, hb, hspan, hli⟩ :=
    exists_linearIndependent (ZMod 2) G.vertexCutFamily
  have hbfinite : b.Finite :=
    (Set.finite_range (fun v : V => G.cutIndicator {v})).subset hb
  have hspanCut : Submodule.span (ZMod 2) b = G.CutSpace :=
    hspan.trans G.cutSpace_eq_span_vertexCutFamily.symm
  refine ⟨b, hb, hspanCut, hli, ?_⟩
  rw [← hspanCut]
  letI := hbfinite.fintype
  rw [finrank_span_set_eq_card hli]
  exact (Set.ncard_eq_toFinset_card' b).symm

/-- **Diestel Theorem 1.9.7 (kernel half).**  For the incidence
matrix boundary map, the cycle space is exactly its kernel. -/
theorem cycleSpace_eq_ker_boundary :
    G.CycleSpace = LinearMap.ker G.boundary :=
  rfl

/-- **Diestel Theorem 1.9.7 (image half).**  For the transposed
incidence matrix map, the cut space is exactly its image. -/
theorem cutSpace_eq_range_coboundary :
    G.CutSpace = LinearMap.range G.coboundary :=
  rfl

/-! ## Incidence and adjacency matrices -/

/-- An entry of `B Bᵀ` counts, modulo two, the edges incident with both
specified vertices. Here `B` is the unoriented incidence matrix over `F₂`. -/
private lemma incidenceMatrix_mul_transpose_apply (u v : V) :
    (G.incidenceMatrix * G.incidenceMatrix.transpose) u v =
      ((Finset.univ.filter fun e : G.edgeFinset =>
        u ∈ (e.1 : Sym2 V) ∧ v ∈ (e.1 : Sym2 V)).card : ZMod 2) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidenceMatrix]
  calc
    (∑ e : G.edgeFinset,
        (if u ∈ (e.1 : Sym2 V) then (1 : ZMod 2) else 0) *
          (if v ∈ (e.1 : Sym2 V) then (1 : ZMod 2) else 0)) =
        ∑ e : G.edgeFinset,
          if u ∈ (e.1 : Sym2 V) ∧ v ∈ (e.1 : Sym2 V) then (1 : ZMod 2) else 0 := by
            apply Finset.sum_congr rfl
            intro e _
            by_cases hu : u ∈ (e.1 : Sym2 V) <;>
              by_cases hv : v ∈ (e.1 : Sym2 V) <;> simp [hu, hv]
    _ = _ := Finset.sum_boole _ Finset.univ

/-- **Diestel Proposition 1.9.8.** Over `F₂`, the unoriented incidence matrix
satisfies `B Bᵀ = A + D`, where `A` is the adjacency matrix and `D` is the
diagonal degree matrix. -/
theorem incidenceMatrix_mul_transpose :
    G.incidenceMatrix * G.incidenceMatrix.transpose =
      G.adjMatrix (ZMod 2) + G.degMatrix (ZMod 2) := by
  classical
  ext u v
  rw [G.incidenceMatrix_mul_transpose_apply u v]
  by_cases huv : u = v
  · subst v
    let emb : G.edgeFinset ↪ Sym2 V := ⟨Subtype.val, Subtype.val_injective⟩
    have hmap :
        ((Finset.univ.filter fun e : G.edgeFinset => u ∈ (e.1 : Sym2 V)).map emb) =
          G.incidenceFinset u := by
      ext e
      simp [emb, G.incidenceFinset_eq_filter, and_comm]
    have hcard :
        (Finset.univ.filter fun e : G.edgeFinset => u ∈ (e.1 : Sym2 V)).card =
          G.degree u := by
      calc
        _ = (((Finset.univ.filter fun e : G.edgeFinset =>
            u ∈ (e.1 : Sym2 V)).map emb).card) := by simp
        _ = (G.incidenceFinset u).card := by rw [hmap]
        _ = G.degree u := G.card_incidenceFinset_eq_degree u
    simp only [and_self]
    rw [hcard]
    simp [SimpleGraph.degMatrix]
  · by_cases hadj : G.Adj u v
    · let e : G.edgeFinset :=
        ⟨s(u, v), G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj)⟩
      have hfilter :
          (Finset.univ.filter fun x : G.edgeFinset =>
            u ∈ (x.1 : Sym2 V) ∧ v ∈ (x.1 : Sym2 V)) = {e} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro hx
          apply Subtype.ext
          exact (Sym2.mem_and_mem_iff huv).mp hx
        · intro hx
          subst x
          exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
      rw [hfilter]
      simp [SimpleGraph.degMatrix, huv, hadj]
    · have hfilter :
          (Finset.univ.filter fun x : G.edgeFinset =>
            u ∈ (x.1 : Sym2 V) ∧ v ∈ (x.1 : Sym2 V)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        have heq : (x.1 : Sym2 V) = s(u, v) :=
          (Sym2.mem_and_mem_iff huv).mp hx'
        apply hadj
        rw [← G.mem_edgeSet]
        rw [← heq]
        exact G.mem_edgeFinset.mp x.property
      rw [hfilter]
      simp [SimpleGraph.degMatrix, huv, hadj]

private abbrev cycleFour : SimpleGraph (Fin 4) := cycleGraph 4

private def cycleFourBicycle : EdgeSpace cycleFour :=
  cycleFour.edgeIndicator Finset.univ

private theorem cutIndicator_apply_adj (S : Finset V) {u v : V}
    (huv : G.Adj u v) :
    G.cutIndicator S
        (⟨s(u, v), G.mem_edgeFinset.mpr huv⟩ : G.edgeFinset) =
      (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  classical
  unfold cutIndicator coboundary incidenceMatrix
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  rw [show (Finset.univ.filter fun x : V => x ∈ s(u, v)) = {u, v} by
    ext x
    simp [Sym2.mem_iff]]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  all_goals simp [Finset.filter_insert, Finset.filter_singleton, hu, hv, huv.ne]
  all_goals norm_num

private theorem cycleFourBicycle_eq_cutIndicator :
    cycleFourBicycle = cycleFour.cutIndicator {0, 2} := by
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : cycleFour.Adj u v := cycleFour.mem_edgeFinset.mp he
      rw [cycleFour.cutIndicator_apply_adj {0, 2} huv]
      simp only [cycleFourBicycle, edgeIndicator, Finset.mem_univ, if_true]
      fin_cases u <;> fin_cases v <;>
        simp_all [cycleFour, cycleGraph_adj, Fin.ext_iff]
      all_goals
        have hcalc : (-2 : Fin 4) = 2 := by decide
        simp only [hcalc] at he
        exact (by omega)

private theorem card_all_edges_incident (v : V) :
    (Finset.univ.filter fun e : G.edgeFinset =>
      v ∈ (e.1 : Sym2 V)).card = G.degree v := by
  let emb : G.edgeFinset ↪ Sym2 V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      ((Finset.univ.filter fun e : G.edgeFinset =>
        v ∈ (e.1 : Sym2 V)).map emb) = G.incidenceFinset v := by
    ext e
    simp [emb, G.incidenceFinset_eq_filter, and_comm]
  calc
    _ = (((Finset.univ.filter fun e : G.edgeFinset =>
        v ∈ (e.1 : Sym2 V)).map emb).card) := by simp
    _ = (G.incidenceFinset v).card := by rw [hmap]
    _ = G.degree v := G.card_incidenceFinset_eq_degree v

private theorem cycleFourBicycle_mem_cycleSpace :
    cycleFourBicycle ∈ cycleFour.CycleSpace := by
  rw [cycleFourBicycle, cycleFour.edgeIndicator_mem_cycleSpace_iff_even_incident]
  intro v
  rw [cycleFour.card_all_edges_incident v, cycleGraph_degree_three_le]
  exact even_two

private theorem cycleFourBicycle_mem_cutSpace :
    cycleFourBicycle ∈ cycleFour.CutSpace := by
  rw [cycleFourBicycle_eq_cutIndicator]
  exact cycleFour.cutIndicator_mem_cutSpace {0, 2}

private theorem cycleFourBicycle_ne_zero : cycleFourBicycle ≠ 0 := by
  intro hzero
  have hadj : cycleFour.Adj (0 : Fin 4) 1 := by decide
  let e : cycleFour.edgeFinset :=
    ⟨s(0, 1), cycleFour.mem_edgeFinset.mpr hadj⟩
  have heq := congrFun hzero e
  simp [cycleFourBicycle, edgeIndicator] at heq

/-- **Diestel Chapter 1, Exercise 29 (counterexample).** Cycles and cuts need
not generate the whole edge space: this already fails for the four-cycle. -/
theorem cycleGraph_four_cycleSpace_sup_cutSpace_ne_top :
    (cycleGraph 4).CycleSpace ⊔ (cycleGraph 4).CutSpace ≠ ⊤ := by
  have hinter_nontrivial : Nontrivial
      ↥((cycleFour.CycleSpace ⊓ cycleFour.CutSpace)) := by
    refine ⟨⟨⟨cycleFourBicycle,
      cycleFourBicycle_mem_cycleSpace, cycleFourBicycle_mem_cutSpace⟩, 0, ?_⟩⟩
    intro h
    exact cycleFourBicycle_ne_zero (congrArg Subtype.val h)
  have hinter_pos : 0 < Module.finrank (ZMod 2)
      ↥(cycleFour.CycleSpace ⊓ cycleFour.CutSpace) := by
    letI := hinter_nontrivial
    exact Module.finrank_pos
  intro htop
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    cycleFour.CycleSpace cycleFour.CutSpace
  have hcyclecut := cycleFour.cycle_cut_dim
  have hedgeDim : Module.finrank (ZMod 2) (EdgeSpace cycleFour) =
      cycleFour.edgeFinset.card := by
    rw [Module.finrank_pi]
    simp
  rw [htop, finrank_top, hedgeDim, hcyclecut] at hdim
  omega

end SimpleGraph
