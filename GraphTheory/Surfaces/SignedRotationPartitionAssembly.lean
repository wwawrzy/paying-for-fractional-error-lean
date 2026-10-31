import GraphTheory.Surfaces.SignedRotationAssembly
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (hGH : G ≤ H)
def partitionDartEquiv :
    (Σ c : H.ConnectedComponent, (G.induce c.supp).Dart) ≃ G.Dart :=
  (Equiv.sigmaCongrRight (fun c : H.ConnectedComponent => closedDartEquiv (G := G) c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)))).trans
      (Equiv.sigmaFiberEquiv (fun d : G.Dart => H.connectedComponentMk d.fst))
def partition_assemblePermutation (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    Equiv.Perm G.Dart :=
  (partitionDartEquiv H hGH).symm.trans
    ((Equiv.sigmaCongrRight (fun c => (s c).σ)).trans (partitionDartEquiv H hGH))

theorem partition_assemblePermutation_component
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : H.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    partition_assemblePermutation H hGH s (partitionDartEquiv H hGH ⟨c,d⟩) = partitionDartEquiv H hGH ⟨c,(s c).σ d⟩ := by
  simp [partition_assemblePermutation]

theorem partition_assemblePermutation_source
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp)) (d : G.Dart) :
    (partition_assemblePermutation H hGH s d).fst = d.fst := by
  obtain ⟨⟨c,d⟩,rfl⟩ := (partitionDartEquiv H hGH).surjective d
  rw [partition_assemblePermutation_component]
  change ((s c).σ d).fst.val = d.fst.val
  exact congrArg Subtype.val ((s c).σ_source d)
theorem partition_assemblePermutation_pow
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : H.ConnectedComponent) (d : (G.induce c.supp).Dart) (n : ℕ) :
    (partition_assemblePermutation H hGH s ^ n) (partitionDartEquiv H hGH ⟨c,d⟩) =
      partitionDartEquiv H hGH ⟨c,((s c).σ ^ n) d⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, partition_assemblePermutation_component,
      pow_succ', Equiv.Perm.mul_apply]

theorem partition_assemblePermutation_cyclic
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (d e : G.Dart) (h : d.fst = e.fst) : (partition_assemblePermutation H hGH s).SameCycle d e := by
  classical
  obtain ⟨⟨c,d⟩,rfl⟩ := (partitionDartEquiv H hGH).surjective d
  obtain ⟨⟨c',e⟩,rfl⟩ := (partitionDartEquiv H hGH).surjective e
  have hdc : H.connectedComponentMk (partitionDartEquiv H hGH ⟨c,d⟩).fst = c := d.fst.property
  have hec : H.connectedComponentMk (partitionDartEquiv H hGH ⟨c',e⟩).fst = c' := e.fst.property
  have hcc : c = c' := hdc.symm.trans ((congrArg H.connectedComponentMk h).trans hec)
  subst c'
  have hde : d.fst = e.fst := Subtype.ext h
  obtain ⟨n,hn⟩ := ((s c).cyclic d e hde).exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, partition_assemblePermutation_pow, hn]

def partition_assembleTwist (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (d : G.Dart) : Bool :=
  let z := (partitionDartEquiv H hGH).symm d
  (s z.1).twist z.2

theorem partition_assembleTwist_symm
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp)) (d : G.Dart) :
    partition_assembleTwist H hGH s d.symm = partition_assembleTwist H hGH s d := by
  obtain ⟨⟨c,d⟩,rfl⟩ := (partitionDartEquiv H hGH).surjective d
  have he : (partitionDartEquiv H hGH ⟨c,d⟩).symm = partitionDartEquiv H hGH ⟨c,d.symm⟩ := rfl
  rw [he]
  dsimp only [partition_assembleTwist]
  rw [(partitionDartEquiv H hGH).symm_apply_apply ⟨c,d.symm⟩,
    (partitionDartEquiv H hGH).symm_apply_apply ⟨c,d⟩]
  exact (s c).twist_symm d

def partition_assemble (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    SignedRotation G where
  σ := partition_assemblePermutation H hGH s
  σ_source := partition_assemblePermutation_source H hGH s
  cyclic := partition_assemblePermutation_cyclic H hGH s
  twist := partition_assembleTwist H hGH s
  twist_symm := partition_assembleTwist_symm H hGH s

theorem partition_assemble_restrict_sigma
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : H.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    ((partition_assemble H hGH s).restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).σ d = (s c).σ d := by
  have h := (partition_assemble H hGH s).closedRotation_dart c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)) d
  change partitionDartEquiv H hGH ⟨c,((partition_assemble H hGH s).restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).σ d⟩ =
    partition_assemblePermutation H hGH s (partitionDartEquiv H hGH ⟨c,d⟩) at h
  rw [partition_assemblePermutation_component] at h
  have he := (partitionDartEquiv H hGH).injective h
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

theorem partition_assemble_restrict_twist
    (s : ∀ c : H.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : H.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    ((partition_assemble H hGH s).restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).twist d = (s c).twist d := by
  change partition_assembleTwist H hGH s (partitionDartEquiv H hGH ⟨c,d⟩) = _
  dsimp only [partition_assembleTwist]
  rw [(partitionDartEquiv H hGH).symm_apply_apply ⟨c,d⟩]

variable (r : SignedRotation G)
include hGH
theorem partition_dart_card_sum [Fintype H.ConnectedComponent] :
    Nat.card G.Dart = ∑ c : H.ConnectedComponent, Nat.card (G.induce c.supp).Dart := by
  classical
  letI (c : H.ConnectedComponent) : Finite (G.induce c.supp).Dart := by infer_instance
  rw [← Nat.card_congr (partitionDartEquiv H hGH), Nat.card_sigma]

theorem partition_edge_card_sum [Fintype H.ConnectedComponent] :
    Nat.card r.Edge = ∑ c : H.ConnectedComponent,
      Nat.card (r.restrictClosed c.supp
        (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Edge := by
  classical
  have h := partition_dart_card_sum H hGH
  rw [r.dart_card_twice_edges] at h
  have hc (c : H.ConnectedComponent) : Nat.card (G.induce c.supp).Dart =
      2 * Nat.card (r.restrictClosed c.supp
        (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Edge :=
    (r.restrictClosed c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).dart_card_twice_edges
  simp_rw [hc] at h
  rw [← Finset.mul_sum] at h
  omega

def partitionSupportEquiv :
    (Σ c : H.ConnectedComponent, (G.induce c.supp).support) ≃ G.support :=
  (Equiv.sigmaCongrRight (fun c : H.ConnectedComponent => closedSupportEquiv (G := G) c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)))).trans
      (Equiv.sigmaFiberEquiv (fun v : G.support => H.connectedComponentMk v.val))

noncomputable def partitionVertexEquiv :
    (Σ c : H.ConnectedComponent, (r.restrictClosed c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Vertex) ≃ r.Vertex := by
  classical
  exact (Equiv.sigmaCongrRight (fun c : H.ConnectedComponent =>
    (r.restrictClosed c.supp (fun {_ _} hu huv =>
      c.mem_supp_of_adj_mem_supp hu (hGH huv))).vertexEquiv)).trans
      ((partitionSupportEquiv H hGH).trans r.vertexEquiv.symm)

theorem partition_vertex_card_sum [Fintype H.ConnectedComponent] :
    Nat.card r.Vertex = ∑ c : H.ConnectedComponent,
      Nat.card (r.restrictClosed c.supp
        (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Vertex := by
  classical
  letI (c : H.ConnectedComponent) : Finite (r.restrictClosed c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Vertex :=
    inferInstanceAs (Finite (Quotient (pairSetoid sideFlip (r.restrictClosed c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).cornerFlip)))
  rw [← Nat.card_congr (partitionVertexEquiv H hGH r), Nat.card_sigma]

end SimpleGraph.SignedRotation


