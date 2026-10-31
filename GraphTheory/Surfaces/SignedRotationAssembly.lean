import GraphTheory.Surfaces.SignedRotationComponentEdges
import GraphTheory.Surfaces.SignedRotationGenusSum
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
def assemblePermutation (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    Equiv.Perm G.Dart :=
  (componentDartEquiv (G := G)).symm.trans
    ((Equiv.sigmaCongrRight (fun c => (s c).σ)).trans (componentDartEquiv (G := G)))

theorem assemblePermutation_component
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : G.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    assemblePermutation s (componentDartEquiv ⟨c,d⟩) = componentDartEquiv ⟨c,(s c).σ d⟩ := by
  simp [assemblePermutation]

theorem assemblePermutation_source
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp)) (d : G.Dart) :
    (assemblePermutation s d).fst = d.fst := by
  obtain ⟨⟨c,d⟩,rfl⟩ := (componentDartEquiv (G := G)).surjective d
  rw [assemblePermutation_component]
  change ((s c).σ d).fst.val = d.fst.val
  exact congrArg Subtype.val ((s c).σ_source d)
theorem assemblePermutation_pow
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : G.ConnectedComponent) (d : (G.induce c.supp).Dart) (n : ℕ) :
    (assemblePermutation s ^ n) (componentDartEquiv ⟨c,d⟩) =
      componentDartEquiv ⟨c,((s c).σ ^ n) d⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, assemblePermutation_component,
      pow_succ', Equiv.Perm.mul_apply]

theorem assemblePermutation_cyclic
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (d e : G.Dart) (h : d.fst = e.fst) : (assemblePermutation s).SameCycle d e := by
  classical
  obtain ⟨⟨c,d⟩,rfl⟩ := (componentDartEquiv (G := G)).surjective d
  obtain ⟨⟨c',e⟩,rfl⟩ := (componentDartEquiv (G := G)).surjective e
  have hdc : G.connectedComponentMk (componentDartEquiv ⟨c,d⟩).fst = c := d.fst.property
  have hec : G.connectedComponentMk (componentDartEquiv ⟨c',e⟩).fst = c' := e.fst.property
  have hcc : c = c' := hdc.symm.trans ((congrArg G.connectedComponentMk h).trans hec)
  subst c'
  have hde : d.fst = e.fst := Subtype.ext h
  obtain ⟨n,hn⟩ := ((s c).cyclic d e hde).exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, assemblePermutation_pow, hn]

def assembleTwist (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (d : G.Dart) : Bool :=
  let z := (componentDartEquiv (G := G)).symm d
  (s z.1).twist z.2

theorem assembleTwist_symm
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp)) (d : G.Dart) :
    assembleTwist s d.symm = assembleTwist s d := by
  obtain ⟨⟨c,d⟩,rfl⟩ := (componentDartEquiv (G := G)).surjective d
  have he : (componentDartEquiv ⟨c,d⟩).symm = componentDartEquiv ⟨c,d.symm⟩ := rfl
  rw [he]
  dsimp only [assembleTwist]
  rw [(componentDartEquiv (G := G)).symm_apply_apply ⟨c,d.symm⟩,
    (componentDartEquiv (G := G)).symm_apply_apply ⟨c,d⟩]
  exact (s c).twist_symm d

def assemble (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    SignedRotation G where
  σ := assemblePermutation s
  σ_source := assemblePermutation_source s
  cyclic := assemblePermutation_cyclic s
  twist := assembleTwist s
  twist_symm := assembleTwist_symm s

theorem assemble_restrict_sigma
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : G.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    ((assemble s).restrictComponent c).σ d = (s c).σ d := by
  have h := (assemble s).closedRotation_dart c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv) d
  change componentDartEquiv ⟨c,((assemble s).restrictComponent c).σ d⟩ =
    assemblePermutation s (componentDartEquiv ⟨c,d⟩) at h
  rw [assemblePermutation_component] at h
  have he := (componentDartEquiv (G := G)).injective h
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

theorem assemble_restrict_twist
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : G.ConnectedComponent) (d : (G.induce c.supp).Dart) :
    ((assemble s).restrictComponent c).twist d = (s c).twist d := by
  change assembleTwist s (componentDartEquiv ⟨c,d⟩) = _
  dsimp only [assembleTwist]
  rw [(componentDartEquiv (G := G)).symm_apply_apply ⟨c,d⟩]

theorem ext_data {r t : SignedRotation G} (hσ : ∀ d, r.σ d = t.σ d)
    (ht : ∀ d, r.twist d = t.twist d) : r = t := by
  cases r with
  | mk rp rc rt rh =>
    cases t with
    | mk tp tc tt th =>
      have hp : rp = tp := by
        cases rp with
        | mk σ hσs =>
          cases tp with
          | mk τ hτs =>
            have he : σ = τ := Equiv.ext hσ
            cases he
            rfl
      cases hp
      have he : rt = tt := funext ht
      cases he
      rfl

theorem assemble_restrict
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp))
    (c : G.ConnectedComponent) : (assemble s).restrictComponent c = s c := by
  classical
  exact ext_data (assemble_restrict_sigma s c) (assemble_restrict_twist s c)

theorem assemble_genus [Fintype G.ConnectedComponent]
    (s : ∀ c : G.ConnectedComponent, SignedRotation (G.induce c.supp)) :
    (assemble s).eulerGenus = ∑ c : G.ConnectedComponent, (s c).eulerGenus := by
  rw [(assemble s).eulerGenus_sum]
  simp only [assemble_restrict]

end SimpleGraph.SignedRotation



