import GraphTheory.Surfaces.SignedRotation

/-! Restriction of dart rotations to vertex sets closed under adjacency.
Such sets include connected components; both endpoints of every retained
dart remain in the induced graph. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
  (s : Set V) (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)

def closedDartEquiv : (G.induce s).Dart ≃ {d : G.Dart // d.fst ∈ s} where
  toFun d := ⟨⟨(d.fst.val, d.snd.val), d.adj⟩, d.fst.property⟩
  invFun d := ⟨(⟨d.val.fst, d.property⟩, ⟨d.val.snd, hs d.property d.val.adj⟩), d.val.adj⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

def closedRotation : Equiv.Perm (G.induce s).Dart :=
  (closedDartEquiv s hs).trans
    ((r.σ.subtypePerm (p := fun d => d.fst ∈ s)
      (fun d => by
        change (r.σ d).fst ∈ s ↔ d.fst ∈ s
        rw [r.σ_source])).trans (closedDartEquiv s hs).symm)

theorem closedRotation_source (d : (G.induce s).Dart) :
    (r.closedRotation s hs d).fst = d.fst := by
  apply Subtype.ext
  exact r.σ_source ((closedDartEquiv s hs) d).val

theorem closedRotation_dart (d : (G.induce s).Dart) :
    ((closedDartEquiv s hs) (r.closedRotation s hs d)).val =
      r.σ ((closedDartEquiv s hs d).val) := by
  simp [closedRotation]

theorem closedRotation_pow_dart (d : (G.induce s).Dart) (n : ℕ) :
    ((closedDartEquiv s hs) ((r.closedRotation s hs ^ n) d)).val =
      (r.σ ^ n) ((closedDartEquiv s hs d).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      r.closedRotation_dart, ih]

theorem closedRotation_symm_dart (d : (G.induce s).Dart) :
    ((closedDartEquiv s hs) ((r.closedRotation s hs).symm d)).val =
      r.σ.symm ((closedDartEquiv s hs d).val) := by
  apply r.σ.injective
  rw [Equiv.apply_symm_apply]
  have h := r.closedRotation_dart s hs ((r.closedRotation s hs).symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem closedRotation_cyclic [Fintype V] [DecidableRel G.Adj]
    (d e : (G.induce s).Dart) (h : d.fst = e.fst) :
    (r.closedRotation s hs).SameCycle d e := by
  have hc := r.cyclic ((closedDartEquiv s hs d).val)
    ((closedDartEquiv s hs e).val) (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  apply (closedDartEquiv s hs).injective
  apply Subtype.ext
  rw [r.closedRotation_pow_dart, hn]

def restrictClosed [Fintype V] [DecidableRel G.Adj] : SignedRotation (G.induce s) where
  σ := r.closedRotation s hs
  σ_source := r.closedRotation_source s hs
  cyclic := r.closedRotation_cyclic s hs
  twist d := r.twist ((closedDartEquiv s hs d).val)
  twist_symm d := r.twist_symm ((closedDartEquiv s hs d).val)

def restrictComponent [Fintype V] [DecidableRel G.Adj] (c : G.ConnectedComponent) :
    SignedRotation (G.induce c.supp) :=
  r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv)

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.closedRotation_source
#print axioms SimpleGraph.SignedRotation.closedRotation_dart
#print axioms SimpleGraph.SignedRotation.closedRotation_cyclic
#print axioms SimpleGraph.SignedRotation.restrictClosed
#print axioms SimpleGraph.SignedRotation.restrictComponent
