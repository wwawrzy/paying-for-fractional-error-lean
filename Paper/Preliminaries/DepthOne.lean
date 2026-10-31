import Paper.Preliminaries.MinorDensity

/-! Radius-one minor models for the auxiliary incidence graphs of initialization.
All-minors density implies this property, but clique-blowup transfers need only
this weaker, actual radius-one notion. -/
namespace Paper.DepthOne
open SevenFoundation
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure StarModel {A : Type u} (J : SimpleGraph A) (G : SimpleGraph V)
    extends SimpleGraph.MinorModel J G where
  root : A → V
  root_mem : ∀ a, root a ∈ branchSet a
  radius_one : ∀ a v, v ∈ branchSet a → root a = v ∨ G.Adj (root a) v

def Bound (t : ℝ) : Prop :=
  ∀ (A : Type u) [Fintype A] [DecidableEq A] (J : SimpleGraph A)
    [DecidableRel J.Adj], StarModel J G → (J.edgeFinset.card : ℝ) ≤ t * Fintype.card A

noncomputable def ofStars (W R : Finset V) (hR : Disjoint R (covered G W)) :
    StarModel (StarMinor.graph G W R) G where
  toMinorModel := StarMinor.model G W R hR
  root i := i.val
  root_mem i := StarMinor.owner_retained G W R hR i
  radius_one i v hv := by
    have h : StarMinor.owner G W v = i.val := hv
    rcases StarMinor.owner_star G W v with he | ha
    · exact Or.inl (h.symm.trans he)
    · exact Or.inr (by rwa [h] at ha)

def restrict {A : Type u} {J : SimpleGraph A} (M : StarModel J G) (S : Set A) :
    StarModel (J.induce S) G where
  branchSet a := M.branchSet a.val
  nonempty a := M.nonempty a.val
  disjoint a b h := M.disjoint a.val b.val (fun he => h (Subtype.ext he))
  connected a := M.connected a.val
  adjacent a b h := M.adjacent a.val b.val h
  root a := M.root a.val
  root_mem a := M.root_mem a.val
  radius_one a v h := M.radius_one a.val v h

theorem induced_bound {A : Type u} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (M : StarModel J G) {t : ℝ} (h : Bound G t) :
    Incidence.InducedDensityBound J t := by
  classical
  intro S
  have hb := h (S : Set A) (J.induce (S : Set A)) (restrict G M (S : Set A))
  simpa only [SimpleGraph.inducedEdgeCount, Fintype.card_eq_nat_card,
    Finset.coe_sort_coe, Nat.card_eq_finsetCard] using hb

theorem bound_of_minor_density {t : ℝ} (h : MinorDensity.Bound G t) : Bound G t := by
  intro A _ _ J _ M
  exact h A J ⟨M.toMinorModel⟩
end Paper.DepthOne
