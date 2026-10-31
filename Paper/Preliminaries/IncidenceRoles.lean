import Paper.Preliminaries.BlowupDensity
import Paper.Preliminaries.DepthOneEmbedding
import Paper.Preliminaries.FiberSlots
import Paper.Preliminaries.CoreIncidence

/-! Physically embed actual incidence roles in a bounded clique blowup. -/
namespace Paper.IncidenceRoles
attribute [local instance] Classical.propDecidable
open BlowupProjection
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def embed {m : ℕ} (H : Finset (Finset V)) (origin : H → V) (slot : H → Fin m) :
    V ⊕ H → V × Fin (m + 1)
  | .inl v => (v, 0)
  | .inr C => (origin C, (slot C).succ)

theorem embed_injective {m : ℕ} (H : Finset (Finset V)) (origin : H → V) (slot : H → Fin m)
    (hinj : Function.Injective (fun C => (origin C, slot C))) :
    Function.Injective (embed H origin slot) := by
  intro a b he
  cases a with
  | inl v =>
    cases b with
    | inl w => exact congrArg Sum.inl (congrArg Prod.fst he)
    | inr C =>
      have hh := congrArg (fun p : V × Fin (m + 1) => p.2.val) he
      change 0 = (slot C).val + 1 at hh
      omega
  | inr C =>
    cases b with
    | inl v =>
      have hh := congrArg (fun p : V × Fin (m + 1) => p.2.val) he
      change (slot C).val + 1 = 0 at hh
      omega
    | inr D =>
      have hp := congrArg (fun p : V × Fin (m + 1) => p.1) he
      have hs := congrArg (fun p : V × Fin (m + 1) => p.2.val) he
      have hslot : slot C = slot D := Fin.ext (by change (slot C).val + 1 = (slot D).val + 1 at hs; omega)
      exact congrArg Sum.inr (hinj (Prod.ext hp hslot))

theorem embed_edges {m : ℕ} (H : Finset (Finset V)) (origin : H → V) (slot : H → Fin m)
    (hstar : ∀ C : H, ∀ v ∈ C.val, v = origin C ∨ G.Adj v (origin C)) :
    ∀ a b, (CoreIncidence.graph H).Adj a b →
      (blowup G (m + 1)).Adj (embed H origin slot a) (embed H origin slot b) := by
  intro a b hab
  cases a with
  | inl v =>
    cases b with
    | inl w => exact False.elim hab
    | inr C =>
      refine ⟨?_, hstar C v hab⟩
      intro he
      have hh := congrArg (fun p : V × Fin (m + 1) => p.2.val) he
      change 0 = (slot C).val + 1 at hh
      omega
  | inr C =>
    cases b with
    | inl v =>
      refine ⟨?_, (hstar C v hab).elim (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)⟩
      intro he
      have hh := congrArg (fun p : V × Fin (m + 1) => p.2.val) he
      change (slot C).val + 1 = 0 at hh
      omega
    | inr D => exact False.elim hab

theorem density (H : Finset (Finset V)) (origin : H → V) (m : ℕ)
    (hfib : ∀ v, Fintype.card {C : H // origin C = v} ≤ m)
    (hstar : ∀ C : H, ∀ v ∈ C.val, v = origin C ∨ G.Adj v (origin C))
    {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) :
    DepthOne.Bound (CoreIncidence.graph H) (a * ((m + 1 : ℕ) : ℝ) ^ 4 + (m + 1 : ℕ)) := by
  classical
  obtain ⟨slot, hinj⟩ := FiberSlots.exists_slots origin m hfib
  apply DepthOneEmbedding.bound (embed H origin slot) (embed_injective H origin slot hinj) (embed_edges G H origin slot hstar)
  exact BlowupDensity.bound (by omega) hden ha
end Paper.IncidenceRoles
