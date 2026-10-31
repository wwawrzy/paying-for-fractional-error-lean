import Paper.Owners.Construction.OwnerPayloadRead

/-! Read a root payload throughout its entire owner star, including vertices
which are not remaining demands. The actual read program uses one broadcast. -/
namespace Paper.OwnerPayloadStarRead
open BroadcastModel SevenFoundation
variable {V A : Type} [LinearOrder V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem owner_local (D : Finset V) (v : V) :
    OwnerSupport.owner G D v = v ∨ G.Adj (OwnerSupport.owner G D v) v := by
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  by_cases hv : v ∈ D
  · exact Or.inl (OwnerSupport.owner_center G D hv)
  by_cases hn : ((closed G v) ∩ D).Nonempty
  · have hm := (Finset.mem_inter.mp (Finset.min'_mem ((closed G v) ∩ D) hn)).1
    have he : OwnerSupport.owner G D v = ((closed G v) ∩ D).min' hn := by
      unfold OwnerSupport.owner
      rw [hinst]
      simp only [if_neg hv, dif_pos hn]
    rw [← he] at hm
    exact ((mem_closed G _ _).mp hm).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact Or.inl (by
      unfold OwnerSupport.owner
      rw [hinst]
      simp only [if_neg hv, dif_neg hn])

theorem correct {w : ℕ} (P : BitCode A w) (D : Finset V)
    (active : Finset V) (f : V → A) (s : V → OwnerPayloadRead.Input V A)
    (ho : ∀ u, (s u).owner = OwnerSupport.owner G D u)
    (hr : ∀ u, (s u).remaining = true)
    (ha : ∀ u, (s u).active = decide (u ∈ active))
    (hp : ∀ u, (s u).payload = f u) (v : V) :
    (OwnerPayloadRead.program P).run G s v =
      if OwnerSupport.owner G D v ∈ active then
        some (OwnerSupport.owner G D v, f (OwnerSupport.owner G D v)) else none := by
  change OwnerPayloadRead.read v (G.neighborFinset v) (s v)
    (fun u => ((s u.val).active, (s u.val).payload)) = _
  unfold OwnerPayloadRead.read
  rw [hr v, if_pos rfl, ho v]
  by_cases he : OwnerSupport.owner G D v = v
  · rw [if_pos he, ha v, hp v, he]
    by_cases h : v ∈ active <;> simp only [h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · have hn : OwnerSupport.owner G D v ∈ G.neighborFinset v :=
      (SimpleGraph.mem_neighborFinset G v _).mpr ((owner_local G D v).resolve_left he).symm
    rw [if_neg he, dif_pos hn]
    dsimp only
    simp only [ha, hp]
    by_cases h : OwnerSupport.owner G D v ∈ active <;>
      simp only [h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]

end Paper.OwnerPayloadStarRead
