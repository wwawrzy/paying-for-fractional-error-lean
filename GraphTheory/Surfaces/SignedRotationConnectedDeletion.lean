import GraphTheory.Surfaces.SignedRotationBridgeDeletion
namespace SimpleGraph.SignedRotation
theorem eulerGenus_transport {W : Type*} {H K : SimpleGraph W} (he : H = K) (r : SignedRotation H) :
    (he ▸ r).eulerGenus = r.eulerGenus := by
  subst K
  rfl
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem connected_of_added_edge_of_reachable (hH : (G ⊔ edge u v).Connected)
    (huv : G.Reachable u v) : G.Connected := by
  have hu (x : V) : G.Reachable u x := by
    rcases reachable_endpoint_cases G u v hH x with hx | hx
    · exact hx
    · exact huv.trans hx
  letI : Nonempty V := hH.nonempty
  exact ⟨fun x y => (hu x).symm.trans (hu y)⟩

theorem deletion_genus_le_of_endpoints_reachable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hH : (G ⊔ edge u v).Connected)
    (huv : G.Reachable u v) :
    (deleteAddedEdge G u v hne hmiss r).eulerGenus ≤ r.eulerGenus := by
  exact deletion_genus_le_of_connected G u v hne hmiss r
    (connected_of_added_edge_of_reachable G u v hH huv)
end SimpleGraph.SignedRotation
namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem exists_deletion_genus_le_of_connected (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hH : (G ⊔ edge u v).Connected) :
    ∃ s : SignedRotation G, s.eulerGenus ≤ r.eulerGenus := by
  classical
  by_cases hu : ∃ w, G.Adj u w
  · by_cases hv : ∃ w, G.Adj v w
    · have hends : ∀ b : Bool, ∃ d : G.Dart,
          (augmentedDart G u v hne (Sum.inr b)).fst = d.fst := by
        intro b
        cases b
        · obtain ⟨w,hw⟩ := hu; exact ⟨⟨(u,w),hw⟩,rfl⟩
        · obtain ⟨w,hw⟩ := hv; exact ⟨⟨(v,w),hw⟩,rfl⟩
      refine ⟨deleteAddedEdge G u v hne hmiss r, ?_⟩
      by_cases hr : G.Reachable u v
      · exact deletion_genus_le_of_endpoints_reachable G u v hne hmiss r hH hr
      · exact bridge_deletion_genus_le G u v hne hmiss r hH hr hends
    · have he : G ⊔ edge u v = G ⊔ edge v u := by
        congr 1
        ext x y
        simp only [edge_adj]
        tauto
      let r' : SignedRotation (G ⊔ edge v u) := he ▸ r
      have hg : r'.eulerGenus = r.eulerGenus := eulerGenus_transport he r
      have hc : (G ⊔ edge v u).Connected := he ▸ hH
      have hm : ¬ G.Adj v u := fun h => hmiss h.symm
      refine ⟨deleteAddedEdge G v u hne.symm hm r', ?_⟩
      rw [← hg]
      exact leaf_deletion_genus_le G v u hne.symm hm r'
        (fun w hw => hv ⟨w,hw⟩) hu hc
  · by_cases hv : ∃ w, G.Adj v w
    · exact ⟨deleteAddedEdge G u v hne hmiss r,
        leaf_deletion_genus_le G u v hne hmiss r (fun w hw => hu ⟨w,hw⟩) hv hH⟩
    · have hi (a : V) (ha : ¬ ∃ w, G.Adj a w) (x : V) (hr : G.Reachable a x) : a = x := by
        by_contra hax
        obtain ⟨w,hw⟩ := hr.nonempty_neighborSet_left hax
        exact ha ⟨w,hw⟩
      have hempty : ∀ x y, ¬ G.Adj x y := by
        intro x y hxy
        rcases reachable_endpoint_cases G u v hH x with hx | hx
        · have he := hi u hu x hx
          exact hu ⟨y,he ▸ hxy⟩
        · have he := hi v hv x hx
          exact hv ⟨y,he ▸ hxy⟩
      exact ⟨deleteAddedEdge G u v hne hmiss r,
        deletion_genus_le_of_empty G u v hne hmiss r hempty hH⟩
end SimpleGraph.SignedRotation
