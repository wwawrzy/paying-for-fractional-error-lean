import Paper.Preliminaries.GuardedRoutes
import Paper.Owners.Construction.HeavyComponent

/-! Each remaining owner component maps inside one actual physical deletion
component. Root weights transfer its half-balance without assuming it. -/
namespace Paper.RouteComponents
attribute [local instance] Classical.propDecidable
open DeletionComponents HeavyComponent GuardedRoutes
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {K : SimpleGraph A} {G : SimpleGraph B} [DecidableRel K.Adj] [DecidableRel G.Adj]

noncomputable def target (S : System K G) (Z : Finset B)
    (C : (deleted K (cut S Z)).ConnectedComponent) : (deleted G Z).ConnectedComponent :=
  (deleted G Z).connectedComponentMk (rootAfter S Z C.out)

theorem image_subset (S : System K G) (Z : Finset B)
    (C : (deleted K (cut S Z)).ConnectedComponent) :
    (physical K (cut S Z) C).image S.root ⊆ physical G Z (target S Z C) := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨haNot, haC⟩ := (mem_physical K (cut S Z) C a).mp ha
  have hr := C.reachable_of_mem_supp C.out_eq haC
  have hs := GuardedRoutes.reachable S Z hr
  have he := (SimpleGraph.ConnectedComponent.sound hs).symm
  apply (mem_physical G Z (target S Z C) (S.root a)).mpr
  refine ⟨root_avoids S Z haNot, ?_⟩
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr he

noncomputable def roots (S : System K G) : Finset B := Finset.univ.image S.root
noncomputable def rootWeight (S : System K G) (b : B) : ℝ := if b ∈ roots S then 1 else 0

theorem weight_nonneg (S : System K G) (b : B) : 0 ≤ rootWeight S b := by
  unfold rootWeight
  split <;> norm_num

theorem mass_eq (S : System K G) (T : Finset B) : mass (rootWeight S) T = (T ∩ roots S).card := by
  classical
  have he : T.filter (fun b => b ∈ roots S) = T ∩ roots S := by ext b; simp
  unfold mass rootWeight
  rw [← Finset.sum_filter, he]
  simp

theorem total (S : System K G) : (∑ b, rootWeight S b) = Fintype.card A := by
  have hh := mass_eq S (Finset.univ : Finset B)
  rw [Finset.inter_eq_right.mpr (Finset.subset_univ (roots S))] at hh
  have hc : (roots S).card = Fintype.card A := by
    rw [roots, Finset.card_image_of_injective _ S.injective, Finset.card_univ]
  simpa only [mass, hc] using hh

theorem component_mass (S : System K G) (Z : Finset B)
    (C : (deleted K (cut S Z)).ConnectedComponent) :
    ((physical K (cut S Z) C).card : ℝ) ≤ mass (rootWeight S) (physical G Z (target S Z C)) := by
  classical
  rw [mass_eq]
  have hs : (physical K (cut S Z) C).image S.root ⊆ physical G Z (target S Z C) ∩ roots S := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_inter.mpr ⟨image_subset S Z C (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ S.injective] at hc
  exact_mod_cast hc

theorem balanced_transfer (S : System K G) (Z : Finset B)
    (hbalance : ∀ D : (deleted G Z).ConnectedComponent,
      mass (rootWeight S) (physical G Z D) ≤ (∑ b, rootWeight S b) / 2) :
    ∀ C : (deleted K (cut S Z)).ConnectedComponent,
      ((physical K (cut S Z) C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  intro C
  have hh := (component_mass S Z C).trans (hbalance (target S Z C))
  simpa only [total S] using hh
end Paper.RouteComponents
