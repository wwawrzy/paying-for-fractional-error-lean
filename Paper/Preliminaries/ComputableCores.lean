import Paper.Preliminaries.CoreHierarchy

/-! Finite computable sunflower-core enumeration without a public vertex
universe. Only supplied finite lists and their union are enumerated. -/
namespace Paper.ComputableCores
variable {V : Type} [DecidableEq V]

def sunflower (F : Finset (Finset V)) (C : Finset V) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s ∩ t = C

instance decidableSunflower (F : Finset (Finset V)) (C : Finset V) : Decidable (sunflower F C) := by
  unfold sunflower
  infer_instance

def cores (H : Finset (Finset V)) (q : ℕ) : Finset (Finset V) :=
  (H.biUnion id).powerset.filter (fun C => C.Nonempty ∧
    (H.powerset.filter (fun F => F.card = q ∧ sunflower F C)).Nonempty)

theorem mem_cores (H : Finset (Finset V)) (q : ℕ) (C : Finset V) :
    C ∈ cores H q ↔ C ⊆ H.biUnion id ∧ C.Nonempty ∧
      ∃ F ⊆ H, F.card = q ∧ sunflower F C := by
  rw [cores, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hn, F, hF⟩
    obtain ⟨hFH, hq, hs⟩ := Finset.mem_filter.mp hF
    exact ⟨hsub, hn, F, Finset.mem_powerset.mp hFH, hq, hs⟩
  · rintro ⟨hsub, hn, F, hF, hq, hs⟩
    exact ⟨hsub, hn, F, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hF, hq, hs⟩⟩

variable [Fintype V]

theorem eq_cores (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) :
    cores H q = CoreHierarchy.cores H q := by
  ext C
  rw [mem_cores, CoreHierarchy.mem_cores]
  constructor
  · rintro ⟨_, hn, F, hF, hqF, hsun⟩
    exact ⟨hn, F, hF, hqF, hsun⟩
  · intro hC
    refine ⟨?_, hC⟩
    obtain ⟨s, hs, hCs⟩ := CoreHierarchy.core_subset_original H q hq
      ((CoreHierarchy.mem_cores H q C).mpr hC)
    exact hCs.trans (fun v hv => Finset.mem_biUnion.mpr ⟨s, hs, hv⟩)
end Paper.ComputableCores
