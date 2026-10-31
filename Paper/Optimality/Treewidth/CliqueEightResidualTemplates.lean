import Paper.Optimality.Treewidth.CliqueCompleteTwoContractions
namespace Paper.CliqueEightResidualTemplates
open SimpleGraph CliqueTwoContractions
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def missing (a b : Fin 5) : Finset (Sym2 (Fin 8)) :=
  {s(0,1),s(0,2),s(3,4),s(5,6),s(1,⟨a.val+3,by omega⟩),s(2,⟨b.val+3,by omega⟩)}
def graph (a b : Fin 5) : SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ s(i,j) ∉ missing a b
  symm := by intro i j h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance (a b : Fin 5) : DecidableRel (graph a b).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ s(i,j) ∉ missing a b))

instance blocks_decidable (e : Fin 8 ≃ Fin 8) (i : Fin 6) (v : Fin 8) :
    Decidable (v ∈ blocks e i) := by
  by_cases h0 : i = 0
  · simp only [blocks,if_pos h0,Set.mem_insert_iff,Set.mem_singleton_iff]
    infer_instance
  · by_cases h1 : i = 1
    · simp only [blocks,if_neg h0,if_pos h1,Set.mem_insert_iff,Set.mem_singleton_iff]
      infer_instance
    · simp only [blocks,if_neg h0,if_neg h1,Set.mem_singleton_iff]
      infer_instance

theorem case_0_2 : (completeGraph (Fin 6)).IsMinor (graph 0 2) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 0 2) e (by decide) (by decide) (by decide)

theorem case_0_3 : (completeGraph (Fin 6)).IsMinor (graph 0 3) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 0 3) e (by decide) (by decide) (by decide)

theorem case_0_4 : (completeGraph (Fin 6)).IsMinor (graph 0 4) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,6,7,5,3]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 0 4) e (by decide) (by decide) (by decide)

theorem case_1_2 : (completeGraph (Fin 6)).IsMinor (graph 1 2) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 1 2) e (by decide) (by decide) (by decide)

theorem case_1_3 : (completeGraph (Fin 6)).IsMinor (graph 1 3) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 1 3) e (by decide) (by decide) (by decide)

theorem case_1_4 : (completeGraph (Fin 6)).IsMinor (graph 1 4) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,3,6,7,5,4]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 1 4) e (by decide) (by decide) (by decide)

theorem case_2_0 : (completeGraph (Fin 6)).IsMinor (graph 2 0) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 2 0) e (by decide) (by decide) (by decide)

theorem case_2_1 : (completeGraph (Fin 6)).IsMinor (graph 2 1) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 2 1) e (by decide) (by decide) (by decide)

theorem case_2_4 : (completeGraph (Fin 6)).IsMinor (graph 2 4) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 2 4) e (by decide) (by decide) (by decide)

theorem case_3_0 : (completeGraph (Fin 6)).IsMinor (graph 3 0) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 3 0) e (by decide) (by decide) (by decide)

theorem case_3_1 : (completeGraph (Fin 6)).IsMinor (graph 3 1) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 3 1) e (by decide) (by decide) (by decide)

theorem case_3_4 : (completeGraph (Fin 6)).IsMinor (graph 3 4) := by
  let f : Fin 8 → Fin 8 := ![0,2,1,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 3 4) e (by decide) (by decide) (by decide)

theorem case_4_0 : (completeGraph (Fin 6)).IsMinor (graph 4 0) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,6,7,5,3]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 4 0) e (by decide) (by decide) (by decide)

theorem case_4_1 : (completeGraph (Fin 6)).IsMinor (graph 4 1) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,3,6,7,5,4]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 4 1) e (by decide) (by decide) (by decide)

theorem case_4_2 : (completeGraph (Fin 6)).IsMinor (graph 4 2) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,6,7,3,5]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 4 2) e (by decide) (by decide) (by decide)

theorem case_4_3 : (completeGraph (Fin 6)).IsMinor (graph 4 3) := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,5,7,3,6]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 4 3) e (by decide) (by decide) (by decide)

theorem case_4_4 : (completeGraph (Fin 6)).IsMinor (graph 4 4) := by
  let f : Fin 8 → Fin 8 := ![0,5,1,2,4,6,3,7]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact CliqueCompleteTwoContractions.complete_minor (graph 4 4) e (by decide) (by decide) (by decide)

theorem surviving (a b : Fin 5) (hf : (graph a b).IsKMinorFree 6)
    (hd : ∀ v, ((graph a b)ᶜ).degree v ≤ 2) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by
  fin_cases a <;> fin_cases b
  · have hh := hd (3 : Fin 8)
    change ((graph 0 0)ᶜ).degree (3 : Fin 8) ≤ 2 at hh
    have he : ((graph 0 0)ᶜ).degree (3 : Fin 8) = 3 := by decide
    omega
  · decide
  · exact False.elim (hf case_0_2)
  · exact False.elim (hf case_0_3)
  · exact False.elim (hf case_0_4)
  · decide
  · have hh := hd (4 : Fin 8)
    change ((graph 1 1)ᶜ).degree (4 : Fin 8) ≤ 2 at hh
    have he : ((graph 1 1)ᶜ).degree (4 : Fin 8) = 3 := by decide
    omega
  · exact False.elim (hf case_1_2)
  · exact False.elim (hf case_1_3)
  · exact False.elim (hf case_1_4)
  · exact False.elim (hf case_2_0)
  · exact False.elim (hf case_2_1)
  · have hh := hd (5 : Fin 8)
    change ((graph 2 2)ᶜ).degree (5 : Fin 8) ≤ 2 at hh
    have he : ((graph 2 2)ᶜ).degree (5 : Fin 8) = 3 := by decide
    omega
  · decide
  · exact False.elim (hf case_2_4)
  · exact False.elim (hf case_3_0)
  · exact False.elim (hf case_3_1)
  · decide
  · have hh := hd (6 : Fin 8)
    change ((graph 3 3)ᶜ).degree (6 : Fin 8) ≤ 2 at hh
    have he : ((graph 3 3)ᶜ).degree (6 : Fin 8) = 3 := by decide
    omega
  · exact False.elim (hf case_3_4)
  · exact False.elim (hf case_4_0)
  · exact False.elim (hf case_4_1)
  · exact False.elim (hf case_4_2)
  · exact False.elim (hf case_4_3)
  · exact False.elim (hf case_4_4)

end Paper.CliqueEightResidualTemplates
