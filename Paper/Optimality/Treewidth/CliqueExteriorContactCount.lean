import Paper.Optimality.Treewidth.CliqueExteriorContacts
import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.CliqueExteriorContactCount
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable
noncomputable def missing (v x : V) : Finset V := ((G.neighborFinset v).erase x).filter (fun y => ¬G.Adj x y)
theorem degree_balance (v x : V) (hx : G.Adj v x) :
    G.degree x+(missing G v x).card = G.degree v+
      G.inducedDegree x ((insert v (G.neighborFinset v))ᶜ) := by
  classical
  let N := G.neighborFinset v
  let C := insert v N
  have hxN : x ∈ N := (G.mem_neighborFinset v x).mpr hx
  have hvN : v ∉ N := G.notMem_neighborFinset_self v
  have hp := CliquePartitionDegrees.partition G C x
  have hc : G.inducedDegree x C = G.inducedDegree x N+1 := by
    dsimp only [SimpleGraph.inducedDegree,C]
    rw [Finset.filter_insert]
    simp only [hx.symm,if_true]
    rw [Finset.card_insert_of_notMem (fun hh => hvN (Finset.mem_filter.mp hh).1)]
  have ha : ((N.erase x).filter (G.Adj x)) = N.filter (G.Adj x) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_erase]
    constructor
    · intro h; exact ⟨h.1.2,h.2⟩
    · intro h; exact ⟨⟨fun he => G.irrefl (he ▸ h.2),h.1⟩,h.2⟩
  have hh := Finset.card_filter_add_card_filter_not (s := N.erase x) (G.Adj x)
  rw [ha,Finset.card_erase_of_mem hxN,G.card_neighborFinset_eq_degree] at hh
  change G.inducedDegree x N+(missing G v x).card=G.degree v-1 at hh
  have hpos : 0 < G.degree v := by
    exact (G.degree_pos_iff_exists_adj v).mpr ⟨x,hx⟩
  rw [hc] at hp
  change G.degree x+(missing G v x).card=G.degree v+G.inducedDegree x Cᶜ
  omega

theorem missing_le_outside (v x : V) (hx : G.Adj v x) (hmin : G.degree v ≤ G.degree x) :
    (missing G v x).card ≤ G.inducedDegree x ((insert v (G.neighborFinset v))ᶜ) := by
  have hh := degree_balance G v x hx
  omega

theorem two_contacts (v x : V) (hx : G.Adj v x) (hmin : G.degree v ≤ G.degree x)
    (hmiss : 2 ≤ (missing G v x).card) :
    ∃ a ∈ (insert v (G.neighborSet v))ᶜ, ∃ b ∈ (insert v (G.neighborSet v))ᶜ,
      a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  classical
  have hh := missing_le_outside G v x hx hmin
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
    (show 1 < (((insert v (G.neighborFinset v))ᶜ).filter (G.Adj x)).card by
      change 1 < G.inducedDegree x ((insert v (G.neighborFinset v))ᶜ)
      omega)
  obtain ⟨haC,hxa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbC,hxb⟩ := Finset.mem_filter.mp hb
  refine ⟨a,?_,b,?_,hab,hxa,hxb⟩
  · simpa only [Finset.mem_compl,Finset.mem_insert,G.mem_neighborFinset,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_setOf_eq] using haC
  · simpa only [Finset.mem_compl,Finset.mem_insert,G.mem_neighborFinset,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_setOf_eq] using hbC
end Paper.CliqueExteriorContactCount
#print axioms Paper.CliqueExteriorContactCount.degree_balance
#print axioms Paper.CliqueExteriorContactCount.missing_le_outside
#print axioms Paper.CliqueExteriorContactCount.two_contacts
