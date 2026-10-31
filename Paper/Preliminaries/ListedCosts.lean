import Paper.Preliminaries.DemandValues
import Paper.Preliminaries.SolutionWord

/-! Reconstruct bounded cost/ID tags from a bounded ID list and the actual
value-vector query. This is local computation, with no extra messages. -/
namespace Paper.ListedCosts
variable {V : Type} [LinearOrder V]

def tags (B K : ℕ) (l : List V) (values : Fin K → ℕ) : SolutionWord.Word V B :=
  ListPacket.unpack (fun i => (ListPacket.pack K l i).map (fun u =>
    toLex (⟨min (values i) B, by have := min_le_right (values i) B; omega⟩, u)))

theorem length (B K : ℕ) (l : List V) (values : Fin K → ℕ) :
    (tags B K l values).length ≤ K := ListPacket.unpack_length _

theorem correct (B K : ℕ) (l : List V) (hlen : l.length ≤ K) (c : V → Fin (B + 1)) :
    tags B K l (DemandValues.values K l c) = l.map (CostTag.tag c) := by
  have he : (fun i : Fin K => (ListPacket.pack K l i).map (fun u =>
      toLex (⟨min (DemandValues.values K l c i) B,
        by have := min_le_right (DemandValues.values K l c i) B; omega⟩, u))) =
      ListPacket.pack K (l.map (CostTag.tag c)) := by
    funext i
    cases hi : l[i.val]? with
    | none => simp [ListPacket.pack, List.getElem?_map, hi]
    | some r =>
      simp only [ListPacket.pack, List.getElem?_map, hi, Option.map_some]
      apply congrArg some
      apply congrArg toLex
      apply Prod.ext
      · apply Fin.ext
        simp only [DemandValues.values, hi]
        exact min_eq_left (by have := (c r).isLt; omega)
      · rfl
  rw [tags, he]
  exact ListPacket.unpack_pack K _ (by simpa only [List.length_map] using hlen)
end Paper.ListedCosts
