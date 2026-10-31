import Paper.Solver.LocalSearch.GeneralCoveringOwnerFramePublicParts
import Paper.Solver.LocalSearch.GeneralCoveringRandomFractionalPhysical

/-! Pointwise comparison with the accepted physical randomized program.
The reference task answers are read from its actual sparse dictionaries;
all masks, metadata, costs and carriers are connected by proved execution
equalities. No observer or task-score contract is supplied. -/
namespace Paper.GeneralCoveringOwnerFrameTaskPointwise
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs
open GeneralCoveringOwnerFrameTaskCandidates
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def randomInput {B Δ k b n : ℕ} (s : V → Input V B)
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) := fun v => ((s v).1, ((s v).2, β v))

noncomputable def geometry {ids B : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (s : V → Input V B)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :=
  GeneralCoveringTaskFractionalRepair.geometry G I
    (GeneralCoveringRandomFractionalPhysical.original G I L Δ k hk t ht b n B (randomInput s β) d)

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj :=
      fun _ _ => Classical.propDecidable _

section Original
variable {ids B : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
variable (t : ℕ) (ht : 0 < t) (b n : ℕ) (s : V → Input V B)
variable (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
variable (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
local notation "J" => graph G d.cover d.D d.R L Q
local notation "e" => GeneralCoveringTaskPartitionMarks.lowEmbedding d.D Q
local notation "H" => GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L Q
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image d.D Q
local notation "P" => ActiveFiniteBitPartition.partition H Δ k hk t b n U β
local notation "S" => GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L hk t β
local notation "g" => geometry G I L Δ k hk t ht b n s d β
local notation "task" => candidate G I d.cover d.D d.R L Δ k t b n β

theorem candidate_eq (a q : ℕ) (hB : 1 ≤ B) (v anchor : V)
    (ha : anchor ∈ (frames G I L Δ k n s v).anchors) (mask : Fin (partSlots Δ k) → Bool)
    (hv : (task anchor mask).valid = true) :
    (GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v (task anchor mask)).val =
      GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB
        (PublicPartPullback.pull e (task anchor mask).owners) v := by
  let T := (task anchor mask).owners
  let Z := PublicPartPullback.pull e T
  have hd := sound G I d.cover d.targets d.D d.R L Δ k t b n hk ht d.incidence d.local_rows
    s d.center d.demand d.candidates d.inverse β v anchor ha mask hv
  have hT : T ∈ (P).parts := hd.1
  have hZ : Z ∈ (S).parts := GeneralCoveringOwnerFramePublicParts.pull_part G d.cover d.D d.R L Δ k hk t b n β T hT
  have himage : Z.image e = T := GeneralCoveringOwnerFramePublicParts.image_pull G d.cover d.D d.R L Δ k hk t b n β T hT
  have howners : (task anchor mask).owners = GeneralCoveringOwnerRoleFrames.partIds d.D Q Z := himage.symm
  have hanchor : anchor ∈ GeneralCoveringOwnerRoleFrames.partIds d.D Q Z := howners ▸ hd.2.1
  have hb : ∀ i ∈ Z, (task anchor mask).boundary i.val.val =
      decide (i ∈ BoundaryOwners.vertices J Finset.univ (S).parts) := by
    intro i hi
    have hiT : e i ∈ T := (PublicPartPullback.mem_pull e T i).mp hi
    exact (hd.2.2.2.2 _ hiT).trans (Bool.decide_congr
      (GeneralCoveringOwnerFramePublicParts.boundary G d.cover d.D d.R L Δ k hk t b n β i).symm)
  have hr := GeneralCoveringOwnerFrameTaskRuntime.score G I L Δ k n d.cover d.targets d.D d.R
    d.incidence d.local_rows s d.center d.demand d.candidates d.inverse Z _
    ((S).connected Z hZ) ((S).size Z hZ) anchor hanchor (task anchor mask) hv howners hb a q hB v
  change (GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v (task anchor mask)).val =
    GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB Z v
  rw [GeneralCoveringTaskFractionalAggregate.partNumerator_eq G I g a q hB Z hZ v,
    GeneralCoveringTaskFractionalInvariant.part_numerator G I g Z hZ a q hB]
  apply congrArg Fin.val
  rw [hr]
  unfold GeneralCoveringTaskFractionalParallel.clientOutput
  congr 2
  funext u
  exact (GeneralCoveringRandomFractionalPhysical.native_cost G I L Δ k t b n B (randomInput s β) u).symm

theorem part_zero (a q : ℕ) (hB : 1 ≤ B) (v : V) (T : Finset V) (hT : T ∈ (P).parts)
    (hn : ¬∃ anchor ∈ (frames G I L Δ k n s v).anchors, MaskedMinimum.minimum T = some anchor) :
    GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB (PublicPartPullback.pull e T) v = 0 := by
  let Z := PublicPartPullback.pull e T
  have hZ : Z ∈ (S).parts := GeneralCoveringOwnerFramePublicParts.pull_part G d.cover d.D d.R L Δ k hk t b n β T hT
  have himage : Z.image e = T := GeneralCoveringOwnerFramePublicParts.image_pull G d.cover d.D d.R L Δ k hk t b n β T hT
  have hv : v ∉ vertices G d.cover d.D d.R L Q Z := by
    intro hv
    obtain ⟨i, hi⟩ := (S).nonempty Z hZ
    have hiT : e i ∈ T := himage ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨anchor, hmin, _⟩ := MaskedMinimum.minimum_le hiT
    have ha : anchor ∈ GeneralCoveringOwnerRoleFrames.partIds d.D Q Z := by
      change anchor ∈ Z.image e
      rw [himage]
      exact MaskedMinimum.minimum_mem hmin
    have hc := GeneralCoveringOwnerFrameTaskRuntime.carrier G I L Δ k n d.cover d.targets d.D d.R
      d.incidence d.local_rows s d.center d.demand d.candidates d.inverse Z
      ((S).connected Z hZ) ((S).size Z hZ) anchor ha hv
    have hanchor : anchor ∈ (frames G I L Δ k n s v).anchors := (Finset.mem_filter.mp hc).2
    exact hn ⟨anchor, hanchor, hmin⟩
  change GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB Z v = 0
  rw [GeneralCoveringTaskFractionalAggregate.partNumerator_eq G I g a q hB Z hZ v]
  simp only [GeneralCoveringTaskFractionalParallel.numerator,
    GeneralCoveringTaskFractionalParallel.lookup_outside G I g Z hZ a q hB v hv,
    Option.map_none, Option.getD_none]

theorem retained_tasks (a q : ℕ) (hB : 1 ≤ B) (v : V) :
    ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G (randomInput s β) v).1.2.2.1 =
      (GeneralCoveringTaskFractionalAggregate.program I L a B k q hB).runEncoded G
        (GeneralCoveringTaskFractionalRepair.roleInput G I L Δ
          (GeneralCoveringRandomFractionalPhysical.nativeInput G I L Δ k t b n B (randomInput s β))) v := by
  simp only [GeneralCoveringRandomFractionalPhysical.native_eq,
    GeneralCoveringTaskFractionalRepair.run_program, GeneralCoveringTaskFractionalRepair.before_eq]

include hk ht

/-- Every valid anchored mask is counted once, every invalid mask is zero,
and unreceived actual parts have zero own coordinate. The resulting sum is
the retained task numerator of the SAME accepted randomized physical run. -/
theorem sum (a q : ℕ) (hB : 1 ≤ B) (v : V) :
    (∑ anchor ∈ (frames G I L Δ k n s v).anchors,
      ∑ mask : Fin (partSlots Δ k) → Bool,
        (GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v (task anchor mask)).val) =
      ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G (randomInput s β) v).1.2.2.1 := by
  classical
  let A := (frames G I L Δ k n s v).anchors
  let Pair := V × (Fin (partSlots Δ k) → Bool)
  let Valid : Pair → Prop := fun p => p.1 ∈ A ∧ (task p.1 p.2).valid = true
  let f : Pair → ℕ := fun p => if p.1 ∈ A then
    (GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s p.1 v (task p.1 p.2)).val else 0
  have hz : (∑ p : {p : Pair // ¬Valid p}, f p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    dsimp only [f]
    by_cases ha : p.val.1 ∈ A
    · rw [if_pos ha]
      have hv : (task p.val.1 p.val.2).valid = false := by
        cases he : (task p.val.1 p.val.2).valid with
        | false => rfl
        | true => exact False.elim (p.property ⟨ha, he⟩)
      rw [GeneralCoveringOwnerFrameTaskRuntime.score_invalid G I L Δ a B k n q hB s p.val.1 v _ hv]
      rfl
    · rw [if_neg ha]
  have hsource := Fintype.sum_subtype_add_sum_subtype Valid f
  rw [hz, add_zero] at hsource
  let Public := {T : Finset V // T ∈ (P).parts}
  let Eligible : Public → Prop := fun T => ∃ anchor ∈ A, MaskedMinimum.minimum T.val = some anchor
  let value : Public → ℕ := fun T => GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB
    (PublicPartPullback.pull e T.val) v
  have hzparts : (∑ T : {T : Public // ¬Eligible T}, value T.val) = 0 := by
    apply Finset.sum_eq_zero
    intro T _
    exact part_zero G I L Δ k hk t ht b n s d β a q hB v T.val.val T.val.property T.property
  have hparts := Fintype.sum_subtype_add_sum_subtype Eligible value
  rw [hzparts, add_zero] at hparts
  let ee : {T : Finset V // T ∈ (P).parts ∧ ∃ anchor ∈ A, MaskedMinimum.minimum T = some anchor} ≃
      {T : Public // Eligible T} :=
    { toFun := fun T => ⟨⟨T.val, T.property.1⟩, T.property.2⟩
      invFun := fun T => ⟨T.val.val, T.val.property, T.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hequiv : (∑ p : {p : Pair // Valid p}, f p.val) =
      ∑ T : {T : Public // Eligible T}, value T.val := by
    apply Fintype.sum_equiv
      ((GeneralCoveringOwnerFrameTaskCandidates.equiv G I d.cover d.targets d.D d.R L Δ k t b n hk ht
        d.incidence d.local_rows s d.center d.demand d.candidates d.inverse β v).trans ee)
    intro p
    change (if p.val.1 ∈ A then
      (GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s p.val.1 v (task p.val.1 p.val.2)).val else 0) = _
    rw [if_pos p.property.1]
    exact candidate_eq G I L Δ k hk t ht b n s d β a q hB v p.val.1 p.property.1 p.val.2 p.property.2
  calc
    _ = ∑ anchor ∈ A, ∑ mask : Fin (partSlots Δ k) → Bool, f (anchor, mask) := by
      apply Finset.sum_congr rfl
      intro anchor ha
      change anchor ∈ A at ha
      apply Finset.sum_congr rfl
      intro mask _
      simp only [f, if_pos ha]
    _ = ∑ anchor : V, ∑ mask : Fin (partSlots Δ k) → Bool, f (anchor, mask) := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro anchor _ ha
      simp only [f, if_neg ha, Finset.sum_const_zero]
    _ = ∑ p : Pair, f p := (Fintype.sum_prod_type _).symm
    _ = ∑ p : {p : Pair // Valid p}, f p.val := hsource.symm
    _ = ∑ T : {T : Public // Eligible T}, value T.val := hequiv
    _ = ∑ T : Public, value T := hparts
    _ = ∑ T : {T : Finset (Low d.D Q) // T ∈ (S).parts},
        GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB T.val v := by
      exact Fintype.sum_equiv (GeneralCoveringOwnerFramePublicParts.equiv G d.cover d.D d.R L Δ k hk t b n β)
        value (fun T => GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB T.val v) (fun _ => rfl)
    _ = ∑ T ∈ (S).parts, GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB T v := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (S).parts (fun T => GeneralCoveringTaskFractionalAggregate.partNumerator G I g a q hB T v)
    _ = _ := by
      rw [retained_tasks G I L Δ k t b n s β a q hB v]
      exact (GeneralCoveringTaskFractionalAggregate.output_sum G I g a q hB v).symm

end Original
end Paper.GeneralCoveringOwnerFrameTaskPointwise

#print axioms Paper.GeneralCoveringOwnerFrameTaskPointwise.candidate_eq
#print axioms Paper.GeneralCoveringOwnerFrameTaskPointwise.part_zero
#print axioms Paper.GeneralCoveringOwnerFrameTaskPointwise.retained_tasks
#print axioms Paper.GeneralCoveringOwnerFrameTaskPointwise.sum
