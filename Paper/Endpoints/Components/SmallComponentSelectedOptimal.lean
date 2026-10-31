import Paper.Endpoints.Components.SmallComponentSelectedWord

namespace Paper.SmallComponentSelectedOptimal

theorem logical_selected_optimal
    {V : Type} [Fintype V] [LinearOrder V]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (v : V) (hv : v ∈ X.supp)
    (hsolved : ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 = true) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let D := H.filter (fun u => ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s u).2 = true)
    D ⊆ Paper.CoveringSupport.admissible cover (R ∩ H) ∧
      Paper.GeneralCoveringIntegral.Covers cover (R ∩ H) D ∧
      D.sum (fun u => (s u).cost.val) ≤ K ∧
      ∀ O : Finset V, O ⊆ Paper.CoveringSupport.admissible cover (R ∩ H) →
        Paper.GeneralCoveringIntegral.Covers cover (R ∩ H) O →
        D.sum (fun u => (s u).cost.val) ≤ O.sum (fun u => (s u).cost.val) := by
  classical
  let I := Paper.CoveringIncidence.graph cover R
  let H := Paper.IncidenceComponent.vertices I X
  let t := Paper.SmallComponentProgram.acceptedInput I ids K s
  let ans := (Paper.NormalizedComponentSearch.program ids
    (2 * Paper.SmallComponentProgram.radius K) a B K hB).runEncoded I t
  let D := H.filter (fun u => ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded I s u).2 = true)
  change D ⊆ Paper.CoveringSupport.admissible cover (R ∩ H) ∧
    Paper.GeneralCoveringIntegral.Covers cover (R ∩ H) D ∧
    D.sum (fun u => (s u).cost.val) ≤ K ∧
    ∀ O : Finset V, O ⊆ Paper.CoveringSupport.admissible cover (R ∩ H) →
      Paper.GeneralCoveringIntegral.Covers cover (R ∩ H) O →
      D.sum (fun u => (s u).cost.val) ≤ O.sum (fun u => (s u).cost.val)
  obtain ⟨w, hw, hcost, hflags⟩ :=
    Paper.SmallComponentSelectedWord.logical_selected_word cover targets R hinc a ha hden
      B K hB ids s hd hC ht X v hv hsolved
  rw [Paper.SmallComponentProgram.logical_run] at hsolved
  have hactive := ((Paper.SmallComponentDecode.decode_solved_iff K v
    (ans v, (t v).active)).mp hsolved).1
  obtain ⟨hall, hdiam⟩ :=
    Paper.SmallComponentAcceptedContext.accepted_component_context I ids K s X v hv hactive
  obtain ⟨hsupp, hadm, hcover, hcostw, hmin⟩ :=
    Paper.ParallelComponentSearch.returned_original_optimal cover targets R X
      (2 * Paper.SmallComponentProgram.radius K) hdiam hinc a ha hden B K hB ids t hall
      (fun x => hd x) (fun x => hC x) (fun x => ht x) (fun x hx => hc x hx) v hv w hw hcost
  have heq : D = Paper.SmallComponentSetDecision.support w := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      obtain ⟨huH, hsel⟩ := Finset.mem_filter.mp hu
      exact (Paper.SmallComponentSetDecision.mem_support w u).mpr
        ((hflags u ((Paper.IncidenceComponent.mem_vertices I X u).mp huH)).mp hsel)
    · intro hu
      have huH : u ∈ H := hsupp hu
      exact Finset.mem_filter.mpr ⟨huH,
        (hflags u ((Paper.IncidenceComponent.mem_vertices I X u).mp huH)).mpr
          ((Paper.SmallComponentSetDecision.mem_support w u).mp hu)⟩
  rw [heq]
  exact ⟨hadm, hcover, hcostw.trans hcost, hmin⟩

end Paper.SmallComponentSelectedOptimal

#print axioms Paper.SmallComponentSelectedOptimal.logical_selected_optimal
