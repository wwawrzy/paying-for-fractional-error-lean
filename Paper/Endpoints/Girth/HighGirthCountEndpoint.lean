import Paper.Endpoints.Girth.HighGirthRetainedDensity
set_option maxHeartbeats 400000
namespace Paper.HighGirthCountEndpoint
theorem selected_vertex_count_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (a : Real) (ha : 1 ≤ a) (ha_upper : a < (8 : Real) / 7)
    (hden : Paper.Incidence.InducedDensityBound G a) :
    (8 - 7 * a) / 2 * (Paper.HighGirthAttachments.count G x : Real) ≤
      a * (Paper.HighGirthRounding.first G x).card +
      (4 * a - 2) * (Paper.HighGirthRounding.middle G x).card +
      (4 - 3 * a) * (2 * Paper.HighGirthRounding.penalty G x + Paper.HighGirthRounding.oversupply G x) ∧
    ((Paper.HighGirthRounding.output G x).card : Real) ≤
      (Paper.HighGirthRounding.first G x).card +
      a * (Paper.HighGirthRounding.middle G x).card / (3 - 2 * a) +
      5 * (Paper.HighGirthAttachments.count G x : Real) +
      4 * (Paper.HighGirthRounding.middle G x).card := by
  classical
  constructor
  swap
  · exact Paper.HighGirthSelectedCount.selected_vertex_bound G x a ha ha_upper hden
  let u : Real := (Paper.HighGirthRetainedSet.vertices G x).card
  let q : Real := Paper.HighGirthAttachments.count G x
  let s : Real := (Paper.HighGirthAttachments.connectors G x).card
  let w : Real := (Paper.HighGirthRounding.first G x).card
  let l : Real := (Paper.HighGirthRounding.middle G x).card
  let c : Real := (Paper.HighGirthComponentCounting.freeComponents G x).card
  let cp : Real := (Paper.HighGirthComponentCounting.pathComponents G x).card
  let c1 : Real := (Paper.HighGirthFreeAttachmentClasses.one G x).card
  let c2 : Real := (Paper.HighGirthFreeAttachmentClasses.two G x).card
  let b2 : Real := (Paper.HighGirthFewAttachments.twoFamily G x).card
  let P := Paper.HighGirthRounding.penalty G x
  let O := Paper.HighGirthRounding.oversupply G x
  have hd := Paper.HighGirthRetainedDensity.retained_density_bound G x a hden
  change u-cp+q+s ≤ a*(u+s+w) at hd
  have hcp : cp ≤ c+2*l := by dsimp only [cp,c,l]; exact_mod_cast (Paper.HighGirthPathComponentCount.path_component_count G x).2
  have hsq : s ≤ q := by dsimp only [s,q]; exact_mod_cast (Paper.HighGirthAttachmentCounts.attachment_count_bounds G x).2.2
  have ht : u+4*c+c2 ≤ 5*q+4*l+b2 := by dsimp only [u,c,c2,q,l,b2]; exact_mod_cast Paper.HighGirthRetainedSize.retained_set_size_bound G x
  have hclasses := Paper.HighGirthFreeClassBounds.free_attachment_class_bounds G x
  have hc : 3*c ≤ q+2*c1+c2 := by dsimp only [c,q,c1,c2]; exact_mod_cast hclasses.1
  have hc2 : c1+2*c2 ≤ q := by dsimp only [c1,c2,q]; exact_mod_cast hclasses.2
  have heq : Paper.HighGirthFreeAttachmentClasses.one G x = Paper.HighGirthFewAttachments.oneFamily G x := by
    ext K
    simp [Paper.HighGirthFreeAttachmentClasses.one,Paper.HighGirthComponentCounting.freeComponents,
      Paper.HighGirthComponentCounting.pathComponents,Paper.HighGirthFewAttachments.oneFamily,
      Paper.HighGirthFreePaths.isFreePath,and_assoc]
  have hhalf : c1+b2 ≤ 4*P+2*O := by
    have hh := Paper.HighGirthFewAttachments.count_bound G x hx
    rw [←heq] at hh
    exact hh
  have ha1 : 0 ≤ a-1 := by linarith
  have ha5 : 0 ≤ 5-4*a := by linarith
  have ha8 : 0 ≤ 8-7*a := by linarith
  have ha4 : 0 ≤ (4-3*a)/2 := by linarith
  have hsprod := mul_nonneg ha1 (sub_nonneg.mpr hsq)
  have hd' : (2-a)*q ≤ (a-1)*u+c+2*l+a*w := by nlinarith [hd,hcp,hsprod]
  have htprod := mul_le_mul_of_nonneg_left ht ha1
  have h1 : (7-6*a)*q ≤ a*w+(4*a-2)*l+(5-4*a)*c-(a-1)*(c2-b2) := by
    nlinarith [hd',htprod]
  have hcprod := mul_le_mul_of_nonneg_left hc ha5
  have h2 : (16-14*a)/3*q ≤ a*w+(4*a-2)*l+(10-8*a)/3*c1+(8-7*a)/3*c2+(a-1)*b2 := by
    nlinarith [h1,hcprod]
  have hc2prod := mul_le_mul_of_nonneg_left hc2 ha8
  have h3 : (8-7*a)/2*q ≤ a*w+(4*a-2)*l+(4-3*a)/2*c1+(a-1)*b2 := by
    nlinarith [h2,hc2prod]
  have hbnonneg : 0 ≤ b2 := Nat.cast_nonneg _
  have hbprod := mul_nonneg (show 0 ≤ (4-3*a)/2-(a-1) by linarith) hbnonneg
  have hhprod := mul_le_mul_of_nonneg_left hhalf ha4
  change (8-7*a)/2*q ≤ a*w+(4*a-2)*l+(4-3*a)*(2*P+O)
  nlinarith [h3,hbprod,hhprod]
end Paper.HighGirthCountEndpoint
#print axioms Paper.HighGirthCountEndpoint.selected_vertex_count_bounds
