module

public import SharpTailMatching.Probability.ThinningDeficit
public import SharpTailMatching.Probability.InitialExclusion
public import SharpTailMatching.Probability.Covariance
public import SharpTailMatching.Probability.Endpoints
public import SharpTailMatching.ProximityAlgebra

/-! # The unconditional comparison estimate for a maximizing law -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem failureDeficit_eq_excess (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal x) :
    failureDeficit (k-1) μ = 1-(k : ℝ)*x+normalizedExcess k μ/(k : ℝ) := by
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hmeanR : (mean μ).toReal = x := by rw [hmean,ENNReal.toReal_ofReal hx]
  have hdev := ProductBound.positive_negative_deviation
    (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) (fun i w => (w i : ℝ))
    (fun i => Integrable.of_mem_Icc 0 1
      (show Measurable (fun w : Fin k → ℝ≥0 => (w i : ℝ)) from by fun_prop).aemeasurable
      (iid_coordinate_unit_bounds k μ hsupp i))
  simp only [iid_coordinate_mean,hmeanR,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hdev
  unfold failureDeficit
  rw [Nat.sub_add_cancel hk]
  change (∫ w,max (1-iidSum k w) 0 ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = _
  change (∫ w,max (1-iidSum k w) 0 ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
    (∫ w,max (iidSum k w-1) 0 ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))+1-(k : ℝ)*x at hdev
  rw [hdev]
  unfold normalizedExcess
  field_simp
  ring

theorem support_fraction_identity {x p d : ℝ} (hx : x ≠ 0) (hp : p ≠ 0) (hd : d ≠ 0) :
    (x+x*p/d)/(x+x*p/d-x) = (d+p)/p := by
  rw [show x+x*p/d-x = x*p/d by ring]
  field_simp [hx,hp,hd]

theorem critical_maximizer_segment_proximity (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c θ a : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haeq : a = (k : ℝ)/((k : ℝ)+c))
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Q : ProbabilityMeasure ℝ≥0) (hsupp : (Q : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean Q = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k Q = ComparisonGeometry.segmentExcess t θ)
    (hmax : Maximizes k (1/((k : ℝ)+c)) (addZeroLaw Q (1-a) (sub_nonneg.mpr ha1) (by linarith))) :
    let P := addZeroLaw Q (1-a) (sub_nonneg.mpr ha1) (by linarith)
    let x := 1/((k : ℝ)+c)
    supportCutoff (k-1) x P-conditionalDeficit (k-1) P <
      (failureScale (k-1) x P-3*x)/20 := by
  let P := addZeroLaw Q (1-a) (sub_nonneg.mpr ha1) (by linarith)
  let x := 1/((k : ℝ)+c)
  let p := 1-tailProbability k P
  let p0 := (1-x)^k
  let F := tailProbability k P
  let H := tailProbability (k-1) P
  let E := normalizedExcess k P/(k : ℝ)
  let V := ComparisonGeometry.shortTailStarSum k a t θ
  let Es := ComparisonGeometry.scaledExcessStarSum k a t θ/(k : ℝ)
  let rs := ComparisonGeometry.comparisonR k a p0 t θ
  let Ms := ComparisonGeometry.comparisonM k a p0 t θ
  let r := conditionalDeficit (k-1) P
  let M := supportCutoff (k-1) x P
  let L := (t : ℝ)*((t : ℝ)-1)/(2*(k : ℝ))
  let rb := x*((t : ℝ)+c)*ComparisonGeometry.nodeFailureValue t/p0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ k := by omega
  have hx : 0 < x := by dsimp [x]; positivity
  have hax : (k : ℝ)*x = a := by rw [haeq]; dsimp [x]; ring
  have hxa : a/(k : ℝ) = x := by rw [← hax]; field_simp
  have hbasic := CriticalEstimates.critical_elementary_bounds hk hc hcross
  have halt : a < 1 := by simpa only [mul_one_div,← haeq] using hbasic.2.1
  have hxlt : x < (k : ℝ)⁻¹ := by
    apply (mul_lt_mul_iff_right₀ hkpos).mp
    rw [mul_inv_cancel₀ hkpos.ne',hax]
    exact halt
  have hmaxP : Maximizes k x P := hmax
  have hmax' : Maximizes (k-1+1) x P := by simpa only [Nat.sub_add_cancel hk1] using hmaxP
  have hxlt' : x < ((k-1+1 : ℕ) : ℝ)⁻¹ := by simpa only [Nat.sub_add_cancel hk1] using hxlt
  have hlarge := hmaxP.2 (smallBernoulliLaw k hk1 x hx.le hxlt.le) (by rw [mean_smallBernoulliLaw])
  rw [tailProbability_smallBernoulliLaw,hax] at hlarge
  have hp : 0 < p := sub_pos.mpr (tailProbability_lt_one hk1 hx.le hxlt P hmaxP.1)
  have hp0eq : p0 = 1-a^k := by
    rw [haeq]
    exact ComparisonGeometry.critical_failure_identity k hk1 c hc hcross
  have hpp : p ≤ p0 := by rw [hp0eq]; dsimp [p]; linarith only [hlarge]
  have hp0 : 0 < p0 := hp.trans_le hpp
  have hgap : 0 < F-H := by
    have h := maximizer_tail_gap_pos hx hxlt' hmax'
    simpa only [Nat.sub_add_cancel hk1] using h
  have hrM : r ≤ M := maximizer_conditionalDeficit_le_cutoff hx hxlt' hmax'
  have hD := maximizer_supportCutoff_sub_mean hx hxlt' hmax'
  have hM : M = x+x*p/(F-H) := by
    dsimp [M,supportCutoff]
    rw [Nat.sub_add_cancel hk1]
    change x*(1-H)/(F-H) = x+x*p/(F-H)
    have hid : p = 1-F := rfl
    rw [hid]
    field_simp
    ring
  have hMom := failureDeficit_eq_excess k hk1 x hx.le P
    (maximizer_no_mass_above_one hk1 hx.le hxlt hmaxP) (maximizer_mean_eq hk1 hx.le hxlt hmaxP)
  rw [hax] at hMom
  have hr : r = ((1-a)+E)/p := by
    dsimp [r,conditionalDeficit]
    rw [Nat.sub_add_cancel hk1,hMom]
  have hactual := critical_thinning_comparisons k t hk ht htk c θ a hc hcross ha ha1 haeq
    Q hsupp hmean hexcess
  change H ≤ V ∧ Es-L*V ≤ E-L*H at hactual
  have hnodes := ComparisonGeometry.critical_interpolated_proximity k t hk ht htk c θ hc hcross hθ hθ1
  dsimp at hnodes
  rw [← haeq] at hnodes
  change V < a^k ∧ a/(k : ℝ)/5 < rs-(19/20)*Ms at hnodes
  rw [hxa] at hnodes
  have hV : 0 < a^k-V := sub_pos.mpr hnodes.1
  have hMs : Ms = x+x*p0/(a^k-V) := by
    dsimp [Ms,ComparisonGeometry.comparisonM]
    rw [hxa]
  have hxMs : x < Ms := by rw [hMs]; exact lt_add_of_pos_right _ (div_pos (mul_pos hx hp0) hV)
  have hMM : M ≤ Ms := by
    rw [hM,hMs]
    apply add_le_add le_rfl
    have hden : a^k-V ≤ F-H := by dsimp [F]; linarith only [hlarge,hactual.1]
    exact (div_le_div_of_nonneg_left (mul_nonneg hx.le hp.le) hV hden).trans
      ((div_le_div_iff_of_pos_right hV).mpr (mul_le_mul_of_nonneg_left hpp hx.le))
  have hbase := ComparisonGeometry.critical_base_deficit_bounds hk ht hc hcross
  change x < rb ∧ L*x/(rb-x)^2 < 9/10 at hbase
  have hbr : rb ≤ r := critical_conditionalDeficit_lower k t hk ht c θ a hc hcross ha ha1 haeq
    hθ hθ1 Q hsupp hmean hexcess hlarge hp
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := by
    have htm : 0 ≤ (t : ℝ)-1 := by linarith
    dsimp [L]
    positivity
  have hratioM : M/(M-x) = (1-H)/p := by
    rw [hM,support_fraction_identity hx.ne' hp.ne' hgap.ne']
    congr 1
    dsimp [p,F]
    ring
  have hratioMs : Ms/(Ms-x) = (1-V)/p0 := by
    rw [hMs,support_fraction_identity hx.ne' hp0.ne' hV.ne']
    congr 1
    rw [hp0eq]
    ring
  have hrs : rs = ((1-a)+Es)/p0 := rfl
  have hNpos : 0 ≤ (1-a)+Es+L*(1-V) := by
    have hrspos : 0 < rs := by linarith only [hnodes.2,hxMs,hx]
    have hnum := (div_pos_iff_of_pos_right hp0).mp (hrs ▸ hrspos)
    have hfail : 0 ≤ 1-V := by linarith only [hp0eq,hp0,hnodes.1]
    have hmul := mul_nonneg hL hfail
    linarith only [hnum,hmul]
  have hcomp : rs+L*Ms/(Ms-x) ≤ r+L*M/(M-x) := by
    have hleft : rs+L*Ms/(Ms-x) = ((1-a)+Es+L*(1-V))/p0 := by
      rw [hrs,show L*Ms/(Ms-x) = L*(Ms/(Ms-x)) by ring,hratioMs]
      ring
    have hright : r+L*M/(M-x) = ((1-a)+E+L*(1-H))/p := by
      rw [hr,show L*M/(M-x) = L*(M/(M-x)) by ring,hratioM]
      ring
    rw [hleft,hright]
    exact (div_le_div_of_nonneg_left hNpos hp hpp).trans
      ((div_le_div_iff_of_pos_right hp).mpr (by linarith only [hactual.2]))
  have hprox := ComparisonAlgebra.mean_deficit_proximity hx hL hbase.1 hbr hrM hMM hbase.2 hcomp hnodes.2
  change M-r < (failureScale (k-1) x P-3*x)/20
  change M-x = failureScale (k-1) x P at hD
  rw [← hD]
  linarith only [hprox.2.1]

/-- The full quantitative support comparison for a genuine critical maximizer.
The only extra datum is its proved normalized representation. A nonzero
normalized excess automatically chooses a valid comparison segment. -/
theorem critical_normalized_maximizer_proximity {k : ℕ} (hk : 6 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k : ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k : ℝ)*x)^k)
    {μ Q : ProbabilityMeasure ℝ≥0} (hμ : Maximizes k x μ)
    (hrep : (μ : Measure ℝ≥0) = ENNReal.ofReal (1-(k : ℝ)*x) • Measure.dirac 0+
      ENNReal.ofReal ((k : ℝ)*x) • (Q : Measure ℝ≥0))
    (hsupp : (Q : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean Q = ENNReal.ofReal (k : ℝ)⁻¹)
    (hnonzero : normalizedExcess k Q ≠ 0) :
    supportCutoff (k-1) x μ-conditionalDeficit (k-1) μ <
      (failureScale (k-1) x μ-3*x)/20 := by
  let a := (k : ℝ)*x
  let c := x⁻¹-(k : ℝ)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 0 < a := mul_pos hkpos hx
  have halt : a < 1 := by
    simpa only [mul_inv_cancel₀ hkpos.ne'] using mul_lt_mul_of_pos_left hxlt hkpos
  let P := addZeroLaw Q (1-a) (sub_nonneg.mpr halt.le) (by linarith)
  have hμeq : μ = P := by
    apply Subtype.ext
    change (μ : Measure ℝ≥0) = ENNReal.ofReal (1-(1-a)) • (Q : Measure ℝ≥0)+
      ENNReal.ofReal (1-a) • Measure.dirac 0
    simpa only [sub_sub_cancel,add_comm] using hrep
  have hc := CriticalEstimates.critical_parameter_from_beta (by omega : 2 ≤ k) hx hxlt hcross
  change 0 < c ∧ c ≤ 1/2 ∧ CriticalEstimates.criticalDifference k c = 1 at hc
  have hden : (k : ℝ)+c = x⁻¹ := by dsimp [c]; ring
  have haeq : a = (k : ℝ)/((k : ℝ)+c) := by rw [hden,div_eq_mul_inv,inv_inv]
  have hxeq : 1/((k : ℝ)+c) = x := by rw [hden,one_div,inv_inv]
  have hratio : (1-a)/a = c/(k : ℝ) := by dsimp [a,c]; field_simp
  have hlarge := hμ.2 (smallBernoulliLaw k (by omega) x hx.le hxlt.le) (by rw [mean_smallBernoulliLaw])
  rw [tailProbability_smallBernoulliLaw,hμeq] at hlarge
  change a^k ≤ tailProbability k P at hlarge
  have hinterval := (initial_exclusion_large k hk c a hc.1.le hc.2.2 ha halt.le hratio
    Q hsupp hmean hlarge).resolve_left hnonzero
  have hbounds := normalized_excess_bounds (by omega : 1 ≤ k) Q hsupp hmean
  obtain ⟨t,θ,ht,htk,hθ,hθ1,hseg⟩ := ComparisonGeometry.exists_excess_segment k (by omega)
    (normalizedExcess k Q) hbounds.1 hinterval.2
  have ht4 : 4 ≤ t := by
    by_contra hnot
    have htu : t+1 ≤ 4 := by omega
    have h01 := ComparisonGeometry.maxExcessNode_strictMono ht (show 1 ≤ t+1 by omega) (Nat.lt_succ_self t)
    have h14 := ComparisonGeometry.maxExcessNode_strictMono.monotoneOn
      (show 1 ≤ t+1 by omega) (show 1 ≤ 4 by omega) htu
    have hmul := mul_le_mul_of_nonneg_left h01.le (sub_nonneg.mpr hθ1)
    have hsegub : ComparisonGeometry.segmentExcess t θ ≤ ComparisonGeometry.maxExcessNode (t+1) := by
      unfold ComparisonGeometry.segmentExcess
      nlinarith only [hmul]
    rw [← hseg] at hsegub
    exact (not_lt_of_ge (hsegub.trans h14)) hinterval.1
  have hmaxP : Maximizes k (1/((k : ℝ)+c)) P := by rw [hxeq,← hμeq]; exact hμ
  have hprox := critical_maximizer_segment_proximity k t hk ht4 htk c θ a hc.1.le hc.2.2
    ha halt.le haeq hθ hθ1 Q hsupp hmean hseg hmaxP
  change supportCutoff (k-1) (1/((k : ℝ)+c)) P-conditionalDeficit (k-1) P <
    (failureScale (k-1) (1/((k : ℝ)+c)) P-3*(1/((k : ℝ)+c)))/20 at hprox
  rw [hxeq,← hμeq] at hprox
  exact hprox

end SharpTailMatching.Probability
