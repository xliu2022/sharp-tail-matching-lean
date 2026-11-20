module

public import SharpTailMatching.Probability.WeightedThinning
public import SharpTailMatching.Probability.BaseDeficitBounds

/-! # A direct lower bound for the deficit under binomial thinning -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def selectorWeight {ι : Type*} (T S : Finset ι) (a : ℝ) : ℝ :=
  a^S.card*(1-a)^(T.card-S.card)

theorem selector_weight_moments {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (a : ℝ) (y : ι → ℝ) :
    (∑ S ∈ T.powerset,selectorWeight T S a) = 1 ∧
    (∑ S ∈ T.powerset,selectorWeight T S a*(∑ i ∈ S,y i)) = a*(∑ i ∈ T,y i) := by
  induction T using Finset.induction_on with
  | empty => simp [selectorWeight]
  | @insert i T hi ih =>
    have hnot (S : Finset ι) (hS : S ∈ T.powerset) : i ∉ S :=
      fun his => hi ((Finset.mem_powerset.mp hS) his)
    have hcard (S : Finset ι) (hS : S ∈ T.powerset) : S.card ≤ T.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hS)
    have hno (S : Finset ι) (hS : S ∈ T.powerset) :
        selectorWeight (insert i T) S a = (1-a)*selectorWeight T S a := by
      unfold selectorWeight
      rw [Finset.card_insert_of_notMem hi,show T.card+1-S.card = (T.card-S.card)+1 by
        have := hcard S hS; omega,pow_succ]
      ring
    have hyes (S : Finset ι) (hS : S ∈ T.powerset) :
        selectorWeight (insert i T) (insert i S) a = a*selectorWeight T S a := by
      unfold selectorWeight
      rw [Finset.card_insert_of_notMem hi,Finset.card_insert_of_notMem (hnot S hS),
        Nat.add_sub_add_right,pow_succ]
      ring
    constructor
    · rw [Finset.sum_powerset_insert hi]
      have h0 : (∑ S ∈ T.powerset,selectorWeight (insert i T) S a) =
          (1-a)*(∑ S ∈ T.powerset,selectorWeight T S a) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hno
      have h1 : (∑ S ∈ T.powerset,selectorWeight (insert i T) (insert i S) a) =
          a*(∑ S ∈ T.powerset,selectorWeight T S a) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hyes
      rw [h0,h1,ih.1]
      ring
    · rw [Finset.sum_powerset_insert hi]
      have h0 : (∑ S ∈ T.powerset,selectorWeight (insert i T) S a*(∑ j ∈ S,y j)) =
          (1-a)*(∑ S ∈ T.powerset,selectorWeight T S a*(∑ j ∈ S,y j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [hno S hS]
        ring
      have h1 : (∑ S ∈ T.powerset,selectorWeight (insert i T) (insert i S) a*(∑ j ∈ insert i S,y j)) =
          a*y i*(∑ S ∈ T.powerset,selectorWeight T S a)+
            a*(∑ S ∈ T.powerset,selectorWeight T S a*(∑ j ∈ S,y j)) := by
        rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        rw [hyes S hS,Finset.sum_insert (hnot S hS)]
        ring
      rw [h0,h1,ih.1,ih.2,Finset.sum_insert hi]
      ring

def selectedPoint (k : ℕ) (S : Finset (Fin k)) (w : Fin k → ℝ≥0) : Fin k → ℝ≥0 :=
  fun i => if i ∈ S then w i else 0

theorem selectedPoint_measurable (k : ℕ) (S : Finset (Fin k)) : Measurable (selectedPoint k S) := by
  classical
  apply Measurable.of_eval
  intro i
  unfold selectedPoint
  split_ifs <;> fun_prop

theorem selectedPoint_sum (k : ℕ) (S : Finset (Fin k)) (w : Fin k → ℝ≥0) :
    iidSum k (selectedPoint k S w) = ∑ i ∈ S,(w i : ℝ) := by
  classical
  have hf : (fun i => (selectedPoint k S w i : ℝ)) =
      (fun i => if i ∈ S then (w i : ℝ) else 0) := by
    funext i
    unfold selectedPoint
    split_ifs <;> rfl
  unfold iidSum
  rw [hf]
  simpa only [Finset.univ_inter] using Finset.sum_ite_mem Finset.univ S (fun i => (w i : ℝ))

theorem selectedPoint_map (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) (S : Finset (Fin k)) :
    (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))).map (selectedPoint k S) =
      Measure.pi (selectedMeasure k (μ : Measure ℝ≥0) S) := by
  classical
  let f (i : Fin k) (z : ℝ≥0) := if i ∈ S then z else 0
  have hf (i : Fin k) : Measurable (f i) := by dsimp [f]; split_ifs <;> fun_prop
  have heq (i : Fin k) : (μ : Measure ℝ≥0).map (f i) = selectedMeasure k (μ : Measure ℝ≥0) S i := by
    by_cases hi : i ∈ S
    · simp [f,selectedMeasure,hi]
    · simp [f,selectedMeasure,hi,Measure.map_const]
  have h := Measure.pi_map_pi (μ := fun _ : Fin k => (μ : Measure ℝ≥0)) (f := f)
    (fun i => (hf i).aemeasurable)
  unfold selectedPoint
  simpa only [heq,f] using h

def sumDeficit (k : ℕ) (w : Fin k → ℝ≥0) : ℝ := max (1-iidSum k w) 0

theorem sumDeficit_measurable (k : ℕ) : Measurable (sumDeficit k) := by
  unfold sumDeficit iidSum
  fun_prop

theorem sumDeficit_bounds (k : ℕ) (w : Fin k → ℝ≥0) :
    0 ≤ sumDeficit k w ∧ sumDeficit k w ≤ 1 := by
  exact ⟨le_max_right _ _,max_le (by have := iidSum_nonneg k w; linarith) (by norm_num)⟩

theorem sumDeficit_integrable (k : ℕ) (ν : Measure (Fin k → ℝ≥0)) [IsFiniteMeasure ν] :
    Integrable (sumDeficit k) ν := by
  apply Integrable.of_bound (sumDeficit_measurable k).aestronglyMeasurable 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs,abs_of_nonneg (sumDeficit_bounds k w).1]
  exact (sumDeficit_bounds k w).2

theorem selectedDeficit_integrable (k : ℕ) (S : Finset (Fin k))
    (ν : Measure (Fin k → ℝ≥0)) [IsFiniteMeasure ν] :
    Integrable (fun w => sumDeficit k (selectedPoint k S w)) ν := by
  apply Integrable.of_bound ((sumDeficit_measurable k).comp (selectedPoint_measurable k S)).aestronglyMeasurable 1
  filter_upwards [] with w
  simp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_nonneg (sumDeficit_bounds k _).1]
  exact (sumDeficit_bounds k _).2

theorem integral_thinning_deficit_expansion (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ w,sumDeficit k w ∂Measure.pi (fun _ : Fin k =>
      (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith) : Measure ℝ≥0))) =
    ∫ w,(∑ S : Finset (Fin k),selectorWeight Finset.univ S a*sumDeficit k (selectedPoint k S w))
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)) := by
  classical
  have hmeasure : (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith) : Measure ℝ≥0) =
      ENNReal.ofReal a • (μ : Measure ℝ≥0)+ENNReal.ofReal (1-a) • Measure.dirac 0 := by
    change ENNReal.ofReal (1-(1-a)) • _+_ = _
    rw [show 1-(1-a) = a by ring]
  simp_rw [hmeasure]
  rw [pi_binary_expansion k (μ : Measure ℝ≥0) _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    integral_finsetSum_measure]
  · simp only [integral_smul_measure,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal (sub_nonneg.mpr ha1),smul_eq_mul]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro S _
      rw [integral_const_mul]
      have hmap := integral_map (μ := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
        (selectedPoint_measurable k S).aemeasurable
        (sumDeficit_measurable k).aestronglyMeasurable
      rw [selectedPoint_map k μ S] at hmap
      rw [← hmap]
      simp only [selectorWeight,Finset.card_univ,Fintype.card_fin]
    · intro S _
      exact (selectedDeficit_integrable k S _).const_mul _
  · intro S _
    exact (sumDeficit_integrable k _).smul_measure (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

theorem selector_deficit_lower (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (w : Fin k → ℝ≥0) :
    (1-a)*({z | iidSum k z < 1}.indicator (fun _ => (1 : ℝ))) w+a*sumDeficit k w ≤
      ∑ S : Finset (Fin k),selectorWeight Finset.univ S a*sumDeficit k (selectedPoint k S w) := by
  classical
  have hm := selector_weight_moments (Finset.univ : Finset (Fin k)) a (fun i => (w i : ℝ))
  simp only [Finset.powerset_univ] at hm
  have hwgt (S : Finset (Fin k)) : 0 ≤ selectorWeight Finset.univ S a := by
    unfold selectorWeight
    exact mul_nonneg (pow_nonneg ha _) (pow_nonneg (sub_nonneg.mpr ha1) _)
  by_cases hw : iidSum k w < 1
  · have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin k))))
      (fun S _ => mul_le_mul_of_nonneg_left
        (le_max_left (1-iidSum k (selectedPoint k S w)) 0) (hwgt S))
    have hid : (∑ S : Finset (Fin k),selectorWeight Finset.univ S a*(1-iidSum k (selectedPoint k S w))) =
        1-a*iidSum k w := by
      simp_rw [selectedPoint_sum,mul_sub,mul_one]
      rw [Finset.sum_sub_distrib,hm.1,hm.2]
      rfl
    rw [hid] at hsum
    rw [Set.indicator_of_mem (show w ∈ {z | iidSum k z < 1} from hw)]
    simp only [sumDeficit,max_eq_left (by linarith : 0 ≤ 1-iidSum k w),mul_one]
    linarith only [hsum]
  · rw [Set.indicator_of_notMem (show w ∉ {z | iidSum k z < 1} from hw)]
    simp only [sumDeficit,max_eq_right (by linarith : 1-iidSum k w ≤ 0),
      mul_zero,add_zero]
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hwgt S) (le_max_right _ _))

theorem iid_failure_indicator_integral (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ w,({z | iidSum k z < 1}.indicator (fun _ => (1 : ℝ))) w
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = 1-tailProbability k μ := by
  have hset : MeasurableSet {w : Fin k → ℝ≥0 | iidSum k w < 1} := by
    unfold iidSum
    measurability
  rw [integral_indicator_const (1 : ℝ) hset,smul_eq_mul,mul_one]
  have hevent : {w : Fin k → ℝ≥0 | iidSum k w < 1} = {w : Fin k → ℝ≥0 | ∑ i,w i < 1} := by
    ext w
    simp only [Set.mem_ofPred_eq,iidSum,← NNReal.coe_sum]
    exact_mod_cast (Iff.rfl : (∑ i,w i) < 1 ↔ (∑ i,w i) < 1)
  rw [hevent]
  exact failure_toReal_eq_one_sub_tail k μ

theorem thinning_deficit_lower (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1-a)*(1-tailProbability k μ)+a*(∫ w,sumDeficit k w
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) ≤
    ∫ w,sumDeficit k w ∂Measure.pi (fun _ : Fin k =>
      (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith) : Measure ℝ≥0)) := by
  classical
  let ν := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))
  have hset : MeasurableSet {w : Fin k → ℝ≥0 | iidSum k w < 1} := by
    unfold iidSum
    measurability
  have hind : Integrable ({w | iidSum k w < 1}.indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const _).indicator hset
  have hlower := integral_mono ((hind.const_mul (1-a)).add ((sumDeficit_integrable k ν).const_mul a))
    (integrable_finsetSum Finset.univ (fun S _ => (selectedDeficit_integrable k S ν).const_mul _))
    (selector_deficit_lower k a ha ha1)
  simp only [Pi.add_apply] at hlower
  rw [integral_add (hind.const_mul (1-a)) ((sumDeficit_integrable k ν).const_mul a),
    integral_const_mul,integral_const_mul] at hlower
  change (1-a)*(∫ w,({z | iidSum k z < 1}.indicator (fun _ => (1 : ℝ))) w ∂ν)+_ ≤ _ at hlower
  rw [iid_failure_indicator_integral k μ] at hlower
  rw [integral_thinning_deficit_expansion k μ a ha ha1]
  exact hlower

theorem normalized_thinning_deficit_lower (k : ℕ) (hk : 1 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1-a)*(1-tailProbability k μ)+(a/(k : ℝ))*normalizedExcess k μ ≤
      failureDeficit (k-1) (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) := by
  have h := thinning_deficit_lower k μ a ha ha1
  have hdev := partialExcess_deviation k k (by omega) le_rfl μ hsupp hmean
  rw [Nat.sub_self,Nat.cast_zero,zero_add,partialExcess_last] at hdev
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hnorm : (a/(k : ℝ))*normalizedExcess k μ =
      a*(∫ w,sumDeficit k w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) := by
    rw [← hdev]
    unfold sumDeficit
    field_simp
  rw [hnorm]
  unfold failureDeficit
  rw [Nat.sub_add_cancel hk]
  simpa only [sumDeficit] using h

namespace ComparisonGeometry

theorem nodeFailureValue_mono {t u : ℕ} (ht : 2 ≤ t) (htu : t ≤ u) :
    nodeFailureValue t ≤ nodeFailureValue u := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast (show 2 ≤ u by omega)
  have hmono := zero_nodePower_strictMono.monotoneOn
    (show (t : ℝ) ∈ Set.Ioi 1 by change 1 < (t : ℝ); linarith)
    (show (u : ℝ) ∈ Set.Ioi 1 by change 1 < (u : ℝ); linarith) (by exact_mod_cast htu)
  have htn := nodePowerNat_eq_real 0 t (by omega) (by omega)
  have hun := nodePowerNat_eq_real 0 u (by omega) (by omega)
  simp only [Nat.cast_zero] at htn hun
  rw [← htn,← hun] at hmono
  simpa only [nodePowerNat,Nat.sub_zero,nodeFailureValue] using hmono

theorem failureCurve_segment_lower (t : ℕ) (ht : 2 ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    nodeFailureValue t ≤ EnvelopeAlgebra.failureCurve (t : ℝ) t (segmentExcess t θ) := by
  have hconc := (EnvelopeAlgebra.failureCurve_strictConcave (t : ℝ) t
    (by exact_mod_cast (show 0 < t by omega)) (by omega)).concaveOn.2
    (maxExcessNode_nonneg t (by omega)) (maxExcessNode_nonneg (t+1) (by omega))
    (sub_nonneg.mpr hθ1) hθ (by ring : 1-θ+θ = 1)
  simp only [smul_eq_mul,failureCurve_maxExcess_left t (by omega),
    failureCurve_maxExcess_right t (by omega)] at hconc
  change (1-θ)*nodeFailureValue t+θ*nodeFailureValue (t+1) ≤
    EnvelopeAlgebra.failureCurve (t : ℝ) t (segmentExcess t θ) at hconc
  have hmono := mul_le_mul_of_nonneg_left (nodeFailureValue_mono ht (Nat.le_succ t)) hθ
  linarith

theorem segmentExcess_ge_left (t : ℕ) (ht : 1 ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    maxExcessNode t ≤ segmentExcess t θ := by
  have hmono := maxExcessNode_strictMono ht (show 1 ≤ t+1 by omega) (Nat.lt_succ_self t)
  have hmul := mul_le_mul_of_nonneg_left hmono.le hθ
  unfold segmentExcess
  linarith

end ComparisonGeometry

theorem critical_conditionalDeficit_lower (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t)
    (c θ a : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haeq : a = (k : ℝ)/((k : ℝ)+c))
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ)
    (hF : a^k ≤ tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)))
    (hp : 0 < 1-tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith))) :
    (1/((k : ℝ)+c))*((t : ℝ)+c)*ComparisonGeometry.nodeFailureValue t/
      ((1-1/((k : ℝ)+c))^k) ≤
      conditionalDeficit (k-1) (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) := by
  let P := addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)
  let x := 1/((k : ℝ)+c)
  let p0 := (1-x)^k
  let H := ComparisonGeometry.nodeFailureValue t
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxrel : a/(k : ℝ) = x := by rw [haeq]; dsimp [x]; field_simp
  have hdrel : 1-a = c*x := by rw [haeq]; dsimp [x]; field_simp; ring
  have hp0eq : p0 = 1-a^k := by
    rw [haeq]
    exact ComparisonGeometry.critical_failure_identity k (by omega) c hc hcross
  have hpp : 1-tailProbability k P ≤ p0 := by rw [hp0eq]; linarith only [hF]
  have hp0 : 0 < p0 := hp.trans_le hpp
  have hnode := ComparisonGeometry.failureCurve_segment_lower t (by omega) θ hθ hθ1
  have hbranch := normalized_failure_branch k t (by omega) (by omega) μ hsupp hmean
  rw [hexcess] at hbranch
  have hfail : H ≤ 1-tailProbability k μ := hnode.trans hbranch
  have hw := ComparisonGeometry.segmentExcess_ge_left t (by omega) θ hθ
  have hwreal : (t : ℝ)*H ≤ normalizedExcess k μ := by
    rw [hexcess]
    simpa only [ComparisonGeometry.maxExcessNode,ComparisonGeometry.nodeExcessNat,
      Nat.cast_zero,neg_zero,zero_add,ComparisonGeometry.nodePowerNat,Nat.sub_zero,H,
      ComparisonGeometry.nodeFailureValue] using hw
  have hdef := normalized_thinning_deficit_lower k (by omega) μ hsupp hmean a ha.le ha1
  rw [hxrel] at hdef
  change (1-a)*(1-tailProbability k μ)+x*normalizedExcess k μ ≤ failureDeficit (k-1) P at hdef
  have h1 := mul_le_mul_of_nonneg_left hfail (sub_nonneg.mpr ha1)
  have h2 := mul_le_mul_of_nonneg_left hwreal hx.le
  have hnum : x*((t : ℝ)+c)*H ≤ failureDeficit (k-1) P := by
    rw [hdrel] at h1 hdef
    nlinarith only [h1,h2,hdef]
  have hH : 0 ≤ H := by
    dsimp [H,ComparisonGeometry.nodeFailureValue]
    have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := by linarith
    exact pow_nonneg (sub_nonneg.mpr ((div_le_one htpos).mpr (by linarith))) _
  have hnumpos : 0 ≤ x*((t : ℝ)+c)*H := by positivity
  change x*((t : ℝ)+c)*H/p0 ≤ conditionalDeficit (k-1) P
  unfold conditionalDeficit
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)]
  exact (div_le_div_of_nonneg_left hnumpos hp hpp).trans ((div_le_div_iff_of_pos_right hp).mpr hnum)

end SharpTailMatching.Probability
