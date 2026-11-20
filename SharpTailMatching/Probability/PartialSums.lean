module

public import SharpTailMatching.Probability.EnvelopeSupport
public import SharpTailMatching.Probability.EndpointRigidity

/-! # The comparison envelopes for the actual iid partial sums -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def partialExcess (k j : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  (k : ℝ)*(∫ w : Fin j → ℝ≥0, max (iidSum j w-1) 0
    ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0)))

theorem iid_coordinate_mean (j : ℕ) (μ : ProbabilityMeasure ℝ≥0) (i : Fin j) :
    (∫ w : Fin j → ℝ≥0, (w i : ℝ) ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) =
      (mean μ).toReal := by
  have h := integral_map (μ := Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0)))
    (f := fun z : ℝ≥0 => (z : ℝ)) (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [(measurePreserving_eval (fun _ : Fin j => (μ : Measure ℝ≥0)) i).map_eq] at h
  exact h.symm.trans (integral_coe_eq_mean_toReal μ)

theorem iid_coordinate_unit_bounds (j : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) (i : Fin j) :
    ∀ᵐ w ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0)),
      0 ≤ (w i : ℝ) ∧ (w i : ℝ) ≤ 1 := by
  filter_upwards [(Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin j => (μ : Measure ℝ≥0)) (i := i)).eventually
    (unit_supported_ae_le_one μ hsupp)] with w hw
  exact ⟨(w i).coe_nonneg,by exact_mod_cast hw⟩

theorem iid_failure_eq_one_sub_tail (j : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    ProductBound.failureProbability (Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0)))
      (fun i w => (w i : ℝ)) = 1-tailProbability j μ := by
  rw [ProductBound.failureProbability_eq_measure]
  · have hevent : {w : Fin j → ℝ≥0 | ProductBound.total (fun i w => (w i : ℝ)) w < 1} =
        {w : Fin j → ℝ≥0 | (∑ i,w i) < 1} := by
      ext w
      simp only [Set.mem_ofPred_eq,ProductBound.total]
      exact_mod_cast (Iff.rfl : (∑ i,w i) < 1 ↔ (∑ i,w i) < 1)
    rw [hevent]
    exact failure_toReal_eq_one_sub_tail j μ
  · intro i
    fun_prop

theorem partialExcess_deviation (k j : ℕ) (hk : 0 < k) (hjk : j ≤ k)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    (k : ℝ)*(∫ w : Fin j → ℝ≥0, max (1-iidSum j w) 0
      ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) =
        (k-j : ℕ)+partialExcess k j μ := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
  have hmeanR : (mean μ).toReal = (k : ℝ)⁻¹ := by rw [hmean,ENNReal.toReal_ofReal (by positivity)]
  have hdev := ProductBound.positive_negative_deviation
    (Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) (fun i w => (w i : ℝ))
    (fun i => Integrable.of_mem_Icc 0 1
      (show Measurable (fun w : Fin j → ℝ≥0 => (w i : ℝ)) from by fun_prop).aemeasurable
      (iid_coordinate_unit_bounds j μ hsupp i))
  simp only [iid_coordinate_mean,hmeanR,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hdev
  change (∫ w, max (1-iidSum j w) 0 ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) =
    (∫ w, max (iidSum j w-1) 0 ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) +
      1-(j : ℝ)*(k : ℝ)⁻¹ at hdev
  rw [hdev,partialExcess,Nat.cast_sub hjk]
  field_simp
  ring

theorem partialExcess_bounds (k j : ℕ) (hk : 0 < k) (hjk : j ≤ k)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    0 ≤ partialExcess k j μ ∧
      partialExcess k j μ ≤ ComparisonGeometry.nodeExcessNat (k-j) k := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => le_max_right _ _))
  · have h := mul_le_mul_of_nonneg_left (unit_supported_deficit_product_bound j μ hsupp)
      (Nat.cast_nonneg k)
    rw [partialExcess_deviation k j hk hjk μ hsupp hmean,hmean,
      ENNReal.toReal_ofReal (by positivity)] at h
    unfold ComparisonGeometry.nodeExcessNat ComparisonGeometry.nodePowerNat
    rw [Nat.sub_sub_self hjk]
    simp only [one_div]
    linarith

theorem partial_success_envelope (k j t : ℕ) (hk : 0 < k) (hj : 0 < j)
    (hjk : j ≤ k) (ht : k-j < t) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    tailProbability j μ ≤ EnvelopeAlgebra.successCurve (t : ℝ) (t-(k-j))
      ((k-j : ℕ)+partialExcess k j μ) := by
  have h := ProductBound.normalized_partial_success_envelope
    (Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) k j t hk hj hjk ht
    (fun i w => (w i : ℝ)) (fun _ => by fun_prop)
    (iIndepFun_pi (fun _ => by fun_prop)) 1 (by norm_num)
    (iid_coordinate_unit_bounds j μ hsupp)
    (fun i => by rw [iid_coordinate_mean,hmean,ENNReal.toReal_ofReal (by positivity)])
  rw [iid_failure_eq_one_sub_tail] at h
  have hid : ProductBound.scaledExcess (Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) k
      (fun i w => (w i : ℝ)) = partialExcess k j μ := rfl
  rw [hid] at h
  linarith

theorem partial_star_slope_bound (k j t : ℕ) (hj : 0 < j) (hjk : j < k)
    (ht : k-j < t) (htk : t < k) (θ : ℝ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    tailProbability j μ-ComparisonGeometry.tailStar k j t θ ≤
      ComparisonGeometry.chordSlope (k-j : ℕ) t (t+1 : ℕ)*
        (partialExcess k j μ-ComparisonGeometry.excessStar k j t θ) := by
  have hk : 0 < k := by omega
  have hbounds := partialExcess_bounds k j hk hjk.le μ hsupp hmean
  exact ComparisonGeometry.envelope_star_slope_bound k j t hjk ht htk _ _ θ hbounds.1 hbounds.2
    (fun s hs _ => partial_success_envelope k j s hk hj hjk.le hs μ hsupp hmean)

theorem partialExcess_last (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    partialExcess k k μ = normalizedExcess k μ := rfl

theorem partialExcess_one (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) : partialExcess k 1 μ = 0 := by
  have hzero : (fun w : Fin 1 → ℝ≥0 => max (iidSum 1 w-1) 0) =ᵐ[
      Measure.pi (fun _ : Fin 1 => (μ : Measure ℝ≥0))] 0 := by
    filter_upwards [iid_coordinate_unit_bounds 1 μ hsupp 0] with w hw
    simp only [iidSum,Fin.sum_univ_one,Pi.zero_apply]
    exact max_eq_right (by linarith [hw.2])
  unfold partialExcess
  rw [integral_congr_ae hzero]
  simp only [Pi.zero_apply,integral_zero,mul_zero]

theorem iid_tail_integral (j : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ w : Fin j → ℝ≥0, (if 1 ≤ iidSum j w then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) = tailProbability j μ := by
  have hA : MeasurableSet {w : Fin j → ℝ≥0 | 1 ≤ iidSum j w} := by
    unfold iidSum
    measurability
  have hfun : (fun w : Fin j → ℝ≥0 => if 1 ≤ iidSum j w then (1 : ℝ) else 0) =
      ({w : Fin j → ℝ≥0 | 1 ≤ iidSum j w} : Set (Fin j → ℝ≥0)).indicator (fun _ => (1 : ℝ)) := rfl
  rw [hfun]
  have hval : (∫ w, ({w : Fin j → ℝ≥0 | 1 ≤ iidSum j w} : Set (Fin j → ℝ≥0)).indicator
      (fun _ => (1 : ℝ)) w ∂Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) =
      (Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))).real {w | 1 ≤ iidSum j w} := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const
      (μ := Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))) (1 : ℝ) hA
  rw [hval]
  have hevent : {w : Fin j → ℝ≥0 | 1 ≤ iidSum j w} = {w : Fin j → ℝ≥0 | 1 ≤ ∑ i,w i} := by
    ext w
    simp only [Set.mem_ofPred_eq,iidSum]
    exact_mod_cast (Iff.rfl : 1 ≤ (∑ i,w i) ↔ 1 ≤ (∑ i,w i))
  rw [hevent]
  rfl

/-- Adding one independent sample increases the scaled excess by at least
the preceding success probability. This is the recurrence used in the
weighted telescoping argument. -/
theorem partialExcess_rec (k j : ℕ) (hk : 0 < k) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    partialExcess k j μ+tailProbability j μ ≤ partialExcess k (j+1) μ := by
  let ν : Measure (Fin j → ℝ≥0) := Measure.pi (fun _ : Fin j => (μ : Measure ℝ≥0))
  let ν' : Measure (Fin (j+1) → ℝ≥0) := Measure.pi (fun _ : Fin (j+1) => (μ : Measure ℝ≥0))
  have hfamily : (Fin.cons (μ : Measure ℝ≥0) (fun _ : Fin j => (μ : Measure ℝ≥0))) =
      (fun _ : Fin (j+1) => (μ : Measure ℝ≥0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hmap : ((μ : Measure ℝ≥0).prod ν).map
      (fun p : ℝ≥0 × (Fin j → ℝ≥0) => Fin.cons p.1 p.2) = ν' := by
    simpa only [ν,ν',hfamily] using pi_cons_map j (μ : Measure ℝ≥0)
      (fun _ : Fin j => (μ : Measure ℝ≥0))
  have hmp : MeasurePreserving (fun p : ℝ≥0 × (Fin j → ℝ≥0) => Fin.cons p.1 p.2)
      ((μ : Measure ℝ≥0).prod ν) ν' := ⟨by fun_prop,hmap⟩
  have hsum (p : ℝ≥0 × (Fin j → ℝ≥0)) :
      iidSum (j+1) (Fin.cons p.1 p.2) = (p.1 : ℝ)+iidSum j p.2 := by
    simp [iidSum,Fin.sum_univ_succ]
  have hE : Integrable (fun w => max (iidSum j w-1) 0) ν :=
    (((unit_supported_iidSum_memLp j μ hsupp 1).integrable (by norm_num)).sub (integrable_const 1)).pos_part
  have hE' : Integrable (fun w => max (iidSum (j+1) w-1) 0) ν' :=
    (((unit_supported_iidSum_memLp (j+1) μ hsupp 1).integrable (by norm_num)).sub
      (integrable_const 1)).pos_part
  have hEprod : Integrable (fun p : ℝ≥0 × (Fin j → ℝ≥0) =>
      max ((p.1 : ℝ)+iidSum j p.2-1) 0) ((μ : Measure ℝ≥0).prod ν) := by
    simpa only [Function.comp_def,hsum] using hmp.integrable_comp_of_integrable hE'
  have hInt : (∫ w, max (iidSum (j+1) w-1) 0 ∂ν') =
      ∫ p : ℝ≥0 × (Fin j → ℝ≥0), max ((p.1 : ℝ)+iidSum j p.2-1) 0
        ∂((μ : Measure ℝ≥0).prod ν) := by
    rw [← hmap,integral_map (by fun_prop)
      (by rw [hmap]; exact hE'.aestronglyMeasurable)]
    simp only [hsum]
  let I : (Fin j → ℝ≥0) → ℝ := fun w => if 1 ≤ iidSum j w then 1 else 0
  have hI : Integrable I ν := by
    have hA : MeasurableSet {w : Fin j → ℝ≥0 | 1 ≤ iidSum j w} := by
      unfold iidSum
      measurability
    exact (integrable_const (1 : ℝ)).indicator hA
  have hY := (unit_supported_memLp μ hsupp 1).integrable (by norm_num)
  have hle := integral_mono ((hE.comp_snd (μ : Measure ℝ≥0)).add (hY.mul_prod hI)) hEprod
    (show (fun p : ℝ≥0 × (Fin j → ℝ≥0) => max (iidSum j p.2-1) 0+(p.1 : ℝ)*I p.2) ≤
      (fun p => max ((p.1 : ℝ)+iidSum j p.2-1) 0) from by
      intro p
      dsimp [I]
      by_cases hp : 1 ≤ iidSum j p.2
      · rw [ite_eq_left hp,max_eq_left (by linarith : 0 ≤ iidSum j p.2-1),mul_one]
        linarith [le_max_left ((p.1 : ℝ)+iidSum j p.2-1) 0]
      · rw [ite_eq_right hp,max_eq_right (by linarith : iidSum j p.2-1 ≤ 0),mul_zero,add_zero]
        exact le_max_right _ _)
  simp only [Pi.add_apply] at hle
  rw [integral_add (hE.comp_snd (μ : Measure ℝ≥0)) (hY.mul_prod hI),
    integral_fun_snd (fun w => max (iidSum j w-1) 0),
    probReal_univ,one_smul,integral_prod_mul (fun z : ℝ≥0 => (z : ℝ)) I,
    integral_coe_eq_mean_toReal,← hInt] at hle
  have hIval : (∫ w,I w ∂ν) = tailProbability j μ := iid_tail_integral j μ
  rw [hIval,hmean,ENNReal.toReal_ofReal (by positivity)] at hle
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
  have hscaled := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k)
  have hid : (k : ℝ)*((∫ w,max (iidSum j w-1) 0 ∂ν)+(k : ℝ)⁻¹*tailProbability j μ) =
      partialExcess k j μ+tailProbability j μ := by
    unfold partialExcess
    dsimp [ν]
    field_simp
  rw [hid] at hscaled
  exact hscaled

end SharpTailMatching.Probability
